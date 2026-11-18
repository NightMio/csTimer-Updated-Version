"use strict";

var scrHinter = execMain(function(CubieCube) {
	var rawScr = [];
	var rawScrTxt = null;
	var genState = null;
	var genScr = null;
	var scrState = new CubieCube();
	var preConj = 0;
	var rawScrValid = true;

	function setScramble(scramble) {
		rawScrTxt = scramble;
		scramble = cubeutil.getConjMoves(scramble);
		var scr = cubeutil.parseScramble(scramble, "URFDLB");
		rawScr = scr.slice();
		genState = null;
		genScr = null;
		rawScrValid = true;

		scrState = new mathlib.CubieCube();
		for (var i = 0; i < scr.length; i++) {
			var m = scr[i][0] * 3 + scr[i][2] - 1;
			if (m < 0 || m >= 18) { //TODO wide move convert
				rawScrValid = false;
				continue;
			}
			scrState.selfMoveStr('URFDLB'.charAt(scr[i][0]) + " 2'".charAt(scr[i][2] - 1));
		}
	}

	function checkInSeq(state, gen, seq, puzzle) {
		var c = new CubieCube();
		var d = new CubieCube();
		if (gen) {
			c.init(gen.ca, gen.ea);
		}
		var is222 = puzzle == '222';
		var next = 99;
		if (cubeutil.cubiesMatch(c, state, is222)) {
			next = 0;
		}
		var pow;
		for (var i = 0; i < seq.length; i++) {
			var a = seq[i][0] * 3;
			if (seq[i][0] < 0 || seq[i][0] > 5) {
				return null;
			}
			for (pow = 0; pow < 3; pow++) {
				CubieCube.CubeMult(c, CubieCube.moveCube[a + pow], d);
				if (cubeutil.cubiesMatch(d, state, is222)) {
					next = (pow == seq[i][2] - 1) ? i + 1 : i;
					break;
				}
			}
			if (next == i) {
				break;
			}
			var m = seq[i][0] * 3 + seq[i][2] - 1;
			if (m < 0 || m >= 18) {
				return null;
			}
			CubieCube.CubeMult(c, CubieCube.moveCube[m], d);
			c.init(d.ca, d.ea);
		}
		if (next == 99) {
			return null;
		}
		var ret = [];
		for (var i = 0; i < seq.length; i++) {
			var m = seq[i];
			if (next == 0 && i == 0) {
				m = [m[0], m[1], (m[2] - pow + 7) % 4];
			}
			if (i == next) ret.push(':');
			ret.push('URFDLB'.charAt(m[0]) + [null, "", "2", "'"][m[2]]);
			if (i == next) ret.push(':');
		}
		ret = ret.join(' ');
		ret = cubeutil.getConjMoves(ret, true);
		return ret;
	}

	function checkState(state, puzzle) {
		if (!rawScrTxt || !rawScrValid || !giikerutil.isConnected()
				|| tools.getCurPuzzle() != puzzle || timer.getCurTime() != 0 || timer.status() > 0) {
			return;
		}
		var toMoveFix = null;
		var toMoveRaw = null;
		if (genState) {
			toMoveFix = checkInSeq(state, genState, genScr, puzzle);
		}
		if (toMoveFix == null || toMoveFix.indexOf(':') == -1) {
			toMoveRaw = checkInSeq(state, null, rawScr, puzzle);
			genState = null;
			toMoveFix = null;
		}
		if (toMoveRaw == null && toMoveFix == null) {
			genState = new CubieCube();
			genState.init(state.ca, state.ea);
			var stateInv = new CubieCube();
			stateInv.invFrom(state);
			var toSolve = new CubieCube();
			CubieCube.CubeMult(stateInv, scrState, toSolve);
			genScr = scramble_333.genFacelet(toSolve.toFaceCube());
			genScr = cubeutil.parseScramble(genScr, "URFDLB");
			toMoveFix = checkInSeq(state, genState, genScr, puzzle);
		}
		if (toMoveFix == null && toMoveRaw == null) {
			return;
		}
		var toMove = toMoveFix ? scrambleToHtml(toMoveFix) : scrambleToHtml(toMoveRaw);
		kernel.pushSignal('scrfix', toMove);
	}

	function scramblePartToHtml(part, cssClass) {
		return part && $.map(part.split(' '), function (move) { return move && ("<span class='" + cssClass + "'>" + move.trim() + "</span>") }).join('');
	}

	function scrambleToHtml(scrTxt) {
		var scrHtml = "";
		var isScrambled = scrTxt.indexOf(':') == -1;
		var scrParts = $.map(scrTxt.split(':', 3), function (part) { return part.trim() });
		if (isScrambled) {
			scrHtml += scramblePartToHtml(scrParts[0], 'smrtScrAct');
			scrHtml += "<span class='smrtScrMrk'>&#x2713;</span>";
		} else {
			scrHtml += scramblePartToHtml(scrParts[0], 'smrtScrDim');
			scrHtml += scramblePartToHtml(scrParts[1], 'smrtScrCur');
			scrHtml += scramblePartToHtml(scrParts[2], 'smrtScrAct');
		}
		return scrHtml;
	}

	function checkScramble(curCubie, curPuzzle) {
		if (rawScrTxt == "" || !rawScrValid) {
			return false;
		}
		return cubeutil.cubiesMatch(scrState, curCubie, curPuzzle == '222');
	}

	function getScrCubie() {
		return scrState;
	}

	return {
		setScramble: setScramble,
		getScrCubie: getScrCubie,
		checkScramble: checkScramble,
		checkState: checkState
	}
}, [mathlib.CubieCube]);

var giikerutil = execMain(function(CubieCube) {

	var connectClick = $('<span class="click"></span>');
	var debugClick = $('<span class="click" style="font-family:iconfont;padding-left:0.5em;">\ue69d</span>');
	var resetClick = $('<span>' + GIIKER_RESET + '</span>').addClass('click');
	var algCubingClick = $('<a target="_blank">' + GIIKER_RAWPRETTY.split('|')[0] + '(N/A)</a>').addClass('click');
	var lastSolveClick = $('<a target="_blank">' + GIIKER_RAWPRETTY.split('|')[1] + '(N/A)</a>').addClass('click');
	var canvas = $('<canvas>').css({
		'display': 'block',
		'box-sizing': 'content-box',
		'margin': 'auto',
		'padding': '5px'
	});
	var canvasTd = $('<tr>').append($('<td colspan=2 style="padding:0;">').append(canvas));
	var deviceName = null;
	var batteryIcon = '<span style="font-family:iconfont;">\ueaea</span> ';
	var slopeIcon = '<span style="font-family:iconfont;">\ue6b6</span> ';
	var batteryTd = $('<td>').html(batteryIcon +  '??%');
	var slopeTd = $('<td>').html(slopeIcon + '0%');
	var statusDiv = $('<table class="table">');

	var drawState = (function() {
		var colors = [];
		var width = 30;
		var ctx;
		var trans = [
			[1, -0.5, 1.5, 0, 0.5, 0],
			[0.5, 0, 3, -0.5, 1, 1.5],
			[1, 0, 0, 0, 1, 1.5],
			[1, 0.5, 5.5, 0, 0.5, 0],
			[-0.5, 0, 7, -0.5, -1, 4.5],
			[-1, 0, 10, 0, -1, 4.5]
		];

		function face(f, facelet) {
			var t = trans[f].slice();
			for (var i = 0; i < t.length; i++) {
				t[i] *= width;
			}
			for (var x = 0; x < 3; x++) {
				for (var y = 0; y < 3; y++) {
					$.ctxDrawPolygon(ctx, colors["DLBURF".indexOf(facelet[(f * 3 + y) * 3 + x])], [
						[x, x, x + 1, x + 1],
						[y, y + 1, y + 1, y]
					], t);
				}
			}
		}

		function drawState() {
			if (!canvas) {
				return;
			}
			if (kernel.getProp('giiVRC') != 'n' && kernel.getProp('input') == 'g') {
				canvasTd.hide();
				return;
			}
			colors = kernel.getProp('colcube').match(/#[0-9a-fA-F]{3}/g);
			canvasTd.show();
			ctx = canvas[0].getContext('2d');
			var imgSize = kernel.getProp('imgSize') / 60;
			canvas.width((10 / 4.5 * 21 * imgSize) + 'em');
			canvas.height((21 * imgSize) + 'em');
			canvas.attr('width', 10 * width);
			canvas.attr('height', 4.5 * width);
			for (var i = 0; i < 6; i++) {
				face(i, curState);
			}
		}
		return drawState;
	})();

	function renderStatus() {
		if (kernel.getProp('giiVRC') != 'n' && kernel.getProp('input') == 'g') {
			statusDiv.css('font-size', '');
		} else {
			statusDiv.css('font-size', '75%');
		}
		statusDiv.empty();
		statusDiv.append($('<tr>').append($('<td colspan=2>').append(connectClick, debugClick)));
		if (isAnyConnected() && deviceName) {
			statusDiv.append($('<tr>').append(batteryTd, slopeTd))
				.append($('<tr>').append($('<td colspan=2>').append(resetClick.unbind('click').click(markSolved))))
				.append($('<tr>').append($('<td>').append(algCubingClick),$('<td>').append(lastSolveClick)))
				.append(canvasTd);
			connectClick.html(deviceName).unbind('click').click(disconnect);
			drawState();
		} else {
			connectClick.html(TOOLS_GIIKER + '<br>' + GIIKER_CONNECT).unbind('click').click(init);
		}
		debugClick.unbind('click').click(debugInfo.showDialog);
	}

	function execFunc(fdiv) {
		if (!fdiv) {
			return;
		}
		fdiv.empty().append(statusDiv);
		renderStatus();
		startBatTicker();
		renderBatDiv();
	}

	var batId = 0;
	var batValue = 0;

	var lowBatWarned = false;
	function showLowBatteryNotice(level) {
		var div = $('<div class="lowbattery-notice">').css({
			'position': 'fixed',
			'right': '1em',
			'top': '1em',
			'z-index': 99999,
			'background': 'rgba(200,30,30,0.95)',
			'color': '#fff',
			'padding': '0.7em 1.1em',
			'border-radius': '0.5em',
			'font-size': '1.05em',
			'box-shadow': '0 2px 10px rgba(0,0,0,0.35)',
			'cursor': 'pointer'
		}).html('\u26a0 \u9b54\u65b9\u7535\u91cf\u4ec5 ' + level + '%\uff0c\u5efa\u8bae\u5145\u7535\uff08\u70b9\u51fb\u5173\u95ed\uff09').appendTo('body');
		div.click(function() {
			div.remove();
		});
		setTimeout(function() {
			div.fadeOut(600, function() {
				div.remove();
			});
		}, 8000);
	}

	function checkLowBattery() {
		if (!lowBatWarned && batValue && batValue < 10) {
			lowBatWarned = true;
			showLowBatteryNotice(batValue);
		}
	}

	/* ============================================================
	 * 电量指示器：右上角电池图标（3 格）+ 百分比 + 预计降到 10% 的剩余时间
	 *  >75%   外壳白，3 格白
	 *  50~75% 外壳白，2 格黄
	 *  25~50% 外壳白，1 格红
	 *  10~25% 外壳鲜红，0 格
	 *  <10%   0 格，外壳深红/鲜红交替闪烁（1 秒一次）
	 * ============================================================ */
	var batHistory = [];
	var batDiv = null;
	var batTickTid = 0;
	var batBlinkOn = true;

	function buildBatDiv() {
		if (batDiv) {
			return batDiv;
		}
		batDiv = $('<div class="vrcbat">').css({
			'position': 'fixed',
			'right': '1.1em',
			'top': '0.35em',
			'z-index': 9999,
			'pointer-events': 'none',
			'text-align': 'center',
			'font-family': 'Consolas, monospace',
			'user-select': 'none',
			'line-height': '1.05'
		}).appendTo('body');
		batDiv.html(
			'<div class="vrcbat-svg" style="height:22px;"></div>' +
			'<div class="vrcbat-pct" style="font-size:0.92em;font-weight:bold;"></div>' +
			'<div class="vrcbat-eta" style="font-size:0.75em;opacity:0.9;"></div>'
		);
		return batDiv;
	}

	function batSvg(shell, litCount, litColor, blankColor) {
		var cells = '';
		for (var i = 0; i < 3; i++) {
			var x = (4.2 + i * 11.2).toFixed(1);
			cells += '<rect x="' + x + '" y="4.2" width="9.4" height="13.6" rx="1.4" fill="' +
				(i < litCount ? litColor : blankColor) + '"/>';
		}
		return '<svg width="46" height="22" viewBox="0 0 46 22" xmlns="http://www.w3.org/2000/svg">' +
			'<rect x="1.3" y="1.3" width="38.2" height="19.4" rx="3.4" fill="none" stroke="' + shell + '" stroke-width="2.4"/>' +
			'<rect x="41.2" y="7.4" width="3.6" height="7.2" rx="1.2" fill="' + shell + '"/>' +
			cells + '</svg>';
	}

	function batStyleFor(level) {
		var blank = 'rgba(90,90,90,0.35)';
		if (!level) {
			return { shell: 'rgba(140,140,140,0.9)', lit: 0, litColor: '#fff', blank: blank };
		}
		if (level > 75) {
			return { shell: '#ffffff', lit: 3, litColor: '#ffffff', blank: blank };
		}
		if (level > 50) {
			return { shell: '#ffffff', lit: 2, litColor: '#ffd21e', blank: blank };
		}
		if (level > 25) {
			return { shell: '#ffffff', lit: 1, litColor: '#ff3b30', blank: blank };
		}
		if (level > 10) {
			return { shell: '#ff3b30', lit: 0, litColor: '#ff3b30', blank: blank };
		}
		return { shell: '#8b0000', lit: 0, litColor: '#ff3b30', blank: blank };
	}

	function fmtEta(ms) {
		if (!isFinite(ms) || ms <= 0) {
			return '--:--:--';
		}
		var s = Math.floor(ms / 1000);
		var h = Math.floor(s / 3600);
		var m = Math.floor((s % 3600) / 60);
		var sec = s % 60;
		return ('0' + h).slice(-2) + ':' + ('0' + m).slice(-2) + ':' + ('0' + sec).slice(-2);
	}

	function estimateRemainMs(level) {
		if (!level || batHistory.length < 2) {
			return NaN;
		}
		var a = batHistory[0];
		var b = batHistory[batHistory.length - 1];
		var dt = b.t - a.t;
		if (dt < 20000 || b.v >= a.v) {
			return NaN;
		}
		var rate = (a.v - b.v) / dt; // 每毫秒掉的百分点
		if (rate <= 0) {
			return NaN;
		}
		return (level - 10) / rate;
	}

	function renderBatDiv() {
		var div = buildBatDiv();
		// 没连魔方时整个电池不显示，避免占着右上角
		var connected = false;
		try {
			connected = isAnyConnected() && !!batValue;
		} catch (e) {}
		if (!connected) {
			div.hide();
			return;
		}
		div.show();
		var level = batValue || 0;
		var st = batStyleFor(level);
		if (level && level <= 10) {
			st.shell = batBlinkOn ? '#ff3b30' : '#8b0000';
		}
		div.find('.vrcbat-svg').html(batSvg(st.shell, st.lit, st.litColor, st.blank));
		div.find('.vrcbat-pct').text(level ? (level + '%') : '--%')
			.css('color', !level ? 'rgba(130,130,130,1)' : (level <= 10 ? '#d32f2f' : (level <= 25 ? '#e64a19' : 'rgba(60,60,60,1)')));
		div.find('.vrcbat-eta').text(level ? fmtEta(estimateRemainMs(level)) : '')
			.css('color', 'rgba(100,100,100,0.95)');
	}

	function startBatTicker() {
		if (batTickTid) {
			return;
		}
		batTickTid = setInterval(function() {
			batBlinkOn = !batBlinkOn;
			renderBatDiv();
			try {
				renderDeviceRow();
			} catch (e) {}
		}, 1000);
	}

	function updateBattery(value) {
		batValue = value[0];
		batteryTd.html(batteryIcon + (batValue || '??') + '%');
		deviceName = value[1];
		connectClick.html(deviceName);
		if (batValue) {
			var now = $.now();
			if (!batHistory.length || now - batHistory[batHistory.length - 1].t > 30000 ||
				batHistory[batHistory.length - 1].v != batValue) {
				batHistory.push({ t: now, v: batValue });
				while (batHistory.length > 40) {
					batHistory.shift();
				}
			}
		}
		checkLowBattery();
		startBatTicker();
		renderBatDiv();
	}

	function pollUpdateBattery() {
		if (isAnyConnected()) {
			GiikerCube.getCube().getBatteryLevel().then(function(value) {
				updateBattery(value);
			});
			batId = setTimeout(pollUpdateBattery, 60000);
		} else {
			batId = 0;
		}
	}

	var callback = $.noop;
	var evtCallback = $.noop;

	var curRawState = mathlib.SOLVED_FACELET;
	var curRawCubie = new CubieCube();
	var curCubie = new CubieCube();
	var curState = curRawState;
	var solvedStateInv = new CubieCube();
	var curPuzzle = '333';

	var detectTid = 0;

	function giikerErrorDetect() {
		if (detectTid) {
			clearTimeout(detectTid);
			detectTid = 0;
		}
		if (curPuzzle == '333' && kernel.getProp('giiAED')) {
			detectTid = setTimeout(function() {
				if (checkMoves(moveTsList.slice(moveTsStart)) == 99) {
					return;
				}
				var facelet = curCubie.toFaceCube();
				if (cubeutil.getProgress(facelet, 'cfop') <= 2) { // all unsolved pieces is on same face
					return;
				}
				var gen = scramble_333.genFacelet(curCubie.toFaceCube());
				if (gen.length / 3 < 10) {
					DEBUG && console.log('[giiker]', 'Possible error, gen=' + gen.replace(/ /g, '') + ', ignore');
					return;
				}
				DEBUG && console.log('[giiker]', 'Almost error, gen=' + gen.replace(/ /g, '') + ', mark solved');
				markSolved();
			}, 1000);
		}
	}

	var nodeSearchd = 0;

	function checkMoves(moveTsList) {
		if (moveTsList.length % 2 == 1) {
			return 99;
		}
		var stateToEnd = [];
		stateToEnd[moveTsList.length] = new CubieCube();
		for (var i = moveTsList.length - 1; i >= 0; i--) {
			stateToEnd[i] = new CubieCube();
			CubieCube.CubeMult(CubieCube.moveCube[moveTsList[i][0]], stateToEnd[i + 1], stateToEnd[i]);
		}
		for (var i = 1; i < 3; i++) {
			nodeSearchd = 0;
			if (checkSwap(moveTsList, 0, i, new CubieCube(), stateToEnd)) {
				return i;
			} else if (nodeSearchd > 9999) {
				return 99;
			}
		}
		return 99;
	}

	function checkSwap(moveTsList, start, nswap, stateFromStart, stateToEnd) {
		if (nswap == 0) {
			return stateFromStart.isEqual(new CubieCube().invFrom(stateToEnd[start]));
		}
		var cctmp = new CubieCube();
		for (var i = start; i < moveTsList.length - 1; i++) {
			// try to swap moves[i] and moves[i + 1]
			if (~~(moveTsList[i][0] / 3) % 3 == ~~(moveTsList[i + 1][0] / 3) % 3) {
				CubieCube.CubeMult(stateFromStart, CubieCube.moveCube[moveTsList[i][0]], cctmp);
				stateFromStart.init(cctmp.ca, cctmp.ea);
				continue;
			}
			var state = new CubieCube().init(stateFromStart.ca, stateFromStart.ea);
			CubieCube.CubeMult(state, CubieCube.moveCube[moveTsList[i + 1][0]], cctmp);
			CubieCube.CubeMult(cctmp, CubieCube.moveCube[moveTsList[i][0]], state);
			CubieCube.CubeMult(state, stateToEnd[i + 2], cctmp);
			if (++nodeSearchd > 9999) {
				return false;
			}
			if (cctmp.edgeCycles() < nswap) {
				var ret = checkSwap(moveTsList, i + 2, nswap - 1, state, stateToEnd);
			}
			if (ret) {
				return true;
			}
			CubieCube.CubeMult(stateFromStart, CubieCube.moveCube[moveTsList[i][0]], cctmp);
			stateFromStart.init(cctmp.ca, cctmp.ea);
		}
		return false;
	}

	function markSolved() {
		solvedStateInv.invFrom(curRawCubie);
		curState = mathlib.SOLVED_FACELET;
		kernel.setProp('giiSolved', curRawState);
		moveTsStart = moveTsList.length;
		scrambleLength = 0;
		drawState();
		callback(curState, [], [null, $.now()], deviceName, curPuzzle);
	}

	var moveTsList = []; //[[move, deviceTime, locTime], ...], locTime might be null
	var moveTsStart = 0;

	function giikerCallback(facelet, prevMoves, lastTs, hardware, puzzle) {
		var locTime = $.now();
		curPuzzle = puzzle || '333';
		lastTs = lastTs || [locTime, locTime];
		if (deviceName != hardware) {
			deviceName = hardware;
			renderStatus();
		}
		curRawState = facelet;
		curRawCubie.fromFacelet(curRawState);
		CubieCube.CubeMult(solvedStateInv, curRawCubie, curCubie);
		curState = curCubie.toFaceCube();

		if (prevMoves.length > 0) {
			var move = "URFDLB".indexOf(prevMoves[0][0]) * 3 + " 2'".indexOf(prevMoves[0][1]);
			moveTsList.push([move, lastTs[0], lastTs[1]]);
		}
		if (scrambleLength > 0) {
			updateRawMovesClick();
		}
		if (moveTsList.length > 10) {
			updateSlopeSpan();
		}
		if (curState == mathlib.SOLVED_FACELET) {
			reconsSolve();
			moveTsStart = moveTsList.length;
			scrambleLength = 0;
		}
		drawState();
		batId == 0 && pollUpdateBattery();
		giikerErrorDetect();
		var retState = curState;
		if (hackedSolvedCubieInv) {
			CubieCube.CubeMult(hackedSolvedCubieInv, curCubie, hackedCubie);
			retState = hackedCubie.toFaceCube();
		}
		callback(retState, prevMoves, lastTs, deviceName, curPuzzle);
		scrHinter.checkState(curCubie, curPuzzle);
	}

	// ---- 多智能魔方 ---------------------------------------------------------
	// 浏览器 requestDevice 一次只能选中一个设备（没有多选 API），
	// 所以"多连"的做法是：点一次「再连一个」加一台，然后在下拉里切换当前使用的魔方。
	var extraDevices = [];
	var activeDeviceId = 0;
	var deviceSeq = 0;
	var lastDeviceSig = '';

	function listDevices() {
		var ret = [{
			id: 0,
			inst: GiikerCube,
			name: deviceName || '主魔方',
			puzzle: curPuzzle || '',
			snap: null
		}];
		for (var i = 0; i < extraDevices.length; i++) {
			ret.push(extraDevices[i]);
		}
		return ret;
	}

	function getDeviceRec(id) {
		var all = listDevices();
		for (var i = 0; i < all.length; i++) {
			if (all[i].id == id) {
				return all[i];
			}
		}
		return null;
	}

	function isAnyConnected() {
		try {
			if (GiikerCube['isConnected']()) {
				return true;
			}
		} catch (e) {}
		for (var i = 0; i < extraDevices.length; i++) {
			try {
				if (extraDevices[i].inst.isConnected()) {
					return true;
				}
			} catch (e) {}
		}
		return false;
	}

	function makeDeviceCallback(id) {
		return function (facelet, prevMoves, lastTs, hardware, puzzle) {
			var rec = getDeviceRec(id);
			if (rec) {
				rec.name = hardware || rec.name;
				rec.puzzle = puzzle || rec.puzzle;
				rec.snap = {
					facelet: facelet,
					prevMoves: prevMoves,
					lastTs: lastTs,
					hardware: hardware,
					puzzle: puzzle
				};
			}
			if (id == activeDeviceId) {
				giikerCallback(facelet, prevMoves, lastTs, hardware, puzzle);
			} else {
				renderDeviceRow();
			}
		};
	}

	function switchDevice(id) {
		var rec = getDeviceRec(id);
		if (!rec) {
			return;
		}
		activeDeviceId = ~~id;
		if (!rec.snap) {
			renderDeviceRow();
			return;
		}
		// 换魔方相当于重新开始一次解：清掉上一步的增量与时间轴，用完整 facelet 重建
		cleanup();
		deviceName = '';
		giikerCallback(rec.snap.facelet, [], rec.snap.lastTs, rec.snap.hardware, rec.snap.puzzle);
		renderDeviceRow();
	}

	function addDevice() {
		var id = ++deviceSeq;
		var inst = execMain(BtDeviceGroupFactory);
		var rec = {
			id: id,
			inst: inst,
			name: '魔方 ' + id,
			puzzle: '',
			snap: null
		};
		extraDevices.push(rec);
		inst.setCallback(makeDeviceCallback(id));
		inst.setEventCallback(function (info, evt) {
			if (id == activeDeviceId) {
				giikerEvtCallback(info, evt);
			}
			renderDeviceRow();
		});
		inst.setGyroCallback(giikerGyroCallback);
		return inst.init().then(function () {
			renderDeviceRow();
			logohint.push(LGHINT_BTCONSUC);
			// 新连上的魔方立即可用，直接切过去
			if (rec.snap) {
				switchDevice(id);
			}
		}).catch(function (e) {
			giikerutil.log('[giiker] addDevice failed', e);
			for (var i = 0; i < extraDevices.length; i++) {
				if (extraDevices[i].id == id) {
					extraDevices.splice(i, 1);
					break;
				}
			}
			renderDeviceRow();
		});
	}

	function disconnectDevice(id) {
		var rec = getDeviceRec(id);
		if (!rec) {
			return Promise.resolve();
		}
		return Promise.resolve(rec.inst.stop()).then(function () {
			if (rec.id != 0) {
				for (var i = 0; i < extraDevices.length; i++) {
					if (extraDevices[i].id == rec.id) {
						extraDevices.splice(i, 1);
						break;
					}
				}
			}
			if (activeDeviceId == rec.id) {
				activeDeviceId = 0;
			}
			renderDeviceRow();
		}).catch(function () {
			renderDeviceRow();
		});
	}

	function buildDeviceRow() {
		var cell = $('#dsCubeRow td');
		if (!cell.length) {
			return null;
		}
		if (cell.data('dsBuilt')) {
			return cell;
		}
		cell.data('dsBuilt', true);
		cell.empty();
		var wrap = $('<div>').css({
			'padding': '0.15em 0',
			'white-space': 'nowrap'
		});
		wrap.append($('<span>').text('已连接魔方：'));
		var sel = $('<select id="dsCubeSelect">').css({
			'font-size': '0.95em',
			'max-width': '12em'
		});
		var btnAdd = $('<input type="button">').val('再连一个').css({
			'margin-left': '0.5em',
			'cursor': 'pointer'
		}).click(function () {
			addDevice();
		});
		var btnDisc = $('<input type="button">').val('断开').css({
			'margin-left': '0.3em',
			'cursor': 'pointer'
		}).click(function () {
			disconnectDevice(~~$('#dsCubeSelect').val());
		});
		wrap.append(sel).append(btnAdd).append(btnDisc);
		cell.append(wrap);
		return cell;
	}

	function renderDeviceRow() {
		var cell = buildDeviceRow();
		if (!cell) {
			return;
		}
		var sel = $('#dsCubeSelect');
		if (!sel.length) {
			return;
		}
		var all = listDevices();
		var sig = activeDeviceId + '|';
		for (var i = 0; i < all.length; i++) {
			var cc = false;
			try {
				cc = all[i].inst.isConnected();
			} catch (e) {}
			sig += all[i].id + ':' + (all[i].name || '') + ':' + (cc ? 1 : 0) + ',';
		}
		if (sig === lastDeviceSig && sel.children().length) {
			sel.val(String(activeDeviceId));
			return;
		}
		lastDeviceSig = sig;
		sel.empty();
		for (var i = 0; i < all.length; i++) {
			var d = all[i];
			var label = d.name || ('魔方 ' + d.id);
			if (d.puzzle) {
				label += ' (' + d.puzzle + ')';
			}
			var connected = false;
			try {
				connected = d.inst.isConnected();
			} catch (e) {}
			if (!connected) {
				label += ' · 未连接';
			}
			sel.append($('<option>').val(d.id).text(label));
		}
		sel.val(String(activeDeviceId));
		sel.unbind('change').change(function () {
			switchDevice(~~$(this).val());
		});
	}
	// ---- 陀螺仪 (gyroscope) -------------------------------------------------
	var gyroStat = {
		frames: 0,      // 收到的 GYRO 帧总数
		lastTs: 0,      // 最后一次收到帧的时刻
		rate: 0,        // 最近 1 秒内的帧数（近似帧率）
		quat: null,     // {w,x,y,z} 原始读数（GAN 坐标系）
		vel: null,      // {x,y,z} 角速度原始读数（4bit 有符号）
		supported: null,// 固件声明是否支持陀螺仪
		enabled: null,  // 固件声明陀螺仪开关状态
		name: null      // 硬件型号名
	};
	var gyroRateWin = [];

	function resetGyroStat() {
		gyroStat.frames = 0;
		gyroStat.lastTs = 0;
		gyroStat.rate = 0;
		gyroStat.quat = null;
		gyroStat.vel = null;
		gyroStat.supported = null;
		gyroStat.enabled = null;
		gyroStat.name = null;
		gyroRateWin = [];
	}

	function giikerGyroCallback(quat, vel, locTime) {
		var now = locTime || $.now();
		gyroStat.frames++;
		gyroStat.lastTs = now;
		gyroStat.quat = quat;
		gyroStat.vel = vel;
		gyroRateWin.push(now);
		while (gyroRateWin.length > 0 && now - gyroRateWin[0] > 1000) {
			gyroRateWin.shift();
		}
		gyroStat.rate = gyroRateWin.length;
		if (gyroStat.frames == 1) {
			// 只在首帧推一次信号，避免每帧都触发监听器遍历；UI 侧用 rAF 拉取最新值。
			kernel.pushSignal('giikerGyroStart', [quat, vel, now]);
		}
	}

	function setGyroMeta(supported, enabled, name) {
		gyroStat.supported = supported;
		gyroStat.enabled = enabled;
		gyroStat.name = name;
	}

	function getGyroStat() {
		return gyroStat;
	}

	// ---- gyroscope (GAN Gen2 / Gen4) ----

	var gyroStat = {
		frames: 0,
		rate: 0,
		lastTs: 0,
		quat: null,
		vel: null,
		supported: null, // null = unknown, false = this model has no gyro, true = has gyro
		enabled: null,   // null = unknown, false = gyro reported off, true = gyro on
		name: null
	};
	var gyroRateWin = [];

	function giikerGyroCallback(quat, vel, locTime) {
		var now = locTime || $.now();
		gyroStat.frames++;
		gyroStat.lastTs = now;
		gyroStat.quat = quat;
		gyroStat.vel = vel;
		gyroRateWin.push(now);
		while (gyroRateWin.length > 0 && now - gyroRateWin[0] > 1000) {
			gyroRateWin.shift();
		}
		gyroStat.rate = gyroRateWin.length;
		if (gyroStat.frames == 1) {
			kernel.pushSignal('giikerGyroFirst', [quat, vel, locTime]);
		}
	}

	function getGyroStat() {
		return gyroStat;
	}

	function setGyroMeta(supported, name) {
		if (supported != null) {
			gyroStat.supported = !!supported;
		}
		if (name) {
			gyroStat.name = name;
		}
		kernel.pushSignal('giikerGyroMeta', [gyroStat.supported, gyroStat.name]);
	}

	function resetGyroStat() {
		gyroStat.frames = 0;
		gyroStat.rate = 0;
		gyroStat.lastTs = 0;
		gyroStat.quat = null;
		gyroStat.vel = null;
		gyroRateWin = [];
	}

	var gyroStat = {
		frames: 0,
		rate: 0,
		lastTs: 0,
		quat: null,
		vel: null,
		supported: null,
		enabled: null,
		name: null
	};
	var gyroRateWin = [];

	function giikerGyroCallback(quat, vel, locTime) {
		var now = locTime || $.now();
		gyroStat.frames++;
		gyroStat.lastTs = now;
		gyroStat.quat = quat;
		gyroStat.vel = vel;
		gyroRateWin.push(now);
		while (gyroRateWin.length > 0 && now - gyroRateWin[0] > 1000) {
			gyroRateWin.shift();
		}
		gyroStat.rate = gyroRateWin.length;
		if (gyroStat.frames == 1) {
			kernel.pushSignal('giikerGyroStart', [quat, vel, locTime]);
		}
	}

	function getGyroStat() {
		return gyroStat;
	}

	function setGyroMeta(supported, enabled, name) {
		if (gyroStat.supported === supported && gyroStat.enabled === enabled && gyroStat.name === name) {
			return;
		}
		gyroStat.supported = supported;
		gyroStat.enabled = enabled;
		gyroStat.name = name;
		kernel.pushSignal('giikerGyroMeta', [supported, enabled, name]);
	}

	var gyroStat = {
		frames: 0,
		lastTs: 0,
		rate: 0,
		quat: null,
		vel: null,
		supported: null,
		enabled: null,
		name: null
	};
	var gyroRateWin = [];

	function giikerGyroCallback(quat, vel, locTime) {
		gyroStat.frames++;
		gyroStat.lastTs = locTime || $.now();
		gyroStat.quat = quat;
		gyroStat.vel = vel;
		gyroRateWin.push(gyroStat.lastTs);
		while (gyroRateWin.length > 1 && gyroStat.lastTs - gyroRateWin[0] > 1000) {
			gyroRateWin.shift();
		}
		gyroStat.rate = gyroRateWin.length;
		if (gyroStat.frames == 1) {
			kernel.pushSignal('giikerGyroStart', [quat, vel, locTime]);
		}
	}

	function getGyroStat() {
		return gyroStat;
	}

	function setGyroMeta(supported, enabled, name) {
		gyroStat.supported = supported;
		gyroStat.enabled = enabled;
		gyroStat.name = name;
		kernel.pushSignal('giikerGyroMeta', [supported, enabled, name]);
	}

	var gyroStat = {
		frames: 0,
		lastTs: 0,
		rate: 0,
		quat: null,
		vel: null,
		supported: null,
		enabled: null,
		name: null
	};
	var gyroRateWin = [];

	function resetGyroStat() {
		gyroStat.frames = 0;
		gyroStat.lastTs = 0;
		gyroStat.rate = 0;
		gyroStat.quat = null;
		gyroStat.vel = null;
		gyroRateWin = [];
	}

	function giikerGyroCallback(quat, vel, locTime) {
		var now = locTime || $.now();
		gyroStat.frames++;
		gyroStat.lastTs = now;
		gyroStat.quat = quat;
		gyroStat.vel = vel;
		gyroRateWin.push(now);
		while (gyroRateWin.length > 0 && now - gyroRateWin[0] > 1000) {
			gyroRateWin.shift();
		}
		gyroStat.rate = gyroRateWin.length;
	}

	function getGyroStat() {
		return gyroStat;
	}

	// supported = 固件声明支持陀螺仪；enabled = 这次连接是否真的收到了 GYRO 帧
	function setGyroMeta(supported, name) {
		gyroStat.supported = supported;
		gyroStat.name = name || gyroStat.name;
	}

	function tsLinearFit(moveTsList, inv) {
		var sumX = 0;
		var sumY = 0;
		var sumXY = 0;
		var sumXX = 0;
		var sumYY = 0;
		var n = 0;
		for (var i = 0; i < moveTsList.length; i++) {
			var x = moveTsList[i][inv ? 2 : 1];
			var y = moveTsList[i][inv ? 1 : 2];
			if (x == null || y == null) {
				continue;
			}
			n++;
			sumX += x;
			sumY += y;
			sumXY += x * y;
			sumXX += x * x;
			sumYY += y * y;
		}
		var varY = n * sumYY - sumY * sumY;
		var varX = n * sumXX - sumX * sumX;
		var covXY = n * sumXY - sumX * sumY;
		var slope = varX < 1e-3 ? 1 : covXY / varX;
		var intercept = n < 1 ? 0 : sumY / n - slope * sumX / n;
		var r2 = varX < 1e-3 || varY < 1e-3 ? 1 : Math.pow(covXY, 2) / varX / varY;
		var s_slope = n < 3 || varX < 1e-3 ? 0 : Math.sqrt(varY / varX * (1 - r2) / (n - 2));
		return [slope, intercept, r2, s_slope];
	}

	function tsApplyFixes(moveTsList) {
		// Fix device timestamps values for lost and recovered cube moves.
		// This is needed at least for iCarry2 (GAN protocol v3). Due to protocol
		// limitations recovered moves does not have device and local timestamps.
		if (moveTsList.length >= 2) {
			// 1st pass - tail-to-head, align lost move device timestamps to next move -50ms
			for (var i = moveTsList.length - 1; i > 0; i--) {
				if (moveTsList[i][1] != null && moveTsList[i - 1][1] == null)
					moveTsList[i - 1][1] = moveTsList[i][1] - 50;
			}
			// 2nd pass - head-to-tail, align lost move device timestamp to prev move +50ms
			for (var i = 0; i < moveTsList.length - 1; i++) {
				if (moveTsList[i][1] != null && moveTsList[i + 1][1] == null)
					moveTsList[i + 1][1] = moveTsList[i][1] + 50;
			}
		}
		return moveTsList;
	}

	function tsLinearFix(moveTsList, startTime, endTime) {
		if (moveTsList.length == 0) {
			return moveTsList;
		}
		moveTsList = tsApplyFixes(moveTsList);
		var param = tsLinearFit(moveTsList);
		var slope = param[0];
		var intercept = param[1];
		var first = Math.round(slope * moveTsList[0][1] + intercept);
		var last = Math.round(slope * moveTsList.at(-1)[1] + intercept);
		if (startTime == null || startTime > first) {
			startTime = first;
		} else if (endTime != null && endTime < last) {
			startTime -= Math.min(first - startTime, last - endTime);
		}
		for (var i = 0; i < moveTsList.length; i++) {
			moveTsList[i][1] = Math.round(slope * moveTsList[i][1] + intercept) - startTime;
		}
		return moveTsList;
	}

	function updateRawMovesClick() {
		var moveCount = moveTsList.length - moveTsStart;
		var scrambleStr = "";
		for (var i = 0; i < scrambleLength; i++) {
			var move = moveTsList[i + moveTsStart][0];
			scrambleStr += "URFDLB".charAt(~~(move / 3)) + " 2'".charAt(move % 3);
		}
		var solveStr = "";
		var solvMoves = [];
		for (var i = scrambleLength; i < moveCount; i++) {
			solvMoves.push(moveTsList[i + moveTsStart].slice());
		}
		solvMoves = tsLinearFix(solvMoves);
		for (var i = 0; i < solvMoves.length; i++) {
			var move = solvMoves[i];
			solveStr += "URFDLB".charAt(~~(move[0] / 3)) + " 2'".charAt(move[0] % 3) + "/*" + move[1] + "*/";
		}
		updateAlgClick(algCubingClick, GIIKER_RAWPRETTY.split('|')[0] + ' (' + moveCount + ')', scrambleStr, solveStr)
	}

	function updateSlopeSpan() {
		if (moveTsList.length - moveTsStart > 50 && moveTsStart > 0 && moveTsList[moveTsStart - 1][2] < timer.getStartTime()) {
			moveTsList = moveTsList.slice(moveTsStart);
			moveTsStart = 0;
		}
		var param = tsLinearFit(moveTsList, true);
		slopeTd.html(slopeIcon + Math.round((param[0] - 1) * 100000) / 1000 + '%');
	}

	function updateAlgClick(click, text, setup, alg) {
		if (setup || alg) {
			click.attr('href', cubeutil.getAlgCubingUrl(alg, setup, curPuzzle));
		} else {
			click.removeAttr('href');
		}
		click.html(text);
	}

	function setLastSolve(solve) {
		updateAlgClick(lastSolveClick, "Pretty", cubeutil.getConjMoves(curScramble), solve)
	}

	function giikerEvtCallback(info, event) {
		if (info == 'disconnect') {
			logohint.push(LGHINT_BTDISCON);
			renderStatus();
			kernel.pushSignal('scrfix', curScramble);
			return typeof evtCallback == 'function' && evtCallback(info, event);
		}
	}

	function cleanup() {
		batId = 0;
		batValue = 0;
		deviceName = null;
		curRawState = mathlib.SOLVED_FACELET;
		curRawCubie = new CubieCube();
		curCubie = new CubieCube();
		curState = curRawState;
		solvedStateInv = new CubieCube();
		moveTsList = [];
		moveTsStart = 0;
		scrambleLength = 0;
		hackedSolvedCubieInv = null;
		hackedCubie = new CubieCube();
		slopeTd.html(slopeIcon + '0%');
		updateAlgClick(algCubingClick, GIIKER_RAWPRETTY.split('|')[0] + '(N/A)');
		updateAlgClick(lastSolveClick, GIIKER_RAWPRETTY.split('|')[1] + '(N/A)');
	}

	function init() {
		cleanup();
		curRawState = kernel.getProp('giiSolved', mathlib.SOLVED_FACELET);
		curRawCubie.fromFacelet(curRawState);
		solvedStateInv.invFrom(curRawCubie);
		GiikerCube.setCallback(giikerCallback);
		GiikerCube.setEventCallback(giikerEvtCallback);
		GiikerCube.setGyroCallback(giikerGyroCallback);
		resetGyroStat();
		if (!isAnyConnected()) {
			return GiikerCube.init().then(function () {
				logohint.push(LGHINT_BTCONSUC);
				renderDeviceRow();
			});
		} else {
			renderDeviceRow();
			return Promise.resolve();
		}
	}

	function stop() {
		var ps = [];
		for (var i = 0; i < extraDevices.length; i++) {
			ps.push(Promise.resolve(extraDevices[i].inst.stop()).catch($.noop));
		}
		extraDevices = [];
		activeDeviceId = 0;
		ps.push(Promise.resolve(GiikerCube.stop()).catch($.noop));
		return Promise.all(ps).then(function () {
			giikerEvtCallback('disconnect');
			renderDeviceRow();
		});
	}

	function disconnect() {
		if (isAnyConnected() && confirm(GIIKER_DBG.split('|')[1])) {
			stop();
		}
	}

	function checkScramble() {
		return scrHinter.checkScramble(curCubie, curPuzzle);
	}

	var curScramble;

	function procSignal(signal, value) {
		if (signal == 'scrambling') {
			curScramble = "";
		} else if (signal == 'scramble' || signal == 'scrambleX') {
			var scrType = value[0];
			curScramble = value[1];
			if (!/^(222|333)$/.exec(tools.puzzleType(scrType))) {
				curScramble = "";
			}
			scrHinter.setScramble(curScramble);
			scrHinter.checkState(curCubie, curPuzzle);
		} else if (signal == 'property') {
			if (['giiVRC', 'imgSize'].indexOf(value[0]) >= 0) {
				renderStatus();
			} else if (/^(preScrT?|isTrainScr)$/.exec(value[0])) {
				scrHinter.setScramble(curScramble);
				scrHinter.checkState(curCubie, curPuzzle);
			}
		} else if (signal == 'timestd' && !value[4]) {
			toReconsSolve = [timer.getStartTime(), value[0][1], value[1]];
			setTimeout(reconsSolve, 0);
		}
	}

	var toReconsSolve = null;

	function reconsSolve() {
		if (!toReconsSolve) {
			return;
		}
		var startTime = toReconsSolve[0];
		var startIdx = moveTsList.length;
		var toScramble = toReconsSolve[2];
		if (startIdx > 0 && moveTsList[startIdx - 1][2] > toReconsSolve[0] + toReconsSolve[1] + 1000) {
			toReconsSolve = null;
		}
		for (var i = moveTsList.length - 1; i >= 0; i--) {
			if (moveTsList[i][2] < startTime - 500) {
				break;
			}
			startIdx = i;
		}
		if (startIdx == moveTsList.length) {
			return;
		}

		var c1 = new mathlib.CubieCube();
		var solvMoves = [];
		var conj = mathlib.CubieCube.rotMulI[0][cubeutil.getPreConj()];
		for (var i = startIdx; i < moveTsList.length; i++) {
			var move = moveTsList[i].slice();
			var m = mathlib.CubieCube.rotMulM[conj][move[0]];
			move[0] = 'URFDLB'.charAt(~~(m/3)) + " 2'".charAt(m % 3);
			solvMoves.push(move);
			c1.selfMoveStr(move[0]);
		}
		solvMoves = tsLinearFix(solvMoves);
		var sol = cubeutil.moveSeq2str(solvMoves);
		kernel.pushSignal('giirecons', [toScramble, [sol, '333']]);

		var scrMoves = (toScramble || "").split(' ');
		var chk = new mathlib.CubieCube();
		for (var i = 0; i < scrMoves.length; i++) {
			chk.selfMoveStr(scrMoves[i]);
		}
		var c2 = new mathlib.CubieCube();
		c2.invFrom(c1);
		if (chk.toFaceCube() == c2.toFaceCube()) {
			DEBUG && console.log('[bluetooth] recons clear, cube solved');
			toReconsSolve = null;
		}
	}

	var scrambleLength = 0;

	function markScrambled(virtual) {
		var targetCubie = curCubie;
		if (virtual) {
			targetCubie = scrHinter.getScrCubie();
		}
		if (!targetCubie.isEqual(curCubie)) {
			DEBUG && console.log('[bluetooth] scramble equal, start hack!');
			hackedSolvedCubieInv = new mathlib.CubieCube();
			hackedCubie.invFrom(curCubie);
			CubieCube.CubeMult(targetCubie, hackedCubie, hackedSolvedCubieInv);
			moveTsStart = moveTsList.length;
			callback(targetCubie.toFaceCube(), [], [null, $.now()], deviceName, curPuzzle);
		}
		scrambleLength = moveTsList.length - moveTsStart;
		updateRawMovesClick();
		updateAlgClick(lastSolveClick, GIIKER_RAWPRETTY.split('|')[1] + '(N/A)');
	}

	var hackedSolvedCubieInv = null;
	var hackedCubie = new CubieCube();

	function isSync() {
		return hackedSolvedCubieInv == null;
	}

	function reSync() {
		if (!hackedSolvedCubieInv) {
			return;
		}
		hackedSolvedCubieInv = null;
		callback(curState, [], [null, $.now()], deviceName, curPuzzle);
	}

	var debugInfo = (function() {
		var msgs = [];
		var isShow = false;
		var debugText = $('<textarea style="width:100%;height:100%;" readonly>');

		function closeCallback() {
			isShow = false;
		}

		function showDialog() {
			isShow = true;
			debugText.val(msgs.join('\n'));
			debugText[0].scrollTop = debugText[0].scrollHeight;
			kernel.showDialog([debugText, closeCallback, closeCallback, closeCallback], 'share', GIIKER_DBG.split('|')[0]);
		}

		function appendLog() {
			var ts = new Date().toISOString();
			var msg = ['[' + ts + ']'];
			for (var i = 0; i < arguments.length; i++) {
				msg.push(String(arguments[i]));
			}
			DEBUG && console.log.apply(null, [].concat([ts], Array.from(arguments)));
			msgs.push(msg.join(' '));
			if (msgs.length > 1000) {
				msgs = msgs.slice(100);
			}
			if (isShow) {
				debugText.val(msgs.join('\n'));
				debugText[0].scrollTop = debugText[0].scrollHeight;
			}
		}
		return {
			showDialog: showDialog,
			appendLog: appendLog
		};
	})();

	$(function() {
		kernel.regListener('giiker', 'scramble', procSignal);
		kernel.regListener('giiker', 'scrambling', procSignal);
		kernel.regListener('giiker', 'scrambleX', procSignal);
		kernel.regListener('giiker', 'timestd', procSignal);
		kernel.regListener('giiker', 'property', procSignal, /^(?:giiVRC|imgSize|preScrT?|isTrainScr)$/);
		tools.regTool('giikerutil', TOOLS_GIIKER, execFunc);
		startBatTicker();
		renderBatDiv();
	});

	function chkAvail() {
		if (!window.navigator || !window.navigator.bluetooth) {
			return Promise.reject(GIIKER_NOBLEMSG);
		}
		var ret = Promise.resolve(true);
		if (window.navigator.bluetooth.getAvailability) {
			ret = window.navigator.bluetooth.getAvailability();
		}
		return ret.then(function(available) {
			debugInfo.appendLog('[bluetooth] is available', available);
			if (!available) {
				return Promise.reject(GIIKER_NOBLEMSG);
			}
			return;
		});
	}

	function getSavedMac(name) {
		// 读上一次成功填过的 MAC。有值就不必再等蓝牙广播（Windows 上常常等不到）。
		try {
			var m = JSON.parse(kernel.getProp('giiMacMap', '{}'));
			return (name && m[name]) || null;
		} catch (e) {
			return null;
		}
	}

	function reqMacAddr(forcePrompt, isWrongKey, deviceMac, defaultMac) {
		var savedMacMap = JSON.parse(kernel.getProp('giiMacMap', '{}'));
		var mac = savedMacMap[deviceName];
		if (deviceMac) {
			if (mac && mac.toUpperCase() == deviceMac.toUpperCase()) {
				debugInfo.appendLog('[bluetoothutil] device mac matched');
			} else {
				mac = deviceMac;
			}
		} else {
			if (!mac || isWrongKey) {
				mac = prompt((isWrongKey ? 'The MAC provided might be wrong!\n' : '') + GIIKER_REQMACMSG, mac || defaultMac || 'xx:xx:xx:xx:xx:xx');
			}
			if (!/^([0-9a-f]{2}[:-]){5}[0-9a-f]{2}$/i.exec(mac)) {
				logohint.push(LGHINT_BTINVMAC);
				return;
			}
		}
		if (mac != savedMacMap[deviceName]) {
			savedMacMap[deviceName] = mac;
			kernel.setProp('giiMacMap', JSON.stringify(savedMacMap));
			debugInfo.appendLog('[bluetoothutil] device mac updated');
		}
		return mac;
	}

	return {
		setCallback: function(func) {
			callback = func;
		},
		setEventCallback: function(func) {
			evtCallback = func;
		},
		markSolved: markSolved,
		checkScramble: checkScramble,
		markScrambled: markScrambled,
		init: init,
		stop: stop,
		isSync: isSync,
		reSync: reSync,
		tsLinearFix: tsLinearFix,
		updateBattery: updateBattery,
		getGyroStat: getGyroStat,
		addDevice: addDevice,
		switchDevice: switchDevice,
		listDevices: listDevices,
		isConnected: isAnyConnected,
		renderDeviceRow: renderDeviceRow,
		setGyroMeta: setGyroMeta,
		setLastSolve: setLastSolve,
		log: debugInfo.appendLog,
		chkAvail: chkAvail,
		reqMacAddr: reqMacAddr,
		getSavedMac: getSavedMac
	}
}, [mathlib.CubieCube]);
