execMain(function(timer) {
	var enable = false;
	var enableVRC = false;
	var waitReadyTid = 0;
	var moveReadyTid = 0;
	var insTime = 0;
	var div = $('<div id="vrcDiv" />');
	var totPhases = 1;
	var currentFacelet = mathlib.SOLVED_FACELET;
	var rawMoves = [];
	var curPuzzle = '333';


	// 连接/切换智能魔方后，自动把打乱类型切到对应阶数
	var lastAutoPuzzle = '';
	// 只在识别到二阶时才动打乱类型；并且每次都检查，不靠缓存。
	// 之前用 lastAutoPuzzle 去重：先连过二阶、又手动切回三阶、再连二阶时
	// 因为缓存的还是 '222' 就不切了，用户看到的就是三阶打乱。
	function autoSwitchScrType(puzzle) {
		if (puzzle != '222') {
			return;
		}
		lastAutoPuzzle = puzzle;
		var curType = (tools.getCurScramble() || [])[0] || '333';
		if (!/^222/.test(curType)) {
			giikerutil.log('[giiker] auto switch scramble type', curType, '-> 222so');
			kernel.setProp('scrType', '222so');
		}
	}

	var giikerVRC = (function() {
		var isReseted = false;
		var curVRCCubie = new mathlib.CubieCube();
		var tmpCubie1 = new mathlib.CubieCube();
		var puzzleObj;
		var curOri = -1;
		var vrcPuzzle = '333';
		// 阶数切换时，puzzleFactory.init 可能是异步的（首次要加载 twisty.js）。
		// 这一帧先记下状态，等重建完成后再重放，否则 applyMoves 会打在旧尺寸的魔方上。
		var pendingFacelet = null;

		function resetVRC(temp, force, targetPuzzle) {
			if ((isReseted && !force) || !enableVRC) {
				return;
			}
			targetPuzzle = targetPuzzle || tools.getCurPuzzle() || '333';
			var size = ['', '', '222', '333'].indexOf(targetPuzzle);
			var options = {
				puzzle: size >= 2 ? ('cube' + size) : 'cube3',
				style: kernel.getProp('giiVRC')
			};
			giikerutil.log('[giiker] resetVRC target=', targetPuzzle, 'size=', size, 'opt.puzzle=', options.puzzle, 'style=', options.style);
			puzzleFactory.init(options, $.noop, div, function(ret, isInit) {
				puzzleObj = ret;
				giikerutil.log('[giiker] resetVRC cb ret=', !!ret, 'isInit=', isInit);
				if (isInit && !puzzleObj) {
					div.css('height', '');
					div.html('--:--');
				}
				if (!temp || isInit) {
					timer.lcd.fixDisplay(false, true);
					setSize(kernel.getProp('timerSize'));
				}
				curVRCCubie.fromFacelet(mathlib.SOLVED_FACELET);
				if (!puzzleObj) {
					return;
				}
				vrcPuzzle = targetPuzzle;
				var preScramble = puzzleObj.parseScramble('U2 U2', true);
				curVRCCubie.ori = 0;
				for (var i = 0; i < preScramble.length; i++) {
					curVRCCubie.selfMoveStr(puzzleObj.move2str(preScramble[i]));
				}
				puzzleObj.applyMoves(preScramble); // process pre scramble (cube orientation)
				var targetOri = kernel.getProp('giiOri');
				targetOri = targetOri == 'auto' ? -1 : ~~targetOri;
				setOri(targetOri);
				// 阶数切换时被推迟的那一帧，现在补上（此时 vrcPuzzle 已等于目标阶数，不会递归）
				var pf = pendingFacelet;
				pendingFacelet = null;
				if (pf) {
					setState(pf, [], false, vrcPuzzle);
				}
			});
			isReseted = true;
		}

		function setSize(value) {
			div.css('height', value * $('#logo').width() / 9 + 'px');
			puzzleObj && puzzleObj.resize();
		}

		// 2x2 角块求解：双向 BFS。
		// 生成系用全部 6 面 x 3 次幂（18 个）。若只用 R/U/F 三面，该生成系的直径远大于 11，
		// 6+6 层搜不到某些状态（实测打乱 R U F' R2 U2 F D' L 就解不出来）。
		// 原实现是单向 BFS：合法状态要搜到第 11 层，等于枚举全部 367 万状态，
		// vis 对象属性数超过 V8 上限 -> "RangeError: Too many properties to enumerate" -> 页面卡死。
		var MOVE222_NAMES = [];
		var MOVE222_CA = [];
		(function() {
		  var faces = 'URFDLB';
		  var pows = ['', '2', "'"];
		  for (var fi = 0; fi < 6; fi++) {
		    for (var p = 0; p < 3; p++) {
		      MOVE222_NAMES.push(faces.charAt(fi) + pows[p]);
		      MOVE222_CA.push(mathlib.CubieCube.moveCube[fi * 3 + p].ca.slice());
		    }
		  }
		})();

		function invMove222(n) {
		  if (n.length == 1) {
		    return n + "'";
		  }
		  if (n.charAt(1) == "'") {
		    return n.charAt(0);
		  }
		  return n;
		}

		// 角块群乘法，纯数组运算（ca[i] = cp + co * 8）：
		// out[i].cp = a.cp[b.cp[i]]，out[i].co = a.co[b.cp[i]] + b.co[i]
		// 不用 CubieCube.CornMult，因为它读 a.co 数组，而这里只有 8 位编码的 ca。
		function cornMul222(ca, mb) {
		  var out = new Array(8);
		  for (var i = 0; i < 8; i++) {
		    var mbi = mb[i];
		    var j = mbi % 8;
		    var mbco = (mbi - j) / 8;
		    var v = ca[j];
		    var cp = v % 8;
		    var co = (v - cp) / 8;
		    out[i] = cp + ((co + mbco) % 3) * 8;
		  }
		  return out;
		}

		function cornerStateValid(ca) {
		  if (!ca || ca.length != 8) {
		    return false;
		  }
		  var seen = 0;
		  var sum = 0;
		  for (var i = 0; i < 8; i++) {
		    var v = ca[i];
		    if (typeof v != 'number' || v < 0 || v > 23) {
		      return false;
		    }
		    var cp = v % 8;
		    var co = (v - cp) / 8;
		    if (seen & (1 << cp)) {
		      return false;
		    }
		    seen |= (1 << cp);
		    sum += co;
		  }
		  return sum % 3 == 0;
		}

		function gen222Facelet(facelet) {
		  var goal = new mathlib.CubieCube();
		  try {
		    goal.fromFacelet(facelet);
		  } catch (e) {
		    return '';
		  }
		  var gca = goal.ca;
		  if (!cornerStateValid(gca)) {
		    return '';
		  }
		  var gkey = gca.join(',');
		  var skey = mathlib.CubieCube.SOLVED.ca.join(',');
		  if (skey == gkey) {
		    return '';
		  }
		  var MAX_NODES = 600000;
		  var fwd = {};
		  var bwd = {};
		  // 前向从目标态出发（得到「目标 -> k」的施加序列），后向从复原态出发（得到「k -> 复原」），
		  // 两者在 k 处相接即为「目标 -> 复原」。方向不能反，否则得到的是「复原 -> 目标」的打乱。
		  fwd[gkey] = '';
		  bwd[skey] = '';
		  var fFront = [{ ca: gca, path: '' }];
		  var bFront = [{ ca: mathlib.CubieCube.SOLVED.ca.slice(), path: '' }];
		  var fCount = 1;
		  var bCount = 1;
		  for (var depth = 0; depth < 7; depth++) {
		    var nf = [];
		    for (var i = 0; i < fFront.length; i++) {
		      var node = fFront[i];
		      for (var mi = 0; mi < MOVE222_CA.length; mi++) {
		        var nca = cornMul222(node.ca, MOVE222_CA[mi]);
		        var k = nca.join(',');
		        if (fwd[k] !== undefined) {
		          continue;
		        }
		        var p1 = node.path ? node.path + ' ' + MOVE222_NAMES[mi] : MOVE222_NAMES[mi];
		        fwd[k] = p1;
		        fCount++;
		        if (bwd[k] !== undefined) {
		          return (p1 + ' ' + bwd[k]).replace(/\s+/g, ' ').trim();
		        }
		        nf.push({ ca: nca, path: p1 });
		      }
		    }
		    fFront = nf;
		    if (fCount > MAX_NODES) {
		      return '';
		    }
		    var nbk = [];
		    for (var j = 0; j < bFront.length; j++) {
		      var node2 = bFront[j];
		      for (var mj = 0; mj < MOVE222_CA.length; mj++) {
		        var nca2 = cornMul222(node2.ca, MOVE222_CA[mj]);
		        var k2 = nca2.join(',');
		        if (bwd[k2] !== undefined) {
		          continue;
		        }
		        var mv = invMove222(MOVE222_NAMES[mj]);
		        var p2 = node2.path ? mv + ' ' + node2.path : mv;
		        bwd[k2] = p2;
		        bCount++;
		        if (fwd[k2] !== undefined) {
		          return (fwd[k2] + ' ' + p2).replace(/\s+/g, ' ').trim();
		        }
		        nbk.push({ ca: nca2, path: p2 });
		      }
		    }
		    bFront = nbk;
		    if (bCount > MAX_NODES) {
		      return '';
		    }
		    if (!fFront.length || !bFront.length) {
		      break;
		    }
		  }
		  return '';
		}
		function setState(state, prevMoves, isFast, puzzle) {
			giikerutil.log('[giiker] setState puzzle=', puzzle, 'vrcPuzzle=', vrcPuzzle, 'hasObj=', !!puzzleObj, 'vrc=', enableVRC);
			if (puzzleObj == undefined || !enableVRC) {
				return;
			}
			if (puzzle && puzzle != vrcPuzzle) {
				// 立刻同步阶数，否则下面 is222 会滞后一帧，用三阶规则判定二阶
				vrcPuzzle = puzzle;
				pendingFacelet = state;
				giikerutil.log('[giiker] setState switch -> resetVRC', puzzle);
				resetVRC(true, true, puzzle);
				// 重建完成后由 resetVRC 的回调重放这一帧，这里直接返回
				return;
			}
			var is222 = vrcPuzzle == '222';
			tmpCubie1.fromFacelet(state);
			var todoMoves = [];
			var shouldReset = true;
			for (var i = 0; i < prevMoves.length; i++) {
				todoMoves.push(prevMoves[i]);
				tmpCubie1.selfMoveStr(prevMoves[i], true);
				if (cubeutil.cubiesMatch(tmpCubie1, curVRCCubie, is222)) {
					shouldReset = false;
					break;
				}
			}
			if (shouldReset) { //cannot get current state according to prevMoves
				resetVRC(false, false, vrcPuzzle);
				curVRCCubie.fromFacelet(mathlib.SOLVED_FACELET);
				if (is222) {
					todoMoves = gen222Facelet(state);
				} else {
					todoMoves = scramble_333.genFacelet(state);
				}
			} else {
				todoMoves = todoMoves.reverse().join(' ');
			}
			var scramble;
			if (todoMoves.match(/^\s*$/) || !puzzleObj) {
				scramble = [];
			} else {
				// state / prevMoves 进到这里之前已经被 bluetoothutil 转成「视角坐标」，
				// 与 puzzleObj 显示的坐标系一致，这里不能再做一次共轭。
				scramble = puzzleObj.parseScramble(cubeutil.getConjMoves(todoMoves, true, curVRCCubie.ori));
			}
			if (scramble.length < 5) {
				puzzleObj.addMoves(scramble);
			} else {
				puzzleObj.applyMoves(scramble);
			}
			isReseted = false;
			curVRCCubie.fromFacelet(state);
		}

		function setOri(ori) {
			curOri = ori;
			if (curOri == -1 || curVRCCubie.ori == curOri) {
				return;
			}
			var todoRot = mathlib.CubieCube.rotMulI[curOri][curVRCCubie.ori];
			var todoMoves = mathlib.CubieCube.rot2str[todoRot].split(/\s+/);
			for (var i = 0; i < todoMoves.length; i++) {
				curVRCCubie.selfMoveStr(todoMoves[i]);
			}
			puzzleObj.applyMoves(puzzleObj.parseScramble(todoMoves.join(' ')));
		}

		return {
			resetVRC: resetVRC, //reset to solved
			setState: setState,
			setOri: setOri,
			setSize: setSize,
			getPuzzleObj: function() {
				return puzzleObj;
			},
			getPuzzleObj: function() {
				return puzzleObj;
			},
			getPuzzleObj: function() {
				return puzzleObj;
			}
		}
	})();

	// 供 tools/gyro.js 访问虚拟魔方的 3D 对象
	window.giikerVRC = giikerVRC;

	// 供其它模块（陀螺仪跟随）拿到虚拟魔方的 3D 对象
	window.giikerVRC = giikerVRC;

	function clearReadyTid() {
		if (waitReadyTid) {
			clearTimeout(waitReadyTid);
			waitReadyTid = 0;
		}
		if (moveReadyTid) {
			clearTimeout(moveReadyTid);
			moveReadyTid = 0;
		}
	}

	// 注意参数顺序：bluetoothutil.js 的 giikerCallback 调 callback 时传 5 个参数
	//   callback(retState, prevMoves, lastTs, deviceName, curPuzzle)
	// 第 4 个是设备名（如 'GAN251Ui_8629'），第 5 个才是 '222'/'333'。
	// 原先这里只声明 4 个参数，导致 puzzle 收到设备名、size 计算成 -1、虚拟魔方永远是 3x3。
	function giikerCallback(facelet, prevMoves, lastTs, hardware, puzzle) {
		var locTime = lastTs[1] || $.now();
		var prevFacelet = currentFacelet;
		currentFacelet = facelet;
		// 回调里没带 puzzle 时沿用上一次的值，不要退回 '333'：
		// 一旦退回，autoSwitchScrType 就会把打乱类型从 222so 抢回三阶。
		curPuzzle = puzzle || curPuzzle;
		autoSwitchScrType(curPuzzle);
		if (!enable) {
			return;
		}
		if (enableVRC) {
			giikerVRC.setState(facelet, prevMoves, false, curPuzzle);
		}
		clearReadyTid();
		var solvingMethod = kernel.getProp('vrcMP', 'n');
		if (timer.status() == -1) {
			if (canStart(currentFacelet)) {
				var delayStart = kernel.getProp('giiSD');
				if (delayStart == 's') {
					//according to scramble
					if (giikerutil.checkScramble()) {
						markScrambled(locTime);
					}
				} else if (delayStart != 'n') {
					waitReadyTid = setTimeout(function() {
						markScrambled(locTime);
					}, ~~delayStart * 1000);
				}
				var moveStart = kernel.getProp('giiSM');
				if (moveStart != 'n') {
					var movere = {
						'x4': /^([URFDLB][ '])\1\1\1/,
						'xi2': /^([URFDLB])( \1'\1 \1'|'\1 \1'\1 )/
					} [moveStart];
					if (movere.exec(prevMoves.join(''))) {
						moveReadyTid = setTimeout(function() {
							markScrambled(locTime);
						}, 1000);
					}
				}
			}
		} else if (timer.status() == -3 || timer.status() == -2) {
			if (timer.checkUseIns()) {
				insTime = locTime - timer.startTime();
			} else {
				insTime = 0;
			}
			timer.startTime(locTime);
			timer.curTime([insTime > 17000 ? -1 : (insTime > 15000 ? 2000 : 0)]);
			timer.status(cubeutil.getStepCount(solvingMethod));
			rawMoves = [];
			for (var i = 0; i < timer.status(); i++) {
				rawMoves[i] = [];
			}
			totPhases = timer.status();
			var initialProgress = cubeutil.getProgress(prevFacelet, solvingMethod);
			timer.updateMulPhase(totPhases, initialProgress, locTime);
			timer.lcd.reset(enableVRC);
			timer.lcd.fixDisplay(false, true);
		}
		if (timer.status() >= 1) {
			if (prevMoves.length > 0)
				rawMoves[timer.status() - 1].push([prevMoves[0], lastTs[0], lastTs[1]]);
			var curProgress = cubeutil.getProgress(facelet, solvingMethod);
			timer.updateMulPhase(totPhases, curProgress, locTime);

			if (isGiiSolved(currentFacelet)) {
				rawMoves.reverse();
				var pretty = cubeutil.getPrettyReconstruction(rawMoves, solvingMethod);
				var moveCnt = pretty.totalMoves;
				giikerutil.setLastSolve(pretty.prettySolve);
				timer.curTime()[1] = locTime - timer.startTime();
				timer.status(-1);
				giikerutil.reSync();
				timer.lcd.fixDisplay(false, true);
				if (timer.curTime()[1] != 0) {
					var sol = giikerutil.tsLinearFix(rawMoves.flat()); // fit deviceTime to locTime
					var cnt = 0;
					DEBUG && console.log('time fit, old=', timer.curTime());
					for (var i = 0; i < rawMoves.length; i++) {
						cnt += rawMoves[i].length;
						timer.curTime()[rawMoves.length - i] = cnt == 0 ? 0 : sol[cnt - 1][1];
					}
					DEBUG && console.log('time fit, new=', timer.curTime());
					sol = cubeutil.getConjMoves(cubeutil.moveSeq2str(sol), true);
					kernel.pushSignal('time', ["", 0, timer.curTime(), 0, [sol, curPuzzle || '333']]);
				} else if (kernel.getProp('giiMode') != 'n') {
					kernel.pushSignal('ctrl', ['scramble', 'next']);
				}
			}
		}
	}

	function canStart(facelet) {
		return facelet != mathlib.SOLVED_FACELET || kernel.getProp('giiMode') != 'n';
	}

	function isGiiSolved(facelet) {
		if (kernel.getProp('giiMode') != 'n') {
			var curScrType = (tools.getCurScramble() || [])[0];
			var chkstep = {
				'coll': 'cpll',
				'cmll': 'cmll',
				'oll': 'oll',
				'eols': 'oll',
				'wvls': 'oll',
				'zbls': 'eoll',
				'f2l': 'f2l',
				'lsll2': 'f2l'
			}[curScrType];
			if (chkstep) {
				return cubeutil.getStepProgress(chkstep, facelet) == 0;
			}
		}
		return cubeutil.isFaceletSolved(facelet, curPuzzle == '222');
	}

	function markScrambled(now) {
		clearReadyTid();
		if (timer.status() == -1) {
			if (kernel.getProp('giiMode') == 'n') {
				if (!giikerutil.checkScramble()) {
					if (curPuzzle == '333') {
						var gen = scramble_333.genFacelet(currentFacelet);
						kernel.pushSignal('scramble', ['333', cubeutil.getConjMoves(gen, true), 0]);
					}
				}
				giikerutil.markScrambled();
			} else {
				giikerutil.markScrambled(true);
			}
			timer.status(-2);
			timer.startTime(now);
			timer.lcd.reset(enableVRC);
			timer.lcd.fixDisplay(true, true);
			if (kernel.getProp('giiBS')) {
				metronome.playTick();
			}
		}
	}

	function setVRC(enable) {
		enableVRC = enable;
		enable ? div.show() : div.hide();
		if (enable) {
			giikerVRC.resetVRC(true, true, curPuzzle);
		}
	}

	$(function() {
		div.appendTo("#container");
		kernel.regListener('giikerVRC', 'property', function(signal, value) {
			if (enableVRC) {
				giikerVRC.resetVRC(true, true, curPuzzle);
				giikerVRC.setState(currentFacelet, [], false, curPuzzle);
			}
		}, /^(?:preScrT?|isTrainScr|giiOri|giiVRC)$/);
		kernel.regListener('giikerVRC', 'reset', function(signal, value) {
			if (!GiikerCube.isConnected()) {
				$.confirm('请先连接智能魔方，再使用重置功能');
				return;
			}
			if (!$.confirm('确定要把魔方状态重置为还原状态吗？（真实魔方不会转动，只重置程序里显示的状态）')) {
				return;
			}
			// 与工具面板里「重置（置为还原）」按钮走完全相同的逻辑
			lastAutoPuzzle = '';
			giikerutil.markSolved();
		});

		kernel.regListener('giikerVRC', 'scramble', function(signal, value) {
			if (enableVRC && timer.status() == -1 && kernel.getProp('giiMode') == 'at' && GiikerCube.isConnected()) {
				clearReadyTid();
				waitReadyTid = setTimeout(function() {
					markScrambled($.now());
				}, 500);
			}
		});
	});

	function startConnect() {
		giikerutil.setCallback(giikerCallback);
		kernel.showDialog([$('<div>' + BT_CONNECT_MSG.split('|')[0] + '</div>').append(timer.getBTDiv()), function () {
			giikerutil.init().catch(function(error) {
				giikerutil.log('[giiker] init failed', error);
				alert(error);
			});
		}, 0, 0], 'share', BT_CONNECT_TITLE.split('|')[0]);
	}

	timer.giiker = {
		setEnable: function(input) { //s: stackmat, m: moyu
			enable = input == 'g';
			if (enable && !GiikerCube.isConnected()) {
				startConnect();
			} else if (!enable) {
				giikerutil.stop();
			}
			setVRC(enable && kernel.getProp('giiVRC') != 'n');
		},
		onkeydown: function(keyCode) {
			var now = $.now();
			if (keyCode == 27 || keyCode == 28) {
				var recordDNF = timer.status() >= 1;
				clearReadyTid();
				timer.status(-1);
				giikerutil.reSync();
				timer.lcd.fixDisplay(false, true);
				if (recordDNF) {
					timer.curTime()[0] = -1;
					rawMoves.reverse();
					var sol = giikerutil.tsLinearFix(rawMoves.flat()); // fit deviceTime to locTime
					var cnt = 0;
					DEBUG && console.log('time fit, old=', timer.curTime());
					for (var i = 0; i < rawMoves.length; i++) {
						cnt += rawMoves[i].length;
						timer.curTime()[rawMoves.length - i] = cnt == 0 ? 0 : sol[cnt - 1][1];
					}
					DEBUG && console.log('time fit, new=', timer.curTime());
					sol = cubeutil.getConjMoves(cubeutil.moveSeq2str(sol), true);
					kernel.pushSignal('time', ["", 0, timer.curTime(), 0, [sol, curPuzzle || '333']]);
				}
			} else if (keyCode == 32 && timer.status() == -1 && kernel.getProp('giiSK') && canStart(currentFacelet)) {
				markScrambled($.now());
			}
		},
		onkeyup: function(keyCode) {
			if (enable && keyCode == 32 && !GiikerCube.isConnected()) {
				startConnect();
			}
		},
		setVRC: setVRC,
		setSize: giikerVRC.setSize
	};
}, [timer]);
