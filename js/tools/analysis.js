"use strict";

/**
 * 解法分析（Solution Analysis）
 *
 * 把每一把复原按玩家选择的解法切成若干阶段，统计每阶段的步数（HTM）、用时、TPS。
 * 三阶支持 CFOP / ZB / Roux，二阶支持 层先 / 面先 / EG。
 *
 * 数据来源：stats 的 times 数组，times[4] = [solStr, puzzle]，
 * solStr 形如 "R@1234 U'@1290 ..."（每步带设备时间戳，已由 giiker 做过线性校准）。
 *
 * 阶段判定：
 *   三阶直接复用 cubeutil.getProgress / getStepNames（原版已有 cf4op / cf3zb / roux）。
 *   二阶原版没有，这里用 54 格 facelet 掩码自己实现，掩码按三阶索引书写
 *   （2x2 的四个角贴纸在三阶 facelet 里的位置是固定的），再用 6 轴旋转遍历，
 *   这样"从任意一面开始"都能识别。
 */
var dsAnalysis = execMain(function() {

	// ==================== 方法定义 ====================
	// steps 的下标与 progress 值一一对应：progress 从 p 掉到 p-1 的那一段存在 data[p-1]。
	// 所以 steps[0] 是最后完成的阶段，steps[N-1] 是最先完成的阶段。

	var METHODS = {
		'cfop': {
			name: 'CFOP',
			puzzle: '333',
			key: 'cf4op',
			steps: ['pll', 'oll', 'f2l-4', 'f2l-3', 'f2l-2', 'f2l-1', 'cross']
		},
		'zb': {
			name: 'ZB',
			puzzle: '333',
			key: 'cf3zb',
			steps: ['zbll', 'zbf2l', 'f2l-3', 'f2l-2', 'f2l-1', 'cross']
		},
		'roux': {
			name: 'Roux',
			puzzle: '333',
			key: 'roux',
			steps: ['l6e', 'cmll', 'sb', 'fb']
		},
		'lbl': {
			name: '层先',
			puzzle: '222',
			key: 'lbl222',
			steps: ['pbl', 'oll', 'layer']
		},
		'face': {
			name: '面先',
			puzzle: '222',
			key: 'face222',
			steps: ['pbl', 'face2', 'face1']
		},
		'eg': {
			name: 'EG',
			puzzle: '222',
			key: 'eg222',
			steps: ['eg', 'face']
		}
	};

	var STEP_NAME = {
		'cross': '十字',
		'f2l-1': 'F2L 1',
		'f2l-2': 'F2L 2',
		'f2l-3': 'F2L 3',
		'f2l-4': 'F2L 4',
		'oll': 'OLL',
		'pll': 'PLL',
		'zbf2l': 'ZBLS',
		'zbll': 'ZBLL',
		'fb': '第一桥',
		'sb': '第二桥',
		'cmll': 'CMLL',
		'l6e': 'L6E',
		'layer': '第一层',
		'pbl': 'PBL',
		'face': '一面',
		'face1': '第一面',
		'face2': '对面',
		'eg': 'EG'
	};

	// ==================== 54 格旋转表（与 cubeutil 内一致） ====================

	var cubeRots = (function genRots() {

		function faceletRot(facelet, rot) {
			var ret = [];
			for (var i = 0; i < 54; i++) {
				ret[rot[i]] = facelet[i];
			}
			return ret;
		}

		var cubeRotY = mathlib.CubieCube.rotCube[3].toPerm();
		mathlib.circle(cubeRotY, 13, 49, 40, 22);
		var cubeRotX = mathlib.CubieCube.rotCube[15].toPerm();
		mathlib.circle(cubeRotX, 4, 22, 31, 49);
		var cubeRotZ = mathlib.CubieCube.rotCube[17].toPerm();
		mathlib.circle(cubeRotZ, 4, 40, 31, 13);

		var ret = [];
		var cur = [];
		for (var i = 0; i < 54; i++) {
			cur[i] = i;
		}
		for (var a = 0; a < 24; a++) {
			ret[a] = cur.slice();
			cur = faceletRot(cur, (a & 1) ? cubeRotX : cubeRotZ);
			if (a % 6 == 5) {
				cur = faceletRot(cur, cubeRotZ);
				cur = faceletRot(cur, cubeRotZ);
			}
			if (a % 12 == 11) {
				cur = faceletRot(cur, cubeRotY);
				cur = faceletRot(cur, cubeRotY);
			}
		}
		return ret;
	})();

	function toEqus(facelet) {
		var col2equ = {};
		for (var i = 0; i < facelet.length; i++) {
			var col = facelet[i];
			if (col == '-') {
				continue;
			}
			col2equ[col] = col2equ[col] || [];
			col2equ[col].push(i);
		}
		var equs = [];
		for (var col in col2equ) {
			if (col2equ[col].length > 1) {
				equs.push(col2equ[col]);
			}
		}
		return equs;
	}

	var solvedMask = toEqus(mathlib.SOLVED_FACELET);

	// 返回 0 表示该掩码下全部同色（即这一阶段"结构对了"），1 表示不同色
	function solvedProgress(param, mask) {
		var cubeRot = cubeRots[param[1]];
		var facelet = param[0];
		mask = mask || solvedMask;
		for (var i = 0; i < mask.length; i++) {
			var equ = mask[i];
			var col = facelet[cubeRot[equ[0]]];
			for (var j = 1; j < equ.length; j++) {
				if (facelet[cubeRot[equ[j]]] != col) {
					return 1;
				}
			}
		}
		return 0;
	}

	function getProgressNAxis(facelet, process, n_axis) {
		var minRet = 99;
		for (var a = 0; a < n_axis; a++) {
			minRet = Math.min(minRet, process([facelet, a]));
		}
		return minRet;
	}

	// ==================== 二阶掩码 ====================
	//
	// 三阶 facelet 索引（54 格）：
	//   U  0  1  2 /  3  4  5 /  6  7  8      R  9 10 11 / 12 13 14 / 15 16 17
	//   F 18 19 20 / 21 22 23 / 24 25 26      D 27 28 29 / 30 31 32 / 33 34 35
	//   L 36 37 38 / 39 40 41 / 42 43 44      B 45 46 47 / 48 49 50 / 51 52 53
	//
	// 2x2 的角贴纸只落在每个面的四个角上：
	//   U: 0(ULB) 2(UBR) 6(UFL) 8(URF)
	//   R: 9(URF) 11(UBR) 15(DFR) 17(DRB)
	//   F: 18(UFL) 20(URF) 24(DLF) 26(DFR)
	//   D: 27(DLF) 29(DFR) 33(DBL) 35(DRB)
	//   L: 36(ULB) 38(UFL) 42(DBL) 44(DLF)
	//   B: 45(UBR) 47(ULB) 51(DRB) 53(DBL)

	// 某一面四个贴纸同色（只要求朝向，不管侧面）
	var M222_FACE_U = toEqus("0-0---0-0" + "---------------------------------------------");

	// U 面 + D 面各自同色（两面朝向都完成）
	var M222_FACE_UD = toEqus(
		"0-0---0-0" +
		"---------" +
		"---------" +
		"d-d---d-d" +
		"---------" +
		"---------");

	// U 层整层完成：U 面同色 + 四个侧面的 U 层贴纸各自成对同色
	var M222_LAYER_U = toEqus(
		"0-0---0-0" +
		"r-r------" +
		"f-f------" +
		"---------" +
		"l-l------" +
		"b-b------");

	// 层先的中间阶段：一层完成 且 对面已经同色（顶层朝向做完，但位置还没换）
	// 必须比 M222_LAYER_U 更严格，否则「顶面碰巧同色」会被当成已完成顶层。
	var M222_LBL_OLL = toEqus(
		"0-0---0-0" +
		"r-r------" +
		"f-f------" +
		"d-d---d-d" +
		"l-l------" +
		"b-b------");

	// 层先：3 什么都没做 / 2 第一层完成 / 1 顶层朝向完成 / 0 复原
	// 注意 solvedProgress 返回 0 表示「该掩码下已经同色/完成」，1 表示未完成。
	// 判定顺序必须从最严格到最宽松：复原 → 一层+对面同色 → 一层完成。
	function prog222LBL(param) {
		if (!solvedProgress(param)) {
			return 0;
		} else if (!solvedProgress(param, M222_LBL_OLL)) {
			return 1;
		} else if (!solvedProgress(param, M222_LAYER_U)) {
			return 2;
		}
		return 3;
	}

	// 面先：3 什么都没做 / 2 一面朝向完成 / 1 两面朝向完成 / 0 复原
	function prog222Face(param) {
		if (!solvedProgress(param)) {
			return 0;
		} else if (!solvedProgress(param, M222_FACE_UD)) {
			return 1;
		} else if (!solvedProgress(param, M222_FACE_U)) {
			return 2;
		}
		return 3;
	}

	// EG：2 什么都没做 / 1 一面朝向完成 / 0 复原
	function prog222EG(param) {
		if (!solvedProgress(param)) {
			return 0;
		} else if (!solvedProgress(param, M222_FACE_U)) {
			return 1;
		}
		return 2;
	}

	function getProgress(facelet, methodKey) {
		switch (methodKey) {
			case 'lbl222':
				return getProgressNAxis(facelet, prog222LBL, 6);
			case 'face222':
				return getProgressNAxis(facelet, prog222Face, 6);
			case 'eg222':
				return getProgressNAxis(facelet, prog222EG, 6);
			default:
				return cubeutil.getProgress(facelet, methodKey);
		}
	}

	// ==================== HTM 计数 ====================

	function MoveCounterHTM() {
		this.clear();
	}

	MoveCounterHTM.prototype.push = function(move) {
		// 兼容两种输入：数字（selfMoveStr 的返回值）或形如 "U"/"R'"/"F2" 的字符串。
		// 早期版本合并分段时直接 push 了字符串，~~("U" / 3) 会算成 0，
		// 于是所有转动都被当成同一轴、计数永远只有 1，必须在这里归一化。
		if (typeof move == 'string') {
			var ax = "URFDLB".indexOf(move.charAt(0));
			if (ax < 0) {
				return;
			}
			move = ax * 3 + Math.max(0, " 2'".indexOf(move.charAt(1) || '-'));
		}
		if (typeof move != 'number' || isNaN(move)) {
			return;
		}
		var axis = ~~(move / 3);
		var amask = 1 << axis;
		if (axis % 3 != this.lastMove % 3) {
			this.lastMove = axis;
			this.lastPow = 0;
		}
		this.moveCnt += (this.lastPow & amask) == amask ? 0 : 1;
		this.lastPow |= amask;
		this.moves.push(move);
	};

	MoveCounterHTM.prototype.clear = function() {
		this.lastPow = 0;
		this.lastMove = -3;
		this.moveCnt = 0;
		this.moves = [];
	};

	// ==================== 分析引擎 ====================

	// 判断一条成绩是不是二阶的。优先看记录里存的 puzzle 标记，
	// 老成绩没有这个字段，再退回看打乱类型。
	function is222Record(times) {
		var pz = times && times[4] && times[4][1];
		if (pz) {
			return /^222/.test(String(pz));
		}
		var scr = times && times[1];
		var type = (scr && scr[0]) || '';
		return /^222/.test(String(type));
	}

	/**
	 * 把一把成绩切成阶段。
	 * @param times  stats 里的一条成绩记录
	 * @param def    METHODS 里的方法定义
	 * @return {segments: [{idx, startMs, endMs, moveCnt, moves}], totalMs, totalMoves}
	 */
	function analyzeSolve(times, def) {
		if (!times || !times[4] || !times[4][0]) {
			return null;
		}
		var stepCount = def.steps.length;
		var solution = String(times[4][0]).split(/ +/);

		// 二阶方法不能拿去分析三阶成绩，反之亦然。
		// 二阶状态在 54 格 facelet 里棱面永远是"复原色"，
		// 所以三阶的进度函数会把它误判成已复原（progress = 0），必须挡掉。
		var recIs222 = is222Record(times);
		if ((def.puzzle == '222') != recIs222) {
			return null;
		}

		var c = new mathlib.CubieCube();
		c.ori = 0;

		// solStr 记录的是"从打乱态复原"的序列，倒着走一遍就回到打乱态
		for (var i = solution.length - 1; i >= 0; i--) {
			c.selfMoveStr(solution[i], true);
		}
		c.selfConj();

		var progress = getProgress(c.toFaceCube(), def.key);
		if (progress == undefined || progress > stepCount) {
			// 方法不匹配（例如用二阶方法分析三阶成绩）
			return null;
		}

		var data = [];
		var cnter = new MoveCounterHTM();
		var stepMoves = [];
		var tsStart = c.tstamp || 0;
		var tsFirst = tsStart;

		for (var i = 0; i < solution.length; i++) {
			var effMove = c.selfMoveStr(solution[i], false);
			if (effMove != undefined) {
				tsFirst = Math.min(tsFirst, c.tstamp);
				cnter.push(effMove);
				var axis = ~~(effMove / 3);
				stepMoves.push(["URFDLB".charAt(axis % 6) + " 2'".charAt(effMove % 3), c.tstamp]);
				if (axis >= 6) { // slice move：HTM 里按两层算
					stepMoves.push(["DLBURF".charAt(axis % 6) + "'2 ".charAt(effMove % 3), c.tstamp]);
				}
			}
			var curProg = getProgress(c.toFaceCube(), def.key);
			if (curProg < progress) {
				data[--progress] = [tsStart, tsFirst, c.tstamp, cnter.moveCnt, stepMoves.slice()];
				while (progress > curProg) {
					data[--progress] = [c.tstamp, c.tstamp, c.tstamp, 0, []];
				}
				cnter.clear();
				stepMoves = [];
				tsStart = c.tstamp;
				tsFirst = c.tstamp;
			}
		}

		// 把"只差一步"的空段并到下一段（原版 calcRecons 的处理）。
		// 二阶不做这一步：二阶的 PBL 本来就只有 1~2 步，合并会把整个 PBL 段吞掉，
		// 变成"第一层 4 步、PBL 0 步"这种明显不合理的显示。
		if (def.puzzle != '222') {
			for (var i = 0; i < data.length; i++) {
				if (!data[i] || data[i][3] != 1) {
					continue;
				}
				var j = i + 1;
				while (j < data.length && data[j] && data[j][3] == 0) {
					j++;
				}
				if (j >= data.length) {
					break;
				}
				cnter.clear();
				var ts = data[i][2];
				Array.prototype.push.apply(data[j][4], data[i][4]);
				for (var m = 0; m < data[j][4].length; m++) {
					cnter.push(data[j][4][m][0]);
				}
				data[j][2] = ts;
				data[j][3] = cnter.moveCnt;
				data[i] = [ts, ts, ts, 0, []];
			}
		}

		var segments = [];
		for (var i = 0; i < stepCount; i++) {
			var d = data[i] || [0, 0, 0, 0, []];
			var startMs = d[0] || 0;
			var endMs = d[2] || 0;
			segments.push({
				idx: i,
				name: def.steps[i],
				startMs: startMs,
				endMs: endMs,
				timeMs: Math.max(0, endMs - startMs),
				moveCnt: d[3] || 0,
				moves: d[4] || []
			});
		}

		// 总用时 = 最后一个动作的时间戳（相对计时开始）。
		// 不能取循环里最后一次赋的值：segments 是按 def.steps 排的，
		// 最后一个元素是「最先完成的阶段」，它的 endMs 反而最小。
		var totalMs = 0;
		var totalMoves = 0;
		for (var i = 0; i < segments.length; i++) {
			if (segments[i].moveCnt > 0) {
				totalMs = Math.max(totalMs, segments[i].endMs);
				totalMoves += segments[i].moveCnt;
			}
		}

		// 观察时间：解法串第一个转动的时间戳，就是"从计时开始到第一次转动"的间隔
		var inspMs = 0;
		var m0 = /@(\d+)/.exec(solution[0] || '');
		if (m0) {
			inspMs = ~~m0[1];
		}

		return {
			segments: segments,
			totalMs: totalMs,
			totalMoves: totalMoves,
			inspectionMs: inspMs
		};
	}

	// ==================== 历史平均 ====================

	var cache = {};

	// 每把成绩属于哪种解法。单独存在一个属性里，不去动 stats 的成绩结构，
	// 免得影响导入导出。key = 日期秒 + 完成毫秒，同一分组里几乎不会重复。
	var tagStore = null;

	function recKey(times) {
		return String((times && times[3]) || 0) + '_' +
			String((times && times[0] && times[0][1]) || 0);
	}

	function loadTags() {
		if (tagStore) {
			return tagStore;
		}
		try {
			tagStore = JSON.parse(localStorage.getItem('dsTags') || '{}') || {};
		} catch (e) {
			tagStore = {};
		}
		return tagStore;
	}

	function saveTags() {
		try {
			localStorage.setItem('dsTags', JSON.stringify(loadTags()));
		} catch (e) {}
	}

	function tagOf(times) {
		return loadTags()[recKey(times)] || null;
	}

	function setTag(times, methodKey) {
		loadTags()[recKey(times)] = methodKey;
		saveTags();
	}

	function scrTextOf(times) {
		var s = times && times[1];
		if (!s) {
			return '';
		}
		if (typeof s == 'string') {
			return s;
		}
		return s[1] || s[0] || '';
	}

	function timesLen() {
		var t = stats.getTimesStatsTable();
		return t ? t.timesLen : 0;
	}

	function isPuzzleOf(times, puzzle) {
		return (puzzle == '222') == is222Record(times);
	}

	function collectAll(methodKey) {
		var def = METHODS[methodKey];
		var n = timesLen();
		var key = methodKey + '|' + n;
		if (cache[key]) {
			return cache[key];
		}
		var list = [];
		var dirty = false;
		for (var i = 0; i < n; i++) {
			var times = stats.timesAt(i);
			if (!times || !times[4] || !times[4][0] || times[0][0] < 0) {
				continue;
			}
			if (!isPuzzleOf(times, def.puzzle)) {
				continue;
			}
			// 这把是别的解法练的，不算进当前解法的统计
			var tag = tagOf(times);
			if (tag && tag != methodKey) {
				continue;
			}
			if (!tag) {
				// 老成绩没有标记，归到第一次分析它的解法上
				loadTags()[recKey(times)] = methodKey;
				dirty = true;
			}
			var res = analyzeSolve(times, def);
			if (res) {
				res.idx = i;
				list.push(res);
			}
		}
		if (dirty) {
			saveTags();
		}
		cache = {};
		cache[key] = list;
		return list;
	}

	function averageOf(list) {
		var stepCount = -1;
		var sum = [];
		var cnt = [];
		var totMs = 0, totMv = 0, totCnt = 0;
		for (var i = 0; i < list.length; i++) {
			var segs = list[i].segments;
			if (stepCount < 0) {
				stepCount = segs.length;
				for (var j = 0; j < stepCount; j++) {
					sum.push([0, 0, 0]); // [步数, 用时, 次数]
					cnt.push(0);
				}
			}
			if (totMs == 0 && list[i].totalMs > 0) {
				totMs = 0;
			}
			totMs += list[i].totalMs;
			totMv += list[i].totalMoves;
			totCnt++;
			for (var j = 0; j < segs.length && j < stepCount; j++) {
				if (segs[j].moveCnt <= 0) {
					continue;
				}
				sum[j][0] += segs[j].moveCnt;
				sum[j][1] += segs[j].timeMs;
				sum[j][2]++;
			}
		}
		var avg = [];
		for (var j = 0; j < stepCount; j++) {
			if (sum[j][2] == 0) {
				avg.push(null);
			} else {
				avg.push({
					moveCnt: sum[j][0] / sum[j][2],
					timeMs: sum[j][1] / sum[j][2]
				});
			}
		}
		return {
			segments: avg,
			totalMs: totCnt ? totMs / totCnt : 0,
			totalMoves: totCnt ? totMv / totCnt : 0,
			count: totCnt
		};
	}

	// ==================== UI ====================

	var div = $('<div id="dsBox" style="font-size:0.72em;line-height:1.2;max-width:34em;">');
	var methodSelect = $('<select style="font-size:1em;">');
	var table = $('<table class="table" style="width:100%;table-layout:fixed;margin-top:0.15em;">');
	var infoSpan = $('<span style="margin-left:0.6em;opacity:0.8;"></span>');
	var scrDiv = $('<div style="opacity:0.55;font-size:0.92em;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;"></div>');
	var isEnable = false;
	var curMethod = 'cfop';

	function curPuzzleType() {
		var pz = '';
		try {
			pz = (tools.getCurPuzzle && tools.getCurPuzzle()) || '';
		} catch (e) {
			pz = '';
		}
		return /^222/.test(String(pz)) ? '222' : '333';
	}

	// 每种魔方默认用哪个解法：二阶用户多半练面先，三阶用 CFOP
	var PREFER = {
		'333': 'cfop',
		'222': 'face'
	};

	function firstMethodOf(pz) {
		if (PREFER[pz] && METHODS[PREFER[pz]] && METHODS[PREFER[pz]].puzzle == pz) {
			return PREFER[pz];
		}
		for (var k in METHODS) {
			if (METHODS[k].puzzle == pz) {
				return k;
			}
		}
		return null;
	}

	// 二阶只列二阶解法，三阶只列三阶解法
	function rebuildMethodSelect() {
		var pz = curPuzzleType();
		var keep = curMethod;
		if (!METHODS[keep] || METHODS[keep].puzzle != pz) {
			keep = firstMethodOf(pz);
		}
		if (!keep) {
			return;
		}
		methodSelect.empty();
		for (var k in METHODS) {
			if (METHODS[k].puzzle != pz) {
				continue;
			}
			methodSelect.append($('<option>').val(k).text(METHODS[k].name));
		}
		curMethod = keep;
		methodSelect.val(keep);
		kernel.setProp('dsMethod', keep);
	}

	(function initMethodSelect() {
		methodSelect.change(function() {
			curMethod = methodSelect.val();
			kernel.setProp('dsMethod', curMethod);
			update();
		});
		rebuildMethodSelect();
	})();

	function fmtMs(ms) {
		if (!ms || ms <= 0) {
			return '-';
		}
		return kernel.pretty(Math.round(ms));
	}

	function fmtNum(v, digits) {
		if (v == null) {
			return '-';
		}
		return (Math.round(v * Math.pow(10, digits)) / Math.pow(10, digits)).toFixed(digits);
	}

	function tps(mv, ms) {
		if (!mv || !ms || ms <= 0) {
			return null;
		}
		return mv / (ms / 1000);
	}

	function update() {
		if (!isEnable) {
			return;
		}
		var def = METHODS[curMethod];
		if (!def) {
			return;
		}
		var all = collectAll(curMethod);

		// 当前这一把 = 最后一条属于该解法、且能切分成功的成绩
		var cur = null;
		var n = timesLen();
		for (var i = n - 1; i >= 0; i--) {
			var times = stats.timesAt(i);
			if (!times || !times[4] || !times[4][0] || times[0][0] < 0) {
				continue;
			}
			if (!isPuzzleOf(times, def.puzzle)) {
				continue;
			}
			var tg = tagOf(times);
			if (tg && tg != curMethod) {
				continue;
			}
			cur = analyzeSolve(times, def);
			if (cur) {
				cur.idx = i;
				cur.number = i + 1;
				cur.scramble = scrTextOf(times);
				cur.timeMs = (times[0] && times[0][1]) || 0;
				break;
			}
		}

		var avg = averageOf(all);

		var head = '<tr>' +
			'<th rowspan="2" style="text-align:left;width:22%;">阶段</th>' +
			'<th colspan="3">本次</th>' +
			'<th colspan="3">平均</th></tr>' +
			'<tr><th>步</th><th>用时</th><th>TPS</th>' +
			'<th>步</th><th>用时</th><th>TPS</th></tr>';
		var rows = [];
		var order = [];
		for (var i = def.steps.length - 1; i >= 0; i--) {
			order.push(i);
		}

		var tIns = 0, tExec = 0;
		for (var k = 0; k < order.length; k++) {
			var i = order[k];
			var seg = cur ? cur.segments[i] : null;
			var ag = avg.segments[i];
			var name = STEP_NAME[def.steps[i]] || def.steps[i];
			var cmv = seg && seg.moveCnt > 0 ? seg.moveCnt : null;
			var cms = seg && seg.moveCnt > 0 ? seg.timeMs : null;
			var atps = ag ? tps(ag.moveCnt, ag.timeMs) : null;
			rows.push('<tr>' +
				'<td style="text-align:left;">' + name + '</td>' +
				'<td>' + (cmv == null ? '-' : cmv) + '</td>' +
				'<td>' + fmtMs(cms) + '</td>' +
				'<td>' + fmtNum(tps(cmv, cms), 2) + '</td>' +
				'<td>' + fmtNum(ag && ag.moveCnt, 2) + '</td>' +
				'<td>' + fmtMs(ag && ag.timeMs) + '</td>' +
				'<td>' + fmtNum(atps, 2) + '</td>' +
				'</tr>');
			if (seg && seg.moveCnt > 0) {
				tIns += 0;
				tExec += seg.timeMs;
			}
		}

		rows.push('<tr style="font-weight:bold;">' +
			'<td style="text-align:left;">合计</td>' +
			'<td>' + (cur ? cur.totalMoves : '-') + '</td>' +
			'<td>' + (cur ? fmtMs(cur.totalMs) : '-') + '</td>' +
			'<td>' + (cur ? fmtNum(tps(cur.totalMoves, cur.totalMs), 2) : '-') + '</td>' +
			'<td>' + (avg.count ? fmtNum(avg.totalMoves, 2) : '-') + '</td>' +
			'<td>' + (avg.count ? fmtMs(avg.totalMs) : '-') + '</td>' +
			'<td>' + (avg.count ? fmtNum(tps(avg.totalMoves, avg.totalMs), 2) : '-') + '</td>' +
			'</tr>');

		var info = $('<div style="padding:0.1em 0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;">')
			.append('解法：').append(methodSelect).append(infoSpan);

		infoSpan.empty();
		if (cur) {
			infoSpan.append('第 ' + cur.number + ' 把 · ' + fmtMs(cur.timeMs) + ' · ');
		}
		infoSpan.append('已分析 ' + avg.count + ' 把');
		if (cur && cur.inspectionMs > 0) {
			infoSpan.append(' · 观察 ' + fmtMs(cur.inspectionMs) + ' / 执行 ' + fmtMs(cur.totalMs));
		}

		scrDiv.empty();
		if (cur && cur.scramble) {
			scrDiv.text('打乱：' + cur.scramble).attr('title', cur.scramble);
		} else if (!cur) {
			scrDiv.text(avg.count > 0 ? '这一把切分不出来，往前找也失败了' : '还没有属于「' + def.name + '」的成绩');
		}

		table.empty()
			.append(head)
			.append(rows.join(''));
		div.empty().append(info).append(scrDiv).append(table);
	}

	function execFunc(fdiv, signal) {
		if (!(isEnable = (fdiv != undefined))) {
			return;
		}
		fdiv.empty().append(div);
		if (signal == 'scramble' || signal == 'property') {
			rebuildMethodSelect();
		}
		update();
	}

	$(function() {
		kernel.regProp('analysis', 'dsMethod', ~3,
			(typeof PROPERTY_DSMETHOD != 'undefined' ? PROPERTY_DSMETHOD : 'Solution Analysis Method'),
			['cfop', ['cfop', 'zb', 'roux', 'lbl', 'face', 'eg'], ['CFOP', 'ZB', 'Roux', '层先', '面先', 'EG']], 1);
		curMethod = kernel.getProp('dsMethod', 'cfop');
		rebuildMethodSelect();
		methodSelect.val(curMethod);
		tools.regTool('analysis', '解法分析', execFunc);
		kernel.regListener('analysis', 'time', function() {
			cache = {};
			// 新成绩立刻归到当前解法，避免被之后切换的解法抢走。
			// 延后一点，等 stats 把这条成绩真正写进 times。
			setTimeout(function() {
				var n = timesLen();
				if (n > 0) {
					var t = stats.timesAt(n - 1);
					if (t && t[4] && t[4][0]) {
						setTag(t, curMethod);
					}
				}
				update();
			}, 60);
		});
		kernel.regListener('analysis', 'property', function(signal, value) {
			if (/^(?:dsMethod|toolsfunc)$/.test(value[0])) {
				cache = {};
				if (value[0] == 'dsMethod') {
					curMethod = kernel.getProp('dsMethod', 'cfop');
					methodSelect.val(curMethod);
				}
				update();
			}
		}, /^(?:dsMethod|toolsfunc)$/);
	});

	return {
		analyzeSolve: analyzeSolve,
		getMethods: function() {
			return METHODS;
		},
		getProgress: getProgress,
		execFunc: execFunc
	};
});
