// 智能魔方陀螺仪：3D 跟随 + 标定
//
// GYRO 帧本来就和 MOVE 帧走同一条 notify 通道，固件只要在推数据我们就能收到，
// 不需要额外"开启"。实测 GAN12 ui FreePlay 一连接就在持续上报（约 20 Hz）。
//
// 固件每秒只推 20 帧出头，直接照搬会一卡一顿，所以这里对四元数做球面插值，
// 用 rAF（约 60fps）补间，视觉上连续。
//
// 坐标系：
//   GAN 设备坐标系：+X = 红面(R)，+Y = 蓝面(B)，+Z = 白面(U)
//   csTimer 世界系： +X = 红面(R)，+Y = 白面(U)，+Z = 绿面(F)
//   两者差一个绕 X 轴 -90° 的旋转，四元数 Q_M = (-√½, 0, 0, √½)
//   设备姿态 q 转到 csTimer 世界系：q' = Q_M · q_rel · conj(Q_M)
//
// 界面：不占主界面，全部收进「设置 → 虚拟&蓝牙魔方」面板底部那一行
//       （#dsGyroRow 由 kernel.js 的 generateDiv 预留）。

var dsGyro = execMain(function() {

	var Q_M = {
		w: Math.SQRT1_2,
		x: -Math.SQRT1_2,
		y: 0,
		z: 0
	};

	// 插值时间常数（毫秒）：越小越跟手、越大越平滑
	var SMOOTH_TAU = 45;
	// 跟随时的贴纸放大倍数：默认 stickerWidth=1.7，放大到接近 2 能填满缝隙
	var STICKER_SCALE = 1.15;
	// 多久没收到帧就算断开
	var IDLE_MS = 3000;

	var follow = false;
	var calibQ = null;
	var renderQ = null;      // 用于渲染的插值中间量（GAN 系相对姿态）
	var lastTick = 0;
	var rafId = 0;
	var tickTid = 0;
	var vrcWaitCnt = 0;
	var scaledObj = null;
	var lastSeenTs = 0;
	var autoFollow = true;
	var rowEls = null;

	try {
		var savedAuto = localStorage.getItem('dsGyroAuto');
		if (savedAuto === '0') {
			autoFollow = false;
		}
	} catch (e) {}

	// 轻量提示条（csTimer 本体没有 $.toast，别用它）
	function toast(msg) {
		try {
			var d = $('#dsGyroToast');
			if (!d.length) {
				d = $('<div id="dsGyroToast"></div>').css({
					position: 'fixed',
					left: '50%',
					top: '16%',
					transform: 'translateX(-50%)',
					background: 'rgba(0,0,0,0.78)',
					color: '#fff',
					padding: '0.45em 1em',
					borderRadius: '0.4em',
					fontSize: '14px',
					zIndex: 10001,
					'pointer-events': 'none',
					whiteSpace: 'nowrap'
				}).appendTo('body');
			}
			d.text(msg).stop(true, true).fadeIn(120).delay(1600).fadeOut(400);
		} catch (e) {}
	}

	function qmul(a, b) {
		return {
			w: a.w * b.w - a.x * b.x - a.y * b.y - a.z * b.z,
			x: a.w * b.x + a.x * b.w + a.y * b.z - a.z * b.y,
			y: a.w * b.y - a.x * b.z + a.y * b.w + a.z * b.x,
			z: a.w * b.z + a.x * b.y - a.y * b.x + a.z * b.w
		};
	}

	function qconj(a) {
		return {
			w: a.w,
			x: -a.x,
			y: -a.y,
			z: -a.z
		};
	}

	function qdot(a, b) {
		return a.w * b.w + a.x * b.x + a.y * b.y + a.z * b.z;
	}

	function qnorm(a) {
		var n = Math.sqrt(a.w * a.w + a.x * a.x + a.y * a.y + a.z * a.z);
		if (!n || !isFinite(n)) {
			return {
				w: 1,
				x: 0,
				y: 0,
				z: 0
			};
		}
		return {
			w: a.w / n,
			x: a.x / n,
			y: a.y / n,
			z: a.z / n
		};
	}

	// 球面线性插值：陀螺仪 20Hz，渲染 60Hz，靠它把跳变变成连续转动
	function qslerp(a, b, t) {
		var d = qdot(a, b);
		if (d < 0) {
			b = {
				w: -b.w,
				x: -b.x,
				y: -b.y,
				z: -b.z
			};
			d = -d;
		}
		if (d > 0.9995) {
			return qnorm({
				w: a.w + (b.w - a.w) * t,
				x: a.x + (b.x - a.x) * t,
				y: a.y + (b.y - a.y) * t,
				z: a.z + (b.z - a.z) * t
			});
		}
		var theta = Math.acos(d);
		var st = Math.sin(theta);
		var wa = Math.sin((1 - t) * theta) / st;
		var wb = Math.sin(t * theta) / st;
		return {
			w: a.w * wa + b.w * wb,
			x: a.x * wa + b.x * wb,
			y: a.y * wa + b.y * wb,
			z: a.z * wa + b.z * wb
		};
	}

	function getGyroStat() {
		return (typeof giikerutil != 'undefined' && giikerutil.getGyroStat) ? giikerutil.getGyroStat() : null;
	}

	function getPuzzleObj() {
		try {
			if (typeof giikerVRC == 'undefined' || !giikerVRC.getPuzzleObj) {
				return null;
			}
			return giikerVRC.getPuzzleObj();
		} catch (e) {
			return null;
		}
	}

	function getObj3d() {
		try {
			var po = getPuzzleObj();
			var tw = po && po.twisty;
			return (tw && tw._3d) || null;
		} catch (e) {
			return null;
		}
	}

	// csTimer 的渲染是事件驱动的（只在 applyMoves 末尾 render 一次），
	// 光改 quaternion 不会重绘，必须自己触发。
	function forceRender() {
		try {
			var po = getPuzzleObj();
			if (po && po.twistyScene && po.twistyScene.render) {
				po.twistyScene.render();
			}
		} catch (e) {}
	}

	// 标定之后让相机正对前面（用户 m04415/m04419 要的效果：不再是从 45° 斜上方
	// 看到「黄顶+绿前」，而是像图二那样只看到绿色前面本身）。
	// theta=0、phi=0 时 camera.position = (0, 0, dist)，视线沿 +Z，正对 F 面。
	// 停止跟随/断开连接时恢复 csTimer 默认的 (0, 6)，也就是原来的斜视角。
	function setCameraFront(on) {
		try {
			var po = getPuzzleObj();
			if (!po) {
				return;
			}
			// 正视时只看到一个面，投影比斜视小得多；顺手把相机拉近一点，
			// 否则魔方在屏幕上会突然缩成一小块。转动时仍然留有余量。
			window.__vrcDistScale = on ? 0.85 : 1;
			var sc = po.twistyScene;
			if (sc && sc.moveCamera) {
				sc.moveCamera(0, on ? 0 : 6, true);
				return;
			}
			var tw = po.twisty;
			if (tw && tw.moveCamera) {
				tw.moveCamera(0, on ? 0 : 6, true);
			}
		} catch (e) {}
	}

	// 每个小块的贴纸是独立 mesh，默认留了约 15% 的缝。跟随的时候魔方可以任意
	// 角度观察，缝就没有意义了，放大贴纸把缝填掉，只留边框黑线表示分隔。
	function setStickerScale(obj, k) {
		if (!obj || !obj.children) {
			return;
		}
		for (var i = 0; i < obj.children.length; i++) {
			var st = obj.children[i];
			if (!st || !st.children) {
				continue;
			}
			for (var j = 0; j < st.children.length; j++) {
				var m = st.children[j];
				if (m && m.scale && m.scale.set) {
					m.scale.set(k, k, 1);
				}
			}
		}
	}

	// 跟随的时候魔方会绕任意轴倾斜，默认视野装不下对角方向，会把魔方裁掉。
	function setDistScale(s) {
		window.__vrcDistScale = s;
		try {
			var po = getPuzzleObj();
			if (po && po.twistyScene && po.twistyScene.resize) {
				po.twistyScene.resize();
			}
		} catch (e) {}
	}

	function hasGyroFrame(st) {
		return st && st.frames > 0 && ($.now() - st.lastTs) < IDLE_MS;
	}

	function statusInfo() {
		var st = getGyroStat();
		if (!st || (!st.name && !st.frames && st.supported === null)) {
			return {
				color: '#999',
				text: '未连接'
			};
		}
		if (hasGyroFrame(st)) {
			return {
				color: '#2ecc40',
				text: '工作中 ' + st.rate + ' Hz'
			};
		}
		if (st.frames > 0) {
			return {
				color: '#ff9500',
				text: '已停止上报'
			};
		}
		if (st.supported === false) {
			return {
				color: '#999',
				text: '此型号不支持'
			};
		}
		return {
			color: '#ff9500',
			text: '没有数据'
		};
	}

	// 相对旋转必须在「屏幕世界系」里算：
	//   R = (Q_M·q) · conj(Q_M·calibQ)
	// 标定后 q == calibQ 时 R = 单位四元数（屏幕停在当前坐标的正立姿态）。
	// 关键：两边的 Q_M 都要乘到 q / calibQ 的左边，且 calibQ 也要参与。
	// 旧写法 Q_M·conj(calibQ)·q·conj(Q_M) 等于把相对旋转先按「标定那一刻的设备朝向」
	// 共轭了一遍：设备越歪（比如 PLL/DF 下把魔方翻成黄顶），转轴偏得越多，
	// 表现就是「换个坐标后方向和现实反了」。
	function targetQuat() {
		var st = getGyroStat();
		if (!st || !st.quat) {
			return null;
		}
		var q = qnorm(st.quat);
		if (!calibQ) {
			calibQ = q;
		}
		return qmul(qmul(Q_M, q), qconj(qmul(Q_M, calibQ)));
	}

	// 「魔方视角」(giiOri) 会把显示内容整体转过去；陀螺仪跟随时必须把它抵消，
	// 否则屏幕上看到的是「转过去之后再跟你转」，用户会觉得顺逆时针反了
	// （PLL 训练这类项目会自动切到 DF(z2) 视角，最容易撞上）。
	// 显示 = 外层 · 内容 = (q · R⁻¹) · (R · M) = q · M。
	var oriCache = null;
	var oriQ = null;
	var AXIS_Q = [
		{ w: Math.SQRT1_2, x: -Math.SQRT1_2, y: 0, z: 0 },   // x：绕 X 轴 -90°
		{ w: Math.SQRT1_2, x: 0, y: -Math.SQRT1_2, z: 0 },   // y：绕 Y 轴 -90°
		{ w: Math.SQRT1_2, x: 0, y: 0, z: -Math.SQRT1_2 }    // z：绕 Z 轴 -90°
	];

	function viewQuat() {
		var ori = 0;
		try { ori = kernel.getProp('giiOri'); } catch (e) { ori = 0; }
		if (ori == 'auto') { ori = 0; }
		ori = ~~ori;
		if (ori === oriCache && oriQ) { return oriQ; }
		oriCache = ori;
		oriQ = { w: 1, x: 0, y: 0, z: 0 };
		if (!ori) { return oriQ; }
		try {
			var rot = mathlib.CubieCube.rotMulI[ori][0];
			var parts = String(mathlib.CubieCube.rot2str[rot] || '').split(/\s+/);
			for (var i = 0; i < parts.length; i++) {
				var m = /^([xyz])(2|')?$/.exec(parts[i]);
				if (!m) { continue; }
				var aq = AXIS_Q['xyz'.indexOf(m[1])];
				var times = m[2] == '2' ? 2 : (m[2] == "'" ? 3 : 1);
				for (var k = 0; k < times; k++) { oriQ = qmul(oriQ, aq); }
			}
		} catch (e) {}
		return oriQ;
	}

	// 实际显示姿态的旋转：中心块只随整体旋转移动，读三个面的中心颜色即可唯一确定。
	// 这样不用猜是哪个设置（视角 / 训练模式预旋转 / 打乱）把魔方转过去的。
	var V_DIR = {
		U: [0, 1, 0], R: [1, 0, 0], F: [0, 0, 1],
		D: [0, -1, 0], L: [-1, 0, 0], B: [0, 0, -1]
	};
	var viewQ = null;

	function matToQuat(m) {
		var tr = m[0][0] + m[1][1] + m[2][2];
		var q = { w: 1, x: 0, y: 0, z: 0 };
		var s;
		if (tr > 0) {
			s = Math.sqrt(tr + 1) * 2;
			q.w = 0.25 * s;
			q.x = (m[2][1] - m[1][2]) / s;
			q.y = (m[0][2] - m[2][0]) / s;
			q.z = (m[1][0] - m[0][1]) / s;
		} else if (m[0][0] > m[1][1] && m[0][0] > m[2][2]) {
			s = Math.sqrt(1 + m[0][0] - m[1][1] - m[2][2]) * 2;
			q.w = (m[2][1] - m[1][2]) / s;
			q.x = 0.25 * s;
			q.y = (m[0][1] + m[1][0]) / s;
			q.z = (m[0][2] + m[2][0]) / s;
		} else if (m[1][1] > m[2][2]) {
			s = Math.sqrt(1 + m[1][1] - m[0][0] - m[2][2]) * 2;
			q.w = (m[0][2] - m[2][0]) / s;
			q.x = (m[0][1] + m[1][0]) / s;
			q.y = 0.25 * s;
			q.z = (m[1][2] + m[2][1]) / s;
		} else {
			s = Math.sqrt(1 + m[2][2] - m[0][0] - m[1][1]) * 2;
			q.w = (m[1][0] - m[0][1]) / s;
			q.x = (m[0][2] + m[2][0]) / s;
			q.y = (m[1][2] + m[2][1]) / s;
			q.z = 0.25 * s;
		}
		return qnorm(q);
	}


	function readViewQuat() {
		try {
			var po = getPuzzleObj();
			var tw = po && po.twisty;
			if (!tw || !tw.getFacelet) {
				return null;
			}
			var fc = tw.getFacelet(tw);
			if (!fc || fc.length < 54) {
				return null;
			}
			var a = fc.charAt(4);
			var b = fc.charAt(13);
			var c = fc.charAt(22);
			var va = V_DIR[a];
			var vb = V_DIR[b];
			var vc = V_DIR[c];
			if (!va || !vb || !vc || a == b || b == c || a == c) {
				return null;
			}
			var q = matToQuat([vb, va, vc]);
			// 说明：preScrT（训练模式的前置打乱，PLL 默认 z2）在切换时会触发
			// giikerVRC.resetVRC(true, true, ...) 重建虚拟魔方，所以 facelet 里
			// 的中心块已经体现了这个整体旋转，这里不需要再叠一次 preConj，否则会抵消。
			return q;
		} catch (e) {
			return null;
		}
	}

	// 设置面板里显示用：把补偿旋转描述成「绕某轴 X°」
	function quatDesc(q) {
		if (!q) {
			return '无';
		}
		var w = Math.min(1, Math.abs(q.w));
		var ang = 2 * Math.acos(w) * 180 / Math.PI;
		if (ang < 1) {
			return '无';
		}
		var x = Math.abs(q.x);
		var y = Math.abs(q.y);
		var z = Math.abs(q.z);
		var ax = (x >= y && x >= z) ? 'X' : (y >= z ? 'Y' : 'Z');
		return ax + ' 轴 ' + ang.toFixed(0) + '°';
	}

	// 给设置面板显示用：直接读虚拟魔方顶面/前面中心颜色，就是当前坐标名（DF / UF ...）
	function viewLabel() {
		try {
			var po = getPuzzleObj();
			var tw = po && po.twisty;
			var fc = (tw && tw.getFacelet) ? tw.getFacelet(tw) : null;
			if (fc && fc.length >= 54) {
				return fc.charAt(4) + fc.charAt(22);
			}
		} catch (e) {}
		return '?';
	}

	function paint(qrel) {
		var obj = getObj3d();
		if (!obj) {
			return;
		}
		// qrel 已经是「屏幕世界系」里的旋转（targetQuat 里做过 Q_M 共轭），
		// 这里不能再共轭一次，否则等于把 Q_M 应用两遍：绕 X 看不出来，
		// 但绕 Y/Z 的转动会变成绕另一个轴的转动（方向和现实对不上）。
		//
		// 另外虚拟魔方的逻辑状态（facelet）里已经包含了当前坐标的整体旋转
		// （PLL 训练模式 preScrT=z2 时中心块就是 DLF），所以也不能再左乘视角旋转，
		// 否则等于转两次、屏幕上回到 UF。
		var qc = qrel;
		obj.useQuaternion = true;
		obj.quaternion.set(qc.x, qc.y, qc.z, qc.w);
		if (obj !== scaledObj) {
			setStickerScale(obj, STICKER_SCALE);
			scaledObj = obj;
		}
		forceRender();
	}

	// 单步：读目标姿态 → 平滑插值 → 渲染。
	// 无头测试里 rAF 不一定推进，所以把这一步单独抽出来，测试可以手动 _step(dt)。
	function step(dtOverride) {
		var now = $.now();
		var dt = dtOverride || (lastTick ? Math.min(now - lastTick, 200) : 16);
		lastTick = now;
		var tgt = targetQuat();
		if (!tgt) {
			return;
		}
		if (!getObj3d()) {
			if (++vrcWaitCnt % 30 == 1 && vrcWaitCnt < 300) {
				ensureVRC();
			}
			return;
		}
		if (!renderQ) {
			renderQ = tgt;
		} else {
			var alpha = 1 - Math.exp(-dt / SMOOTH_TAU);
			renderQ = qslerp(renderQ, tgt, alpha);
		}
		paint(renderQ);
	}

	function loop() {
		if (!follow) {
			return;
		}
		rafId = requestAnimationFrame(loop);
		step();
	}

	function ensureVRC() {
		try {
			if (typeof giikerVRC != 'undefined' && giikerVRC.resetVRC) {
				giikerVRC.resetVRC(true, true, tools.getCurPuzzle() || '333');
			}
		} catch (e) {}
	}

	function startFollow() {
		if (follow) {
			return;
		}
		follow = true;
		calibQ = null;
		renderQ = null;
		lastTick = 0;
		vrcWaitCnt = 0;
		scaledObj = null;
		try {
			viewQ = readViewQuat();
		} catch (e) {}
		setDistScale(1.45);
		if (!rafId) {
			rafId = requestAnimationFrame(loop);
		}
		renderRow();
	}

	function stopFollow(reset) {
		follow = false;
		if (rafId) {
			cancelAnimationFrame(rafId);
			rafId = 0;
		}
		if (reset) {
			var obj = getObj3d();
			if (obj) {
				obj.useQuaternion = false;
				obj.quaternion.set(0, 0, 0, 1);
				setStickerScale(obj, 1);
			}
			scaledObj = null;
			setDistScale(1);
			forceRender();
			setCameraFront(false);
		}
		renderRow();
	}

	function doCalibrate() {
		var st = getGyroStat();
		if (!st || !st.quat) {
			toast('还没有收到陀螺仪数据，无法标定');
			return;
		}
		var ident = { w: 1, x: 0, y: 0, z: 0 };
		calibQ = qnorm(st.quat);
		lastTick = 0;
		// 标定 = 把「现在这个手持姿态」定义为相对零点。设备相对旋转归零后，
		// 屏幕魔方就停在它当前坐标下的正立姿态上（PLL/DF 时就是黄顶绿前）。
		// 这里必须是单位四元数，不能写 renderQ = vq，否则会先跳到错误姿态再插值回来。
		renderQ = ident;
		if (follow) {
			paint(ident);
		}
		var topFace = '?';
		try {
			var po = getPuzzleObj();
			var tw = po && po.twisty;
			var fc = (tw && tw.getFacelet) ? tw.getFacelet(tw) : null;
			if (fc) { topFace = fc.charAt(4); }
		} catch (e) {}
		setCameraFront(true);
		toast('已标定：正对前面（顶面 ' + topFace + '）');
	}

	function setAutoFollow(v) {
		autoFollow = !!v;
		try {
			localStorage.setItem('dsGyroAuto', autoFollow ? '1' : '0');
		} catch (e) {}
		if (autoFollow && hasGyroFrame(getGyroStat())) {
			startFollow();
		} else if (!autoFollow) {
			stopFollow(true);
		}
	}

	// ---- 设置面板里那一行 ----------------------------------------------------
	function buildRow() {
		var holder = $('#dsGyroRow td');
		if (!holder.length) {
			rowEls = null;
			return false;
		}
		if (rowEls && $.contains(document.documentElement, rowEls.box[0])) {
			return true;
		}
		holder.empty();
		var box = $('<div>').css({
			padding: '0.15em 0',
			whiteSpace: 'nowrap'
		});
		var dot = $('<span>').css({
			display: 'inline-block',
			width: '0.6em',
			height: '0.6em',
			borderRadius: '50%',
			background: '#999',
			marginRight: '0.3em',
			verticalAlign: 'middle'
		});
		var txt = $('<span>').text('陀螺仪');
		var btnCal = $('<input type="button">').val('标定').css({
			marginLeft: '0.4em'
		}).click(doCalibrate);
		var btnFollow = $('<input type="button">').css({
			marginLeft: '0.3em'
		}).click(function() {
			if (follow) {
				stopFollow(true);
			} else {
				if (!hasGyroFrame(getGyroStat())) {
					toast('还没有收到陀螺仪数据');
					return;
				}
				startFollow();
			}
		});
		var lab = $('<label>').css({
			marginLeft: '0.6em',
			cursor: 'pointer'
		});
		var chk = $('<input type="checkbox">').css({
			marginRight: '0.2em',
			verticalAlign: 'middle'
		}).prop('checked', autoFollow).change(function() {
			setAutoFollow($(this).prop('checked'));
		});
		lab.append(chk).append('连接后自动跟随');
		var viewTxt = $('<span>').css({
			marginLeft: '0.8em',
			opacity: 0.7
		}).text('当前坐标：?');
		box.append(dot).append(txt).append(btnCal).append(btnFollow).append(lab).append(viewTxt);
		holder.append(box);
		rowEls = {
			box: box,
			dot: dot,
			txt: txt,
			btnFollow: btnFollow,
			viewTxt: viewTxt
		};
		return true;
	}

	function renderRow() {
		if (!buildRow()) {
			return;
		}
		var info = statusInfo();
		rowEls.dot.css('background', info.color);
		rowEls.txt.text('陀螺仪：' + info.text);
		if (rowEls.viewTxt) {
			rowEls.viewTxt.text('当前坐标：' + viewLabel());
		}
		if (rowEls.btnFollow) {
			rowEls.btnFollow.val(follow ? '停止跟随' : '开始跟随');
			rowEls.btnFollow.css('opacity', hasGyroFrame(getGyroStat()) ? 1 : 0.5);
		}
	}

	// ---- 自动跟随 / 自动停止 --------------------------------------------------
	kernel.regListener('dsGyro', 'giikerGyroStart', function() {
		if (autoFollow) {
			startFollow();
		}
	});

	function tick() {
		var st = getGyroStat();
		if (st && st.lastTs && st.lastTs !== lastSeenTs) {
			lastSeenTs = st.lastTs;
		}
		// 断开或固件停推之后自动收手，避免魔方卡在歪着的姿态
		if (follow && !hasGyroFrame(st)) {
			stopFollow(true);
		}
		// 虚拟魔方的实际显示姿态可能被整体转过（视角设置 / 训练模式 / 打乱），
		// 每半秒从 facelet 重新读一次，跟随时再把它抵消掉。
		try {
			var vq = readViewQuat();
			if (vq) {
				viewQ = vq;
			}
		} catch (e) {}
		renderRow();
	}

	function startTicker() {
		if (tickTid) {
			return;
		}
		tickTid = setInterval(tick, 500);
		tick();
	}

	$(function() {
		try {
			startTicker();
		} catch (e) {}
	});

	return {
		isFollowing: function() {
			return follow;
		},
		getStatus: statusInfo,
		calibrate: doCalibrate,
		_step: step,
		_tgt: targetQuat,
		_dbg: function() { return { calibQ: calibQ, renderQ: renderQ, viewQ: viewQ }; },
		getViewQuat: function() {
			return readViewQuat();
		},
		isAuto: function() {
			return autoFollow;
		},
		stop: function() {
			stopFollow(true);
		},
		start: startFollow,
		_cam: setCameraFront
	};
});