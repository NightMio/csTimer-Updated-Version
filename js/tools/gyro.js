// 智能魔方陀螺仪：状态指示 + 3D 跟随 + 标定
//
// GYRO 帧本来就和 MOVE 帧走同一条 notify 通道，固件只要在推数据我们就能收到，
// 不需要额外"开启"。实测 GAN12 ui FreePlay 一连接就在持续上报。
//
// 固件每秒只推 20 帧出头，直接照搬会一卡一顿，所以这里对四元数做球面插值，
// 用 rAF（约 60fps）补间，视觉上连续。
//
// 坐标系：
//   GAN 设备坐标系：+X = 红面(R)，+Y = 蓝面(B)，+Z = 白面(U)
//   csTimer 世界系： +X = 红面(R)，+Y = 白面(U)，+Z = 绿面(F)
//   两者差一个绕 X 轴 -90° 的旋转，四元数 Q_M = (-√½, 0, 0, √½)
//   设备姿态 q 转到 csTimer 世界系：q' = Q_M · q_rel · conj(Q_M)

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

	var follow = false;
	var calibQ = null;
	var renderQ = null;      // 用于渲染的插值中间量（GAN 系相对姿态）
	var lastTick = 0;
	var rafId = 0;
	var div = null;
	var txtEl = null;
	var dotEl = null;
	var btnFollow = null;
	var tickTid = 0;
	var vrcWaitCnt = 0;
	var attached = false;
	var autoShowPatched = false;
	var scaledObj = null;

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
		return st && st.frames > 0 && ($.now() - st.lastTs) < 3000;
	}

	function statusInfo() {
		var st = getGyroStat();
		if (!st || (!st.name && !st.frames && st.supported === null)) {
			return {
				color: '#888',
				text: '未连接'
			};
		}
		if (hasGyroFrame(st)) {
			return {
				color: '#2ecc40',
				text: st.rate + ' Hz'
			};
		}
		if (st.frames > 0) {
			return {
				color: '#ff9500',
				text: '已停'
			};
		}
		if (st.supported === false) {
			return {
				color: '#888',
				text: '不支持'
			};
		}
		return {
			color: '#ff9500',
			text: '无数据'
		};
	}

	function targetQuat() {
		var st = getGyroStat();
		if (!st || !st.quat) {
			return null;
		}
		var q = qnorm(st.quat);
		if (!calibQ) {
			calibQ = q;
		}
		return qmul(qconj(calibQ), q);
	}

	function paint(qrel) {
		var obj = getObj3d();
		if (!obj) {
			return;
		}
		var qc = qmul(qmul(Q_M, qrel), qconj(Q_M));
		obj.useQuaternion = true;
		obj.quaternion.set(qc.x, qc.y, qc.z, qc.w);
		if (obj !== scaledObj) {
			setStickerScale(obj, STICKER_SCALE);
			scaledObj = obj;
		}
		forceRender();
	}

	function loop() {
		if (!follow) {
			return;
		}
		rafId = requestAnimationFrame(loop);
		var now = $.now();
		var dt = lastTick ? Math.min(now - lastTick, 200) : 16;
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

	function ensureVRC() {
		try {
			if (typeof giikerVRC != 'undefined' && giikerVRC.resetVRC) {
				giikerVRC.resetVRC(true, true, tools.getCurPuzzle() || '333');
			}
		} catch (e) {}
	}

	function startFollow() {
		follow = true;
		calibQ = null;
		renderQ = null;
		lastTick = 0;
		vrcWaitCnt = 0;
		scaledObj = null;
		setDistScale(1.45);
		if (!rafId) {
			rafId = requestAnimationFrame(loop);
		}
		renderButtons();
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
		}
		renderButtons();
	}

	function doCalibrate() {
		var st = getGyroStat();
		if (!st || !st.quat) {
			$.toast('还没有收到陀螺仪数据，无法标定');
			return;
		}
		calibQ = qnorm(st.quat);
		renderQ = null;
		$.toast('已把魔方当前朝向设为默认朝向');
	}

	function renderButtons() {
		if (!btnFollow) {
			return;
		}
		btnFollow.text(follow ? '停止' : '跟随');
		btnFollow.css('background', follow ? '#2ecc40' : '');
		btnFollow.css('color', follow ? '#fff' : '');
	}

	function render() {
		var info = statusInfo();
		if (dotEl) {
			dotEl.css('background', info.color);
		}
		if (txtEl) {
			txtEl.text(info.text);
		}
		if (btnFollow) {
			btnFollow.css('opacity', hasGyroFrame(getGyroStat()) ? 1 : 0.45);
		}
		attachDiv();
		patchAutoShow();
	}

	// 挂在虚拟魔方画布正下方。用 fixed 定位手动跟住画布，
	// 既不会受父容器 font-size / overflow 影响，也不会跑出窗口。
	function positionDiv() {
		if (!div || !attached) {
			return;
		}
		try {
			var c = $('#vrcDiv canvas');
			if (!c.length) {
				div.css({
					top: 'auto',
					bottom: '12px'
				});
				return;
			}
			var off = c.offset();
			var top = off.top + c.outerHeight() + 2;
			var maxTop = $(window).height() - 26;
			if (top > maxTop) {
				top = maxTop;
			}
			if (top < 0) {
				top = 0;
			}
			div.css({
				bottom: 'auto',
				top: top + 'px'
			});
		} catch (e) {}
	}

	function attachDiv() {
		if (!div) {
			return;
		}
		if (!attached) {
			$('body').append(div);
			div.css({
				position: 'fixed',
				left: '50%',
				transform: 'translateX(-50%)',
				background: 'rgba(255,255,255,0.85)',
				border: '1px solid rgba(0,0,0,0.12)',
				borderRadius: '4px',
				padding: '2px 8px',
				zIndex: 9997
			});
			attached = true;
		}
		positionDiv();
	}

	function buildDiv() {
		if (div) {
			return;
		}
		// 字号必须用 px：父容器（虚拟魔方）的 font-size 是按画布尺寸算出来的，
		// 用 em 会被放大成几百像素。
		div = $("<div id='dsGyroDiv'></div>").css({
			fontSize: '13px',
			lineHeight: '20px',
			color: '#444',
			whiteSpace: 'nowrap',
			pointerEvents: 'auto'
		});
		dotEl = $("<span></span>").css({
			display: 'inline-block',
			width: '8px',
			height: '8px',
			borderRadius: '50%',
			background: '#888',
			marginRight: '5px',
			verticalAlign: 'middle'
		});
		txtEl = $("<span></span>").text('陀螺仪');
		btnFollow = $("<button type='button'>跟随</button>").css({
			marginLeft: '6px',
			fontSize: '12px',
			lineHeight: '16px',
			padding: '0 6px',
			cursor: 'pointer',
			border: '1px solid rgba(0,0,0,0.2)',
			borderRadius: '3px',
			background: '#f6f6f6'
		}).click(function() {
			if (follow) {
				stopFollow(true);
			} else {
				if (!hasGyroFrame(getGyroStat())) {
					$.toast('还没有陀螺仪数据，无法跟随');
					return;
				}
				startFollow();
			}
		});
		var btnCal = $("<button type='button'>标定</button>").css({
			marginLeft: '4px',
			fontSize: '12px',
			lineHeight: '16px',
			padding: '0 6px',
			cursor: 'pointer',
			border: '1px solid rgba(0,0,0,0.2)',
			borderRadius: '3px',
			background: '#f6f6f6'
		}).click(doCalibrate);
		div.append(dotEl).append(txtEl).append(btnFollow).append(btnCal);
	}

	// 跟随 csTimer「计时过程中隐藏所有元素」：计时开始/结束时同步显隐。
	// setAutoShow 挂在 kernel.ui 上，不是 kernel 本身。
	function patchAutoShow() {
		if (autoShowPatched) {
			return;
		}
		var ui = kernel && kernel.ui;
		if (!ui || typeof ui.setAutoShow != 'function') {
			return;
		}
		autoShowPatched = true;
		var orig = ui.setAutoShow;
		ui.setAutoShow = function(visible) {
			orig.apply(ui, arguments);
			var vis = visible || !kernel.getProp('ahide');
			div.toggle(!!vis);
		};
	}

	function startTicker() {
		if (tickTid) {
			return;
		}
		tickTid = setInterval(render, 500);
		render();
	}

	$(function() {
		try {
			buildDiv();
			startTicker();
		} catch (e) {}
	});

	return {
		isFollowing: function() {
			return follow;
		},
		getStatus: statusInfo,
		stop: function() {
			stopFollow(true);
		}
	};
});
