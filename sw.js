// csTimer 本地版 Service Worker
// 目标：让「安装到桌面」的 PWA 在断网时也能打开。
//
// 策略：
//   - 页面导航（navigate）：网络优先，失败回落到缓存 —— 保证更新能及时生效
//   - 其它同源 GET：缓存优先 + 后台更新（stale-while-revalidate）—— 首屏快、离线可用
//   - 跨域请求（WCA 登录等）：一律放行，不碰

var CACHE_NAME = 'cstimer-ds-v1';

// 首屏必需的最小集合，装完就能离线开门
var PRECACHE = [
	'./',
	'./index.html',
	'./css/style.css',
	'./cstimer.webmanifest'
];

self.addEventListener('install', function (event) {
	event.waitUntil(
		caches.open(CACHE_NAME).then(function (cache) {
			// 单个失败不影响整体安装
			return Promise.all(PRECACHE.map(function (url) {
				return cache.add(new Request(url, { cache: 'reload' })).catch(function () {});
			}));
		}).then(function () {
			return self.skipWaiting();
		})
	);
});

self.addEventListener('activate', function (event) {
	event.waitUntil(
		caches.keys().then(function (names) {
			return Promise.all(names.map(function (name) {
				if (name !== CACHE_NAME) {
					return caches.delete(name);
				}
			}));
		}).then(function () {
			return self.clients.claim();
		})
	);
});

self.addEventListener('fetch', function (event) {
	var req = event.request;
	if (req.method !== 'GET') {
		return;
	}
	var url;
	try {
		url = new URL(req.url);
	} catch (e) {
		return;
	}
	if (url.origin !== self.location.origin) {
		return;
	}
	if (url.pathname.indexOf('/report') >= 0) {
		return;
	}

	// 页面本体：网络优先
	if (req.mode === 'navigate') {
		event.respondWith(
			fetch(req).then(function (res) {
				var copy = res.clone();
				caches.open(CACHE_NAME).then(function (cache) {
					cache.put(req, copy);
				});
				return res;
			}).catch(function () {
				return caches.match(req).then(function (hit) {
					return hit || caches.match('./index.html');
				});
			})
		);
		return;
	}

	// 静态资源：先给缓存，同时后台更新
	event.respondWith(
		caches.match(req).then(function (hit) {
			var fetching = fetch(req).then(function (res) {
				if (res && res.status === 200 && res.type === 'basic') {
					var copy = res.clone();
					caches.open(CACHE_NAME).then(function (cache) {
						cache.put(req, copy);
					});
				}
				return res;
			}).catch(function () {
				return hit || Response.error();
			});
			return hit || fetching;
		})
	);
});
