/* Service worker: แอปเปิดได้ออฟไลน์ + เก็บแผนที่ที่เคยดู
   เพิ่มเลขเวอร์ชันนี้ทุกครั้งที่แก้ไฟล์แอป เพื่อให้เครื่องอัปเดต */
var VER = "tcc-v18";
var SHELL = VER + "-shell";
var TILES = "tcc-tiles-v1"; // ชื่อเดียวกับใน app.js
var FILES = ["./", "index.html", "app.css", "app.js", "config.js", "manifest.webmanifest",
  "icon-192.png", "icon-512.png", "icon-maskable-512.png", "apple-touch-icon.png"];
var TILE_RE = /\/\d{1,2}\/\d+\/\d+(@2x)?(\.\w+)?$/;
var TILE_MAX = 6000;

self.addEventListener("install", function (e) {
  e.waitUntil(caches.open(SHELL).then(function (c) { return c.addAll(FILES); }).then(function () { return self.skipWaiting(); }));
});

self.addEventListener("activate", function (e) {
  e.waitUntil(caches.keys().then(function (keys) {
    return Promise.all(keys.filter(function (k) { return k !== SHELL && k !== TILES; }).map(function (k) { return caches.delete(k); }));
  }).then(function () { return self.clients.claim(); }));
});

function trimTiles(c) {
  return c.keys().then(function (keys) {
    if (keys.length <= TILE_MAX) return;
    return Promise.all(keys.slice(0, keys.length - TILE_MAX + 500).map(function (k) { return c.delete(k); }));
  });
}

self.addEventListener("fetch", function (e) {
  var req = e.request;
  if (req.method !== "GET") return;
  var url = new URL(req.url);

  // แผนที่: เอาจากแคชก่อน ไม่มีค่อยโหลดแล้วเก็บไว้
  if (url.origin !== self.location.origin) {
    if (req.destination === "image" && TILE_RE.test(url.pathname)) {
      e.respondWith(caches.open(TILES).then(function (c) {
        return c.match(req).then(function (hit) {
          if (hit) return hit;
          return fetch(req).then(function (res) {
            if (res && res.ok) { c.put(req, res.clone()).then(function () { return trimTiles(c); }); }
            return res;
          });
        });
      }));
    }
    return;
  }

  // ไฟล์ของแอป: ใช้ของในแคชทันที แล้วอัปเดตเงียบๆ ครั้งต่อไป
  e.respondWith(caches.open(SHELL).then(function (c) {
    return c.match(req, { ignoreSearch: true }).then(function (hit) {
      var net = fetch(req).then(function (res) {
        if (res && res.ok) c.put(req, res.clone());
        return res;
      }).catch(function () { return hit || (req.mode === "navigate" ? c.match("index.html") : undefined); });
      return hit || net;
    });
  }));
});

self.addEventListener("notificationclick", function (e) {
  e.notification.close();
  e.waitUntil(self.clients.matchAll({ type: "window" }).then(function (list) {
    if (list.length) return list[0].focus();
    return self.clients.openWindow("./");
  }));
});
