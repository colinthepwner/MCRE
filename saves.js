(function () {
    'use strict';

    var MOUNT = '/games';
    var SCAN_MS = 3000;
    var API = 'api/';
    var LARGE_FILE_BYTES = 1024 * 1024;
    var SMALL_CHANGE_DEBOUNCE_MS = 4000;
    var LARGE_FILE_INTERVAL_MS = 60000;
    var MTIME_SLOP_MS = 1500;

    var Module = window.Module = window.Module || {};

    var fs = null;
    var origSyncfs = null;
    var ready = false;
    var busy = false;
    var idbSnap = null;
    var disk = {
        enabled: false,
        down: false,
        storeId: null,
        synced: {}
    };

    function toMs(t) { return t instanceof Date ? t.getTime() : +t; }
    function same(a, b) { return !!a && !!b && a.s === b.s && Math.abs(a.m - b.m) <= MTIME_SLOP_MS; }
    function keys(o) { return Object.keys(o); }

    function changedPaths(prev, cur) {
        var out = [];
        keys(cur).forEach(function (p) {
            var a = prev[p], b = cur[p];
            if (!a || a.m !== b.m || a.s !== b.s) out.push(p);
        });
        keys(prev).forEach(function (p) { if (!cur[p]) out.push(p); });
        return out;
    }

    function syncedKey() { return 'mcpe.diskSync.' + disk.storeId; }
    function loadSynced() {
        try { return JSON.parse(localStorage.getItem(syncedKey()) || '{}') || {}; } catch (e) { return {}; }
    }
    function storeSynced() {
        try { localStorage.setItem(syncedKey(), JSON.stringify(disk.synced)); } catch (e) {   }
    }

    function fetchWithTimeout(url, opts, ms) {
        opts = opts || {};
        var ctl = typeof AbortController !== 'undefined' ? new AbortController() : null;
        if (ctl) opts.signal = ctl.signal;
        opts.cache = 'no-store';
        var t = ctl ? setTimeout(function () { ctl.abort(); }, ms || 10000) : null;
        return fetch(url, opts).finally(function () { if (t) clearTimeout(t); });
    }

    function httpError(what, r) {
        var e = new Error(what + ': HTTP ' + r.status);
        e.status = r.status;
        return e;
    }

    function apiUrl(path, rel, m) {
        var u = API + path;
        if (rel != null) u += '?p=' + encodeURIComponent(rel);
        if (m != null) u += '&m=' + Math.floor(m);
        return u;
    }

    function scan() {
        var out = {};
        (function walk(dir, rel) {
            var names;
            try { names = fs.readdir(dir); } catch (e) { return; }
            for (var i = 0; i < names.length; i++) {
                var name = names[i];
                if (name === '.' || name === '..') continue;
                var full = dir + '/' + name;
                var r = rel ? rel + '/' + name : name;
                var st;
                try { st = fs.stat(full); } catch (e) { continue; }
                if (fs.isDir(st.mode)) walk(full, r);
                else if (fs.isFile(st.mode)) out[r] = { m: toMs(st.mtime), s: st.size };
            }
        })(MOUNT, '');
        return out;
    }

    function writeLocal(rel, bytes, mtime) {
        var full = MOUNT + '/' + rel;
        var dir = full.substring(0, full.lastIndexOf('/'));
        fs.mkdirTree(dir);
        fs.writeFile(full, bytes);
        fs.utime(full, mtime, mtime);
    }

    function deleteLocal(rel) {
        var full = MOUNT + '/' + rel;
        try { fs.unlink(full); } catch (e) { return; }
        var dir = full.substring(0, full.lastIndexOf('/'));
        while (dir.length > MOUNT.length) {
            try {
                if (fs.readdir(dir).length > 2) break;
                fs.rmdir(dir);
            } catch (e) { break; }
            dir = dir.substring(0, dir.lastIndexOf('/'));
        }
    }

    function persistIdb() {
        return new Promise(function (resolve) {
            origSyncfs.call(fs, false, function (err) {
                if (err) console.warn('[saves] IndexedDB save failed:', err);
                resolve(!err);
            });
        });
    }

    function diskList() {
        return fetchWithTimeout(apiUrl('saves'), {}, 3000).then(function (r) {
            if (!r.ok) throw new Error('HTTP ' + r.status);
            return r.json();
        });
    }

    function diskGet(rel) {
        return fetchWithTimeout(apiUrl('saves/file', rel), {}, 30000).then(function (r) {
            if (!r.ok) throw new Error('GET ' + rel + ': HTTP ' + r.status);
            return r.arrayBuffer();
        }).then(function (buf) { return new Uint8Array(buf); });
    }

    function diskPut(rel, bytes, mtime) {
        return fetchWithTimeout(apiUrl('saves/file', rel, mtime), {
            method: 'PUT',
            headers: { 'X-MC-Save': '1', 'X-MC-Store': disk.storeId, 'Content-Type': 'application/octet-stream' },
            body: bytes,
            keepalive: bytes.length < 60000
        }, 30000).then(function (r) {
            if (!r.ok) throw httpError('PUT ' + rel, r);
        });
    }

    function diskDelete(rel) {
        return fetchWithTimeout(apiUrl('saves/file', rel), {
            method: 'DELETE', headers: { 'X-MC-Save': '1', 'X-MC-Store': disk.storeId }, keepalive: true
        }, 10000).then(function (r) {
            if (!r.ok) throw httpError('DELETE ' + rel, r);
        });
    }

    function reconcile() {
        return diskList().then(function (listing) {
            if (!listing || !listing.storeId || !listing.files) throw new Error('unexpected listing');
            disk.storeId = listing.storeId;
            disk.synced = loadSynced();

            var remote = {};
            listing.files.forEach(function (f) { remote[f.p] = { m: f.m, s: f.s }; });
            var local = scan();
            var base = disk.synced;

            var all = {};
            [remote, local, base].forEach(function (o) { keys(o).forEach(function (k) { all[k] = 1; }); });

            var downloads = [], uploads = [], localDeletes = [];
            keys(all).forEach(function (p) {
                var d = remote[p], l = local[p], b = base[p];
                if (d && l) {
                    if (same(d, l)) base[p] = l;
                    else if (b && same(b, l)) downloads.push(p);
                    else if (b && same(b, d)) uploads.push(p);
                    else if (d.m > l.m) downloads.push(p);
                    else uploads.push(p);
                } else if (d) {
                    downloads.push(p);
                } else if (l) {
                    if (b && same(b, l)) localDeletes.push(p);
                    else uploads.push(p);
                } else {
                    delete base[p];
                }
            });

            var chain = Promise.resolve();
            downloads.forEach(function (p) {
                chain = chain.then(function () {
                    return diskGet(p).then(function (bytes) {
                        writeLocal(p, bytes, remote[p].m);
                        base[p] = { m: remote[p].m, s: bytes.length };
                    });
                });
            });
            localDeletes.forEach(function (p) {
                chain = chain.then(function () { deleteLocal(p); delete base[p]; });
            });
            uploads.forEach(function (p) {
                chain = chain.then(function () { return pushFile(p); });
            });
            return chain.then(function () {
                disk.enabled = true;
                storeSynced();
                if (downloads.length || uploads.length || localDeletes.length) {
                    console.log('[saves] synced with saves folder: ' + downloads.length + ' restored, ' +
                        uploads.length + ' backed up, ' + localDeletes.length + ' removed');
                }
            });
        });
    }

    function pushFile(rel) {
        var full = MOUNT + '/' + rel;
        var st = fs.stat(full);
        var sig = { m: toMs(st.mtime), s: st.size };
        var bytes = fs.readFile(full);
        return diskPut(rel, bytes, sig.m).then(function () { disk.synced[rel] = sig; });
    }

    function pushChanges(local) {
        var work = [];
        keys(local).forEach(function (p) {
            var b = disk.synced[p];
            if (!b || b.m !== local[p].m || b.s !== local[p].s) work.push(['put', p]);
        });
        keys(disk.synced).forEach(function (p) { if (!local[p]) work.push(['del', p]); });
        if (!work.length) return Promise.resolve(false);

        function run(w) {
            if (w[0] === 'put') {
                try { fs.stat(MOUNT + '/' + w[1]); } catch (e) { return Promise.resolve(); }
                return pushFile(w[1]);
            }
            return diskDelete(w[1]).then(function () { delete disk.synced[w[1]]; });
        }
        function isLarge(w) { return w[0] === 'put' && local[w[1]].s >= LARGE_FILE_BYTES; }

        var first = Promise.all(work.filter(function (w) { return !isLarge(w); }).map(run));
        var chain = first;
        work.filter(isLarge).forEach(function (w) {
            chain = chain.then(function () { return run(w); });
        });
        return chain.then(function () { storeSynced(); return true; });
    }

    var lastPersist = 0;

    function tick(force) {
        if (!ready || busy) return Promise.resolve();
        var local = scan();
        var idbChanges = changedPaths(idbSnap || {}, local);
        var diskBehind = disk.enabled && !disk.down && changedPaths(disk.synced, local).length > 0;
        if (!idbChanges.length && !diskBehind) return Promise.resolve();

        var since = Date.now() - lastPersist;
        var small = idbChanges.some(function (p) { return !local[p] || local[p].s < LARGE_FILE_BYTES; });
        if (!force && since < LARGE_FILE_INTERVAL_MS && !(small && since >= SMALL_CHANGE_DEBOUNCE_MS))
            return Promise.resolve();

        busy = true;
        lastPersist = Date.now();
        var useDisk = disk.enabled && !disk.down;

        var idbJob = idbChanges.length
            ? persistIdb().then(function (ok) { if (ok) idbSnap = local; return ok; })
            : Promise.resolve(false);
        var diskJob = !useDisk ? Promise.resolve(false) : pushChanges(local).then(null, function (err) {
            disk.down = true;
            if (err && err.status === 409) {
                console.warn('[saves] saves folder changed under this page; disk sync paused until reload');
                toast('Saves folder changed - restart the game to sync', 5000);
                return false;
            }
            console.warn('[saves] could not write to the saves folder:', err);
            toast('Launcher closed - saving in the browser only', 4000);
            watchForServer();
            return false;
        });

        return Promise.all([idbJob, diskJob]).then(function (r) {
            if (useDisk ? r[1] : r[0]) toast('Saved');
        }).finally(function () { busy = false; });
    }

    var watching = false;
    function watchForServer() {
        if (watching) return;
        watching = true;
        var iv = setInterval(function () {
            diskList().then(function (listing) {
                clearInterval(iv);
                watching = false;
                if (listing.storeId === disk.storeId) {
                    disk.down = false;
                    toast('Launcher back - saving to disk again', 3000);
                    tick(true);
                }
            }, function () {   });
        }, 15000);
    }

    function gameSaveNow() {
        try {
            var asyncBusy = typeof Asyncify !== 'undefined' && Asyncify.currData;
            if (!asyncBusy && typeof Module._mcSaveNow === 'function') Module._mcSaveNow();
        } catch (e) {
            console.warn('[saves] save-now failed:', e);
        }
    }

    function flush() {
        if (!ready) return;
        gameSaveNow();
        busy = false;
        tick(true);
    }

    var toastEl = null, toastTimer = null;
    function toast(text, ms) {
        if (!document.body) return;
        if (!toastEl) {
            toastEl = document.createElement('div');
            toastEl.style.cssText = 'position:fixed;right:12px;bottom:10px;z-index:9998;pointer-events:none;' +
                'font:13px/1.4 monospace;color:#fff;background:rgba(0,0,0,.55);padding:4px 10px;' +
                'border-radius:3px;opacity:0;transition:opacity .4s';
            document.body.appendChild(toastEl);
        }
        toastEl.textContent = text;
        toastEl.style.opacity = '1';
        clearTimeout(toastTimer);
        toastTimer = setTimeout(function () { toastEl.style.opacity = '0'; }, ms || 1500);
    }

    function boot(callback, err) {
        ready = true;
        idbSnap = scan();
        setInterval(function () { tick(false); }, SCAN_MS);
        document.addEventListener('visibilitychange', function () {
            if (document.visibilityState === 'hidden') flush();
        });
        window.addEventListener('pagehide', flush);

        var lastEarlyFlush = 0;
        function earlyFlush() {
            var now = Date.now();
            if (now - lastEarlyFlush < 5000) return;
            lastEarlyFlush = now;
            setTimeout(function () { gameSaveNow(); tick(true); }, 250);
        }
        document.addEventListener('pointerlockchange', function () {
            if (!document.pointerLockElement) earlyFlush();
        });
        window.addEventListener('blur', earlyFlush);

        try {
            callback(err);
        } catch (e) {
            if (e !== 'unwind') throw e;
        }
    }

    Module.preRun = Module.preRun || [];
    if (typeof Module.preRun === 'function') Module.preRun = [Module.preRun];
    Module.preRun.push(function () {
        fs = Module.FS;
        origSyncfs = fs.syncfs;
        var first = true;

        fs.syncfs = function (populate, callback) {
            if (typeof populate === 'function') { callback = populate; populate = false; }

            if (populate && first) {
                first = false;
                return origSyncfs.call(fs, true, function (err) {
                    if (err) console.warn('[saves] IndexedDB load error:', err);
                    reconcile().then(function () {
                        return persistIdb();
                    }, function (e) {
                        console.log('[saves] saves folder not available, using browser storage only (' + e.message + ')');
                    }).finally(function () {
                        boot(callback, err);
                    });
                });
            }

            return origSyncfs.call(fs, populate, function (err) {
                if (callback) callback(err);
                if (!populate) setTimeout(function () { tick(false); }, 300);
            });
        };
    });

    try {
        if (navigator.storage && navigator.storage.persist) navigator.storage.persist();
    } catch (e) {   }
})();
