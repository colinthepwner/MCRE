(function () {
    'use strict';

    var MOUNT = '/games';
    var SCAN_MS = 3000;
    var API = 'api/';
    var LARGE_FILE_BYTES = 1024 * 1024;
    function isBig(path, size) { return size >= LARGE_FILE_BYTES || path.indexOf('region/') >= 0; }
    var SMALL_CHANGE_DEBOUNCE_MS = 4000;
    var LARGE_FILE_INTERVAL_MS = 60000;
    var BLOCK_BYTES = 64 * 1024;
    var BLOCK_DB = 'mcre-big-files';
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

    function syncIdbOnce() {
        return new Promise(function (resolve) {
            origSyncfs.call(fs, false, function (err) {
                if (err) console.warn('[saves] IndexedDB save failed:', err);
                resolve(!err);
            });
        });
    }

    function persistIdb() {
        return syncIdbOnce().then(function (ok) {
            if (ok) return true;
            resetIdbConnections();
            return syncIdbOnce();
        });
    }

    function resetIdbConnections() {
        try {
            if (typeof IDBFS !== 'undefined' && IDBFS.dbs) {
                Object.keys(IDBFS.dbs).forEach(function (k) {
                    try { IDBFS.dbs[k].close(); } catch (e) {   }
                    delete IDBFS.dbs[k];
                });
            }
        } catch (e) {   }
        closeBlockDb();
    }

    function patchIdbfs() {
        if (typeof IDBFS === 'undefined' || IDBFS.__mcreBig) return;
        IDBFS.__mcreBig = true;
        var orig = IDBFS.getLocalSet;
        IDBFS.getLocalSet = function (mount, callback) {
            return orig.call(IDBFS, mount, function (err, set) {
                if (!err && set && set.entries) {
                    Object.keys(set.entries).forEach(function (path) {
                        try {
                            var st = fs.stat(path);
                            if (fs.isFile(st.mode) && isBig(path, st.size)) delete set.entries[path];
                        } catch (e) {   }
                    });
                }
                callback(err, set);
            });
        };
    }

    var bdb = null;
    var stored = {};

    function openBlockDb() {
        if (bdb) return Promise.resolve(bdb);
        return new Promise(function (resolve, reject) {
            var rq = indexedDB.open(BLOCK_DB, 1);
            rq.onupgradeneeded = function () {
                rq.result.createObjectStore('meta');
                rq.result.createObjectStore('blocks');
            };
            rq.onsuccess = function () {
                bdb = rq.result;
                bdb.onclose = function () { bdb = null; };
                bdb.onversionchange = function () { closeBlockDb(); };
                resolve(bdb);
            };
            rq.onerror = function () { reject(rq.error); };
        });
    }

    function closeBlockDb() {
        if (bdb) { try { bdb.close(); } catch (e) {   } }
        bdb = null;
    }

    function hashRange(data, start, end) {
        var h = 0x811c9dc5, i = start;
        if (((data.byteOffset + start) & 3) === 0) {
            var words = (end - start) >> 2;
            var w = new Int32Array(data.buffer, data.byteOffset + start, words);
            for (var k = 0; k < words; k++) h = Math.imul(h ^ w[k], 0x01000193);
            i = start + words * 4;
        }
        for (; i < end; i++) h = Math.imul(h ^ data[i], 0x01000193);
        return h >>> 0;
    }

    function hashesOf(data) {
        var out = [];
        for (var i = 0; i * BLOCK_BYTES < data.length; i++)
            out.push(hashRange(data, i * BLOCK_BYTES, Math.min(data.length, (i + 1) * BLOCK_BYTES)));
        return out;
    }

    function loadBig() {
        return openBlockDb().then(function (db) {
            return new Promise(function (resolve, reject) {
                var tx = db.transaction(['meta', 'blocks'], 'readonly');
                var blocks = tx.objectStore('blocks');
                var files = {};
                tx.objectStore('meta').openCursor().onsuccess = function (e) {
                    var c = e.target.result;
                    if (!c) return;
                    var meta = c.value, path = c.key;
                    var f = files[path] = { meta: meta, buf: new Uint8Array(meta.s), got: 0 };
                    for (var i = 0; i < meta.n; i++) (function (i) {
                        blocks.get(path + '#' + i).onsuccess = function (ev) {
                            var v = ev.target.result;
                            if (v) { f.buf.set(new Uint8Array(v), i * meta.b); f.got++; }
                        };
                    })(i);
                    c.continue();
                };
                tx.oncomplete = function () {
                    keys(files).forEach(function (p) {
                        var f = files[p];
                        if (f.got !== f.meta.n) {
                            console.warn('[saves] incomplete copy of ' + p + ' in browser storage; not restoring it');
                            return;
                        }
                        var cur = null;
                        try { cur = fs.stat(MOUNT + '/' + p); } catch (e) {   }
                        if (cur && toMs(cur.mtime) > f.meta.m) return;
                        writeLocal(p, f.buf, f.meta.m);
                        stored[p] = { m: f.meta.m, s: f.meta.s, hashes: hashesOf(f.buf) };
                    });
                    resolve();
                };
                tx.onerror = tx.onabort = function () { reject(tx.error); };
            });
        });
    }

    function persistBig(local) {
        var todo = keys(local).filter(function (p) {
            var l = local[p], st = stored[p];
            return isBig(p, l.s) && !(st && st.m === l.m && st.s === l.s);
        });
        var gone = keys(stored).filter(function (p) { return !local[p] || !isBig(p, local[p].s); });
        if (!todo.length && !gone.length) return Promise.resolve(true);
        function yieldTask() { return new Promise(function (r) { setTimeout(r, 0); }); }
        var work = [];
        function prepare(p) {
            var full = MOUNT + '/' + p;
            var st, data;
            try { st = fs.stat(full); data = fs.readFile(full); } catch (e) { return; }
            var prev = stored[p];
            var hashes = hashesOf(data);
            var puts = [];
            for (var i = 0; i < hashes.length; i++) {
                if (prev && prev.hashes[i] === hashes[i]) continue;
                puts.push([p + '#' + i, data.slice(i * BLOCK_BYTES, Math.min(data.length, (i + 1) * BLOCK_BYTES))]);
            }
            var dels = [];
            if (prev) for (var j = hashes.length; j < prev.hashes.length; j++) dels.push(p + '#' + j);
            work.push({ p: p, puts: puts, dels: dels, meta: { s: data.length, m: toMs(st.mtime), n: hashes.length, b: BLOCK_BYTES }, hashes: hashes });
        }
        var chain = Promise.resolve();
        todo.forEach(function (p) { chain = chain.then(yieldTask).then(function () { prepare(p); }); });
        return chain.then(openBlockDb).then(function (db) {
            return new Promise(function (resolve, reject) {
                var tx = db.transaction(['meta', 'blocks'], 'readwrite');
                var metas = tx.objectStore('meta'), blocks = tx.objectStore('blocks');
                work.forEach(function (w) {
                    w.puts.forEach(function (kv) { blocks.put(kv[1], kv[0]); });
                    w.dels.forEach(function (k) { blocks.delete(k); });
                    metas.put(w.meta, w.p);
                });
                gone.forEach(function (p) {
                    metas.delete(p);
                    for (var i = 0; i < stored[p].hashes.length; i++) blocks.delete(p + '#' + i);
                });
                tx.oncomplete = function () {
                    work.forEach(function (w) { stored[w.p] = { m: w.meta.m, s: w.meta.s, hashes: w.hashes }; });
                    gone.forEach(function (p) { delete stored[p]; });
                    resolve(true);
                };
                tx.onerror = tx.onabort = function () { reject(tx.error); };
            });
        }).then(null, function (err) {
            console.warn('[saves] saving big files to browser storage failed:', err);
            closeBlockDb();
            return false;
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
        function isLarge(w) { return w[0] === 'put' && isBig(w[1], local[w[1]].s); }

        var first = Promise.all(work.filter(function (w) { return !isLarge(w); }).map(run));
        var chain = first;
        work.filter(isLarge).forEach(function (w) {
            chain = chain.then(function () { return run(w); });
        });
        return chain.then(function () { storeSynced(); return true; });
    }

    var lastIdb = 0, lastDisk = 0;
    var forceQueued = false;

    function tick(force) {
        if (!ready) return Promise.resolve();
        if (busy) {
            if (force) forceQueued = true;
            return Promise.resolve();
        }
        var local = scan();
        var now = Date.now();
        var idbChanges = changedPaths(idbSnap || {}, local);
        var useDisk = disk.enabled && !disk.down;
        var diskChanges = useDisk ? changedPaths(disk.synced, local) : [];
        var diskSmall = diskChanges.some(function (p) { return !local[p] || !isBig(p, local[p].s); });

        var idbDue = idbChanges.length > 0 && (force || now - lastIdb >= SMALL_CHANGE_DEBOUNCE_MS);
        var diskDue = diskChanges.length > 0 && (force || now - lastDisk >= LARGE_FILE_INTERVAL_MS ||
            (diskSmall && now - lastDisk >= SMALL_CHANGE_DEBOUNCE_MS));
        if (!idbDue && !diskDue) return Promise.resolve();

        busy = true;
        if (idbDue) lastIdb = now;
        if (diskDue) lastDisk = now;
        useDisk = useDisk && diskDue;

        var idbJob = idbDue
            ? persistBig(local).then(function (bigOk) {
                return persistIdb().then(function (ok) { if (ok && bigOk) idbSnap = local; return ok && bigOk; });
            })
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
            if (useDisk ? r[1] : (r[0] && force)) toast('Saved');
        }).finally(function () {
            busy = false;
            if (forceQueued) {
                forceQueued = false;
                setTimeout(function () { tick(true); }, 0);
            }
        });
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
            else resetIdbConnections();
        });
        window.addEventListener('pagehide', flush);
        window.addEventListener('pageshow', function (e) { if (e.persisted) resetIdbConnections(); });
        document.addEventListener('freeze', flush);

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
                patchIdbfs();
                return origSyncfs.call(fs, true, function (err) {
                    if (err) console.warn('[saves] IndexedDB load error:', err);
                    loadBig().then(null, function (e) {
                        console.warn('[saves] could not read big files from browser storage:', e);
                    }).then(function () {
                        return persistBig(scan());
                    }).then(function () {
                        return reconcile();
                    }).then(function () {
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
