'use strict';

var JVM = null, vm = null, ready = false, failed = false;
var SRC = 'net/minecraft/src/';
var T = null;
var J = null;

function post(o, transfer) { self.postMessage(o, transfer || []); }

self.onmessage = function (ev) {
	var m = ev.data;
	try {
		if (m.t === 'init') init(m);
		else if (m.t === 'tables') T = m;
		else if (m.t === 'job') job(m);
	} catch (e) {
		if (m.t === 'init') { failed = true; post({ t: 'failed', why: String(e && e.message || e) }); }
		else if (m.t === 'job') post({ t: 'done', id: m.id, fallback: true, why: 'worker: ' + String(e && e.message || e) });
	}
};

function init(m) {
	importScripts(m.jvmUrl);
	JVM = self.JVM;
	var maps = m.maps || {};
	var first = m.mods.length ? m.mods[0].tag || 'mcp152' : 'mcp152';
	vm = JVM.create({
		log: function (level, text) { if (level === 'error' && m.debug) console.warn('[java gen] ' + text); },
		install: function (v) {
			v.$tag = first;
			if (maps[first]) JVM.loadMap(v, maps[first], first);
			if (maps.babric && first !== 'babric') JVM.loadMap(v, maps.babric, 'babric');
			JVM.installMc152(v);
		},
	});
	vm.gameTexture = function () { return true; };
	vm.gameResource = function () { return null; };
	var dimKeys = m.dimKeys || {};
	vm.mcDimKeyOf = function (d) { return dimKeys[d] || null; };
	vm.$tag = first;
	vm.$legacy = vm.$tag === 'mcp147';
	var ident = function (x) { return x; };
	vm.game = { mode: 'define', blockToGame: ident, blockToJava: ident, itemToGame: ident, itemToJava: ident };
	var cfg = {};
	m.mods.forEach(function (md) { cfg[md.id] = md.cfg || {}; });
	var running = function () {
		var fr = vm && vm.frames;
		if (fr) for (var i = fr.length - 1; i >= 0; i--) { var s = fr[i].m.cls.source; if (s && s !== 'client' && s.indexOf('lib:') !== 0) return s; }
		return vm && vm.currentMod || '_';
	};
	var norm = function (p) { return String(p || '').replace(/^\/+/, '').replace(/\/+$/, ''); };
	var at = function () { return cfg[running()] || {}; };
	vm.fs = {
		read: function (p) { var f = at()[norm(p)]; return f || null; },
		write: function (p, b) { at()[norm(p)] = b; },
		exists: function (p) { var n = norm(p), c = at(); if (c[n]) return true; return Object.keys(c).some(function (k) { return k.indexOf(n + '/') === 0; }); },
		isDir: function (p) { var n = norm(p), c = at(); return !c[n] && Object.keys(c).some(function (k) { return k.indexOf(n + '/') === 0; }); },
		list: function (p) { var n = norm(p), c = at(), out = {}; Object.keys(c).forEach(function (k) { if (!n || k.indexOf(n + '/') === 0) { var rest = n ? k.slice(n.length + 1) : k; out[rest.split('/')[0]] = 1; } }); return Object.keys(out); },
		mkdirs: function () {}, remove: function () {},
	};
	vm.fs.$mods = true;
	var classesOf = {};
	m.mods.forEach(function (md) {
		var tag = md.tag || 'mcp152';
		if (maps[tag] && !(vm.$maps && vm.$maps[tag])) JVM.loadMap(vm, maps[tag], tag);
		(vm.$modTag || (vm.$modTag = {}))[md.id] = tag;
		var classes = [];
		Object.keys(md.files).forEach(function (k) {
			if (/\.class$/i.test(k)) {
				var cn = k.slice(0, -6);
				if (/(^|[/])(module-info|package-info)$/.test(cn)) return;
				vm.addClassFile(cn, md.files[k], md.id);
				classes.push(cn);
			} else if (!/^META-INF[/]/i.test(k)) vm.resources[k] = md.files[k];
		});
		classesOf[md.id] = classes;
	});
	var libs = [];
	m.mods.forEach(function (md) { (JVM.runtimeLibsFor ? JVM.runtimeLibsFor(vm, md.files) : []).forEach(function (l) { libs.push(l); }); });
	Promise.all(libs.map(function (lib) {
		return fetch(lib.file).then(function (r) { if (!r.ok) throw new Error(r.status); return r.arrayBuffer(); })
			.then(function (b) { return JVM.readZip(new Uint8Array(b)); })
			.then(function (ents) { JVM.addRuntimeLib(vm, lib, ents); }, function () { });
	})).then(function () {
		m.mods.forEach(function (md) {
			var files = md.files, classes = classesOf[md.id];
			vm.currentMod = md.id;
			if (JVM.applyJavaSettings && md.settings) {
				var mfs = { read: function (p) { return cfg[md.id][norm(p)] || null; }, write: function (p, b) { cfg[md.id][norm(p)] = b; },
					exists: function (p) { return !!cfg[md.id][norm(p)]; }, isDir: function () { return false; }, list: function () { return []; }, mkdirs: function () {}, remove: function () {} };
				JVM.applyJavaSettings(mfs, md.settings);
			}
			var kind = JVM.javaKind ? JVM.javaKind(vm, classes, files) : { loader: '', version: '', cant: '' };
			if (kind.cant) return;
			var forgeMods = JVM.findForgeMods ? JVM.findForgeMods(vm, classes) : [];
			if ((kind.loader === 'Babric' && JVM.babricLoad) || (kind.loader === 'BTA' && JVM.btaLoad)) {
				var fjson = null;
				try { fjson = JSON.parse(new TextDecoder().decode(files['fabric.mod.json'])); } catch (e) { fjson = {}; }
				(vm.$stFiles = vm.$stFiles || {})[md.id] = files;
				(vm.$stSaved = vm.$stSaved || {})[md.id] = md.settings || null;
				if (kind.loader === 'BTA') JVM.btaLoad(vm, md.id, fjson, files, classes);
				else JVM.babricLoad(vm, md.id, fjson, files, classes);
			}
			classes.filter(function (c) { return /^(net[/]minecraft[/]src[/])?mod_[^/$]+$/.test(c); }).forEach(function (cn) {
				JVM.run(vm, function () {
					if (JVM.mlProps) JVM.mlProps(vm, vm.loadClass(cn));
					var o = vm.newObject(vm.loadClass(cn));
					vm.callVirtual(o, '<init>', '()V', []);
					vm.callVirtual(o, 'load', '()V', []);
				});
			});
			if (forgeMods.length) {
				var info = null;
				try { var mi = files['mcmod.info']; if (mi) info = JSON.parse(new TextDecoder().decode(mi)); } catch (e) { info = null; }
				if (info && !Array.isArray(info)) info = info.modList || info.modlist || [info];
				JVM.forgeLoad(vm, forgeMods, classes, info);
			}
		});
		ready = true;
		post({ t: 'ready' });
	}).catch(function (e) { failed = true; post({ t: 'failed', why: String(e && e.message || e) }); });
}

var W = 32, D = 32, H = 128;
function inside(x, y, z) { return x >= J.x0 && x < J.x0 + W && z >= J.z0 && z < J.z0 + D && y >= 0 && y < H; }
function idx(x, y, z) { return ((x - J.x0) * D + (z - J.z0)) * H + y; }
function rawAt(x, y, z) {
	if (y < 0 || y >= H) return 0;
	if (!inside(x, y, z)) { J.fallback = J.fallback || 'outside the copy'; return 0; }
	return J.blocks[idx(x, y, z)];
}
function setRaw(x, y, z, raw) {
	if (y < 0 || y >= H) return;
	if (!inside(x, y, z)) { J.fallback = J.fallback || 'outside the copy'; return; }
	var i = idx(x, y, z);
	if (J.blocks[i] === raw) return;
	if (!J.orig.has(i)) J.orig.set(i, J.blocks[i]);
	J.blocks[i] = raw;
}
function genJava(raw) {
	var v = T && raw >= 0 && raw < T.java.length ? T.java[raw] : -1;
	if (v < 0) { J.fallback = J.fallback || 'block ' + raw + ' not in the tables'; return 0; }
	return v;
}
function covered(x, y, z) {
	for (var yy = (y < 0 ? 0 : y + 1); yy < H; ++yy) { var t = rawAt(x, yy, z) & 255; if (t > 0 && T.solid[t]) return true; }
	return false;
}
var bridge = {
	mode: 'gen',
	blockToGame: function (x) { return x; }, blockToJava: function (x) { return x; },
	itemToGame: function (x) { return x; }, itemToJava: function (x) { return x; },
	tileP: function (x, y, z) { return genJava(rawAt(x | 0, y | 0, z | 0)); },
	op: function (name, x, y, z, b, d) {
		x |= 0; y |= 0; z |= 0;
		switch (name) {
		case 'tile': { var p = genJava(rawAt(x, y, z)); return { id: Math.floor(p / 65536), data: p % 65536 }; }
		case 'settile': {
			if (!b) { setRaw(x, y, z, 0); return 0; }
			var jid = b | 0, jd = jid === 38 ? 1 : d | 0;
			var k = jid >= 0 && jid < 4096 && jd >= 0 && jd < 16 ? jid * 16 + jd : -1;
			var wv = k >= 0 && T ? T.game[k] : 0;
			if (wv === 0) { J.fallback = J.fallback || 'java block ' + jid + ':' + jd + ' not in the tables'; return 0; }
			if (wv > 0) { wv--; var gid = wv & 255, gd = wv >> 16 ? (wv >> 8) & 255 : d | 0; setRaw(x, y, z, gid | (gd & 15) << 8); }
			return 0;
		}
		case 'setdata': {
			var raw = rawAt(x, y, z), gid2 = raw & 255;
			if (T.mod[raw]) { if (T.state[raw]) J.fallback = J.fallback || 'state of a mod block'; return 0; }
			setRaw(x, y, z, gid2 | ((b | 0) & 15) << 8);
			return 0;
		}
		case 'destroy': setRaw(x, y, z, 0); return 0;
		case 'sky': return covered(x, y, z) ? 0 : 1;
		case 'fullbright': return covered(x, y, z) ? 0 : 15;
		case 'bright': return covered(x, y, z) ? 0 : 15;
		case 'gentick': if (inside(x, y, z)) J.ticks.push(x, y, z); else J.fallback = J.fallback || 'outside the copy'; return 0;
		case 'biome': {
			if (!inside(x, 64, y)) { J.fallback = J.fallback || 'biome outside the copy'; return 'plains'; }
			return J.biomeNames[J.biomes[(x - J.x0) * D + (y - J.z0)]] || 'plains';
		}
		default:
			J.fallback = J.fallback || 'game action "' + name + '"';
			return undefined;
		}
	},
};
function genMods(r) {
	var own = function (o, key) { var m = o.cls.findMethod(key); return !!(m && m.cls.name !== SRC + 'BaseMod'); };
	return r.mods.filter(function (m) {
		return own(m, 'generateSurface(Lnet/minecraft/src/World;Ljava/util/Random;II)V') || own(m, 'generateNether(Lnet/minecraft/src/World;Ljava/util/Random;II)V');
	});
}
function job(m) {
	if (!ready || !T || T.bind !== m.bind) { post({ t: 'done', id: m.id, fallback: true, why: ready ? 'tables' : 'not ready' }); return; }
	J = { id: m.id, x0: m.x0, z0: m.z0, blocks: m.blocks, biomes: m.biomes, biomeNames: m.biomeNames, orig: new Map(), ticks: [], fallback: null };
	var r = vm.mcReg, cx = m.cx, cz = m.cz, dim = m.dim, seed = m.seed;
	var gm = dim === 0 || dim === -1 ? genMods(r) : [];
	var fg = !!(JVM.forgeWantsGen && JVM.forgeWantsGen(vm));
	var sg = !!(JVM.stationWantsGen && JVM.stationWantsGen(vm));
	var dk = m.dimKey || null;
	var dg = dim === 0 && !!(JVM.decorWantsGen && JVM.decorWantsGen(vm));
	var pendingBefore = JVM.structPendingCount ? JVM.structPendingCount(vm) : 0;
	vm.game = bridge; vm.mcSeed = seed | 0; vm.mcDim = dim; vm.steps = 0;
	JVM.run(vm, function () {
		var world = JVM.mc152.worldObj(vm);
		var wrnd = world && world[':rand'];
		if (wrnd) vm.callVirtual(wrnd, 'setSeed', '(J)V', [BigInt.asIntN(64, BigInt(cx) * 341873128712n + BigInt(cz) * 132897987541n + BigInt(seed | 0))]);
		var S = BigInt(seed | 0), rnd = vm.newObject(vm.loadClass('java/util/Random'));
		vm.callVirtual(rnd, '<init>', '(J)V', [S]);
		var l1 = vm.callVirtual(rnd, 'nextLong', '()J', []) / 2n * 2n + 1n;
		var l2 = vm.callVirtual(rnd, 'nextLong', '()J', []) / 2n * 2n + 1n;
		vm.callVirtual(rnd, 'setSeed', '(J)V', [BigInt.asIntN(64, BigInt.asIntN(64, BigInt(cx) * l1 + BigInt(cz) * l2) ^ S)]);
		gm.forEach(function (mod) {
			vm.currentMod = mod.cls.source || vm.currentMod;
			JVM.run(vm, function () {
				if (dim === 0) vm.callVirtual(mod, 'generateSurface', '(Lnet/minecraft/src/World;Ljava/util/Random;II)V', [world, rnd, cx * 16, cz * 16]);
				else vm.callVirtual(mod, 'generateNether', '(Lnet/minecraft/src/World;Ljava/util/Random;II)V', [world, rnd, cx * 16, cz * 16]);
			});
		});
		if (dg) JVM.decorGenerate(vm, world, cx, cz, rnd);
		if (dk && JVM.dimPopulate) JVM.dimPopulate(vm, dk, cx, cz);
		if (fg) JVM.forgeGenerate(vm, cx, cz);
		if (sg) JVM.stationGenerate(vm, world, cx, cz, rnd, dim);
	});
	if (JVM.structPendingCount && JVM.structPendingCount(vm) > pendingBefore) {
		J.fallback = J.fallback || 'queued for the level';
		if (JVM.structPendingDrop) JVM.structPendingDrop(vm);
	}
	if (J.fallback) { post({ t: 'done', id: m.id, fallback: true, why: J.fallback }); J = null; return; }
	var out = new Int32Array(J.orig.size * 5), n = 0;
	J.orig.forEach(function (was, i) {
		var y = i % H, rest = (i - y) / H, z = rest % D, x = (rest - z) / D;
		out[n++] = x + J.x0; out[n++] = y; out[n++] = z + J.z0; out[n++] = J.blocks[i]; out[n++] = was;
	});
	post({ t: 'done', id: m.id, changes: out, ticks: J.ticks }, [out.buffer]);
	J = null;
}
