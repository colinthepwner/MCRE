(function () {
	'use strict';

	var KEY_PACK = 'mcre.shaders.pack';
	var SCRIPTS = ['shaders.js', 'shaders_gl.js'];
	var ON = 'mcre_shaders_on';

	var loading = null;
	var current = '';
	var wanted = null;
	var built = null;
	var lastError = '';
	var applying = false;

	var api = Module.mcShaders = {};

	function store(k, v) { try { if (v === null) localStorage.removeItem(k); else localStorage.setItem(k, v); } catch (e) { } }
	function read(k) { try { return localStorage.getItem(k); } catch (e) { return null; } }

	function packs() {
		if (!Module.mcMods || !Module.mcMods.shaderPacks) return [];
		return Module.mcMods.shaderPacks();
	}

	api.list = function () {
		return packs().map(function (p) {
			var n = Object.keys(p.files).filter(function (k) { return /\.fsh$/i.test(k); }).length;
			return [p.id, p.name, p.author || '', String(n), p.id === current ? '1' : '0'].join('\t');
		}).join('\n');
	};
	api.packs = packs;
	api.current = function () { return current; };
	api.error = function () { return lastError; };
	api.busy = function () { return applying; };

	function loadScripts() {
		if (loading) return loading;
		loading = new Promise(function (res, rej) {
			var i = 0;
			var next = function () {
				if (i >= SCRIPTS.length) { res(); return; }
				var s = document.createElement('script');
				var v = (typeof MCRE_BUILD !== 'undefined' && MCRE_BUILD === 'dev')
					? '?t=' + Date.now() : (typeof MCRE_BUILD !== 'undefined' ? '?v=' + encodeURIComponent(MCRE_BUILD) : '');
				s.src = SCRIPTS[i++] + v;
				s.onload = next;
				s.onerror = function () { loading = null; rej(new Error(s.src + ' could not be fetched')); };
				document.head.appendChild(s);
			};
			next();
		});
		return loading;
	}

	api.options = function (id) {
		id = id || current;
		var out = {};
		if (!id || !Module.mcMods || !Module.mcMods.settingsOf) return out;
		var vals = Module.mcMods.settingsOf(id) || {};
		Object.keys(vals).forEach(function (k) { if (k !== ON) out[k] = vals[k]; });
		return out;
	};
	function wantsOn(id) {
		if (!Module.mcMods || !Module.mcMods.settingsOf) return true;
		var v = (Module.mcMods.settingsOf(id) || {})[ON];
		return v === undefined ? true : !!v;
	}
	api.setOption = function (id, name, value) {
		if (!Module.mcMods || !Module.mcMods.setSetting) return Promise.resolve('');
		Module.mcMods.setSetting(id, name, value);
		return Promise.resolve('');
	};
	api.optionList = function () {
		if (!built) return [];
		var chosen = api.options(current);
		return built.options.order.map(function (k) {
			var o = built.options.byId[k];
			return {
				id: k, kind: o.kind, note: o.note || '', slider: !!o.slider,
				values: o.values || null,
				value: chosen[k] !== undefined ? chosen[k] : o.def,
				def: o.def
			};
		});
	};
	api.screens = function () { return built ? built.props.screens : {}; };
	api.problems = function () { return built ? built.problems.concat(window.MCShaders ? MCShaders.notes() : []) : []; };

	var reader = null;
	function loadReader() {
		if (window.MCShaders && MCShaders.inspect) return Promise.resolve();
		if (reader) return reader;
		reader = new Promise(function (res, rej) {
			var s = document.createElement('script');
			var v = (typeof MCRE_BUILD !== 'undefined' && MCRE_BUILD === 'dev')
				? '?t=' + Date.now() : (typeof MCRE_BUILD !== 'undefined' ? '?v=' + encodeURIComponent(MCRE_BUILD) : '');
			s.src = 'shaders.js' + v;
			s.onload = function () { res(); };
			s.onerror = function () { reader = null; rej(new Error('shaders.js could not be fetched')); };
			document.head.appendChild(s);
		});
		return reader;
	}

	function pretty(id) {
		var s = String(id).replace(/[_]+/g, ' ').replace(/([a-z])([A-Z])/g, '$1 $2').trim();
		return s.charAt(0).toUpperCase() + s.slice(1);
	}
	function valueLabel(lang, id, v) {
		var own = lang['value.' + id + '.' + v];
		var pre = lang['prefix.' + id] || '', suf = lang['suffix.' + id] || '';
		return (pre + (own !== undefined ? own : v) + suf) || String(v);
	}

	function declsFor(pack) {
		var root = MCShaders.rootOf(pack.files);
		if (!root) throw new Error('no shaders folder in this pack');
		var info = MCShaders.inspect(MCShaders.filesUnder(pack.files, root));
		var opts = info.options, lang = info.lang, screens = info.props.screens || {};
		var out = [{
			id: ON, type: 'toggle', default: true,
			name: 'Use this shader pack',
			description: 'Draws the world with this pack. Only one pack runs at a time.'
		}];
		var seen = {}, starAt = -1;
		var row = function (name, group) {
			var o = opts.byId[name];
			if (!o || seen[name]) return;
			seen[name] = 1;
			var d = {
				id: name, group: group || '',
				name: lang['option.' + name] || pretty(name),
				description: lang['option.' + name + '.comment'] || o.note || ''
			};
			if (o.kind === 'toggle' && !o.values) { d.type = 'toggle'; d.default = !!o.def; }
			else {
				d.type = 'choice';
				d.options = (o.values || [String(o.def)]).map(String);
				if (d.options.indexOf(String(o.def)) < 0) d.options.unshift(String(o.def));
				d.default = String(o.def);
				d.labels = d.options.map(function (v) { return valueLabel(lang, name, v); });
			}
			out.push(d);
		};
		var walk = function (list, group, depth) {
			if (!list || depth > 6) return;
			list.forEach(function (name) {
				if (name === '*') { starAt = out.length; return; }
				if (name === '<empty>' || name === '<profile>') return;
				var sub = /^\[(.+)\]$/.exec(name);
				if (sub) {
					var g = lang['screen.' + sub[1]] || pretty(sub[1]);
					walk(screens[sub[1]], g, depth + 1);
					return;
				}
				row(name, group);
			});
		};
		walk(screens[''], '', 0);
		var rest = opts.order.filter(function (k) { return !seen[k]; });
		if (rest.length) {
			var before = out.length;
			rest.forEach(function (k) { row(k, out.length === before && starAt < 0 ? 'More options' : ''); });
			if (starAt >= 0) {
				var moved = out.splice(before, out.length - before);
				out.splice.apply(out, [starAt, 0].concat(moved));
			}
		}
		return out;
	}

	api.settingsFor = function () {
		var ps = packs();
		if (!ps.length) return Promise.resolve({});
		return loadReader().then(function () {
			var out = {};
			ps.forEach(function (p) {
				try { out[p.id] = declsFor(p); }
				catch (e) { console.warn('shader pack ' + p.id + ': could not read its options -', e); }
			});
			return out;
		}, function (e) { console.warn('shader options unavailable:', e && e.message || e); return {}; });
	};

	function choose() {
		try {
			if (Module.mcGameRules && Module.mcGameRules.get('shadersAllowed') === false) return '';
		} catch (e) { }
		var on = packs().filter(function (p) { return wantsOn(p.id) && !failed[p.id]; });
		if (!on.length) return '';
		var pref = read(KEY_PACK);
		var win = on.filter(function (p) { return p.id === pref; })[0] || on[0];
		if (on.length > 1 && Module.mcMods && Module.mcMods.setSetting) {
			quiet = true;
			try {
				on.forEach(function (p) { if (p.id !== win.id) Module.mcMods.setSetting(p.id, ON, false); });
				if (Module.mcMods.note) Module.mcMods.note('Only one shader pack can run at a time - using ' + win.name);
			} finally { quiet = false; }
		}
		return win.id;
	}
	var quiet = false;
	var failed = {};

	api.apply = function () {
		var id = choose();
		if (id === current && (!id || built) && (wanted === null || wanted === id)) return Promise.resolve('');
		return api.select(id, true);
	};

	api.settingsChanged = function (modId) {
		if (quiet) return Promise.resolve('');
		if (!packs().some(function (p) { return p.id === modId; })) return Promise.resolve('');
		if (wantsOn(modId)) { store(KEY_PACK, modId); delete failed[modId]; }
		else if (read(KEY_PACK) === modId) store(KEY_PACK, null);
		return api.select(choose(), true);
	};

	api.use = function (id) {
		id = String(id || '');
		var ps = packs();
		if (id && !ps.filter(function (p) { return p.id === id; }).length) {
			return Promise.resolve('that shader pack is not installed (its mod has to be on)');
		}
		if (Module.mcMods && Module.mcMods.setSetting) {
			quiet = true;
			try { ps.forEach(function (p) { Module.mcMods.setSetting(p.id, ON, p.id === id); }); }
			finally { quiet = false; }
		}
		store(KEY_PACK, id || null);
		if (id) delete failed[id];
		return api.select(id, true);
	};

	function told(id, error) {
		try {
			if (!Module.mcScripts || !Module.mcScripts.shadersChanged) return;
			var p = packs().filter(function (x) { return x.id === id; })[0];
			Module.mcScripts.shadersChanged({ pack: id, name: (p && p.name) || '', on: !!id && !error, error: error || '' });
		} catch (e) { }
	}

	var chain = Promise.resolve('');
	api.select = function (id, force) {
		id = String(id || '');
		if (!force && id === current) return Promise.resolve('');
		wanted = id;
		var run = function () { return wanted === id ? selectNow(id) : Promise.resolve(''); };
		chain = chain.then(run, run);
		return chain;
	};
	function selectNow(id) {
		lastError = '';
		if (!id) {
			var was = current;
			current = '';
			built = null;
			store(KEY_PACK, null);
			if (window.MCShaders) MCShaders.stop();
			if (was) told('', '');
			return Promise.resolve('');
		}
		applying = true;
		return loadScripts().then(function () {
			call0('mcShDeclare');
			var p = packs().filter(function (x) { return x.id === id; })[0];
			if (!p) throw new Error('that shader pack is not installed any more');
			var root = MCShaders.rootOf(p.files);
			if (!root) throw new Error('no shaders folder in this pack');
			var files = MCShaders.filesUnder(p.files, root);
			var dim = dimFolder(files);
			var centroid = !!(Module.mcCentroid && Module.mcCentroid.state === 'on');
			built = MCShaders.build(files, api.options(id), dim, centroid);
			var w = canvasSize();
			var err = MCShaders.start(built, w[0], w[1]);
			if (err) { built = null; throw new Error(err); }
			current = id;
			store(KEY_PACK, id);
			sendBlockMap(built.blockMap);
			told(id, '');
			return '';
		}).catch(function (e) {
			lastError = String(e && e.message || e);
			built = null;
			current = '';
			failed[id] = 1;
			if (window.MCShaders) MCShaders.stop();
			console.warn('shader pack not loaded:', lastError);
			if (Module.mcMods && Module.mcMods.note) {
				var p2 = packs().filter(function (x) { return x.id === id; })[0];
				Module.mcMods.note(((p2 && p2.name) || 'That shader pack') + ' could not be used: ' + lastError);
			}
			told(id, lastError);
			return lastError;
		}).then(function (r) { applying = false; return r; });
	}

	function dimFolder(files) {
		var dim = 0;
		try { dim = (Module.mcDimension | 0) || 0; } catch (e) { }
		var want = dim === -1 ? 'world-1' : dim === 1 ? 'world1' : '';
		if (!want) return '';
		var has = Object.keys(files).some(function (k) { return k.indexOf(want + '/') === 0; });
		return has ? want : '';
	}

	function canvasSize() {
		var c = document.getElementById('canvas');
		return [(c && c.width) || window.innerWidth || 1, (c && c.height) || window.innerHeight || 1];
	}

	function sendBlockMap(pairs) {
		if (!pairs || !pairs.length) { call('mcShBlockMap', ''); return; }
		var out = [];
		for (var i = 0; i < pairs.length; i++) {
			var ref = refOf(pairs[i][0]);
			if (ref) out.push(ref + '=' + pairs[i][1]);
		}
		call('mcShBlockMap', out.join(';'));
	}
	function refOf(name) {
		try {
			if (!Module.mcMods || !Module.mcMods.refOf) return '';
			var n = String(name).replace(/:.*$/, '');
			return Module.mcMods.refOf(n, '') || Module.mcMods.refOf(name, '') || '';
		} catch (e) { return ''; }
	}
	function call(fn, str) {
		try { Module.ccall(fn, null, ['string'], [str]); } catch (e) { console.warn(fn + ' failed:', e); }
	}
	function call0(fn) {
		try { Module.ccall(fn, null, [], []); } catch (e) { console.warn(fn + ' failed:', e); }
	}

	api.startup = function () { return api.apply(); };

	api.dimensionChanged = function () {
		if (!current) return Promise.resolve('');
		return api.select(current, true);
	};

	Module.mcShaderFailed = function (why) {
		var was = current;
		lastError = String(why || 'the shader pack stopped working');
		built = null;
		current = '';
		if (was) failed[was] = 1;
		store(KEY_PACK, null);
		console.warn('shader pack turned off:', lastError);
		if (Module.mcMods && Module.mcMods.note) Module.mcMods.note('Shaders turned off: ' + lastError);
		told('', lastError);
	};
})();
