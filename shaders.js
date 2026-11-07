(function () {
	'use strict';

	var S = window.MCShaders = window.MCShaders || {};

	S.ATTRS = [
		['mcVertex', 0],
		['mcMultiTexCoord0', 1],
		['mcColor', 2],
		['mcMultiTexCoord1', 3],
		['mcNormal', 4],
		['mc_Entity', 5],
		['mc_midTexCoord', 6],
		['at_tangent', 7]
	];

	S.TEX_ALIAS = {
		gcolor: 'colortex0', gdepth: 'colortex1', gnormal: 'colortex2', composite: 'colortex3',
		gaux1: 'colortex4', gaux2: 'colortex5', gaux3: 'colortex6', gaux4: 'colortex7',
		shadow: 'shadowtex0', watershadow: 'shadowtex0', shadowcolor: 'shadowcolor0',
		gtexture: 'texture', tex: 'texture', mcTexture: 'texture'
	};
	S.FIXED_UNITS = { texture: 0, lightmap: 1 };

	var SAMPLER_NAMES = ['texture', 'lightmap', 'normals', 'specular', 'noisetex',
		'shadowtex0', 'shadowtex1', 'shadowcolor0', 'shadowcolor1',
		'depthtex0', 'depthtex1', 'depthtex2',
		'colortex0', 'colortex1', 'colortex2', 'colortex3',
		'colortex4', 'colortex5', 'colortex6', 'colortex7',
		'dhDepthTex0', 'dhDepthTex1'];
	S.SAMPLER_NAMES = SAMPLER_NAMES;

	S.MATRIX_UNIFORMS = {
		mcMvMat: 'mat4', mcProjMat: 'mat4', mcNormalMat: 'mat3', mcTexMat: 'mat4'
	};

	S.PROGRAMS = [
		{ name: 'shadow', fall: [] },
		{ name: 'shadow_solid', fall: ['shadow'] },
		{ name: 'shadow_cutout', fall: ['shadow'] },
		{ name: 'gbuffers_basic', fall: [] },
		{ name: 'gbuffers_textured', fall: ['gbuffers_basic'] },
		{ name: 'gbuffers_textured_lit', fall: ['gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_skybasic', fall: ['gbuffers_basic'] },
		{ name: 'gbuffers_skytextured', fall: ['gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_clouds', fall: ['gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_terrain', fall: ['gbuffers_textured_lit', 'gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_damagedblock', fall: ['gbuffers_terrain', 'gbuffers_textured_lit', 'gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_block', fall: ['gbuffers_terrain', 'gbuffers_textured_lit', 'gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_beaconbeam', fall: ['gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_entities', fall: ['gbuffers_textured_lit', 'gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_armor_glint', fall: ['gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_spidereyes', fall: ['gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_hand', fall: ['gbuffers_textured_lit', 'gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_hand_water', fall: ['gbuffers_hand', 'gbuffers_textured_lit', 'gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_weather', fall: ['gbuffers_textured_lit', 'gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'gbuffers_water', fall: ['gbuffers_terrain', 'gbuffers_textured_lit', 'gbuffers_textured', 'gbuffers_basic'] },
		{ name: 'deferred', fall: [] }, { name: 'deferred1', fall: [] }, { name: 'deferred2', fall: [] },
		{ name: 'deferred3', fall: [] }, { name: 'deferred4', fall: [] }, { name: 'deferred5', fall: [] },
		{ name: 'deferred6', fall: [] }, { name: 'deferred7', fall: [] },
		{ name: 'composite', fall: [] }, { name: 'composite1', fall: [] }, { name: 'composite2', fall: [] },
		{ name: 'composite3', fall: [] }, { name: 'composite4', fall: [] }, { name: 'composite5', fall: [] },
		{ name: 'composite6', fall: [] }, { name: 'composite7', fall: [] },
		{ name: 'final', fall: [] }
	];
	S.SCREEN_PROGRAM = /^(deferred|composite|final)/;

	S.rootOf = function (files) {
		var keys = Object.keys(files), best = null;
		for (var i = 0; i < keys.length; i++) {
			var m = /^(.*?)shaders\/[^/]*\.(fsh|vsh|gsh|properties|settings)$/i.exec(keys[i]);
			if (!m) continue;
			if (best === null || m[1].length < best.length) best = m[1];
		}
		return best === null ? null : best + 'shaders/';
	};

	S.filesUnder = function (files, root) {
		var out = {}, n = root.length;
		Object.keys(files).forEach(function (k) {
			if (k.length > n && k.slice(0, n).toLowerCase() === root.toLowerCase()) out[k.slice(n)] = files[k];
		});
		return out;
	};

	function text(bytes) {
		if (typeof bytes === 'string') return bytes;
		if (!bytes) return '';
		var s = new TextDecoder('utf-8', { fatal: false }).decode(bytes);
		if (s.charCodeAt(0) === 0xfeff) s = s.slice(1);
		return s.replace(/\r\n?/g, '\n');
	}
	S.text = text;

	function pick(files, path) {
		if (files[path] !== undefined) return files[path];
		var low = path.toLowerCase(), keys = Object.keys(files);
		for (var i = 0; i < keys.length; i++) if (keys[i].toLowerCase() === low) return files[keys[i]];
		return undefined;
	}
	S.pick = pick;

	function includeAll(files, path, src, problems, depth, seen) {
		if (depth > 24) { problems.push('#include nested too deep in ' + path); return src; }
		var dir = path.indexOf('/') >= 0 ? path.slice(0, path.lastIndexOf('/') + 1) : '';
		return src.replace(/^[ \t]*#include[ \t]+["<]([^">]+)[">][ \t]*$/gm, function (all, inc) {
			var p = inc.charAt(0) === '/' ? inc.slice(1) : dir + inc;
			p = p.replace(/[/]\.[/]/g, '/');
			while (/[^/]+[/]\.\.[/]/.test(p)) p = p.replace(/[^/]+[/]\.\.[/]/, '');
			var b = pick(files, p);
			if (b === undefined) { problems.push('#include "' + inc + '" is not in the pack'); return '// (missing ' + inc + ')'; }
			if (seen.indexOf(p) >= 0) { problems.push('#include "' + inc + '" includes itself'); return ''; }
			return includeAll(files, p, text(b), problems, depth + 1, seen.concat([p]));
		});
	}
	S.includeAll = includeAll;

	S.readOptions = function (srcByFile, propText) {
		var opts = {}, order = [];
		var sliders = {};
		(propText || '').replace(/^[ \t]*sliders[ \t]*=([^\n]*)$/gm, function (a, list) {
			list.trim().split(/\s+/).forEach(function (n) { if (n) sliders[n] = true; });
			return a;
		});
		Object.keys(srcByFile).forEach(function (file) {
			var src = srcByFile[file];
			var lines = src.split('\n');
			for (var i = 0; i < lines.length; i++) {
				var line = lines[i];
				var cm = /\/\/\s*(\[[^\]]*\])?(.*)$/.exec(line);
				var values = cm && cm[1] ? cm[1].slice(1, -1).trim().split(/\s+/).filter(Boolean) : null;
				var note = cm ? String(cm[2] || '').trim() : '';
				var code = cm ? line.slice(0, cm.index) : line;
				var off = /^[ \t]*\/\/[ \t]*#define[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]*(?:\/\/|$)/.exec(line);
				var on = /^[ \t]*#define[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]*$/.exec(code);
				var def = /^[ \t]*#define[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]+(\S+)[ \t]*$/.exec(code);
				var cst = /^[ \t]*const[ \t]+(int|float|bool)[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]*=[ \t]*([^;]+);/.exec(code);
				var o = null;
				if (off) o = { id: off[1], kind: 'toggle', def: false };
				else if (on) o = { id: on[1], kind: 'toggle', def: true };
				else if (def && values) o = { id: def[1], kind: 'choice', def: def[2], values: values };
				else if (cst && values) o = { id: cst[2], kind: 'const', type: cst[1], def: cst[3].trim(), values: values };
				if (!o) continue;
				if (opts[o.id]) continue;
				o.note = note.slice(0, 160);
				o.file = file;
				if (o.values && sliders[o.id]) o.slider = true;
				opts[o.id] = o;
				order.push(o.id);
			}
		});
		return { byId: opts, order: order };
	};

	S.applyOptions = function (src, opts, chosen) {
		var lines = src.split('\n');
		for (var i = 0; i < lines.length; i++) {
			var line = lines[i];
			var cm = /\/\/\s*(\[[^\]]*\])?/.exec(line);
			var code = cm ? line.slice(0, cm.index) : line;
			var tail = cm ? line.slice(cm.index) : '';
			var m;
			if ((m = /^([ \t]*)(?:\/\/[ \t]*)?#define[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]*$/.exec(code))) {
				var o = opts.byId[m[2]];
				if (o && o.kind === 'toggle' && chosen[m[2]] !== undefined) {
					lines[i] = m[1] + (chosen[m[2]] ? '' : '//') + '#define ' + m[2] + ' ' + tail;
				}
				continue;
			}
			if ((m = /^([ \t]*)#define[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]+(\S+)[ \t]*$/.exec(code))) {
				if (chosen[m[2]] !== undefined && opts.byId[m[2]] && opts.byId[m[2]].kind === 'choice')
					lines[i] = m[1] + '#define ' + m[2] + ' ' + chosen[m[2]] + ' ' + tail;
				continue;
			}
			if ((m = /^([ \t]*)const[ \t]+(int|float|bool)[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]*=[ \t]*([^;]+);/.exec(code))) {
				if (chosen[m[3]] !== undefined && opts.byId[m[3]] && opts.byId[m[3]].kind === 'const')
					lines[i] = m[1] + 'const ' + m[2] + ' ' + m[3] + ' = ' + chosen[m[3]] + '; ' + tail;
				continue;
			}
		}
		return lines.join('\n');
	};

	S.readLang = function (files) {
		var out = {};
		var src = pick(files, 'lang/en_us.lang');
		if (src === undefined) src = pick(files, 'lang/en_US.lang');
		if (src === undefined) return out;
		text(src).split('\n').forEach(function (line) {
			line = line.replace(/^\s+/, '');
			if (!line || line.charAt(0) === '#') return;
			var eq = line.indexOf('=');
			if (eq < 0) return;
			out[line.slice(0, eq).trim()] = line.slice(eq + 1).replace(/\s+$/, '');
		});
		return out;
	};

	S.inspect = function (files) {
		var propsFile = pick(files, 'shaders.properties');
		var propText = propsFile ? text(propsFile) : '';
		var srcByFile = {};
		Object.keys(files).forEach(function (k) {
			if (/\.(fsh|vsh|gsh|glsl|settings|inc)$/i.test(k)) srcByFile[k] = text(files[k]);
		});
		var programs = S.PROGRAMS.filter(function (P) {
			return pick(files, P.name + '.fsh') !== undefined || pick(files, P.name + '.vsh') !== undefined;
		}).map(function (P) { return P.name; });
		return {
			options: S.readOptions(srcByFile, propText),
			props: S.readProperties(propText),
			lang: S.readLang(files),
			programs: programs
		};
	};

	S.MC_VERSION = 10710;

	S.readProperties = function (src) {
		var p = { screens: {}, sliders: [], uniforms: [], variables: [], raw: {} };
		src = S.evalVersionIfs(src);
		src.split('\n').forEach(function (line) {
			line = line.replace(/^\s+/, '');
			if (!line || line.charAt(0) === '#') return;
			var eq = line.indexOf('=');
			if (eq < 0) return;
			var key = line.slice(0, eq).trim(), val = line.slice(eq + 1).trim();
			p.raw[key] = val;
			var m;
			if (key === 'screen') p.screens[''] = val.split(/\s+/).filter(Boolean);
			else if ((m = /^screen\.(.+)$/.exec(key))) p.screens[m[1]] = val.split(/\s+/).filter(Boolean);
			else if (key === 'sliders') p.sliders = val.split(/\s+/).filter(Boolean);
			else if ((m = /^uniform\.(bool|float|int|vec2|vec3|vec4)\.(.+)$/.exec(key))) p.uniforms.push({ type: m[1], name: m[2], expr: val });
			else if ((m = /^variable\.(bool|float|int|vec2|vec3|vec4)\.(.+)$/.exec(key))) p.variables.push({ type: m[1], name: m[2], expr: val });
		});
		return p;
	};

	S.evalVersionIfs = function (src) {
		var out = [], stack = [];
		src.split('\n').forEach(function (line) {
			var m = /^\s*#(if|elif|else|endif)\b(.*)$/.exec(line);
			if (!m) { if (stack.every(function (s) { return s.live; })) out.push(line); return; }
			var kind = m[1], cond = m[2];
			var value = function () {
				var c = /MC_VERSION\s*(>=|<=|==|>|<|!=)\s*(\d+)/.exec(cond);
				if (!c) return true;
				var v = S.MC_VERSION, n = parseInt(c[2], 10);
				switch (c[1]) {
					case '>=': return v >= n; case '<=': return v <= n; case '>': return v > n;
					case '<': return v < n; case '==': return v === n; default: return v !== n;
				}
			};
			if (kind === 'if') { var t = value(); stack.push({ taken: t, live: t }); }
			else if (kind === 'elif') { var s = stack[stack.length - 1]; if (!s) return; if (s.taken) s.live = false; else { s.live = value(); s.taken = s.live; } }
			else if (kind === 'else') { var s2 = stack[stack.length - 1]; if (!s2) return; s2.live = !s2.taken; s2.taken = true; }
			else stack.pop();
		});
		return out.join('\n');
	};

	S.readBlockProperties = function (src) {
		var out = [];
		S.evalVersionIfs(src).split('\n').forEach(function (line) {
			var m = /^\s*block\.(\d+)\s*=\s*(.*)$/.exec(line);
			if (!m) return;
			var id = parseInt(m[1], 10);
			m[2].split(/\s+/).forEach(function (nm) {
				if (!nm) return;
				out.push([nm.replace(/^minecraft:/i, ''), id]);
			});
		});
		return out;
	};

	var KNOWN_CONSTS = {
		shadowMapResolution: 'int', shadowDistance: 'float', shadowDistanceRenderMul: 'float',
		shadowIntervalSize: 'float', shadowHardwareFiltering: 'bool',
		shadowHardwareFiltering0: 'bool', shadowHardwareFiltering1: 'bool',
		shadowtex0Mipmap: 'bool', shadowtex1Mipmap: 'bool', shadowtexMipmap: 'bool',
		shadowcolor0Mipmap: 'bool', shadowcolor1Mipmap: 'bool',
		shadowtex0Nearest: 'bool', shadowtex1Nearest: 'bool', shadowtexNearest: 'bool',
		shadowcolor0Nearest: 'bool', shadowcolor1Nearest: 'bool',
		generateShadowMipmap: 'bool', generateShadowColorMipmap: 'bool',
		noiseTextureResolution: 'int', sunPathRotation: 'float',
		wetnessHalflife: 'float', drynessHalflife: 'float', centerDepthHalflife: 'float',
		eyeBrightnessHalflife: 'float', ambientOcclusionLevel: 'float',
		superSamplingLevel: 'int', shadowMapFov: 'float'
	};
	function bufferConst(name) {
		var alias = { gcolor: 0, gdepth: 1, gnormal: 2, composite: 3, gaux1: 4, gaux2: 5, gaux3: 6, gaux4: 7 };
		var m = /^colortex([0-7])(Format|Clear|MipmapEnabled|Nearest)$/.exec(name);
		if (m) return { index: parseInt(m[1], 10), what: m[2] };
		m = /^(gcolor|gdepth|gnormal|composite|gaux[1-4])(Format|Clear|MipmapEnabled|Nearest)$/.exec(name);
		if (m) return { index: alias[m[1]], what: m[2] };
		return null;
	}
	S.bufferConst = bufferConst;

	S.readConsts = function (src, into) {
		var re = /^[ \t]*const[ \t]+(int|float|bool|vec2|vec3|vec4)[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]*=[ \t]*([^;]+);/gm, m;
		while ((m = re.exec(src))) {
			var name = m[2], raw = m[3].trim();
			var b = bufferConst(name);
			if (b) {
				var buf = into.buffers[b.index] = into.buffers[b.index] || {};
				if (b.what === 'Format') buf.format = raw.replace(/[^A-Za-z0-9_]/g, '');
				else if (b.what === 'Clear') buf.clear = /true/i.test(raw);
				else if (b.what === 'MipmapEnabled') buf.mipmap = /true/i.test(raw);
				else if (b.what === 'Nearest') buf.nearest = /true/i.test(raw);
				continue;
			}
			if (!KNOWN_CONSTS[name]) continue;
			if (KNOWN_CONSTS[name] === 'bool') into.consts[name] = /true/i.test(raw);
			else { var v = parseFloat(raw); if (!isNaN(v)) into.consts[name] = KNOWN_CONSTS[name] === 'int' ? (v | 0) : v; }
		}
	};

	S.readDrawBuffers = function (src) {
		var m = /[/]\*\s*(?:DRAWBUFFERS|RENDERTARGETS)\s*:\s*([0-9,\s]*)\s*\*[/]/.exec(src);
		if (!m) return null;
		var s = m[1].replace(/\s/g, '');
		if (s.indexOf(',') >= 0) return s.split(',').filter(function (x) { return x !== ''; }).map(Number);
		var out = [];
		for (var i = 0; i < s.length; i++) out.push(s.charCodeAt(i) - 48);
		return out;
	};

	function mentions(src, name) {
		return new RegExp('\\b' + name + '\\b').test(src);
	}
	S.mentions = mentions;

	function hoistGlobals(src) {
		var out = [], init = [];
		var lines = src.split('\n');
		var depth = 0;
		var stack = [];
		var guardOf = function () {
			var parts = [];
			for (var k = 0; k < stack.length; k++) {
				var lv = stack[k], terms = [];
				for (var j = 0; j < lv.past.length; j++) terms.push('!(' + lv.past[j] + ')');
				if (lv.cur !== null) terms.push('(' + lv.cur + ')');
				if (terms.length) parts.push(terms.join(' && '));
			}
			return parts.length ? parts.join(' && ') : '';
		};
		var cond = function (kind, rest) {
			rest = rest.trim();
			if (kind === 'ifdef') return 'defined(' + rest.split(/\s+/)[0] + ')';
			if (kind === 'ifndef') return '!defined(' + rest.split(/\s+/)[0] + ')';
			return rest;
		};
		for (var i = 0; i < lines.length; i++) {
			var line = lines[i];
			var pp = /^\s*#\s*(ifdef|ifndef|if|elif|else|endif)\b(.*)$/.exec(line);
			if (pp) {
				var kind = pp[1], rest = pp[2] || '';
				if (kind === 'ifdef' || kind === 'ifndef' || kind === 'if') stack.push({ past: [], cur: cond(kind, rest) });
				else if (kind === 'elif') { var t = stack[stack.length - 1]; if (t) { if (t.cur !== null) t.past.push(t.cur); t.cur = cond('if', rest); } }
				else if (kind === 'else') { var t2 = stack[stack.length - 1]; if (t2) { if (t2.cur !== null) t2.past.push(t2.cur); t2.cur = null; } }
				else stack.pop();
				out.push(line);
				continue;
			}
			if (depth === 0) {
				var m = /^([ \t]*)(float|int|bool|uint|vec2|vec3|vec4|ivec2|ivec3|ivec4|bvec2|bvec3|bvec4|mat2|mat3|mat4)[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]*=[ \t]*(.+);[ \t]*$/.exec(line);
				if (m && !/\b(const|uniform|in|out|attribute|varying|centroid)\b/.test(m[0])) {
					out.push(m[1] + m[2] + ' ' + m[3] + ';');
					var g = guardOf();
					if (g) init.push('#if ' + g + '\n\t' + m[3] + ' = ' + m[4] + ';\n#endif');
					else init.push('\t' + m[3] + ' = ' + m[4] + ';');
					continue;
				}
			}
			out.push(line);
			var open = line.split('{').length - 1, close = line.split('}').length - 1;
			depth += open - close;
			if (depth < 0) depth = 0;
		}
		return { src: out.join('\n'), init: init };
	}

	function stripComments(src) {
		var out = '', i = 0, n = src.length;
		while (i < n) {
			var c = src.charAt(i), d = src.charAt(i + 1);
			if (c === '/' && d === '/') { while (i < n && src.charAt(i) !== '\n') i++; continue; }
			if (c === '/' && d === '*') {
				i += 2;
				while (i < n && !(src.charAt(i) === '*' && src.charAt(i + 1) === '/')) { if (src.charAt(i) === '\n') out += '\n'; i++; }
				i += 2; continue;
			}
			out += c; i++;
		}
		return out;
	}
	S.stripComments = stripComments;

	function prelude(info, isVertex, centroid) {
		var L = [];
		L.push('#version 300 es');
		L.push('#define MC_VERSION ' + S.MC_VERSION);
		L.push('#define MC_GL_VERSION 300');
		L.push('#define MC_GLSL_VERSION 300');
		L.push('#define MC_RENDER_QUALITY 1.0');
		L.push('#define MC_SHADOW_QUALITY 1.0');
		L.push('#define MC_NORMAL_MAP');
		L.push('#define MC_SPECULAR_MAP');
		L.push('#define MC_RENDER_STAGE_NONE 0');
		L.push('#define MC_GL_RENDERER_ANGLE');
		if (!isVertex) L.push('precision highp float;', 'precision highp int;', 'precision highp sampler2D;', 'precision highp sampler2DShadow;');
		else L.push('precision highp float;', 'precision highp int;');
		if (isVertex) {
			if (info.use.mcVertex) L.push('in vec3 mcVertexIn;', 'uniform vec4 mcVertexFix;', 'vec4 mcVertex;');
			if (info.use.mcColor) L.push('in vec4 mcColor;');
			if (info.use.mcNormal) L.push('in vec3 mcNormal;');
			if (info.use.mcMultiTexCoord0) L.push('in vec4 mcMultiTexCoord0;');
			if (info.use.mcMultiTexCoord1) L.push('in vec4 mcMultiTexCoord1;');
		}
		Object.keys(S.MATRIX_UNIFORMS).forEach(function (u) {
			if (!info.use[u]) return;
			if (u === 'mcTexMat') L.push('uniform mat4 mcTexMat[3];');
			else L.push('uniform ' + S.MATRIX_UNIFORMS[u] + ' ' + u + ';');
		});
		if (info.use.mcFogFragCoord) L.push((isVertex ? 'out' : 'in') + ' float mcFogFragCoord;');
		if (info.use.at_tangent && !info.attribs.at_tangent && isVertex) L.push('vec4 at_tangent;');
		if (info.use.shadow2D) L.push(
			'#define shadow2D(s, c) vec4(texture(s, c))',
			'#define shadow2DLod(s, c, l) vec4(textureLod(s, c, l))');
		if (!isVertex) {
			var db = info.drawBuffers;
			var n = Math.max(info.outputs, db ? db.length : 0);
			for (var i = 0; i < n; i++) {
				var loc = (db && db[i] !== undefined) ? db[i] : i;
				L.push('layout(location = ' + loc + ') out vec4 mcFragData' + i + ';');
			}
		}
		return L.join('\n') + '\n';
	}

	var TANGENT_FN = [
		'vec4 mcTangentOf(vec3 n) {',
		'  vec3 a = abs(n);',
		'  vec3 t;',
		'  if (a.y > a.x && a.y > a.z) t = vec3(1.0, 0.0, 0.0);',
		'  else if (a.x > a.z) t = vec3(0.0, 0.0, sign(n.x));',
		'  else t = vec3(-sign(n.z), 0.0, 0.0);',
		'  if (a.y < 0.99 && a.x < 0.99 && a.z < 0.99) t = normalize(cross(n, vec3(0.0, 1.0, 0.0)));',
		'  return vec4(t, 1.0);',
		'}'
	].join('\n');

	S.translate = function (raw, isVertex, shared, centroid) {
		var info = { use: {}, attribs: {}, uniforms: {}, samplers: {}, outputs: 0, varyings: {}, ints: {} };
		var drawBuffers = isVertex ? null : S.readDrawBuffers(raw);
		var src = stripComments(raw);

		src = src.replace(/^[ \t]*#version[^\n]*$/gm, '');
		src = src.replace(/^[ \t]*#extension[^\n]*$/gm, '');
		src = src.replace(/^[ \t]*#pragma[^\n]*$/gm, '');

		info.use.mcVertex = mentions(src, 'gl_Vertex') || mentions(src, 'ftransform');
		info.use.mcColor = mentions(src, 'gl_Color');
		info.use.mcNormal = mentions(src, 'gl_Normal');
		info.use.mcMvMat = mentions(src, 'gl_ModelViewMatrix') || mentions(src, 'gl_ModelViewProjectionMatrix') || mentions(src, 'ftransform');
		info.use.mcProjMat = mentions(src, 'gl_ProjectionMatrix') || mentions(src, 'gl_ModelViewProjectionMatrix') || mentions(src, 'ftransform');
		info.use.mcNormalMat = mentions(src, 'gl_NormalMatrix');
		info.use.mcTexMat = mentions(src, 'gl_TextureMatrix');
		info.use.mcFogFragCoord = mentions(src, 'gl_FogFragCoord');
		info.use.shadow2D = mentions(src, 'shadow2D') || mentions(src, 'shadow2DLod');
		info.use.at_tangent = mentions(src, 'at_tangent');
		for (var t = 0; t < 8; t++) if (mentions(src, 'gl_MultiTexCoord' + t)) info.use['mcMultiTexCoord' + t] = true;

		src = src.replace(/\btexture\b(?!\s*\()/g, 'mcTexture');

		src.replace(/^[ \t]*attribute[ \t]+[A-Za-z0-9_]+[ \t]+([A-Za-z_][A-Za-z0-9_]*)/gm, function (a, n) { info.attribs[n] = true; return a; });
		src.replace(/^[ \t]*uniform[ \t]+([A-Za-z0-9_]+)[ \t]+([A-Za-z_][A-Za-z0-9_]*)/gm, function (a, ty, n) {
			info.uniforms[n] = ty;
			if (/^sampler/.test(ty)) info.samplers[n] = ty;
			return a;
		});
		src.replace(/\b(?:const[ \t]+|uniform[ \t]+|flat[ \t]+|in[ \t]+|out[ \t]+)*(int|uint|ivec2|ivec3|ivec4|uvec2|uvec3|uvec4)[ \t]+([A-Za-z_][A-Za-z0-9_]*)/g,
			function (a, ty, n) { info.ints[n] = ty; return a; });
		src.replace(/^[ \t]*#[ \t]*define[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]+(-?\d+)[ \t]*$/gm,
			function (a, n) { if (!info.ints[n]) info.ints[n] = 'int'; return a; });

		src.replace(/^[ \t]*(?:centroid[ \t]+)?varying[ \t]+([A-Za-z0-9_]+)[ \t]+([A-Za-z_][A-Za-z0-9_]*)([^;]*);/gm, function (a, ty, n, tail) {
			info.varyings[n] = ty + (tail && tail.indexOf('[') >= 0 ? tail.trim() : '');
			return a;
		});

		var cen = function (all, ty, rest) {
			var q = centroid && /^(float|vec2|vec3|vec4)$/.test(ty) ? 'centroid ' : '';
			return q + (isVertex ? 'out ' : 'in ') + ty + rest;
		};
		src = src.replace(/^[ \t]*attribute[ \t]+([A-Za-z0-9_]+)([ \t]+[^\n]*)$/gm, function (a, ty, rest) { return 'in ' + ty + rest; });
		src = src.replace(/^[ \t]*(?:centroid[ \t]+)?varying[ \t]+([A-Za-z0-9_]+)([ \t]+[^\n]*)$/gm, cen);
		src = src.replace(/^[ \t]*flat[ \t]+(?:in|out)[ \t]+/gm, 'flat ' + (isVertex ? 'out ' : 'in '));

		src = src.split('texture2DProjLod(').join('textureProjLod(');
		src = src.split('texture2DLodOffset(').join('textureLodOffset(');
		src = src.split('texture2DProj(').join('textureProj(');
		src = src.split('texture2DLod(').join('textureLod(');
		src = src.split('texture2DGradARB(').join('textureGrad(');
		src = src.split('texture3D(').join('texture(');
		src = src.split('textureCube(').join('texture(');
		src = src.split('texture2D(').join('texture(');
		src = src.split('shadow2DLod(').join('shadow2DLod(');

		src = src.replace(/\bftransform\s*\(\s*\)/g, '(mcProjMat * mcMvMat * mcVertex)');
		src = src.replace(/\bgl_ModelViewProjectionMatrix\b/g, '(mcProjMat * mcMvMat)');
		src = src.replace(/\bgl_ModelViewMatrixInverse\b/g, 'inverse(mcMvMat)');
		src = src.replace(/\bgl_ProjectionMatrixInverse\b/g, 'inverse(mcProjMat)');
		src = src.replace(/\bgl_ModelViewMatrix\b/g, 'mcMvMat');
		src = src.replace(/\bgl_ProjectionMatrix\b/g, 'mcProjMat');
		src = src.replace(/\bgl_NormalMatrix\b/g, 'mcNormalMat');
		src = src.replace(/\bgl_TextureMatrix\b/g, 'mcTexMat');
		src = src.replace(/\bgl_Vertex\b/g, 'mcVertex');
		src = src.replace(/\bgl_Color\b/g, 'mcColor');
		src = src.replace(/\bgl_Normal\b/g, 'mcNormal');
		src = src.replace(/\bgl_MultiTexCoord([0-7])\b/g, 'mcMultiTexCoord$1');
		src = src.replace(/\bgl_FogFragCoord\b/g, 'mcFogFragCoord');
		src = src.replace(/\bgl_FrontColor\b/g, 'mcColorOut');

		if (!isVertex) {
			var maxSlot = -1;
			src.replace(/\bgl_FragData\s*\[\s*(\d+)\s*\]/g, function (a, i) { maxSlot = Math.max(maxSlot, parseInt(i, 10)); return a; });
			src = src.replace(/\bgl_FragData\s*\[\s*(\d+)\s*\]/g, function (a, i) { return 'mcFragData' + i; });
			if (mentions(src, 'gl_FragColor')) { src = src.replace(/\bgl_FragColor\b/g, 'mcFragData0'); maxSlot = Math.max(maxSlot, 0); }
			info.outputs = maxSlot + 1;
			info.drawBuffers = drawBuffers;
		}

		var h = hoistGlobals(src);
		src = h.src;
		var init = h.init;
		if (isVertex && info.use.at_tangent && !info.attribs.at_tangent) {
			src = TANGENT_FN + '\n' + src;
			init.unshift('\tat_tangent = mcTangentOf(mcNormal);');
		}
		if (isVertex && info.use.mcVertex) init.unshift('\tmcVertex = vec4(mcVertexIn * mcVertexFix.w + mcVertexFix.xyz, 1.0);');
		if (init.length) src = injectIntoMain(src, init.join('\n'));

		if (!isVertex && info.outputs > 0) {
			src = src.replace(/\bvoid\s+main\s*\(/, 'void mcPackMain(');
			var zero = '';
			var dbn = info.drawBuffers ? info.drawBuffers.length : 0;
			for (var z = 0; z < Math.max(info.outputs, dbn); z++) zero += '\tmcFragData' + z + ' = vec4(0.0);\n';
			src += '\nuniform float mcAlphaRef;\nvoid main() {\n' + zero + '\tmcPackMain();\n' +
				'\tif (mcAlphaRef > 0.0 && mcFragData0.a < mcAlphaRef) discard;\n}\n';
		}

		return { src: prelude(info, isVertex, centroid) + src, info: info };
	};

	function injectIntoMain(src, stmts) {
		var m = /\bvoid\s+mcPackMain\s*\([^)]*\)/.exec(src) || /\bvoid\s+main\s*\([^)]*\)/.exec(src);
		if (!m) return src;
		var i = src.indexOf('{', m.index + m[0].length);
		if (i < 0) return src;
		return src.slice(0, i + 1) + '\n' + stmts + '\n' + src.slice(i + 1);
	}
	S.injectIntoMain = injectIntoMain;

	S.matchVaryings = function (vsh, vInfo, fInfo, centroid) {
		var add = [];
		Object.keys(fInfo.varyings).forEach(function (n) {
			if (vInfo.varyings[n]) return;
			var ty = fInfo.varyings[n], base = ty.split('[')[0];
			var q = centroid && /^(float|vec2|vec3|vec4)$/.test(base) ? 'centroid ' : '';
			add.push(q + 'out ' + ty.replace(base, base) + ' ' + n + (ty.indexOf('[') >= 0 ? '' : '') + ';');
			vInfo.varyings[n] = ty;
		});
		if (!add.length) return vsh;
		var at = vsh.indexOf('\n', vsh.indexOf('#version'));
		return vsh.slice(0, at + 1) + add.join('\n') + '\n' + vsh.slice(at + 1);
	};

	S.repair = function (src, log, intNames) {
		var lines = src.split('\n');
		var byLine = {};
		var re = /(?:ERROR|error):\s*\d+:(\d+):\s*([^\n]*)/g, m, edits = 0;
		while ((m = re.exec(log))) {
			var n = parseInt(m[1], 10) - 1, msg = m[2];
			if (n < 0 || n >= lines.length) continue;
			if (byLine[n]) continue;
			byLine[n] = true;
			var line = lines[n];
			if (/global variable initializers must be constant|must be constant expression|constant expression required/i.test(msg)) {
				var c = /^([ \t]*)const[ \t]+([A-Za-z0-9_]+)[ \t]+([A-Za-z_][A-Za-z0-9_]*)[ \t]*=[ \t]*(.+);[ \t]*$/.exec(line);
				if (c) { lines[n] = c[1] + c[2] + ' ' + c[3] + ' = ' + c[4] + ';'; edits++; continue; }
			}
			if (/'const float'|'float'.*to.*'int'|'int'.*from.*'float'/i.test(msg) && /to\s+'?(const\s+)?int/i.test(msg)) {
				var before = line;
				lines[n] = line.replace(/(?<![A-Za-z0-9_.])(\d+)\.(\d*)(?![A-Za-z0-9_])/g, function (a, i) { return i; });
				if (lines[n] !== before) { edits++; continue; }
			}
			if (intNames && /wrong operand types|cannot convert/i.test(msg) && /\bint\b/.test(msg) && /\bfloat\b/.test(msg)) {
				var widened = widenInts(line, intNames);
				if (widened !== line) { lines[n] = widened; edits++; continue; }
			}
			var out = promoteInts(line);
			if (out !== line) { lines[n] = out; edits++; continue; }
		}
		return { src: lines.join('\n'), edits: edits };
	};

	function promoteInts(line) {
		if (/^\s*#/.test(line)) return line;
		var out = '', i = 0, n = line.length, bracket = 0;
		while (i < n) {
			var c = line.charAt(i);
			if (c === '[') { bracket++; out += c; i++; continue; }
			if (c === ']') { bracket--; out += c; i++; continue; }
			if (c >= '0' && c <= '9') {
				var prev = i > 0 ? line.charAt(i - 1) : '';
				var j = i;
				while (j < n && line.charAt(j) >= '0' && line.charAt(j) <= '9') j++;
				var num = line.slice(i, j), after = line.charAt(j);
				var nameish = /[A-Za-z0-9_.]/.test(prev);
				var floatish = after === '.' || after === 'e' || after === 'E' || after === 'u' || after === 'U';
				if (bracket > 0 || nameish || floatish) { out += num; i = j; continue; }
				out += num + '.0';
				i = j;
				continue;
			}
			out += c; i++;
		}
		return out;
	}
	S.promoteInts = promoteInts;

	var WIDEN = { int: 'float', uint: 'float', ivec2: 'vec2', ivec3: 'vec3', ivec4: 'vec4',
		uvec2: 'vec2', uvec3: 'vec3', uvec4: 'vec4' };
	function widenInts(line, intNames) {
		if (/^\s*#/.test(line)) return line;
		return line.replace(/(?<![A-Za-z0-9_.])([A-Za-z_][A-Za-z0-9_]*)((?:\.[xyzwrgbastpq]+)?)\b(?!\s*\()/g,
			function (all, name, swz, at, whole) {
				var ty = intNames[name];
				if (!ty) return all;
				if (/(?:float|vec2|vec3|vec4)\($/.test(whole.slice(0, at))) return all;
				if (swz) return (swz.length === 2 ? 'float' : 'vec' + (swz.length - 1)) + '(' + name + swz + ')';
				return (WIDEN[ty] || 'float') + '(' + name + ')';
			});
	}
	S.widenInts = widenInts;

	S.rehoist = function (src) {
		var h = hoistGlobals(src);
		if (!h.init.length) return src;
		return injectIntoMain(h.src, h.init.join('\n'));
	};

	S.compileExpr = function (expr, name) {
		var src = String(expr);
		var js = translateExpr(src);
		try {
			return new Function('S', 'M', 'with (S) { return (' + js + '); }');
		} catch (e) {
			return null;
		}
	};

	function splitArgs(s) {
		var out = [], depth = 0, start = 0;
		for (var i = 0; i < s.length; i++) {
			var c = s.charAt(i);
			if (c === '(') depth++;
			else if (c === ')') depth--;
			else if (c === ',' && depth === 0) { out.push(s.slice(start, i)); start = i + 1; }
		}
		out.push(s.slice(start));
		return out;
	}

	var FN1 = { abs: 1, acos: 1, asin: 1, atan: 1, ceil: 1, cos: 1, exp: 1, floor: 1, log: 1, sin: 1, sqrt: 1, tan: 1 };
	function translateExpr(s) {
		var re = /\b([A-Za-z_][A-Za-z0-9_]*)\s*\(/;
		var m = re.exec(s);
		if (!m) return s.replace(/\^/g, '!=');
		var open = m.index + m[0].length - 1, depth = 0, i = open;
		for (; i < s.length; i++) { if (s.charAt(i) === '(') depth++; else if (s.charAt(i) === ')') { depth--; if (!depth) break; } }
		var fname = m[1], inner = s.slice(open + 1, i), rest = s.slice(i + 1);
		var args = splitArgs(inner).map(function (a) { return translateExpr(a.trim()); });
		var head = s.slice(0, m.index);
		var out;
		switch (fname) {
			case 'if':
				out = '(';
				for (var k = 0; k + 1 < args.length; k += 2) out += '(' + args[k] + ') ? (' + args[k + 1] + ') : ';
				out += '(' + (args.length % 2 ? args[args.length - 1] : '0') + '))';
				break;
			case 'in':
				out = '(' + args.slice(1).map(function (a) { return '((' + args[0] + ') == (' + a + '))'; }).join(' || ') + ')';
				break;
			case 'between': out = '((' + args[0] + ') >= (' + args[1] + ') && (' + args[0] + ') <= (' + args[2] + '))'; break;
			case 'fmod': out = '(((' + args[0] + ') % (' + args[1] + ') + (' + args[1] + ')) % (' + args[1] + '))'; break;
			case 'frac': out = '((' + args[0] + ') - M.floor(' + args[0] + '))'; break;
			case 'signum': out = 'M.sign(' + args[0] + ')'; break;
			case 'clamp': out = 'M.min(M.max(' + args[0] + ', ' + args[1] + '), ' + args[2] + ')'; break;
			case 'random': out = 'M.random()'; break;
			case 'smooth': out = 'mcSmooth(' + args.join(', ') + ')'; break;
			case 'min': case 'max': out = 'M.' + fname + '(' + args.join(', ') + ')'; break;
			case 'pow': out = 'M.pow(' + args[0] + ', ' + args[1] + ')'; break;
			case 'atan': out = args.length > 1 ? 'M.atan2(' + args[0] + ', ' + args[1] + ')' : 'M.atan(' + args[0] + ')'; break;
			case 'torad': out = '((' + args[0] + ') * 0.017453292519943295)'; break;
			case 'todeg': out = '((' + args[0] + ') * 57.29577951308232)'; break;
			case 'vec2': case 'vec3': case 'vec4': out = '[' + args.join(', ') + ']'; break;
			default:
				if (FN1[fname]) out = 'M.' + fname + '(' + args.join(', ') + ')';
				else out = '(' + args.join(', ') + ')';
				break;
		}
		return translateExpr(head) + out + translateExpr(rest);
	}

	S.build = function (files, chosen, dim, centroid) {
		var problems = [];
		var out = {
			programs: {}, options: null, props: null, consts: {}, buffers: {},
			blockMap: [], problems: problems, dim: dim || '', centroid: !!centroid
		};

		var propsFile = pick(files, 'shaders.properties');
		out.props = S.readProperties(propsFile ? text(propsFile) : '');

		var srcByFile = {};
		Object.keys(files).forEach(function (k) {
			if (/\.(fsh|vsh|gsh|glsl|settings|inc)$/i.test(k)) srcByFile[k] = text(files[k]);
		});
		out.options = S.readOptions(srcByFile, propsFile ? text(propsFile) : '');

		var edited = {};
		Object.keys(srcByFile).forEach(function (k) { edited[k] = S.applyOptions(srcByFile[k], out.options, chosen || {}); });

		var bp = pick(files, 'block.properties');
		if (bp) out.blockMap = S.readBlockProperties(text(bp));

		var lookFor = function (name, ext) {
			var tries = [];
			if (out.dim) tries.push(out.dim + '/' + name + ext);
			tries.push(name + ext);
			for (var i = 0; i < tries.length; i++) if (edited[tries[i]] !== undefined || pick(files, tries[i]) !== undefined) return tries[i];
			return null;
		};
		var srcOf = function (p) { return edited[p] !== undefined ? edited[p] : text(pick(files, p)); };

		S.PROGRAMS.forEach(function (P) {
			var vp = lookFor(P.name, '.vsh'), fp = lookFor(P.name, '.fsh');
			if (!fp && !vp) return;
			var inc = [];
			var vsrc = vp ? includeAll(files, vp, srcOf(vp), inc, 0, [vp]) : null;
			var fsrc = fp ? includeAll(files, fp, srcOf(fp), inc, 0, [fp]) : null;
			inc.forEach(function (t) { problems.push(P.name + ': ' + t); });
			if (!vsrc) vsrc = defaultVertex(fsrc, S.SCREEN_PROGRAM.test(P.name));
			if (!fsrc) fsrc = defaultFragment();

			S.readConsts(vsrc, out);
			S.readConsts(fsrc, out);

			var v = S.translate(vsrc, true, out, out.centroid && !S.SCREEN_PROGRAM.test(P.name));
			var f = S.translate(fsrc, false, out, out.centroid && !S.SCREEN_PROGRAM.test(P.name));
			v.src = S.matchVaryings(v.src, v.info, f.info, out.centroid && !S.SCREEN_PROGRAM.test(P.name));
			out.programs[P.name] = {
				name: P.name, vsh: v.src, fsh: f.src, vInfo: v.info, fInfo: f.info,
				drawBuffers: f.info.drawBuffers, screen: S.SCREEN_PROGRAM.test(P.name)
			};
		});

		out.custom = [];
		out.props.variables.concat(out.props.uniforms).forEach(function (u) {
			var fn = S.compileExpr(u.expr, u.name);
			if (!fn) { problems.push('could not read uniform.' + u.type + '.' + u.name); return; }
			out.custom.push({ name: u.name, type: u.type, fn: fn, isUniform: out.props.uniforms.indexOf(u) >= 0 });
		});

		out.enabled = {};
		Object.keys(out.props.raw).forEach(function (k) {
			var m = /^program\.([A-Za-z0-9_]+)\.enabled$/.exec(k);
			if (!m) return;
			out.enabled[m[1]] = defineExpr(out.props.raw[k], out.options, chosen || {});
		});
		out.scale = {};
		Object.keys(out.props.raw).forEach(function (k) {
			var m = /^scale\.([A-Za-z0-9_]+)$/.exec(k);
			if (m) { var v = parseFloat(out.props.raw[k]); if (v > 0 && v <= 1) out.scale[m[1]] = v; }
		});
		out.blend = {}; out.alphaTest = {};
		Object.keys(out.props.raw).forEach(function (k) {
			var m = /^blend\.([A-Za-z0-9_.]+)$/.exec(k);
			if (m) out.blend[m[1]] = out.props.raw[k].trim();
			m = /^alphaTest\.([A-Za-z0-9_.]+)$/.exec(k);
			if (m) out.alphaTest[m[1]] = out.props.raw[k].trim();
		});
		return out;
	};

	function defineExpr(expr, options, chosen) {
		var js = String(expr).replace(/\b([A-Za-z_][A-Za-z0-9_]*)\b/g, function (a, n) {
			if (n === 'true' || n === 'false') return n;
			var o = options.byId[n];
			var on = chosen[n] !== undefined ? chosen[n] : (o ? o.def : false);
			if (o && o.kind !== 'toggle') return String(on) === '0' ? 'false' : 'true';
			return on ? 'true' : 'false';
		});
		try {   return !!(new Function('return (' + js + ');'))(); } catch (e) { return true; }
	}

	function defaultVertex(fsh, screen) {
		var vary = [];
		if (fsh && mentions(fsh, 'texcoord')) vary.push('varying vec4 texcoord;');
		if (screen) {
			return '#version 120\n' + vary.join('\n') + '\nvoid main() {\n' +
				'  gl_Position = ftransform();\n' +
				(vary.length ? '  texcoord = gl_MultiTexCoord0;\n' : '') + '}\n';
		}
		return '#version 120\nvarying vec4 color;\n' + vary.join('\n') + '\nvoid main() {\n' +
			'  gl_Position = ftransform();\n  color = gl_Color;\n' +
			(vary.length ? '  texcoord = gl_TextureMatrix[0] * gl_MultiTexCoord0;\n' : '') + '}\n';
	}
	function defaultFragment() {
		return '#version 120\nuniform sampler2D texture;\nvarying vec4 color;\nvarying vec4 texcoord;\n' +
			'void main() {\n  gl_FragData[0] = texture2D(texture, texcoord.st) * color;\n}\n';
	}

	S.ready = true;
})();
