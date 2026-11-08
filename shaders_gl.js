(function () {
	'use strict';

	var S = window.MCShaders;
	if (!S) { console.warn('shaders_gl.js loaded without shaders.js'); return; }

	var gl = null;
	var P = null;
	var decl = null;
	var heapF = 0, heapI = 0;
	var frameNo = 0;
	var smooth = {};
	var seq = 0;

	function caps(g) {
		var c = { webgl2: false, float: false, norm16: false, maxUnits: 8, maxDraw: 4, maxSize: 2048 };
		try {
			c.webgl2 = (typeof WebGL2RenderingContext !== 'undefined' && g instanceof WebGL2RenderingContext);
			if (!c.webgl2) return c;
			c.float = !!(g.getExtension('EXT_color_buffer_float') || g.getExtension('EXT_color_buffer_half_float'));
			c.halfOnly = !g.getExtension('EXT_color_buffer_float') && !!g.getExtension('EXT_color_buffer_half_float');
			c.norm16 = !!g.getExtension('EXT_texture_norm16');
			c.lin = !!g.getExtension('OES_texture_float_linear');
			c.maxUnits = g.getParameter(g.MAX_TEXTURE_IMAGE_UNITS) | 0;
			c.maxDraw = g.getParameter(g.MAX_DRAW_BUFFERS) | 0;
			c.maxSize = g.getParameter(g.MAX_TEXTURE_SIZE) | 0;
		} catch (e) { }
		return c;
	}

	function formatOf(name, c) {
		var g = gl;
		var F = {
			RGBA8: [g.RGBA8, g.RGBA, g.UNSIGNED_BYTE], RGB8: [g.RGB8, g.RGB, g.UNSIGNED_BYTE],
			RGBA: [g.RGBA8, g.RGBA, g.UNSIGNED_BYTE], RGB: [g.RGB8, g.RGB, g.UNSIGNED_BYTE],
			RGBA16: c.norm16 ? [0x805B, g.RGBA, g.UNSIGNED_SHORT] : null,
			RGB16: c.norm16 ? [0x8054, g.RGB, g.UNSIGNED_SHORT] : null,
			RGBA16F: c.float ? [g.RGBA16F, g.RGBA, g.HALF_FLOAT] : null,
			RGB16F: c.float ? [g.RGB16F, g.RGB, g.HALF_FLOAT] : null,
			RGBA32F: (c.float && !c.halfOnly) ? [g.RGBA32F, g.RGBA, g.FLOAT] : null,
			RGB32F: (c.float && !c.halfOnly) ? [g.RGB32F, g.RGB, g.FLOAT] : null,
			R11F_G11F_B10F: c.float ? [g.R11F_G11F_B10F, g.RGB, g.HALF_FLOAT] : null,
			RGB10_A2: [g.RGB10_A2, g.RGBA, g.UNSIGNED_INT_2_10_10_10_REV],
			R8: [g.R8, g.RED, g.UNSIGNED_BYTE], RG8: [g.RG8, g.RG, g.UNSIGNED_BYTE],
			R16F: c.float ? [g.R16F, g.RED, g.HALF_FLOAT] : null,
			R32F: (c.float && !c.halfOnly) ? [g.R32F, g.RED, g.FLOAT] : null,
			RG16F: c.float ? [g.RG16F, g.RG, g.HALF_FLOAT] : null,
			RGBA8_SNORM: [g.RGBA8_SNORM, g.RGBA, g.BYTE]
		};
		var want = String(name || 'RGBA8').toUpperCase();
		if (F[want]) return F[want];
		var ladder = { RGBA16: 'RGBA16F', RGB16: 'RGB16F', RGBA32F: 'RGBA16F', RGB32F: 'RGB16F', R32F: 'R16F', R11F_G11F_B10F: 'RGBA16F' };
		var next = ladder[want];
		if (next && F[next]) { note('target format ' + want + ' is not available here - using ' + next); return F[next]; }
		if (want !== 'RGBA8') note('target format ' + want + ' is not available here - using RGBA8');
		return F.RGBA8;
	}

	var notes = [];
	function note(t) { if (notes.indexOf(t) < 0 && notes.length < 40) notes.push(t); }

	var lastSources = {};
	S.sourceOf = function (name, stage) {
		var e = lastSources[name];
		return e ? (stage === 'vsh' ? e.vsh : e.fsh) : null;
	};

	S.overrideFragment = function (name, stmt) {
		var e = lastSources[name], Pg = P && P.progs[name];
		if (!e || !Pg) return 'no such program';
		var src = e.fsh;
		var at = src.lastIndexOf('}');
		if (at < 0) return 'no main';
		src = src.slice(0, at) + '\n' + stmt + '\n' + src.slice(at);
		var vo = {}, fo = {};
		var v = compile(gl.VERTEX_SHADER, e.vsh, name + '.vsh(override)', vo);
		var f = compile(gl.FRAGMENT_SHADER, src, name + '.fsh(override)', fo);
		if (!v || !f) return 'did not compile: ' + (fo.log || vo.log || '').slice(0, 300);
		var prog = gl.createProgram();
		if (!link(prog, v, f, name + '(override)')) { gl.deleteProgram(prog); return 'did not link'; }
		gl.deleteShader(v); gl.deleteShader(f);
		var old = Pg.prog;
		Pg.prog = prog;
		Pg.cache = {};
		Pg.uFix = gl.getUniformLocation(prog, 'mcVertexFix');
		Pg.uAlpha = gl.getUniformLocation(prog, 'mcAlphaRef');
		Pg.fix = null; Pg.alpha = -1;
		for (var n in Pg.u) Pg.u[n].loc = gl.getUniformLocation(prog, n === 'mcTexMat' ? 'mcTexMat[0]' : n);
		gl.useProgram(prog);
		for (var i = 0; i < Pg.samplers.length; i++) {
			var sn = Pg.samplers[i];
			var inv = sn.name;
			for (var k in S.TEX_ALIAS) if (S.TEX_ALIAS[k] === sn.name) { if (gl.getUniformLocation(prog, k)) { inv = k; break; } }
			var sl = gl.getUniformLocation(prog, inv) || gl.getUniformLocation(prog, sn.name);
			if (sl) gl.uniform1i(sl, sn.unit);
		}
		gl.useProgram(null);
		gl.deleteProgram(old);
		return 'ok';
	};

	function compile(type, src, label, out, intNames) {
		var sh = gl.createShader(type);
		var tries = 0, log = '';
		for (; ;) {
			gl.shaderSource(sh, src);
			gl.compileShader(sh);
			if (gl.getShaderParameter(sh, gl.COMPILE_STATUS)) { out.src = src; return sh; }
			log = gl.getShaderInfoLog(sh) || '';
			if (tries++ >= 14) break;
			var r = S.repair(src, log, intNames);
			if (!r.edits) break;
			src = S.rehoist(r.src);
		}
		gl.deleteShader(sh);
		out.log = label + ':\n' + log;
		out.src = src;
		var first = /(?:ERROR|error):\s*\d+:(\d+):([^\n]*)/.exec(log);
		if (first) {
			var ln = src.split('\n')[parseInt(first[1], 10) - 1] || '';
			note(label + ':' + first[1] + first[2].slice(0, 120) + '  |  ' + ln.trim().slice(0, 120));
		} else {
			note(label + ' did not compile - no reason given');
		}
		return null;
	}

	function link(prog, vsh, fsh, label) {
		gl.attachShader(prog, vsh);
		gl.attachShader(prog, fsh);
		S.ATTRS.forEach(function (a) { gl.bindAttribLocation(prog, a[1], a[0]); });
		gl.linkProgram(prog);
		if (gl.getProgramParameter(prog, gl.LINK_STATUS)) return true;
		note(label + ' did not link - ' + String(gl.getProgramInfoLog(prog) || '').slice(0, 160));
		return false;
	}

	function makeProgram(def, built) {
		var vOut = {}, fOut = {};
		var vsh = compile(gl.VERTEX_SHADER, def.vsh, def.name + '.vsh', vOut, def.vInfo.ints);
		if (!vsh) return null;
		var fsh = compile(gl.FRAGMENT_SHADER, def.fsh, def.name + '.fsh', fOut, def.fInfo.ints);
		if (!fsh) { gl.deleteShader(vsh); return null; }
		var prog = gl.createProgram();
		var ok = link(prog, vsh, fsh, def.name);
		gl.deleteShader(vsh); gl.deleteShader(fsh);
		if (!ok) { gl.deleteProgram(prog); return null; }
		lastSources[def.name] = { vsh: vOut.src, fsh: fOut.src };

		var Pg = {
			name: def.name, prog: prog, screen: def.screen, drawBuffers: def.drawBuffers,
			u: {}, cache: {}, samplers: [], writes: def.drawBuffers || [0],
			uFix: gl.getUniformLocation(prog, 'mcVertexFix'),
			uAlpha: gl.getUniformLocation(prog, 'mcAlphaRef'),
			fix: null, alpha: -1
		};
		var names = {};
		Object.keys(def.vInfo.uniforms).forEach(function (n) { names[n] = def.vInfo.uniforms[n]; });
		Object.keys(def.fInfo.uniforms).forEach(function (n) { names[n] = def.fInfo.uniforms[n]; });
		Object.keys(S.MATRIX_UNIFORMS).forEach(function (n) {
			if (def.vInfo.use[n] || def.fInfo.use[n]) names[n] = S.MATRIX_UNIFORMS[n];
		});
		if (def.vInfo.use.mcTexMat || def.fInfo.use.mcTexMat) names.mcTexMat = 'mat4[]';

		gl.useProgram(prog);
		var unit = Pg.screen ? 0 : 2;
		Object.keys(names).forEach(function (n) {
			var loc = gl.getUniformLocation(prog, n === 'mcTexMat' ? 'mcTexMat[0]' : n);
			if (!loc) return;
			var ty = names[n];
			if (/^sampler/.test(ty)) {
				var want = S.TEX_ALIAS[n] || n;
				var u;
				if (!Pg.screen && S.FIXED_UNITS[want] !== undefined) u = S.FIXED_UNITS[want];
				else u = unit++;
				gl.uniform1i(loc, u);
				Pg.samplers.push({ name: want, unit: u, shadowCmp: ty === 'sampler2DShadow' });
				return;
			}
			Pg.u[n] = { loc: loc, type: ty };
		});
		gl.useProgram(null);
		if (unit > built.caps.maxUnits) note(def.name + ' wants ' + unit + ' texture units and this device has ' + built.caps.maxUnits);
		return Pg;
	}

	function makeTex(w, h, fmt, nearest, clampOnly) {
		var t = gl.createTexture();
		gl.bindTexture(gl.TEXTURE_2D, t);
		gl.texImage2D(gl.TEXTURE_2D, 0, fmt[0], w, h, 0, fmt[1], fmt[2], null);
		var filt = nearest ? gl.NEAREST : gl.LINEAR;
		gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, filt);
		gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, filt);
		gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
		gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
		gl.bindTexture(gl.TEXTURE_2D, null);
		return t;
	}

	function buildTargets(p, w, h) {
		var c = p.caps;
		w = Math.max(1, w | 0); h = Math.max(1, h | 0);
		p.w = w; p.h = h;
		for (var i = 0; i < 8; i++) {
			var spec = p.built.buffers[i] || {};
			var fmt = formatOf(spec.format || 'RGBA8', c);
			var t = p.color[i] = p.color[i] || {};
			t.format = fmt; t.clear = spec.clear !== false; t.nearest = !!spec.nearest; t.mipmap = !!spec.mipmap;
			if (t.tex) gl.deleteTexture(t.tex);
			if (t.alt) { gl.deleteTexture(t.alt); t.alt = null; }
			t.tex = makeTex(w, h, fmt, t.nearest);
			if (p.needAlt[i]) t.alt = makeTex(w, h, fmt, t.nearest);
			t.flip = false;
		}
		if (p.depth) gl.deleteTexture(p.depth);
		p.depth = makeDepth(w, h);
		['depthtex1', 'depthtex2'].forEach(function (n) {
			if (p[n]) { gl.deleteTexture(p[n]); p[n] = null; }
			if (p.wants[n]) p[n] = makeDepth(w, h);
		});
		if (!p.fbo) p.fbo = gl.createFramebuffer();
		gl.bindFramebuffer(gl.FRAMEBUFFER, p.fbo);
		gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.TEXTURE_2D, p.depth, 0);
		bindColorAttachments(p, false);
		var st = gl.checkFramebufferStatus(gl.FRAMEBUFFER);
		gl.bindFramebuffer(gl.FRAMEBUFFER, null);
		if (st !== gl.FRAMEBUFFER_COMPLETE) { note('the shader framebuffer is not usable (0x' + st.toString(16) + ')'); return false; }
		return true;
	}

	function makeDepth(w, h) {
		var t = gl.createTexture();
		gl.bindTexture(gl.TEXTURE_2D, t);
		gl.texImage2D(gl.TEXTURE_2D, 0, gl.DEPTH_COMPONENT32F, w, h, 0, gl.DEPTH_COMPONENT, gl.FLOAT, null);
		gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
		gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
		gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
		gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
		gl.bindTexture(gl.TEXTURE_2D, null);
		return t;
	}

	function bindColorAttachments(p, forWrite) {
		for (var i = 0; i < 8; i++) {
			var t = p.color[i];
			var tex = (forWrite && t.alt) ? (t.flip ? t.tex : t.alt) : (t.flip ? t.alt : t.tex);
			gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0 + i, gl.TEXTURE_2D, tex, 0);
		}
	}

	function attachOnly(p, targets) {
		for (var i = 0; i < 8; i++) {
			var write = targets.indexOf(i) >= 0;
			var t = p.color[i];
			var tex = write ? (t.alt ? (t.flip ? t.tex : t.alt) : t.tex) : null;
			gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0 + i, gl.TEXTURE_2D, tex, 0);
		}
		gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.TEXTURE_2D, null, 0);
	}
	function readTex(p, name) {
		var m = /^colortex([0-7])$/.exec(name);
		if (m) { var t = p.color[+m[1]]; return t.flip ? t.alt || t.tex : t.tex; }
		if (name === 'depthtex0') return p.depth;
		if (name === 'depthtex1') return p.depthtex1 || p.depth;
		if (name === 'depthtex2') return p.depthtex2 || p.depthtex1 || p.depth;
		if (name === 'shadowtex0' || name === 'shadowtex1') return p.shadow ? p.shadow.depth : null;
		if (name === 'shadowcolor0') return p.shadow ? p.shadow.color0 : null;
		if (name === 'shadowcolor1') return p.shadow ? p.shadow.color1 || p.shadow.color0 : null;
		if (name === 'noisetex') return p.noise;
		if (name === 'dhDepthTex0' || name === 'dhDepthTex1') return p.depth;
		return null;
	}

	function buildShadow(p) {
		var k = p.built.consts;
		var res = Math.max(64, Math.min(p.caps.maxSize, (k.shadowMapResolution || 1024) | 0));
		var s = p.shadow = { res: res, fbo: gl.createFramebuffer(), depth: makeDepth(res, res), color0: null, color1: null };
		if (p.wants.shadowcolor0) s.color0 = makeTex(res, res, formatOf('RGBA8', p.caps), false);
		if (p.wants.shadowcolor1) s.color1 = makeTex(res, res, formatOf('RGBA8', p.caps), false);
		gl.bindFramebuffer(gl.FRAMEBUFFER, s.fbo);
		gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.TEXTURE_2D, s.depth, 0);
		if (s.color0) gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, s.color0, 0);
		if (s.color1) gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT1, gl.TEXTURE_2D, s.color1, 0);
		var st = gl.checkFramebufferStatus(gl.FRAMEBUFFER);
		gl.bindFramebuffer(gl.FRAMEBUFFER, null);
		if (st !== gl.FRAMEBUFFER_COMPLETE) { note('the shadow map is not usable (0x' + st.toString(16) + ')'); p.shadow = null; return; }

		s.cmp = gl.createSampler();
		gl.samplerParameteri(s.cmp, gl.TEXTURE_COMPARE_MODE, gl.COMPARE_REF_TO_TEXTURE);
		gl.samplerParameteri(s.cmp, gl.TEXTURE_COMPARE_FUNC, gl.LEQUAL);
		var hw = k.shadowHardwareFiltering0 !== false;
		gl.samplerParameteri(s.cmp, gl.TEXTURE_MIN_FILTER, hw && p.caps.lin ? gl.LINEAR : gl.NEAREST);
		gl.samplerParameteri(s.cmp, gl.TEXTURE_MAG_FILTER, hw && p.caps.lin ? gl.LINEAR : gl.NEAREST);
		gl.samplerParameteri(s.cmp, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
		gl.samplerParameteri(s.cmp, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
	}

	function buildNoise(p) {
		var n = Math.max(16, Math.min(1024, (p.built.consts.noiseTextureResolution || 64) | 0));
		var data = new Uint8Array(n * n * 4);
		var seed = 0x9e3779b9;
		for (var i = 0; i < data.length; i++) {
			seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5; seed |= 0;
			data[i] = (seed >>> 8) & 0xff;
		}
		var t = gl.createTexture();
		gl.bindTexture(gl.TEXTURE_2D, t);
		gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, n, n, 0, gl.RGBA, gl.UNSIGNED_BYTE, data);
		gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
		gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
		gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.REPEAT);
		gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.REPEAT);
		gl.bindTexture(gl.TEXTURE_2D, null);
		p.noise = t;
	}

	function showProgram() {
		if (P.showProg !== undefined) return P.showProg;
		var NL = String.fromCharCode(10);
		var vs = ['#version 300 es',
			'in vec4 mcVertexIn;',
			'out vec2 uv;',
			'void main(){ uv = mcVertexIn.xy; gl_Position = vec4(mcVertexIn.xy * 2.0 - 1.0, 0.0, 1.0); }'].join(NL);
		var fs = ['#version 300 es',
			'precision highp float;',
			'in vec2 uv;',
			'uniform sampler2D src;',
			'uniform float mcDepthView;',
			'out vec4 o;',
			'void main(){',
			'  vec3 c = texture(src, uv).rgb;',
			'  if (mcDepthView > 0.5) {',
			'    float d = c.r;',
			'    c = vec3(clamp((d - 0.3) * 4.0, 0.0, 1.0), fract(d * 128.0), d >= 0.9995 ? 1.0 : 0.0);',
			'  }',
			'  o = vec4(c, 1.0);',
			'}'].join(NL);
		var mk = function (ty, src) { var sh = gl.createShader(ty); gl.shaderSource(sh, src); gl.compileShader(sh); return gl.getShaderParameter(sh, gl.COMPILE_STATUS) ? sh : null; };
		var v = mk(gl.VERTEX_SHADER, vs), f = mk(gl.FRAGMENT_SHADER, fs);
		if (!v || !f) return (P.showProg = null);
		var pr = gl.createProgram();
		gl.attachShader(pr, v); gl.attachShader(pr, f);
		gl.bindAttribLocation(pr, 0, 'mcVertexIn');
		gl.linkProgram(pr);
		gl.deleteShader(v); gl.deleteShader(f);
		if (!gl.getProgramParameter(pr, gl.LINK_STATUS)) return (P.showProg = null);
		gl.useProgram(pr); gl.uniform1i(gl.getUniformLocation(pr, 'src'), 0); gl.useProgram(null);
		return (P.showProg = pr);
	}
	function drawTextureToScreen(tex, depthView) {
		var pr = showProgram();
		if (!pr || !tex) return;
		gl.bindFramebuffer(gl.FRAMEBUFFER, null);
		gl.viewport(0, 0, P.w, P.h);
		gl.disable(gl.DEPTH_TEST); gl.disable(gl.BLEND); gl.disable(gl.CULL_FACE); gl.disable(gl.SCISSOR_TEST);
		gl.useProgram(pr);
		gl.uniform1f(gl.getUniformLocation(pr, 'mcDepthView'), depthView ? 1 : 0);
		gl.bindVertexArray(P.quadVao);
		gl.activeTexture(gl.TEXTURE0);
		var was = gl.getParameter(gl.TEXTURE_BINDING_2D);
		gl.bindSampler(0, null);
		gl.bindTexture(gl.TEXTURE_2D, tex);
		gl.drawArrays(gl.TRIANGLE_FAN, 0, 4);
		gl.bindTexture(gl.TEXTURE_2D, was);
		gl.bindVertexArray(null);
		gl.useProgram(null);
		if (typeof GLImmediate !== 'undefined') GLImmediate.fixedFunctionProgram = 0;
	}

	function buildQuad(p) {
		var v = new Float32Array([
			0, 0, 0, 1, 0, 0, 0, 1,
			1, 0, 0, 1, 1, 0, 0, 1,
			1, 1, 0, 1, 1, 1, 0, 1,
			0, 1, 0, 1, 0, 1, 0, 1
		]);
		p.quadVbo = gl.createBuffer();
		gl.bindBuffer(gl.ARRAY_BUFFER, p.quadVbo);
		gl.bufferData(gl.ARRAY_BUFFER, v, gl.STATIC_DRAW);
		p.quadVao = gl.createVertexArray();
		gl.bindVertexArray(p.quadVao);
		gl.bindBuffer(gl.ARRAY_BUFFER, p.quadVbo);
		gl.enableVertexAttribArray(0);
		gl.vertexAttribPointer(0, 4, gl.FLOAT, false, 32, 0);
		gl.enableVertexAttribArray(1);
		gl.vertexAttribPointer(1, 4, gl.FLOAT, false, 32, 16);
		gl.bindVertexArray(null);
		gl.bindBuffer(gl.ARRAY_BUFFER, null);
	}

	S.declare = function (fDecl, iDecl, fPtr, iPtr) {
		decl = { f: {}, i: {} };
		var fo = 0, io = 0;
		String(fDecl).split(';').forEach(function (part) {
			if (!part) return;
			var kv = part.split(','), name = kv[0], type = kv[1];
			var n = { mat4: 16, mat3: 9, vec4: 4, vec3: 3, vec2: 2, float: 1 }[type] || 1;
			decl.f[name] = { off: fo, n: n, type: type };
			fo += n;
		});
		String(iDecl).split(';').forEach(function (part) {
			if (!part) return;
			var kv = part.split(','), name = kv[0], type = kv[1];
			var n = { ivec4: 4, ivec3: 3, ivec2: 2, int: 1, bool: 1 }[type] || 1;
			decl.i[name] = { off: io, n: n, type: type };
			io += n;
		});
		heapF = fPtr; heapI = iPtr;
		decl.floats = fo; decl.ints = io;
		return ((fo & 0xffff) << 16) | (io & 0xffff);
	};

	function mul4(a, b, out) {
		out = out || new Float32Array(16);
		for (var c = 0; c < 4; c++) {
			for (var r = 0; r < 4; r++) {
				out[c * 4 + r] = a[r] * b[c * 4] + a[4 + r] * b[c * 4 + 1] + a[8 + r] * b[c * 4 + 2] + a[12 + r] * b[c * 4 + 3];
			}
		}
		return out;
	}

	function inv4(m, out) {
		out = out || new Float32Array(16);
		var a00 = m[0], a01 = m[1], a02 = m[2], a03 = m[3];
		var a10 = m[4], a11 = m[5], a12 = m[6], a13 = m[7];
		var a20 = m[8], a21 = m[9], a22 = m[10], a23 = m[11];
		var a30 = m[12], a31 = m[13], a32 = m[14], a33 = m[15];
		var b00 = a00 * a11 - a01 * a10, b01 = a00 * a12 - a02 * a10, b02 = a00 * a13 - a03 * a10;
		var b03 = a01 * a12 - a02 * a11, b04 = a01 * a13 - a03 * a11, b05 = a02 * a13 - a03 * a12;
		var b06 = a20 * a31 - a21 * a30, b07 = a20 * a32 - a22 * a30, b08 = a20 * a33 - a23 * a30;
		var b09 = a21 * a32 - a22 * a31, b10 = a21 * a33 - a23 * a31, b11 = a22 * a33 - a23 * a32;
		var det = b00 * b11 - b01 * b10 + b02 * b09 + b03 * b08 - b04 * b07 + b05 * b06;
		if (!det) { out.set(P.identity.mat4); return out; }
		det = 1.0 / det;
		out[0] = (a11 * b11 - a12 * b10 + a13 * b09) * det;
		out[1] = (a02 * b10 - a01 * b11 - a03 * b09) * det;
		out[2] = (a31 * b05 - a32 * b04 + a33 * b03) * det;
		out[3] = (a22 * b04 - a21 * b05 - a23 * b03) * det;
		out[4] = (a12 * b08 - a10 * b11 - a13 * b07) * det;
		out[5] = (a00 * b11 - a02 * b08 + a03 * b07) * det;
		out[6] = (a32 * b02 - a30 * b05 - a33 * b01) * det;
		out[7] = (a20 * b05 - a22 * b02 + a23 * b01) * det;
		out[8] = (a10 * b10 - a11 * b08 + a13 * b06) * det;
		out[9] = (a01 * b08 - a00 * b10 - a03 * b06) * det;
		out[10] = (a30 * b04 - a31 * b02 + a33 * b00) * det;
		out[11] = (a21 * b02 - a20 * b04 - a23 * b00) * det;
		out[12] = (a11 * b07 - a10 * b09 - a12 * b06) * det;
		out[13] = (a00 * b09 - a01 * b07 + a02 * b06) * det;
		out[14] = (a31 * b01 - a30 * b03 - a32 * b00) * det;
		out[15] = (a20 * b03 - a21 * b01 + a22 * b00) * det;
		return out;
	}

	function normalMat(mv, out) {
		var i = inv4(mv, new Float32Array(16));
		out = out || new Float32Array(9);
		out[0] = i[0]; out[1] = i[4]; out[2] = i[8];
		out[3] = i[1]; out[4] = i[5]; out[5] = i[9];
		out[6] = i[2]; out[7] = i[6]; out[8] = i[10];
		return out;
	}

	function rot3(m, v, out) {
		out = out || new Float32Array(3);
		out[0] = m[0] * v[0] + m[4] * v[1] + m[8] * v[2];
		out[1] = m[1] * v[0] + m[5] * v[1] + m[9] * v[2];
		out[2] = m[2] * v[0] + m[6] * v[1] + m[10] * v[2];
		return out;
	}

	function shadowMatrices(lightWorld, dist, pathRot) {
		var f = [-lightWorld[0], -lightWorld[1], -lightWorld[2]];
		var len = Math.hypot(f[0], f[1], f[2]) || 1;
		f = [f[0] / len, f[1] / len, f[2] / len];
		var up = Math.abs(f[1]) > 0.99 ? [0, 0, 1] : [0, 1, 0];
		var sx = [f[1] * up[2] - f[2] * up[1], f[2] * up[0] - f[0] * up[2], f[0] * up[1] - f[1] * up[0]];
		len = Math.hypot(sx[0], sx[1], sx[2]) || 1;
		sx = [sx[0] / len, sx[1] / len, sx[2] / len];
		var uy = [sx[1] * f[2] - sx[2] * f[1], sx[2] * f[0] - sx[0] * f[2], sx[0] * f[1] - sx[1] * f[0]];
		var mv = new Float32Array([
			sx[0], uy[0], -f[0], 0,
			sx[1], uy[1], -f[1], 0,
			sx[2], uy[2], -f[2], 0,
			0, 0, -100, 1
		]);
		if (pathRot) {
			var r = pathRot * Math.PI / 180, c = Math.cos(r), sn = Math.sin(r);
			var rz = new Float32Array([c, sn, 0, 0, -sn, c, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);
			mv = mul4(rz, mv);
		}
		var h = dist > 0 ? dist : 80, n = 0.05, fa = 256.0;
		var pr = new Float32Array([
			1 / h, 0, 0, 0,
			0, 1 / h, 0, 0,
			0, 0, -2 / (fa - n), 0,
			0, 0, -(fa + n) / (fa - n), 1
		]);
		return { mv: mv, pr: pr };
	}

	function captureMatrices() {
		var M = P.mats || (P.mats = {});
		if (typeof GLImmediate === 'undefined' || !GLImmediate.matrix) return;
		var mv = GLImmediate.matrix[0], pr = GLImmediate.matrix[1];
		M.gbufferPreviousModelView = M.gbufferModelView || new Float32Array(mv);
		M.gbufferPreviousProjection = M.gbufferProjection || new Float32Array(pr);
		M.gbufferModelView = new Float32Array(mv);
		M.gbufferProjection = new Float32Array(pr);
		M.gbufferModelViewInverse = inv4(mv);
		M.gbufferProjectionInverse = inv4(pr);

		var sunW = fv('sunWorld') || new Float32Array([0, 1, 0]);
		var D = P.derived || (P.derived = {});
		var s = rot3(mv, sunW);
		D.sunPosition = new Float32Array([s[0] * 100, s[1] * 100, s[2] * 100]);
		D.moonPosition = new Float32Array([-s[0] * 100, -s[1] * 100, -s[2] * 100]);
		var u = rot3(mv, [0, 1, 0]);
		D.upPosition = new Float32Array([u[0] * 100, u[1] * 100, u[2] * 100]);
		var isSun = i1('shadowLightIsSun') !== 0;
		D.shadowLightPosition = isSun ? D.sunPosition : D.moonPosition;

		var k = P.built.consts;
		var sm = shadowMatrices(isSun ? sunW : [-sunW[0], -sunW[1], -sunW[2]],
			k.shadowDistance || 80, k.sunPathRotation || 0);
		M.shadowModelView = sm.mv;
		M.shadowProjection = sm.pr;
		M.shadowModelViewInverse = inv4(sm.mv);
		M.shadowProjectionInverse = inv4(sm.pr);
		M.shadowFromCamera = mul4(sm.mv, M.gbufferModelViewInverse, M.shadowFromCamera);
	}

	function fv(name) {
		var d = decl.f[name];
		if (!d) return null;
		return HEAPF32.subarray((heapF >> 2) + d.off, (heapF >> 2) + d.off + d.n);
	}
	function f1(name) { var d = decl.f[name]; return d ? HEAPF32[(heapF >> 2) + d.off] : 0; }
	function i1(name) { var d = decl.i[name]; return d ? HEAP32[(heapI >> 2) + d.off] : 0; }
	function iv(name) {
		var d = decl.i[name];
		if (!d) return null;
		return HEAP32.subarray((heapI >> 2) + d.off, (heapI >> 2) + d.off + d.n);
	}

	function mcSmooth(id, value, up, down) {
		var dt = Math.max(0.0001, Math.min(0.5, P ? P.frameTime : 0.016));
		var hl = (down === undefined ? up : (value < (smooth[id] === undefined ? value : smooth[id]) ? down : up)) || 1;
		var k = 1 - Math.exp(-dt / Math.max(0.0001, hl));
		var prev = smooth[id] === undefined ? value : smooth[id];
		smooth[id] = prev + (value - prev) * k;
		return smooth[id];
	}

	S.dumpUniforms = function (name) { P.dumpU = name; P.dumpUOut = null; return 1; };
	S.uniformDump = function () { return P ? P.dumpUOut : null; };

	function setUniforms(Pg) {
		var cache = Pg.cache;
		var live = liveMatrices();
		if (P.dumpU && Pg.name === P.dumpU) {
			P.dumpU = null;
			var d = [];
			for (var dn in Pg.u) {
				var du = Pg.u[dn], dv, src;
				if (du.type === 'mat4' || du.type === 'mat3') {
					dv = live[dn] ? 'live' : (P.mats && P.mats[dn]) ? 'captured' : fv(dn) ? 'block' : 'IDENTITY';
					var m = live[dn] || (P.mats && P.mats[dn]) || fv(dn);
					d.push(dn + ' (' + du.type + ', ' + dv + ') ' + (m ? Array.prototype.slice.call(m, 0, 4).map(function (q) { return (+q).toFixed(3); }).join(',') : '-'));
				} else if (/^(vec2|vec3|vec4)$/.test(du.type)) {
					var vv = P.custom[dn] || (P.derived && P.derived[dn]) || fv(dn);
					src = P.custom[dn] ? 'custom' : (P.derived && P.derived[dn]) ? 'derived' : fv(dn) ? 'block' : 'MISSING';
					d.push(dn + ' (' + du.type + ', ' + src + ') ' + (vv ? Array.prototype.slice.call(vv).map(function (q) { return (+q).toFixed(3); }).join(',') : '-'));
				} else if (du.type === 'float') {
					var sv = P.custom[dn] !== undefined ? P.custom[dn] : f1(dn);
					src = P.custom[dn] !== undefined ? 'custom' : decl.f[dn] ? 'block' : 'ZERO';
					d.push(dn + ' (float, ' + src + ') ' + sv + (isNaN(sv) ? '   <-- NaN' : ''));
				} else {
					var nv = P.custom[dn] !== undefined ? (P.custom[dn] | 0) : i1(dn);
					src = P.custom[dn] !== undefined ? 'custom' : decl.i[dn] ? 'block' : 'ZERO';
					d.push(dn + ' (' + du.type + ', ' + src + ') ' + nv);
				}
			}
			P.dumpUOut = d.sort();
		}
		for (var name in Pg.u) {
			var u = Pg.u[name], ty = u.type;
			if (ty === 'mat4' || ty === 'mat3') {
				var m = live[name] || (P.mats && P.mats[name]) || fv(name) || P.identity[ty];
				if (!same(cache, name, m)) {
					if (ty === 'mat4') gl.uniformMatrix4fv(u.loc, false, m); else gl.uniformMatrix3fv(u.loc, false, m);
				}
				continue;
			}
			if (ty === 'mat4[]') {
				if (!cache._texmat) { gl.uniformMatrix4fv(u.loc, false, P.texMats); cache._texmat = 1; }
				continue;
			}
			if (/^(vec2|vec3|vec4)$/.test(ty)) {
				var v = P.custom[name] || (P.derived && P.derived[name]) || fv(name);
				if (!v) continue;
				if (!same(cache, name, v)) {
					if (ty === 'vec2') gl.uniform2fv(u.loc, v); else if (ty === 'vec3') gl.uniform3fv(u.loc, v); else gl.uniform4fv(u.loc, v);
				}
				continue;
			}
			if (ty === 'float') {
				var s = P.custom[name] !== undefined ? P.custom[name] : f1(name);
				if (cache[name] !== s) { cache[name] = s; gl.uniform1f(u.loc, s); }
				continue;
			}
			if (/^(ivec2|ivec3|ivec4)$/.test(ty)) {
				var a = iv(name);
				if (!a) continue;
				if (!same(cache, name, a)) {
					if (ty === 'ivec2') gl.uniform2iv(u.loc, a); else if (ty === 'ivec3') gl.uniform3iv(u.loc, a); else gl.uniform4iv(u.loc, a);
				}
				continue;
			}
			var n = P.custom[name] !== undefined ? (P.custom[name] | 0) : i1(name);
			if (cache[name] !== n) { cache[name] = n; gl.uniform1i(u.loc, n); }
		}
	}
	function same(cache, name, arr) {
		var c = cache[name];
		if (!c || c.length !== arr.length) { cache[name] = arr.slice(0); return false; }
		for (var i = 0; i < arr.length; i++) if (c[i] !== arr[i]) { for (var k = 0; k < arr.length; k++) c[k] = arr[k]; return false; }
		return true;
	}

	function liveMatrices() {
		var out = P.live || (P.live = {});
		if (P.screenPass) {
			out.mcProjMat = P.ortho || (P.ortho = new Float32Array([2, 0, 0, 0, 0, 2, 0, 0, 0, 0, -1, 0, -1, -1, 0, 1]));
			out.mcMvMat = P.identity.mat4;
			out.mcNormalMat = P.identity.mat3;
			return out;
		}
		if (P.inShadow) {
			var SM = P.mats;
			var cur = (typeof GLImmediate !== 'undefined' && GLImmediate.matrix) ? GLImmediate.matrix[0] : null;
			var smv = (cur && SM.shadowFromCamera)
				? mul4(SM.shadowFromCamera, cur, out.shadowMv || (out.shadowMv = new Float32Array(16)))
				: SM.shadowModelView;
			out.mcMvMat = smv;
			out.mcProjMat = SM.shadowProjection;
			out.mcNormalMat = normalMat(smv, out.mcNormalMat3 || (out.mcNormalMat3 = new Float32Array(9)));
			return out;
		}
		if (typeof GLImmediate === 'undefined' || !GLImmediate.matrix) { out.mcMvMat = null; out.mcProjMat = null; out.mcNormalMat = null; return out; }
		out.mcMvMat = GLImmediate.matrix[0];
		out.mcProjMat = GLImmediate.matrix[1];
		out.mcNormalMat = normalMat(GLImmediate.matrix[0], out.mcNormalMat3 || (out.mcNormalMat3 = new Float32Array(9)));
		return out;
	}

	function bindTextures(Pg) {
		var s = Pg.samplers;
		for (var i = 0; i < s.length; i++) {
			var d = s[i];
			if (!Pg.screen && S.FIXED_UNITS[d.name] !== undefined) continue;
			var tex = readTex(P, d.name);
			gl.activeTexture(gl.TEXTURE0 + d.unit);
			d.was = gl.getParameter(gl.TEXTURE_BINDING_2D);
			gl.bindTexture(gl.TEXTURE_2D, tex);
			if (d.shadowCmp && P.shadow) gl.bindSampler(d.unit, P.shadow.cmp);
			else gl.bindSampler(d.unit, null);
		}
		gl.activeTexture(gl.TEXTURE0);
	}
	function unbindTextures(Pg) {
		var s = Pg.samplers;
		for (var i = 0; i < s.length; i++) {
			var d = s[i];
			if (!Pg.screen && S.FIXED_UNITS[d.name] !== undefined) continue;
			gl.activeTexture(gl.TEXTURE0 + d.unit);
			gl.bindTexture(gl.TEXTURE_2D, d.was || null);
			d.was = null;
			gl.bindSampler(d.unit, null);
		}
		gl.activeTexture(gl.TEXTURE0);
	}

	S.start = function (built, w, h) {
		S.stop();
		notes = [];
		gl = (typeof GLctx !== 'undefined') ? GLctx : null;
		if (!gl) return 'there is no WebGL context yet';
		var c = caps(gl);
		if (!c.webgl2) return 'shader packs need WebGL 2, and this browser gave the game WebGL 1';
		if (!decl) return 'the game has not sent the uniform list yet';

		var p = {
			built: built, caps: c, color: [], needAlt: {}, wants: {}, progs: {}, custom: {},
			w: 0, h: 0, frameTime: 0.016, identity: { mat4: ident4(), mat3: ident3() },
			texMats: new Float32Array(48), shadow: null, noise: null, cur: null, curName: '',
			bound: false, lastProg: null
		};
		for (var k = 0; k < 3; k++) for (var j = 0; j < 4; j++) p.texMats[k * 16 + j * 5] = 1;
		p.texMats[16 + 0] = p.texMats[16 + 5] = p.texMats[16 + 10] = 1 / 256;
		p.texMats[16 + 12] = p.texMats[16 + 13] = p.texMats[16 + 14] = 8 / 256;

		var names = Object.keys(built.programs);
		var writtenByScreen = {}, readAnywhere = {};
		names.forEach(function (n) {
			var d = built.programs[n];
			var all = d.vsh + '\n' + d.fsh;
			S.SAMPLER_NAMES.forEach(function (sn) {
				if (S.mentions(all, sn)) readAnywhere[S.TEX_ALIAS[sn] || sn] = true;
			});
			Object.keys(S.TEX_ALIAS).forEach(function (sn) {
				if (S.mentions(all, sn)) readAnywhere[S.TEX_ALIAS[sn]] = true;
			});
			if (d.screen && d.drawBuffers) d.drawBuffers.forEach(function (i) { writtenByScreen[i] = true; });
		});
		p.wants = readAnywhere;
		for (var i = 0; i < 8; i++) p.needAlt[i] = !!(writtenByScreen[i] && readAnywhere['colortex' + i]);

		var ok = true, log = [];
		names.forEach(function (n) {
			var Pg = makeProgram(built.programs[n], p);
			if (Pg) p.progs[n] = Pg; else ok = false;
		});
		if (!p.progs.gbuffers_terrain && !p.progs.gbuffers_textured && !p.progs.gbuffers_basic) {
			teardown(p);
			return 'this pack has no gbuffers program the game can use' + (notes.length ? ' (' + notes[0] + ')' : '');
		}
		S.PROGRAMS.forEach(function (def) {
			if (p.progs[def.name]) return;
			for (var i = 0; i < def.fall.length; i++) if (p.progs[def.fall[i]]) { p.progs[def.name] = p.progs[def.fall[i]]; return; }
		});
		Object.keys(built.enabled).forEach(function (n) { if (!built.enabled[n]) delete p.progs[n]; });

		p.shadowWanted = !!(p.progs.shadow || p.progs.shadow_solid) && (p.wants.shadowtex0 || p.wants.shadowcolor0);
		if (p.shadowWanted) buildShadow(p);
		if (p.wants.noisetex) buildNoise(p);
		buildQuad(p);
		if (!buildTargets(p, w, h)) { teardown(p); return notes[0] || 'the shader framebuffers could not be made'; }

		p.chain = [];
		['deferred', 'deferred1', 'deferred2', 'deferred3', 'deferred4', 'deferred5', 'deferred6', 'deferred7',
			'composite', 'composite1', 'composite2', 'composite3', 'composite4', 'composite5', 'composite6', 'composite7'].forEach(function (n) {
				if (!built.programs[n] || !p.progs[n] || p.progs[n].name !== n) return;
				p.chain.push({ Pg: p.progs[n], targets: built.programs[n].drawBuffers || [0], scale: built.scale[n] || 1 });
			});
		p.finalPg = (p.progs.final && p.progs.final.name === 'final') ? p.progs.final : null;
		p.custom = {};
		p.customDefs = built.custom || [];
		P = p;
		++seq;
		frameNo = 0; smooth = {};
		if (notes.length) console.warn('shader pack notes:\n  ' + notes.join('\n  '));
		return '';
	};

	function teardown(p) {
		if (!p || !gl) return;
		try {
			var seen = [];
			Object.keys(p.progs).forEach(function (n) {
				var Pg = p.progs[n];
				if (Pg && seen.indexOf(Pg.prog) < 0) { seen.push(Pg.prog); gl.deleteProgram(Pg.prog); }
			});
			(p.color || []).forEach(function (t) { if (t.tex) gl.deleteTexture(t.tex); if (t.alt) gl.deleteTexture(t.alt); });
			if (p.depth) gl.deleteTexture(p.depth);
			if (p.depthtex1) gl.deleteTexture(p.depthtex1);
			if (p.depthtex2) gl.deleteTexture(p.depthtex2);
			if (p.fbo) gl.deleteFramebuffer(p.fbo);
			if (p.noise) gl.deleteTexture(p.noise);
			if (p.quadVbo) gl.deleteBuffer(p.quadVbo);
			if (p.quadVao) gl.deleteVertexArray(p.quadVao);
			if (p.shadow) {
				if (p.shadow.depth) gl.deleteTexture(p.shadow.depth);
				if (p.shadow.color0) gl.deleteTexture(p.shadow.color0);
				if (p.shadow.color1) gl.deleteTexture(p.shadow.color1);
				if (p.shadow.fbo) gl.deleteFramebuffer(p.shadow.fbo);
				if (p.shadow.cmp) gl.deleteSampler(p.shadow.cmp);
			}
			(p.vaos || []).forEach(function (v) { gl.deleteVertexArray(v); });
		} catch (e) { }
	}

	S.stop = function (why) {
		if (P) {
			console.warn('shader pipeline stopped: ' + (why || 'no reason given') +
				' | from ' + String((new Error()).stack).split(String.fromCharCode(10)).slice(1, 4).join(' <- '));
			teardown(P); P = null; ++seq;
		}
		return 1;
	};
	S.active = function () { return P ? 1 : 0; };
	S.declaredForTest = function () { return !!decl; };

	var scratchFbo = null;
	var PROBE_POINTS = [[0.5, 0.5], [0.25, 0.8], [0.5, 0.8], [0.75, 0.8], [0.5, 0.95]];
	function centrePixel(tex) {
		if (!tex) return null;
		var was = gl.getParameter(gl.FRAMEBUFFER_BINDING);
		if (!scratchFbo) scratchFbo = gl.createFramebuffer();
		var out = [];
		try {
			gl.bindFramebuffer(gl.FRAMEBUFFER, scratchFbo);
			gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, tex, 0);
			if (gl.checkFramebufferStatus(gl.FRAMEBUFFER) !== gl.FRAMEBUFFER_COMPLETE) return 'unreadable';
			gl.readBuffer(gl.COLOR_ATTACHMENT0);
			var type = gl.getParameter(gl.IMPLEMENTATION_COLOR_READ_TYPE);
			var fmt = gl.getParameter(gl.IMPLEMENTATION_COLOR_READ_FORMAT);
			if (fmt !== gl.RGBA && fmt !== gl.RGB) fmt = gl.RGBA;
			var n = fmt === gl.RGB ? 3 : 4;
			var px, scale = 1;
			if (type === gl.FLOAT) { px = new Float32Array(4); scale = 0; }
			else if (type === gl.HALF_FLOAT) { px = new Uint16Array(4); scale = -1; }
			else if (type === gl.UNSIGNED_SHORT) { px = new Uint16Array(4); scale = 1 / 257; }
			else if (type === gl.UNSIGNED_INT || type === gl.UNSIGNED_INT_2_10_10_10_REV) { px = new Uint32Array(4); scale = 0; }
			else { type = gl.UNSIGNED_BYTE; px = new Uint8Array(4); }
			for (var i = 0; i < PROBE_POINTS.length; i++) {
				gl.readPixels((P.w * PROBE_POINTS[i][0]) | 0, (P.h * (1 - PROBE_POINTS[i][1])) | 0, 1, 1, fmt, type, px);
				var vals = [];
				for (var c = 0; c < n; c++) {
					vals.push(scale === 0 ? px[c].toFixed(3) : scale === -1 ? ('h' + px[c]) : Math.round(px[c] * scale));
				}
				out.push(vals.join(','));
			}
			return out.join(' | ');
		} catch (e) {
			return 'read failed';
		} finally {
			gl.bindFramebuffer(gl.FRAMEBUFFER, was);
		}
	}
	function texOf(i) { var t = P.color[i]; return t.flip ? (t.alt || t.tex) : t.tex; }

	var showBuffer = -1, showRaw = -1, traceFrames = 0, traceLog = [];
	var stateDump = false;
	S.dumpState = function () { stateDump = true; S.lastState = null; return 1; };
	var checkErrors = false;
	S.checkErrors = function (on) { checkErrors = !!on; if (P) P.errs = {}; return 1; };
	S.errorCounts = function () { return P ? (P.errs || {}) : null; };
	function noteErr(where) {
		if (!checkErrors || !P) return;
		var e = gl.getError();
		if (!e) return;
		P.errs = P.errs || {};
		var k = where + ' 0x' + e.toString(16);
		P.errs[k] = (P.errs[k] || 0) + 1;
	}
	S.debugShow = function (i, raw) {
		showBuffer = (i === null || i === undefined) ? -1 : (i | 0);
		showRaw = raw ? showBuffer : -1;
		return showBuffer;
	};
	S.trace = function (n) { traceFrames = n || 1; traceLog = []; return 1; };
	S.traceLog = function () { return traceLog.slice(0); };
	function mark(what) {
		if (!traceFrames || !P) return;
		var fb = gl.getParameter(gl.FRAMEBUFFER_BINDING);
		var where = fb === P.fbo ? 'gbuffer' : fb === null ? 'SCREEN' : (P.shadow && fb === P.shadow.fbo) ? 'shadow' : 'other';
		traceLog.push(what + ' [' + where + ']' +
			'\n      tex0 ' + centrePixel(texOf(0)) +
			'\n      tex1 ' + centrePixel(texOf(1)) +
			'\n      tex2 ' + centrePixel(texOf(2)));
	}

	S.shadowInfo = function () {
		if (!P) return null;
		var k = P.built ? P.built.consts : {};
		var M = P.mats || {};
		return {
			wanted: !!P.shadowWanted, res: P.shadow ? P.shadow.res : 0,
			hasColor0: !!(P.shadow && P.shadow.color0),
			shadowDistance: k.shadowDistance, shadowDistanceRenderMul: k.shadowDistanceRenderMul,
			shadowMapResolution: k.shadowMapResolution, sunPathRotation: k.sunPathRotation,
			shadowIntervalSize: k.shadowIntervalSize,
			sunWorld: Array.from(fv('sunWorld') || []),
			sunAngle: f1('sunAngle'), shadowAngle: f1('shadowAngle'),
			shadowLightIsSun: i1('shadowLightIsSun'),
			shadowModelView: M.shadowModelView ? Array.from(M.shadowModelView) : null,
			shadowProjection: M.shadowProjection ? Array.from(M.shadowProjection) : null,
			gbufferModelView: M.gbufferModelView ? Array.from(M.gbufferModelView) : null
		};
	};

	S.probeTargets = function () {
		if (!P) return null;
		var out = {}, px = new Uint8Array(4);
		var fb = gl.createFramebuffer();
		gl.bindFramebuffer(gl.FRAMEBUFFER, fb);
		for (var i = 0; i < 8; i++) {
			var t = P.color[i];
			var tex = t.flip ? (t.alt || t.tex) : t.tex;
			gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, tex, 0);
			if (gl.checkFramebufferStatus(gl.FRAMEBUFFER) !== gl.FRAMEBUFFER_COMPLETE) { out['colortex' + i] = 'not readable'; continue; }
			try {
				gl.readBuffer(gl.COLOR_ATTACHMENT0);
				gl.readPixels((P.w / 2) | 0, (P.h / 2) | 0, 1, 1, gl.RGBA, gl.UNSIGNED_BYTE, px);
				out['colortex' + i] = [px[0], px[1], px[2], px[3]];
			} catch (e) { out['colortex' + i] = 'read failed: ' + e; }
		}
		gl.bindFramebuffer(gl.FRAMEBUFFER, null);
		gl.deleteFramebuffer(fb);
		out._flips = P.color.map(function (t) { return t.flip ? 1 : 0; });
		out._lastPass = P.curName;
		out._counts = P.counts || null;
		return out;
	};

	S.drawCounts = function () { return P ? (P.lastCounts || P.counts || {}) : null; };

	S.wants = function (what) {
		if (!P) return 0;
		if (what === 'shadow') return (P.shadowWanted && P.progs.shadow) ? 1 : 0;
		return P.wants[what] ? 1 : 0;
	};

	S.shadowRange = function () {
		if (!P || !P.shadow) return 0;
		var k = P.built.consts;
		var d = k.shadowDistance > 0 ? k.shadowDistance : 80;
		if (k.shadowDistanceRenderMul > 0) d *= k.shadowDistanceRenderMul;
		return Math.round(Math.max(16, Math.min(512, d)));
	};

	S.selectionSeq = function () { return seq; };
	S.notes = function () { return notes.slice(0); };

	var traceDraws = false, traced = {};
	S.traceDraws = function (on) {
		if (on) { traceDraws = true; traced = {}; return null; }
		traceDraws = false;
		return traced;
	};

	S.debugGl = function () {
		if (!gl) return null;
		return {
			blend: gl.isEnabled(gl.BLEND),
			blendSrc: gl.getParameter(gl.BLEND_SRC_RGB), blendDst: gl.getParameter(gl.BLEND_DST_RGB),
			depthTest: gl.isEnabled(gl.DEPTH_TEST), depthMask: gl.getParameter(gl.DEPTH_WRITEMASK),
			cull: gl.isEnabled(gl.CULL_FACE), pass: P ? P.curName : ''
		};
	};

	S.debugPrograms = function () {
		if (!P) return null;
		var out = {};
		Object.keys(P.progs).forEach(function (n) {
			var Pg = P.progs[n];
			out[n] = { is: Pg.name, writes: Pg.drawBuffers || [0], samplers: Pg.samplers.map(function (s) { return s.name; }) };
		});
		out._targets = P.color.map(function (t, i) { return i + (t.alt ? '(2)' : '') + (t.clear ? '' : ' kept'); });
		out._shadow = P.shadow ? P.shadow.res : 0;
		out._chain = P.chain.map(function (c) { return c.Pg.name + '->' + c.targets.join(','); });
		out._size = [P.w, P.h];
		return out;
	};

	function ident4() { return new Float32Array([1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]); }
	function ident3() { return new Float32Array([1, 0, 0, 0, 1, 0, 0, 0, 1]); }

	S.frame = function (w, h, frameTime) {
		if (!P) return 0;
		P.frameTime = frameTime > 0 ? frameTime : 0.016;
		if (w !== P.w || h !== P.h) {
			if (!buildTargets(P, w, h)) { S.stop('the targets could not be rebuilt at ' + w + 'x' + h); return 0; }
		}
		frameNo++;
		P.lastCounts = P.counts; P.counts = {};
		var state = frameState();
		P.custom = {};
		for (var i = 0; i < P.customDefs.length; i++) {
			var d = P.customDefs[i];
			try {
				var v = d.fn(state, Math);
				P.custom[d.name] = v;
				state[d.name] = v;
			} catch (e) { P.custom[d.name] = 0; }
		}
		var seen = [];
		for (var n in P.progs) {
			var Pg = P.progs[n];
			if (seen.indexOf(Pg) >= 0) continue;
			seen.push(Pg); Pg.cache = {};
		}
		return 1;
	};

	function frameState() {
		var s = {
			frameCounter: frameNo, frameTime: P.frameTime, frameTimeCounter: f1('frameTimeCounter'),
			worldTime: i1('worldTime'), worldDay: i1('worldDay'), moonPhase: i1('moonPhase'),
			sunAngle: f1('sunAngle'), shadowAngle: f1('shadowAngle'), rainStrength: f1('rainStrength'),
			wetness: f1('wetness'), isEyeInWater: i1('isEyeInWater'), eyeAltitude: f1('eyeAltitude'),
			nightVision: f1('nightVision'), blindness: f1('blindness'), screenBrightness: f1('screenBrightness'),
			biome: i1('biome'), biome_category: i1('biome_category'), temperature: f1('temperature'),
			rainfall: f1('rainfall'), heldItemId: i1('heldItemId'), heldBlockLightValue: i1('heldBlockLightValue'),
			viewWidth: f1('viewWidth'), viewHeight: f1('viewHeight'), aspectRatio: f1('aspectRatio'),
			near: f1('near'), far: f1('far'), hideGUI: i1('hideGUI'), isCreative: i1('isCreative'),
			sunElevation: f1('sunElevation'), dayTime: i1('worldTime'),
			mcSmooth: mcSmooth, pi: Math.PI
		};
		for (var k in BIOME_IDS) s[k] = BIOME_IDS[k];
		s.cameraPosition = fv('cameraPosition');
		return s;
	}

	var BIOME_IDS = {
		BIOME_OCEAN: 0, BIOME_PLAINS: 1, BIOME_DESERT: 2, BIOME_MOUNTAINS: 3, BIOME_EXTREME_HILLS: 3,
		BIOME_FOREST: 4, BIOME_TAIGA: 5, BIOME_SWAMP: 6, BIOME_SWAMPLAND: 6, BIOME_RIVER: 7,
		BIOME_NETHER: 8, BIOME_HELL: 8, BIOME_THE_END: 9, BIOME_SKY: 9, BIOME_FROZEN_OCEAN: 10,
		BIOME_FROZEN_RIVER: 11, BIOME_SNOWY_TUNDRA: 12, BIOME_ICE_PLAINS: 12, BIOME_SNOWY_MOUNTAINS: 13,
		BIOME_MUSHROOM_FIELDS: 14, BIOME_MUSHROOM_ISLAND: 14, BIOME_MUSHROOM_FIELD_SHORE: 15,
		BIOME_BEACH: 16, BIOME_DESERT_HILLS: 17, BIOME_WOODED_HILLS: 18, BIOME_FOREST_HILLS: 18,
		BIOME_TAIGA_HILLS: 19, BIOME_MOUNTAIN_EDGE: 20, BIOME_JUNGLE: 21, BIOME_JUNGLE_HILLS: 22,
		BIOME_JUNGLE_EDGE: 23, BIOME_DEEP_OCEAN: 24, BIOME_STONE_SHORE: 25, BIOME_SNOWY_BEACH: 26,
		BIOME_BIRCH_FOREST: 27, BIOME_BIRCH_FOREST_HILLS: 28, BIOME_DARK_FOREST: 29,
		BIOME_SNOWY_TAIGA: 30, BIOME_SNOWY_TAIGA_HILLS: 31, BIOME_GIANT_TREE_TAIGA: 32,
		BIOME_GIANT_TREE_TAIGA_HILLS: 33, BIOME_WOODED_MOUNTAINS: 34, BIOME_SAVANNA: 35,
		BIOME_SAVANNA_PLATEAU: 36, BIOME_BADLANDS: 37, BIOME_SWAMP_HILLS: 134,
		BIOME_SUNFLOWER_PLAINS: 129, BIOME_FLOWER_FOREST: 132, BIOME_TALL_BIRCH_FOREST: 155,
		BIOME_TALL_BIRCH_HILLS: 156, BIOME_DARK_FOREST_HILLS: 157, BIOME_GRAVELLY_MOUNTAINS: 131,
		BIOME_MODIFIED_JUNGLE: 149, BIOME_MODIFIED_JUNGLE_EDGE: 151, BIOME_COLD_OCEAN: 46,
		BIOME_DEEP_COLD_OCEAN: 49, BIOME_WARM_OCEAN: 44, BIOME_LUKEWARM_OCEAN: 45,
		BIOME_DEEP_LUKEWARM_OCEAN: 48, BIOME_SOUL_SAND_VALLEY: 170, BIOME_BASALT_DELTAS: 173,
		BIOME_WARPED_FOREST: 172, BIOME_TAIGA_MOUNTAINS: 133, BIOME_GIANT_SPRUCE_TAIGA: 160,
		BIOME_GIANT_SPRUCE_TAIGA_HILLS: 161, BIOME_MODIFIED_GRAVELLY_MOUNTAINS: 162
	};

	S.beginWorld = function (r, g, b) {
		if (!P) return 0;
		bump('beginWorld');
		P.counts._clear = [Math.round(r * 255), Math.round(g * 255), Math.round(b * 255)];
		captureMatrices();
		gl.bindFramebuffer(gl.FRAMEBUFFER, P.fbo);
		gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.TEXTURE_2D, P.depth, 0);
		bindColorAttachments(P, false);
		var list = [];
		for (var i = 0; i < 8; i++) list.push(gl.COLOR_ATTACHMENT0 + i);
		gl.drawBuffers(list);
		gl.viewport(0, 0, P.w, P.h);
		gl.depthMask(true);
		gl.clearColor(r, g, b, 1);
		gl.clearDepth(1);
		var rest = [];
		for (i = 1; i < 8; i++) rest.push(P.color[i].clear ? gl.COLOR_ATTACHMENT0 + i : gl.NONE);
		if (P.color[0].clear) {
			gl.drawBuffers([gl.COLOR_ATTACHMENT0]);
			gl.clearColor(r, g, b, 1);
			gl.clear(gl.COLOR_BUFFER_BIT);
		}
		if (rest.some(function (x) { return x !== gl.NONE; })) {
			gl.drawBuffers([gl.NONE].concat(rest));
			gl.clearColor(0, 0, 0, 0);
			gl.clear(gl.COLOR_BUFFER_BIT);
		}
		gl.drawBuffers([gl.COLOR_ATTACHMENT0]);
		gl.clear(gl.DEPTH_BUFFER_BIT);
		P.bound = true;
		P.curName = '';
		P.cur = null;
		mark('after clear');
		return 1;
	};
	S.pass = function (name) {
		if (!P) return 0;
		if (P.curName && P.curName !== name) mark('after ' + P.curName);
		P.curName = name;
		P.cur = P.progs[name] || null;
		var b = P.built.blend[name];
		if (b !== undefined) {
			if (!P.blendSaved) P.blendSaved = {
				on: gl.isEnabled(gl.BLEND),
				sc: gl.getParameter(gl.BLEND_SRC_RGB), dc: gl.getParameter(gl.BLEND_DST_RGB),
				sa: gl.getParameter(gl.BLEND_SRC_ALPHA), da: gl.getParameter(gl.BLEND_DST_ALPHA)
			};
			if (/^off$/i.test(b)) gl.disable(gl.BLEND);
			else {
				gl.enable(gl.BLEND);
				var f = b.split(/\s+/).map(blendFactor);
				if (f.length >= 4) gl.blendFuncSeparate(f[0], f[1], f[2], f[3]);
				else if (f.length >= 2) gl.blendFunc(f[0], f[1]);
			}
		} else restoreBlend();
		return P.cur ? 1 : 0;
	};
	function restoreBlend() {
		if (!P || !P.blendSaved) return;
		var s = P.blendSaved;
		P.blendSaved = null;
		if (s.on) gl.enable(gl.BLEND); else gl.disable(gl.BLEND);
		gl.blendFuncSeparate(s.sc, s.dc, s.sa, s.da);
	}
	function blendFactor(n) {
		var g = gl, T = {
			ZERO: g.ZERO, ONE: g.ONE, SRC_COLOR: g.SRC_COLOR, ONE_MINUS_SRC_COLOR: g.ONE_MINUS_SRC_COLOR,
			DST_COLOR: g.DST_COLOR, ONE_MINUS_DST_COLOR: g.ONE_MINUS_DST_COLOR,
			SRC_ALPHA: g.SRC_ALPHA, ONE_MINUS_SRC_ALPHA: g.ONE_MINUS_SRC_ALPHA,
			DST_ALPHA: g.DST_ALPHA, ONE_MINUS_DST_ALPHA: g.ONE_MINUS_DST_ALPHA,
			SRC_ALPHA_SATURATE: g.SRC_ALPHA_SATURATE
		};
		return T[String(n).toUpperCase()] !== undefined ? T[String(n).toUpperCase()] : g.ONE;
	}

	S.copyDepth = function (which) {
		if (!P) return 0;
		var dst = which === 2 ? P.depthtex2 : P.depthtex1;
		if (!dst) return 0;
		if (!P.depthCopyFbo) P.depthCopyFbo = gl.createFramebuffer();
		gl.bindFramebuffer(gl.DRAW_FRAMEBUFFER, P.depthCopyFbo);
		gl.framebufferTexture2D(gl.DRAW_FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.TEXTURE_2D, dst, 0);
		gl.bindFramebuffer(gl.READ_FRAMEBUFFER, P.fbo);
		gl.blitFramebuffer(0, 0, P.w, P.h, 0, 0, P.w, P.h, gl.DEPTH_BUFFER_BIT, gl.NEAREST);
		gl.bindFramebuffer(gl.FRAMEBUFFER, P.fbo);
		return 1;
	};

	S.shadowBegin = function () {
		if (!P || !P.shadow) return 0;
		captureMatrices();
		var Pg = P.progs.shadow;
		if (!Pg) return 0;
		gl.bindFramebuffer(gl.FRAMEBUFFER, P.shadow.fbo);
		gl.viewport(0, 0, P.shadow.res, P.shadow.res);
		gl.drawBuffers(P.shadow.color1 ? [gl.COLOR_ATTACHMENT0, gl.COLOR_ATTACHMENT1]
			: P.shadow.color0 ? [gl.COLOR_ATTACHMENT0] : [gl.NONE]);
		gl.depthMask(true);
		gl.clearColor(1, 1, 1, 1);
		gl.clearDepth(1);
		gl.clear(gl.DEPTH_BUFFER_BIT | (P.shadow.color0 ? gl.COLOR_BUFFER_BIT : 0));
		if (!P.shadow.color0) gl.colorMask(false, false, false, false);
		gl.disable(gl.BLEND);
		gl.enable(gl.DEPTH_TEST);
		gl.depthFunc(gl.LEQUAL);
		gl.disable(gl.CULL_FACE);
		P.inShadow = true;
		P.curName = 'shadow';
		P.cur = Pg;
		return 1;
	};

	S.shadowEnd = function () {
		if (!P) return 0;
		P.inShadow = false;
		gl.colorMask(true, true, true, true);
		gl.enable(gl.CULL_FACE);
		gl.bindFramebuffer(gl.FRAMEBUFFER, null);
		return 1;
	};

	S.endWorld = function () {
		if (!P) return 0;
		bump('endWorld');
		if (P.curName) mark('after ' + P.curName);
		mark('world done');
		restoreBlend();

		if (showBuffer === 8) {
			drawTextureToScreen(P.shadow ? P.shadow.depth : null, true);
			gl.enable(gl.DEPTH_TEST);
			gl.depthMask(true);
			gl.enable(gl.CULL_FACE);
			P.bound = false;
			if (traceFrames) traceFrames--;
			return 1;
		}

		if (showBuffer >= 0 && showBuffer < 8 && showBuffer === showRaw) {
			drawTextureToScreen(texOf(showBuffer));
			gl.enable(gl.DEPTH_TEST);
			gl.depthMask(true);
			gl.enable(gl.CULL_FACE);
			P.bound = false;
			if (traceFrames) traceFrames--;
			return 1;
		}
		P.screenPass = true;
		gl.bindVertexArray(P.quadVao);
		gl.disable(gl.DEPTH_TEST);
		gl.depthMask(false);
		gl.disable(gl.BLEND);
		gl.disable(gl.CULL_FACE);
		gl.disable(gl.SCISSOR_TEST);

		for (var i = 0; i < P.chain.length; i++) {
			var step = P.chain[i], Pg = step.Pg;
			gl.bindFramebuffer(gl.FRAMEBUFFER, P.fbo);
			attachOnly(P, step.targets);
			gl.drawBuffers(drawBufferList(step.targets));
			var vw = Math.max(1, Math.round(P.w * step.scale)), vh = Math.max(1, Math.round(P.h * step.scale));
			gl.viewport(0, 0, vw, vh);
			gl.useProgram(Pg.prog);
			if (traceFrames) {
				while (gl.getError()) { }
				gl.colorMask(true, true, true, true);
				gl.clearColor(1, 0, 1, 0.5);
				gl.clear(gl.COLOR_BUFFER_BIT);
				traceLog.push('  (' + Pg.name + ' target pre-filled magenta; mask ' +
					JSON.stringify(gl.getParameter(gl.COLOR_WRITEMASK)) + ')');
			}
			if (Pg.uFix) { gl.uniform4f(Pg.uFix, 0, 0, 0, 1); Pg.fix = 'quad'; }
			if (Pg.uAlpha && Pg.alpha !== 0) { Pg.alpha = 0; gl.uniform1f(Pg.uAlpha, 0); }
			setUniforms(Pg);
			bindTextures(Pg);
			gl.drawArrays(gl.TRIANGLE_FAN, 0, 4);
			noteErr('chain:' + Pg.name);
			unbindTextures(Pg);
			for (var k = 0; k < step.targets.length; k++) {
				var t = P.color[step.targets[k]];
				if (t.alt) t.flip = !t.flip;
				if (t.mipmap) { gl.bindTexture(gl.TEXTURE_2D, t.flip ? t.alt : t.tex); gl.generateMipmap(gl.TEXTURE_2D); gl.bindTexture(gl.TEXTURE_2D, null); }
			}
			if (traceFrames) traceLog.push('  (' + Pg.name + ' err ' + gl.getError() + ', viewport ' + vw + 'x' + vh +
				', samplers ' + Pg.samplers.map(function (sm) { return sm.name + '@' + sm.unit; }).join(',') + ')');
			if (traceFrames) traceLog.push('after ' + Pg.name + ' -> ' + step.targets.map(function (ti) {
				return ti + ':' + JSON.stringify(centrePixel(texOf(ti)));
			}).join(' '));
		}

		if (showBuffer >= 0 && showBuffer < 8) {
			drawTextureToScreen(texOf(showBuffer));
			P.screenPass = false;
			gl.bindVertexArray(null);
			gl.useProgram(null);
			if (typeof GLImmediate !== 'undefined') GLImmediate.fixedFunctionProgram = 0;
			if (traceFrames) traceFrames--;
			gl.enable(gl.DEPTH_TEST);
			gl.depthMask(true);
			gl.enable(gl.CULL_FACE);
			P.bound = false;
			return 1;
		}

		gl.bindFramebuffer(gl.FRAMEBUFFER, null);
		gl.viewport(0, 0, P.w, P.h);
		if (P.finalPg) {
			gl.useProgram(P.finalPg.prog);
			if (P.finalPg.uFix) { gl.uniform4f(P.finalPg.uFix, 0, 0, 0, 1); P.finalPg.fix = 'quad'; }
			if (P.finalPg.uAlpha && P.finalPg.alpha !== 0) { P.finalPg.alpha = 0; gl.uniform1f(P.finalPg.uAlpha, 0); }
			setUniforms(P.finalPg);
			bindTextures(P.finalPg);
			gl.drawArrays(gl.TRIANGLE_FAN, 0, 4);
			unbindTextures(P.finalPg);
		} else {
			drawTextureToScreen(texOf(0));
		}

		P.screenPass = false;
		gl.bindVertexArray(null);
		gl.useProgram(null);
		if (typeof GLImmediate !== 'undefined') GLImmediate.fixedFunctionProgram = 0;
		if (traceFrames) traceFrames--;
		gl.enable(gl.DEPTH_TEST);
		gl.depthMask(true);
		gl.enable(gl.CULL_FACE);
		P.bound = false;
		return 1;
	};

	S.terrain = function (recs, n, stride, progName) {
		if (!P) return 0;
		var Pg = P.progs[progName] || P.cur;
		if (!Pg) { bump('terrain:noprog'); return 0; }
		bump('terrain:' + progName + ':' + n);
		if (!P.counts._fbo) {
			var cur = gl.getParameter(gl.FRAMEBUFFER_BINDING);
			P.counts._fbo = (cur === P.fbo) ? 'gbuffer' : (cur === null ? 'DEFAULT(screen)' : 'other');
		}
		var drawn = 0;
		try {
			gl.useProgram(Pg.prog);
			if (typeof GLImmediate !== 'undefined') GLImmediate.fixedFunctionProgram = 0;
			setUniforms(Pg);
			bindTextures(Pg);
			if (!Pg.screen) setDrawBuffersFor(Pg);
			setAlpha(Pg, progName);
			var p = recs >> 2;
			P.vaos = P.vaos || [];
			var map = P.vaoMap || (P.vaoMap = new Map());
			for (var i = 0; i < n; i++, p += 5) {
				var vbo = HEAP32[p], count = HEAP32[p + 1];
				if (count <= 0) continue;
				var buf = GL.buffers[vbo];
				var vao = map.get(vbo);
				if (!vao || vao.mcBuffer !== buf) {
					if (vao) gl.deleteVertexArray(vao);
					vao = gl.createVertexArray();
					vao.mcBuffer = buf;
					gl.bindVertexArray(vao);
					gl.bindBuffer(gl.ARRAY_BUFFER, buf);
					setTerrainPointers(stride);
					map.set(vbo, vao);
					P.vaos.push(vao);
				} else gl.bindVertexArray(vao);
				if (Pg.uFix) gl.uniform4f(Pg.uFix, BIAS + HEAPF32[p + 2], BIAS + HEAPF32[p + 3], BIAS + HEAPF32[p + 4], 1 / 2048);
				if (stateDump && !Pg.screen && progName === 'gbuffers_terrain') {
					stateDump = false;
					S.lastState = {
						prog: progName, count: count, stride: stride,
						fbo: gl.getParameter(gl.FRAMEBUFFER_BINDING) === P.fbo ? 'gbuffer' : 'OTHER',
						bufLive: gl.isBuffer(buf), vaoBuf: vao.mcBuffer === buf,
						unit0: (function () { gl.activeTexture(gl.TEXTURE0); var tx = gl.getParameter(gl.TEXTURE_BINDING_2D); return tx ? 'texture2D bound' : 'NOTHING BOUND'; })(),
						fbStatus: '0x' + gl.checkFramebufferStatus(gl.FRAMEBUFFER).toString(16),
						colorMask: gl.getParameter(gl.COLOR_WRITEMASK),
						depthTest: gl.getParameter(gl.DEPTH_TEST), depthFunc: gl.getParameter(gl.DEPTH_FUNC),
						depthMask: gl.getParameter(gl.DEPTH_WRITEMASK),
						scissor: gl.getParameter(gl.SCISSOR_TEST), scissorBox: Array.from(gl.getParameter(gl.SCISSOR_BOX) || []),
						viewport: Array.from(gl.getParameter(gl.VIEWPORT) || []),
						cull: gl.getParameter(gl.CULL_FACE), cullFace: gl.getParameter(gl.CULL_FACE_MODE),
						frontFace: gl.getParameter(gl.FRONT_FACE),
						blend: gl.getParameter(gl.BLEND),
						draw0: gl.getParameter(gl.DRAW_BUFFER0), draw1: gl.getParameter(gl.DRAW_BUFFER1),
						att0: gl.COLOR_ATTACHMENT0, none: gl.NONE,
						alphaRef: Pg.alpha, fix: [BIAS + HEAPF32[p + 2], BIAS + HEAPF32[p + 3], BIAS + HEAPF32[p + 4]],
						errBefore: gl.getError()
					};
					gl.validateProgram(Pg.prog);
					S.lastState.valid = gl.getProgramParameter(Pg.prog, gl.VALIDATE_STATUS);
					S.lastState.validLog = (gl.getProgramInfoLog(Pg.prog) || '').slice(0, 400);
					S.lastState.linked = gl.getProgramParameter(Pg.prog, gl.LINK_STATUS);
					var na = gl.getProgramParameter(Pg.prog, gl.ACTIVE_ATTRIBUTES);
					S.lastState.attribs = [];
					for (var ai = 0; ai < na; ai++) {
						var inf = gl.getActiveAttrib(Pg.prog, ai);
						var loc = gl.getAttribLocation(Pg.prog, inf.name);
						var en = loc >= 0 && gl.getVertexAttrib(loc, gl.VERTEX_ATTRIB_ARRAY_ENABLED);
						var abuf = loc >= 0 ? gl.getVertexAttrib(loc, gl.VERTEX_ATTRIB_ARRAY_BUFFER_BINDING) : null;
						S.lastState.attribs.push(inf.name + '@' + loc + (en ? ' array' : ' const') +
							(en ? (abuf ? (gl.isBuffer(abuf) ? ' buf-ok' : ' BUF-DEAD') : ' NO-BUFFER') : '') +
							' type0x' + inf.type.toString(16));
					}
					var nu = gl.getProgramParameter(Pg.prog, gl.ACTIVE_UNIFORMS);
					S.lastState.samplerUnits = [];
					for (var ui = 0; ui < nu; ui++) {
						var ui2 = gl.getActiveUniform(Pg.prog, ui);
						if (!/sampler/i.test(String(ui2.type)) && [0x8B5E, 0x8B62, 0x8B5F, 0x8B60, 0x8DC1, 0x8DC4, 0x8DCA, 0x8DD2].indexOf(ui2.type) < 0) continue;
						S.lastState.samplerUnits.push(ui2.name + ' type0x' + ui2.type.toString(16) +
							' unit' + gl.getUniform(Pg.prog, gl.getUniformLocation(Pg.prog, ui2.name)));
					}
					gl.drawArrays(gl.TRIANGLES, 0, count);
					S.lastState.errAfter = gl.getError();
					S.lastState.pixelAfter = centrePixel(texOf(0));
					var ladder = [];
					var step = function (what, fn) {
						while (gl.getError()) { }
						try { fn(); } catch (e) { ladder.push(what + ': threw ' + e); return; }
						gl.drawArrays(gl.TRIANGLES, 0, count);
						ladder.push(what + ': ' + gl.getError());
					};
					step('[ATT0]', function () { gl.drawBuffers([gl.COLOR_ATTACHMENT0]); });
					step('[ATT0, NONE]', function () { gl.drawBuffers([gl.COLOR_ATTACHMENT0, gl.NONE]); });
					step('[NONE, ATT1]', function () { gl.drawBuffers([gl.NONE, gl.COLOR_ATTACHMENT1]); });
					step('[ATT0, ATT1] again', function () { gl.drawBuffers([gl.COLOR_ATTACHMENT0, gl.COLOR_ATTACHMENT1]); });
					S.lastState.attachments = [];
					for (var fi = 0; fi < 3; fi++) {
						try {
							var q = function (pn) { return gl.getFramebufferAttachmentParameter(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0 + fi, pn); };
							S.lastState.attachments.push(fi + ': r' + q(gl.FRAMEBUFFER_ATTACHMENT_RED_SIZE) +
								' g' + q(gl.FRAMEBUFFER_ATTACHMENT_GREEN_SIZE) + ' b' + q(gl.FRAMEBUFFER_ATTACHMENT_BLUE_SIZE) +
								' a' + q(gl.FRAMEBUFFER_ATTACHMENT_ALPHA_SIZE) +
								' type0x' + (q(gl.FRAMEBUFFER_ATTACHMENT_COMPONENT_TYPE) || 0).toString(16) +
								' fmt=' + (P.color[fi].format ? P.color[fi].format[0].toString(16) : '?'));
						} catch (e) { S.lastState.attachments.push(fi + ': ' + e); }
					}
					
					step('no textures anywhere', function () {
						for (var u2 = 0; u2 < 8; u2++) { gl.activeTexture(gl.TEXTURE0 + u2); gl.bindTexture(gl.TEXTURE_2D, null); }
						gl.activeTexture(gl.TEXTURE0);
					});
					step('default framebuffer', function () { gl.bindFramebuffer(gl.FRAMEBUFFER, null); });
					step('fresh vao, position only', function () {
						var v2 = gl.createVertexArray();
						gl.bindVertexArray(v2);
						gl.bindBuffer(gl.ARRAY_BUFFER, buf);
						gl.enableVertexAttribArray(0);
						gl.vertexAttribPointer(0, 3, gl.SHORT, false, stride, 0);
					});
					S.lastState.ladder = ladder;
					gl.bindFramebuffer(gl.FRAMEBUFFER, P.fbo);
					setDrawBuffersFor(Pg);
					gl.bindVertexArray(vao);
					drawn = i + 1;
					continue;
				}
				gl.drawArrays(gl.TRIANGLES, 0, count);
				noteErr('terrain:' + progName);
				drawn = i + 1;
			}
			Pg.fix = 'terrain';
			gl.bindVertexArray(null);
			unbindTextures(Pg);
			gl.useProgram(null);
			if (!Pg.screen) gl.drawBuffers([gl.COLOR_ATTACHMENT0]);
			if (typeof GLImmediate !== 'undefined') GLImmediate.fixedFunctionProgram = 0;
			if (typeof GLctx !== 'undefined') { gl.bindBuffer(gl.ARRAY_BUFFER, null); GLctx.currentArrayBufferBinding = 0; }
		} catch (e) {
			fail('terrain draw', e);
			return drawn;
		}
		return drawn;
	};

	function setTerrainPointers(stride) {
		gl.enableVertexAttribArray(0); gl.vertexAttribPointer(0, 3, gl.SHORT, false, stride, 0);
		gl.enableVertexAttribArray(3); gl.vertexAttribPointer(3, 2, gl.UNSIGNED_BYTE, false, stride, 6);
		gl.enableVertexAttribArray(1); gl.vertexAttribPointer(1, 2, gl.FLOAT, false, stride, 8);
		gl.enableVertexAttribArray(2); gl.vertexAttribPointer(2, 4, gl.UNSIGNED_BYTE, true, stride, 16);
		gl.enableVertexAttribArray(4); gl.vertexAttribPointer(4, 3, gl.BYTE, true, stride, 20);
		gl.enableVertexAttribArray(6); gl.vertexAttribPointer(6, 2, gl.UNSIGNED_SHORT, true, stride, 24);
		gl.enableVertexAttribArray(5); gl.vertexAttribPointer(5, 2, gl.UNSIGNED_SHORT, false, stride, 28);
	}

	var BIAS = 8.0;

	function setAlpha(Pg, progName) {
		if (!Pg.uAlpha) return;
		var ref = 0;
		var over = P.built.alphaTest[progName] || P.built.alphaTest[Pg.name];
		if (over !== undefined) {
			if (/^off$/i.test(over)) ref = 0;
			else { var m = /([A-Z_]+)\s+([0-9.]+)/i.exec(over); ref = m ? parseFloat(m[2]) : 0; }
		} else if (typeof GLEmulation !== 'undefined' && GLEmulation.alphaTestEnabled) {
			ref = GLEmulation.alphaTestRef || 0;
		}
		if (Pg.alpha !== ref) { Pg.alpha = ref; gl.uniform1f(Pg.uAlpha, ref); }
	}

	function drawBufferList(targets) {
		if (!targets || !targets.length) return [gl.COLOR_ATTACHMENT0];
		var max = 0;
		for (var i = 0; i < targets.length; i++) if (targets[i] > max) max = targets[i];
		var list = [];
		for (var a = 0; a <= max; a++) list.push(targets.indexOf(a) >= 0 ? (gl.COLOR_ATTACHMENT0 + a) : gl.NONE);
		return list;
	}
	function setDrawBuffersFor(Pg) {
		gl.drawBuffers(drawBufferList(Pg.drawBuffers));
	}

	S.ff = function (vbo, count, mode, stride, flags, lb, ls, nx, ny, nz) {
		if (!P || !P.cur || count <= 0) { if (P) bump('ff:nopass'); return 0; }
		var Pg = P.cur;
		bump('ff:' + P.curName);
		if (traceDraws) {
			traced[P.curName] = {
				flags: flags, light: [lb, ls], count: count,
				blend: gl.isEnabled(gl.BLEND), writes: Pg.drawBuffers || [0], prog: Pg.name
			};
		}
		try {
			gl.useProgram(Pg.prog);
			if (typeof GLImmediate !== 'undefined') GLImmediate.fixedFunctionProgram = 0;
			setUniforms(Pg);
			bindTextures(Pg);
			if (!Pg.screen) setDrawBuffersFor(Pg);
			setAlpha(Pg, P.curName);
			if (Pg.uFix && Pg.fix !== 'plain') { gl.uniform4f(Pg.uFix, 0, 0, 0, 1); Pg.fix = 'plain'; }
			var map = P.ffVaos || (P.ffVaos = new Map());
			var buf = GL.buffers[vbo];
			var key = vbo * 8 + (flags & 7);
			var vao = map.get(key);
			if (!vao || vao.mcBuffer !== buf) {
				if (vao) gl.deleteVertexArray(vao);
				vao = gl.createVertexArray();
				vao.mcBuffer = buf;
				gl.bindVertexArray(vao);
				gl.bindBuffer(gl.ARRAY_BUFFER, buf);
				gl.enableVertexAttribArray(0);
				gl.vertexAttribPointer(0, 3, gl.FLOAT, false, stride, 0);
				if (flags & 1) { gl.enableVertexAttribArray(1); gl.vertexAttribPointer(1, 2, gl.FLOAT, false, stride, 12); }
				if (flags & 2) { gl.enableVertexAttribArray(2); gl.vertexAttribPointer(2, 4, gl.UNSIGNED_BYTE, true, stride, 20); }
				if (flags & 4) { gl.enableVertexAttribArray(4); gl.vertexAttribPointer(4, 3, gl.BYTE, true, stride, 20); }
				map.set(key, vao);
				(P.vaos = P.vaos || []).push(vao);
			} else gl.bindVertexArray(vao);
			if (!(flags & 1)) gl.vertexAttrib4f(1, 0, 0, 0, 1);
			if (!(flags & 2)) gl.vertexAttrib4f(2, 1, 1, 1, 1);
			if (!(flags & 4)) gl.vertexAttrib4f(4, nx, ny, nz, 0);
			gl.vertexAttrib4f(3, lb, ls, 0, 1);
			gl.vertexAttrib4f(5, -1, 0, 0, 1);
			gl.vertexAttrib4f(6, 0.5, 0.5, 0, 1);
			gl.vertexAttrib4f(7, 1, 0, 0, 1);
			gl.drawArrays(mode, 0, count);
			noteErr('ff:' + P.curName + '(' + Pg.name + ')');
			gl.bindVertexArray(null);
			unbindTextures(Pg);
			gl.useProgram(null);
			if (!Pg.screen) gl.drawBuffers([gl.COLOR_ATTACHMENT0]);
			if (typeof GLImmediate !== 'undefined') GLImmediate.fixedFunctionProgram = 0;
			gl.bindBuffer(gl.ARRAY_BUFFER, null);
			if (typeof GLctx !== 'undefined') GLctx.currentArrayBufferBinding = 0;
			return 1;
		} catch (e) {
			fail('shader draw', e);
			return 0;
		}
	};

	S.setEntity = function (r, g, b, a, entityId, blockEntityId) {
		if (!P) return 0;
		P.custom.entityColor = new Float32Array([r, g, b, a]);
		P.custom.entityId = entityId | 0;
		P.custom.blockEntityId = blockEntityId | 0;
		var seen = [];
		for (var n in P.progs) {
			var Pg = P.progs[n];
			if (seen.indexOf(Pg) >= 0) continue;
			seen.push(Pg);
			delete Pg.cache.entityColor; delete Pg.cache.entityId; delete Pg.cache.blockEntityId;
		}
		return 1;
	};

	function bump(k) { if (!P.counts) P.counts = {}; P.counts[k] = (P.counts[k] || 0) + 1; }

	function fail(what, e) {
		console.warn('shader pack turned off after a problem in the ' + what + ':', e);
		try { gl.bindVertexArray(null); gl.useProgram(null); gl.bindFramebuffer(gl.FRAMEBUFFER, null); } catch (e2) { }
		if (typeof GLImmediate !== 'undefined') GLImmediate.fixedFunctionProgram = 0;
		S.stop();
		if (window.Module && Module.mcShaderFailed) Module.mcShaderFailed(String(e && e.message || e));
	}

	S.glReady = true;
})();
