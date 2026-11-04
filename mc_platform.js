// Minecraft Web - Platform JS Library
// Handles world creation modal dialog and save syncing

mergeInto(LibraryManager.library, {
    mcShowCreateWorldDialog: function () {
        // Create modal overlay
        var overlay = document.createElement('div');
        overlay.id = 'mc-create-world';
        overlay.style.cssText = 'position:fixed;top:0;left:0;width:100%;height:100%;' +
            'background:rgba(0,0,0,0.5);display:flex;align-items:center;' +
            'justify-content:center;z-index:9999;font-family:monospace';

        var box = document.createElement('div');
        box.style.cssText = 'background:#3c3c3c;border:2px solid #888;padding:28px;' +
            'min-width:320px;color:#eee;text-align:center';

        box.innerHTML =
            '<h2 style="margin:0 0 18px;color:#fff;font-size:20px;letter-spacing:1px">Create New World</h2>' +
            '<div style="text-align:left;margin-bottom:14px">' +
            '<label style="font-size:13px;color:#aaa">World Name</label><br>' +
            '<input id="mc-worldname" type="text" value="My World" ' +
            'style="width:100%;box-sizing:border-box;padding:8px;margin-top:5px;' +
            'background:#222;color:#fff;border:1px solid #666;font-size:14px;font-family:monospace">' +
            '</div>' +
            '<div style="text-align:left;margin-bottom:20px">' +
            '<label style="font-size:13px;color:#aaa">Game Mode</label><br>' +
            '<select id="mc-gamemode" style="width:100%;box-sizing:border-box;padding:8px;' +
            'margin-top:5px;background:#222;color:#fff;border:1px solid #666;font-size:14px;font-family:monospace">' +
            '<option value="creative">Creative</option>' +
            '<option value="survival">Survival</option>' +
            '</select>' +
            '</div>' +
            '<div style="display:flex;gap:10px;justify-content:center">' +
            '<button id="mc-create-btn" style="padding:10px 24px;background:#4a8a4a;color:#fff;' +
            'border:none;cursor:pointer;font-size:15px;font-family:monospace;letter-spacing:1px">Create</button>' +
            '<button id="mc-cancel-btn" style="padding:10px 24px;background:#555;color:#fff;' +
            'border:none;cursor:pointer;font-size:15px;font-family:monospace;letter-spacing:1px">Cancel</button>' +
            '</div>';

        overlay.appendChild(box);
        document.body.appendChild(overlay);

        // Focus the name field
        setTimeout(function () {
            var input = document.getElementById('mc-worldname');
            if (input) { input.focus(); input.select(); }
        }, 50);

        // Reset state
        window._mcWorldStatus = -1;
        window._mcWorldResult = null;

        document.getElementById('mc-create-btn').onclick = function () {
            var nm = (document.getElementById('mc-worldname').value || 'My World').trim();
            var mode = document.getElementById('mc-gamemode').value;
            window._mcWorldStatus = 1;
            window._mcWorldResult = nm + '|' + mode;
            document.body.removeChild(overlay);
        };

        document.getElementById('mc-cancel-btn').onclick = function () {
            window._mcWorldStatus = 0;
            window._mcWorldResult = null;
            document.body.removeChild(overlay);
        };

        // Handle Enter key in name field
        document.getElementById('mc-worldname').onkeydown = function (e) {
            if (e.key === 'Enter') document.getElementById('mc-create-btn').click();
            if (e.key === 'Escape') document.getElementById('mc-cancel-btn').click();
        };
    },

    mcGetWorldStatus: function () {
        if (window._mcWorldStatus === undefined) return -1;
        return window._mcWorldStatus;
    },

    mcGetWorldResult: function () {
        var r = window._mcWorldResult;
        if (!r) return 0;
        window._mcWorldResult = null;
        window._mcWorldStatus = -1;
        var len = lengthBytesUTF8(r) + 1;
        var buf = _malloc(len);
        stringToUTF8(r, buf, len);
        return buf;
    },

    // Web build 2026-11-03: centroid interpolation - the cure for the thin lines antialiasing drew
    // through text, grass and everything else textured out of an atlas. Called from C++ through
    // client/renderer/Centroid.h; it lives here rather than in an EM_JS block because the rewrite
    // below needs regular expressions, and the C preprocessor mangles those.
    //
    // THE BUG, as a player meets it: with Antialiasing on, letters grow hairlines along their edges
    // and pick up scraps of their neighbours in the font sheet; distant grass and leaves get
    // coloured seams. Antialiasing off and it is all gone.
    //
    // WHY. Multisampling tests coverage at several points inside a pixel but runs the fragment
    // shader ONCE, with every varying evaluated at the pixel's CENTRE. At the edge of a triangle a
    // pixel can have samples covered while its centre lies just outside the triangle - and then the
    // texture coordinate handed to the shader is extrapolated past the triangle's edge. Every
    // texture here comes from an atlas (terrain.png is a 16 x 16 grid of tiles, the font a 16 x 16
    // grid of glyphs) and each quad's coordinates stop exactly on its cell's border, so a hair past
    // that border is the NEXT cell: the edge pixel gets painted with the neighbouring glyph, or the
    // neighbouring block's tile. One pixel wide, following every silhouette - a line.
    //
    // How far it reaches is how far one pixel is in texels, so it is worst where a texel is small on
    // screen (distant terrain) and on text, whose quads sit exactly on the glyph boundary. It shows
    // only where a primitive edge falls part-way across a pixel, which is why the menus are clean at
    // some window sizes and not at others: the GUI maps height / guiScale units onto height pixels,
    // a whole number of pixels per unit only for some window heights. That is also why it looks
    // random, and why it was never a texture-filtering or mipmap problem.
    //
    // THE FIX is one word in the shaders. `centroid` evaluates the varying at the centroid of the
    // covered samples, which is by definition inside the primitive, so the texture coordinate can
    // never leave the quad's own cell. Nothing else changes: every interior pixel - all of them bar
    // a one-pixel rim - is sampled exactly where it was.
    //
    // DOING IT TO SHADERS WE DO NOT WRITE. Everything except the terrain is drawn through
    // Emscripten's fixed-function emulation, which generates its own GLSL at run time, and
    // `centroid` is GLSL ES 3.00 - WebGL 2 - while those generated shaders are ES 1.00. So this
    // wraps compileShader and rewrites them: `attribute` -> `in`, `varying` -> `centroid out` /
    // `centroid in`, gl_FragColor -> a declared output, texture2D -> texture. A mechanical rewrite,
    // which is only safe because the input is machine generated and always has the same shape - so
    // it is applied ONLY to that emulation's own shaders, recognised by the attribute names it
    // always uses. A shader a mod compiles for itself is left exactly as the mod wrote it.
    //
    // AND IT UNDOES ITSELF. Each shader keeps its original ES 1.00 text; if the rewritten one will
    // not compile, the original goes back and compiles instead. A program may not mix ES 1.00 and
    // ES 3.00 shaders, so if one half of a pair was refused the link fails - linkProgram puts BOTH
    // halves back and links again. The worst case is therefore the picture we had before this
    // existed, never a black screen.
    //
    // Installed only when the running context is actually antialiased: with the setting off there is
    // no extrapolation to cure (a fragment is shaded only when its centre is covered), so the game
    // runs the untouched ES 1.00 shaders exactly as it always did. Needs the JS unminified (no
    // --closure), like the other patches of the emulation.
    mcCentroidInstallJS: function () {
        // (the object is only replaced when the answer changes: this is called once a frame, and a
        // fresh object 60 times a second is 60 pieces of garbage a second for nothing)
        var S = function (st) {
            if (!Module.mcCentroid || Module.mcCentroid.state !== st) Module.mcCentroid = { state: st };
            return st === 'on' ? 1 : 0;
        };
        try {
            if (typeof GLctx === 'undefined' || !GLctx) return S('nocontext');
            if (GLctx.mcCentroidPatched) return S('on');
            try { if (window.mcNoCentroid || localStorage.getItem('mcre.nocentroid') === '1') return S('off'); } catch (e) { }
            // WebGL 2 only: GLSL ES 3.00 is where `centroid` lives. It has to be a real instanceof
            // test - Emscripten hangs WebGL 2 METHOD NAMES off a WebGL 1 context when the matching
            // extension is there (createVertexArray from OES_vertex_array_object, which is how this
            // first reported itself installed on WebGL 1 and then had every shader refused).
            var is2 = (typeof WebGL2RenderingContext !== 'undefined' && GLctx instanceof WebGL2RenderingContext);
            if (!is2) { try { is2 = /WebGL 2/.test(GLctx.getParameter(GLctx.VERSION)); } catch (e) { } }
            if (!is2) return S('nowebgl2');
            var at = GLctx.getContextAttributes ? GLctx.getContextAttributes() : null;
            if (!at || !at.antialias) return S('noaa');

            // The raw entry points, captured now: the rewrite must set the final text without going
            // through anybody else's shaderSource wrapper a second time (EntityLighting.cpp installs
            // one of its own, possibly later than this).
            var rawSource = GLctx.shaderSource.bind(GLctx);
            var rawCompile = GLctx.compileShader.bind(GLctx);
            var rawLink = GLctx.linkProgram.bind(GLctx);

            // Is this one of the emulation's generated fixed-function shaders? It always names its
            // attributes and varyings the same way. gl_FragData would need more than this rewrite,
            // so a shader using it is left alone.
            var mine = function (src) {
                return src.indexOf('#version') < 0
                    && (src.indexOf('a_position') >= 0 || src.indexOf('v_color') >= 0)
                    && src.indexOf('gl_FragData') < 0;
            };

            var toES300 = function (src, isVertex) {
                var s = src;
                if (isVertex) {
                    s = s.replace(/^[ \t]*attribute[ \t]+/gm, 'in ');
                    s = s.replace(/^[ \t]*varying[ \t]+/gm, 'centroid out ');
                } else {
                    s = s.replace(/^[ \t]*varying[ \t]+/gm, 'centroid in ');
                }
                // (split/join, not a regex: the longer names first so texture2D( does not eat them)
                s = s.split('texture2DProj(').join('textureProj(');
                s = s.split('texture2DLod(').join('textureLod(');
                s = s.split('textureCube(').join('texture(');
                s = s.split('texture2D(').join('texture(');
                if (!isVertex && s.indexOf('gl_FragColor') >= 0) {
                    s = s.split('gl_FragColor').join('mc_FragColor');
                    // The output must be declared AFTER the default float precision: an ES 3.00
                    // fragment shader starts with none, so `out vec4` above the precision line is
                    // "No precision specified for (float)" - which is how the first attempt at this
                    // fell back on every single shader while reporting itself as installed.
                    var m = /^[ \t]*precision[ \t][^;]*;[ \t]*$/m.exec(s);
                    if (m) s = s.slice(0, m.index + m[0].length) + '\nout vec4 mc_FragColor;' + s.slice(m.index + m[0].length);
                    else s = 'precision mediump float;\nout vec4 mc_FragColor;\n' + s;
                }
                // `attribute` and `varying` are reserved words in ES 3.00: if one survived the
                // rewrite the shader cannot compile, so do not even offer it.
                if (/\battribute\b|\bvarying\b/.test(s)) return null;
                return '#version 300 es\n' + s;
            };

            GLctx.compileShader = function (sh) {
                try {
                    if (sh && !sh.mcOrig) {
                        var src = GLctx.getShaderSource(sh);
                        if (src && mine(src)) {
                            var isVertex = GLctx.getShaderParameter(sh, GLctx.SHADER_TYPE) === GLctx.VERTEX_SHADER;
                            var out = toES300(src, isVertex);
                            if (out) {
                                sh.mcOrig = src;
                                rawSource(sh, out);
                                rawCompile(sh);
                                if (GLctx.getShaderParameter(sh, GLctx.COMPILE_STATUS)) return;
                                // Refused: put the shader back exactly as the emulation wrote it,
                                // and keep the reason. Without it a silent fall-back looks from the
                                // outside exactly like the fix working.
                                Module.mcCentroidFellBack = (Module.mcCentroidFellBack || 0) + 1;
                                Module.mcCentroidWhy = GLctx.getShaderInfoLog(sh);
                                sh.mcOrig = null;
                                rawSource(sh, src);
                            }
                        }
                    }
                } catch (e) {
                    if (!Module.mcCentroidError) { Module.mcCentroidError = true; console.warn('centroid rewrite off:', e); }
                }
                return rawCompile(sh);
            };

            GLctx.linkProgram = function (prog) {
                rawLink(prog);
                try {
                    if (GLctx.getProgramParameter(prog, GLctx.LINK_STATUS)) return;
                    var shaders = GLctx.getAttachedShaders(prog) || [];
                    var undone = false;
                    for (var i = 0; i < shaders.length; i++) {
                        var sh = shaders[i];
                        if (sh && sh.mcOrig) { rawSource(sh, sh.mcOrig); sh.mcOrig = null; rawCompile(sh); undone = true; }
                    }
                    if (undone) {
                        Module.mcCentroidFellBack = (Module.mcCentroidFellBack || 0) + 1;
                        rawLink(prog);
                    }
                } catch (e) {
                    if (!Module.mcCentroidError) { Module.mcCentroidError = true; console.warn('centroid link fallback:', e); }
                }
            };

            GLctx.mcCentroidPatched = true;
            return S('on');
        } catch (e) {
            console.warn('centroid install failed:', e);
            return S('failed');
        }
    },

    // Web build 2026-11-03: the fast path for everything that is NOT terrain - the GUI, text, item
    // icons, entities, particles, the sky, the hand. Called from gles.cpp, Tesselator::draw and
    // EntityLighting::drawMesh through client/renderer/FastDraw.h. The terrain has had one of these
    // since 2026-10-31 (RenderList.cpp); this is the same idea applied to the rest.
    //
    // WHY. Under -sLEGACY_GL_EMULATION every glDrawArrays runs Emscripten's fixed-function
    // emulation in JS: it looks up a renderer from the current state, binds its program, uploads
    // both matrices, the fog, the alpha-test reference and the texture-environment uniforms,
    // re-points every client attribute and - with GL_UNSAFE_OPTS=0 - disables them all again
    // afterwards. Counted in a real frame flying over a world: about 16 WebGL calls for each of
    // ~100 such draws, which is 1700 of the frame's 2500 calls. Each one is a JS -> browser ->
    // driver crossing: cheap on a desktop, most of the frame on a phone.
    //
    // WHAT IT DOES INSTEAD. One program per state combination, generated here exactly as the
    // emulation would have (its own fog formulas, its alpha-test comparisons, modulate texturing,
    // and the entity lighting EntityLighting.cpp adds), built lazily - a world in flight uses six.
    // Per draw: bind the program, bind a vertex array object for that buffer (so the attribute
    // pointers are set once per buffer instead of once per draw), draw, let go. Uniforms are
    // remembered and re-sent only when they change, so a run of GUI quads sends none at all.
    //
    // WHAT IT REFUSES. This is a fast path, not a second renderer: if a mod has its own program
    // bound, if GL_LIGHTING or a clip plane is on, if the emulation's internals are not where it
    // expects, or if anything throws, it returns 0 and the caller draws through the emulation
    // exactly as before. Module.mcNoFastDraw = 1 turns it off outright.
    //
    // WHAT IT LEAVES BEHIND, which matters as much as what it draws: no program bound and
    // GLImmediate.fixedFunctionProgram 0 (so the next emulated draw binds its own), the default
    // vertex array object bound (otherwise the emulation's next vertexAttribPointer would quietly
    // edit OURS), and the emulation's array-buffer binding back where it was. Exactly what
    // RenderList.cpp restores, and for the same reasons.
    //
    // The vertex layout is the one the whole game uses for these draws (VertecDecl.h): position at
    // 0, texture coordinates at 12, colour bytes at 20 - and in a lit mesh those same bytes hold
    // the baked normal instead (Tesselator::bakeNormals).
    //
    // Needs the JS unminified (no --closure), like the other fast paths.
    mcFfDraw: function (vbo, count, mode, stride, flags) {
        if (count <= 0) return 1;
        var F = Module.mcFF;
        try {
            var gl = GLctx;
            if (!gl || Module.mcNoFastDraw) return 0;
            if (typeof GLImmediate === 'undefined' || typeof GLEmulation === 'undefined') return 0;
            if (!GLImmediate.matrix || !GLImmediate.clientColor || !GLEmulation.fogColor) return 0;
            if (GL.currProgram) return 0;                      // a mod's own program is bound
            if (GLEmulation.lightingEnabled) return 0;          // GL_LIGHTING: leave it to the emulation
            if (typeof gl.createVertexArray !== 'function') return 0;
            if (!F || F.ctx !== gl) F = Module.mcFF = { ctx: gl, progs: {}, vaos: new Map(), broken: false };
            if (F.broken) return 0;

            var tex = (flags & 1) !== 0, col = (flags & 2) !== 0, lit = (flags & 4) !== 0;
            if (lit && (!Module.mcLitL || Module.mcLitCap === undefined)) return 0;

            // Whether a draw is TEXTURED is not the caller's to say. The flag above only says
            // "this buffer carries texture coordinates"; what decides whether the emulation
            // SAMPLES is glEnable/glDisable(GL_TEXTURE_2D) - which is NOT the no-op it looks
            // like. GLEmulation's own glEnable does return early for GL_TEXTURE_2D, but
            // GLImmediate.init wraps glEnable a SECOND time, and that outer wrapper calls
            // TexEnvJIT.hook_enable first. With the unit disabled, TexEnvJIT generates a
            // fragment shader with no texture2D in it at all - just the colour.
            //
            // Getting this wrong is what darkened the sky while flying (user: "fly flickers",
            // 2026-11-04). LevelRenderer::renderSky turns texturing OFF and then draws the sky
            // dome through drawArrayVT - texture coordinates present, texturing off - so this
            // path sampled whatever texture happened to still be bound and multiplied the sky
            // colour by it. Which texture that was depended on what had been drawn last, so the
            // sky changed shade as the view swung around: the flicker.
            var TJ = GLImmediate.TexEnvJIT;
            if (!TJ || typeof TJ.getTexUnitType !== 'function') return 0;
            if (typeof TJ.getActiveTexture === 'function' && TJ.getActiveTexture() !== 0) return 0;
            var t0 = TJ.getTexUnitType(0);
            if (t0 !== 0 && t0 !== 0xDE1) return 0;          // 1D / 3D / cube: leave it to the emulation
            var mt = GLImmediate.MAX_TEXTURES || 1;
            for (var ti = 1; ti < mt; ti++) if (TJ.getTexUnitType(ti)) return 0;   // multitexture
            var texOn = t0 === 0xDE1;
            // Texturing on with no texture coordinates in the buffer: the emulation would sample at
            // the generic a_texCoord0 value. Rare, and not worth reproducing - hand it back.
            if (texOn && !tex) return 0;
            tex = texOn;
            // From here on `flags` must not be used for what is drawn: one buffer that carries
            // texture coordinates needs a different program AND a different vertex array object
            // depending on whether this draw is textured.
            var eflags = (tex ? 1 : 0) | (col ? 2 : 0) | (lit ? 4 : 0);
            var cp = GLEmulation.clipPlaneEnabled;
            if (cp) for (var ci = 0; ci < cp.length; ci++) if (cp[ci]) return 0;

            if (!F.same) {
                // "has this uniform changed since this program last had it?" - and it copies while
                // it compares, so a changed value is remembered in the same pass. Sixteen float
                // comparisons in JS cost a small fraction of the WebGL call they save.
                F.same = function (a, b, n) {
                    for (var i = 0; i < n; i++) if (a[i] !== b[i]) { for (var j = 0; j < n; j++) a[j] = b[j]; return false; }
                    return true;
                };
            }
            if (!F.build) {
                // Built once. The shader is the emulation's own fixed-function program written out
                // by hand for this one state: nothing is added and nothing is left out, so a draw
                // that goes through here paints the same pixels it did through the emulation.
                // `centroid` is used wherever Centroid.cpp says it can be (WebGL 2 + antialiasing
                // on), for the same reason the terrain shader uses it: without it multisampling
                // extrapolates the texture coordinate past the edge of the atlas cell and draws the
                // neighbouring glyph or tile as a hairline.
                F.build = function (gl, tex, col, lit, fogMode, at) {
                    var c = !!(Module.mcCentroid && Module.mcCentroid.state === 'on');
                    var IN = c ? 'in' : 'attribute', OUT = c ? 'centroid out' : 'varying';
                    var FIN = c ? 'centroid in' : 'varying', TX = c ? 'texture' : 'texture2D';
                    var FC = c ? 'mc_FragColor' : 'gl_FragColor';
                    var fog = null;
                    if (fogMode === 0x801) fog = '  float fog = exp(-u_fogDensity * u_fogDensity * v_fog * v_fog);';
                    else if (fogMode === 0x2601) fog = '  float fog = (u_fogEnd - v_fog) * u_fogScale;';
                    else if (fogMode !== 0) fog = '  float fog = exp(-u_fogDensity * v_fog);';
                    var test = '';
                    switch (at) {
                        case 0x200: test = '  discard;'; break;
                        case 0x201: test = '  if (!(' + FC + '.a < u_alphaRef)) discard;'; break;
                        case 0x202: test = '  if (!(' + FC + '.a == u_alphaRef)) discard;'; break;
                        case 0x203: test = '  if (!(' + FC + '.a <= u_alphaRef)) discard;'; break;
                        case 0x204: test = '  if (!(' + FC + '.a > u_alphaRef)) discard;'; break;
                        case 0x205: test = '  if (!(' + FC + '.a != u_alphaRef)) discard;'; break;
                        case 0x206: test = '  if (!(' + FC + '.a >= u_alphaRef)) discard;'; break;
                        default: test = ''; break;
                    }
                    // Java's entity shading, the same few lines EntityLighting.cpp adds to the
                    // emulation's shader - and it must stay the same, or a mob lit here would not
                    // match one lit there when this path refuses a draw.
                    var litPass = lit ? [
                        '  {',
                        '    vec3 mcN = (u_mv * vec4(a_normal, 0.0)).xyz;',
                        '    float mcL = dot(mcN, mcN);',
                        '    mcN = mcL > 1.0e-8 ? mcN * inversesqrt(mcL) : vec3(0.0);',
                        '    float mcS = 0.4 + 0.6 * max(dot(mcN, u_mcL0), 0.0) + 0.6 * max(dot(mcN, u_mcL1), 0.0);',
                        '    vec3 mcC = clamp(v_color.xyz * mcS, 0.0, 1.0);',
                        '    float mcCap = max(u_mcCap, max(v_color.x, max(v_color.y, v_color.z)));',
                        '    v_color.xyz = min(mcC, vec3(mcCap));',
                        '  }'].join('\n') : '';
                    var vs = [
                        c ? '#version 300 es' : '',
                        IN + ' vec3 a_pos;',
                        tex ? IN + ' vec2 a_uv;' : '',
                        col ? IN + ' vec4 a_color;' : '',
                        lit ? IN + ' vec3 a_normal;' : '',
                        'uniform mat4 u_mv;',
                        'uniform mat4 u_proj;',
                        col ? '' : 'uniform vec4 u_color;',
                        lit ? 'uniform vec3 u_mcL0; uniform vec3 u_mcL1; uniform float u_mcCap;' : '',
                        tex ? OUT + ' vec2 v_uv;' : '',
                        OUT + ' vec4 v_color;',
                        fog ? OUT + ' float v_fog;' : '',
                        'void main() {',
                        '  vec4 ec = u_mv * vec4(a_pos, 1.0);',
                        '  gl_Position = u_proj * ec;',
                        tex ? '  v_uv = a_uv;' : '',
                        '  v_color = ' + (col ? 'a_color' : 'u_color') + ';',
                        litPass,
                        // The fog distance is the RADIAL distance from the eye, not the eye-space depth:
                        // build.py rewrites the emulation's own `v_fogFragCoord = abs(ecPosition.z)` into
                        // `length(ecPosition.xyz)` after the link, so fog is a sphere round the player and
                        // does not thin out at the edges of a wide field of view. This line has to match
                        // that patch, not Emscripten's original.
                        fog ? '  v_fog = length(ec.xyz);' : '',
                        '}'].join('\n');
                    var fs = [
                        c ? '#version 300 es' : '',
                        'precision mediump float;',
                        c ? 'out vec4 mc_FragColor;' : '',
                        tex ? 'uniform sampler2D u_tex;' : '',
                        tex ? FIN + ' vec2 v_uv;' : '',
                        FIN + ' vec4 v_color;',
                        fog ? FIN + ' float v_fog; uniform vec4 u_fogColor; uniform float u_fogEnd; uniform float u_fogScale; uniform float u_fogDensity;' : '',
                        test ? 'uniform float u_alphaRef;' : '',
                        'void main() {',
                        '  vec4 c = v_color' + (tex ? ' * ' + TX + '(u_tex, v_uv)' : '') + ';',
                        fog ? fog + ' fog = clamp(fog, 0.0, 1.0); c.rgb = mix(u_fogColor.rgb, c.rgb, fog);' : '',
                        '  ' + FC + ' = c;',
                        test,
                        '}'].join('\n');
                    var mk = function (type, src) {
                        var sh = gl.createShader(type);
                        gl.shaderSource(sh, src);
                        gl.compileShader(sh);
                        if (!gl.getShaderParameter(sh, gl.COMPILE_STATUS)) { console.warn('fast draw shader:', gl.getShaderInfoLog(sh), src); gl.deleteShader(sh); return null; }
                        return sh;
                    };
                    var v = mk(gl.VERTEX_SHADER, vs), f = mk(gl.FRAGMENT_SHADER, fs);
                    if (!v || !f) return null;
                    var prog = gl.createProgram();
                    gl.attachShader(prog, v);
                    gl.attachShader(prog, f);
                    gl.bindAttribLocation(prog, 0, 'a_pos');
                    gl.bindAttribLocation(prog, 1, 'a_uv');
                    gl.bindAttribLocation(prog, 2, 'a_color');
                    gl.bindAttribLocation(prog, 3, 'a_normal');
                    gl.linkProgram(prog);
                    gl.deleteShader(v); gl.deleteShader(f);
                    if (!gl.getProgramParameter(prog, gl.LINK_STATUS)) { console.warn('fast draw program:', gl.getProgramInfoLog(prog)); return null; }
                    var P = {
                        prog: prog, fog: !!fog, at: !!test,
                        uMv: gl.getUniformLocation(prog, 'u_mv'), uProj: gl.getUniformLocation(prog, 'u_proj'),
                        uColor: col ? null : gl.getUniformLocation(prog, 'u_color'),
                        uFogColor: gl.getUniformLocation(prog, 'u_fogColor'), uFogEnd: gl.getUniformLocation(prog, 'u_fogEnd'),
                        uFogScale: gl.getUniformLocation(prog, 'u_fogScale'), uFogDensity: gl.getUniformLocation(prog, 'u_fogDensity'),
                        uAlphaRef: gl.getUniformLocation(prog, 'u_alphaRef'),
                        uL0: gl.getUniformLocation(prog, 'u_mcL0'), uL1: gl.getUniformLocation(prog, 'u_mcL1'),
                        uCap: gl.getUniformLocation(prog, 'u_mcCap'),
                        // what each uniform was last given: NaN so the first draw always sends it
                        mv: new Float32Array(16).fill(NaN), proj: new Float32Array(16).fill(NaN),
                        col: new Float32Array(4).fill(NaN), fogCol: new Float32Array(4).fill(NaN),
                        fogEnd: NaN, fogScale: NaN, fogDensity: NaN, alphaRef: NaN, litV: -1, cap: NaN,
                    };
                    gl.useProgram(prog);
                    if (tex) gl.uniform1i(gl.getUniformLocation(prog, 'u_tex'), 0);
                    gl.useProgram(null);
                    return P;
                };
            }

            var fogMode = GLEmulation.fogEnabled ? (GLEmulation.fogMode | 0) : 0;
            var at = GLEmulation.alphaTestEnabled ? (GLEmulation.alphaTestFunc | 0) : 0x207;
            var key = (tex ? 't' : '') + (col ? 'c' : '') + (lit ? 'l' : '') + fogMode + '/' + at;
            var P = F.progs[key];
            if (P === undefined) {
                P = F.progs[key] = F.build(gl, tex, col, lit, fogMode, at);
                if (!P) { F.broken = true; return 0; }
            }
            if (!P) return 0;

            var buf = GL.buffers[vbo];
            if (!buf) return 0;

            gl.useProgram(P.prog);

            // --- the uniforms that changed since this program last ran -------------------------
            var same = F.same;
            var m = GLImmediate.matrix[0];
            if (!same(P.mv, m, 16)) gl.uniformMatrix4fv(P.uMv, false, m);
            m = GLImmediate.matrix[1];
            if (!same(P.proj, m, 16)) gl.uniformMatrix4fv(P.uProj, false, m);
            if (!col) {
                m = GLImmediate.clientColor;
                if (!same(P.col, m, 4)) gl.uniform4fv(P.uColor, m);
            }
            if (P.fog) {
                m = GLEmulation.fogColor;
                if (!same(P.fogCol, m, 4)) gl.uniform4fv(P.uFogColor, m);
                var fe = GLEmulation.fogEnd, fsc = 1 / (GLEmulation.fogEnd - GLEmulation.fogStart), fd = GLEmulation.fogDensity;
                if (P.fogEnd !== fe) { P.fogEnd = fe; gl.uniform1f(P.uFogEnd, fe); }
                if (P.fogScale !== fsc) { P.fogScale = fsc; gl.uniform1f(P.uFogScale, fsc); }
                if (P.fogDensity !== fd) { P.fogDensity = fd; gl.uniform1f(P.uFogDensity, fd); }
            }
            if (P.at) {
                var ar = GLEmulation.alphaTestRef;
                if (P.alphaRef !== ar) { P.alphaRef = ar; gl.uniform1f(P.uAlphaRef, ar); }
            }
            if (lit) {
                if (P.litV !== Module.mcLitV) {
                    P.litV = Module.mcLitV;
                    var L = Module.mcLitL;
                    gl.uniform3f(P.uL0, L[0], L[1], L[2]);
                    gl.uniform3f(P.uL1, L[3], L[4], L[5]);
                }
                // the cap is per entity and moves without the light directions moving
                if (P.cap !== Module.mcLitCap) { P.cap = Module.mcLitCap; gl.uniform1f(P.uCap, Module.mcLitCap); }
            }

            // --- the buffer's vertex array object ----------------------------------------------
            var vkey = vbo * 64 + eflags * 8 + (stride & 7);
            var vao = F.vaos.get(vkey), made = false;
            if (!vao || vao.mcBuffer !== buf || vao.mcStride !== stride) {
                if (vao) gl.deleteVertexArray(vao);
                // The map is keyed by buffer NAME, so a name reused for a new buffer replaces its
                // entry - but a buffer deleted and never reused leaves one behind, and models make
                // a buffer per part. Put a ceiling on it rather than grow for ever.
                if (F.vaos.size > 4096) { F.vaos.forEach(function (v) { gl.deleteVertexArray(v); }); F.vaos.clear(); }
                vao = gl.createVertexArray();
                vao.mcBuffer = buf;
                vao.mcStride = stride;
                made = true;
                gl.bindVertexArray(vao);
                gl.bindBuffer(0x8892 /*ARRAY_BUFFER*/, buf);
                gl.enableVertexAttribArray(0);
                gl.vertexAttribPointer(0, 3, 0x1406 /*FLOAT*/, false, stride, 0);
                if (tex) { gl.enableVertexAttribArray(1); gl.vertexAttribPointer(1, 2, 0x1406, false, stride, 12); }
                if (col) { gl.enableVertexAttribArray(2); gl.vertexAttribPointer(2, 4, 0x1401 /*UNSIGNED_BYTE*/, true, stride, 20); }
                if (lit) { gl.enableVertexAttribArray(3); gl.vertexAttribPointer(3, 3, 0x1400 /*BYTE*/, true, stride, 20); }
                F.vaos.set(vkey, vao);
            } else {
                gl.bindVertexArray(vao);
            }
            gl.drawArrays(mode, 0, count);
            gl.bindVertexArray(null);
            // ARRAY_BUFFER is not vertex-array state in WebGL 2, so only making a VAO above
            // disturbed the emulation's binding - put that one back.
            if (made) {
                var prev = GLctx.currentArrayBufferBinding;
                gl.bindBuffer(0x8892, prev ? GL.buffers[prev] : null);
            }
            gl.useProgram(null);
            GLImmediate.fixedFunctionProgram = 0;
            return 1;
        } catch (e) {
            if (!Module.mcFfError) { Module.mcFfError = true; console.warn('fast draws disabled:', e); }
            if (F) F.broken = true;
            try { GLctx.bindVertexArray(null); GLctx.useProgram(null); GLImmediate.fixedFunctionProgram = 0; } catch (e2) { }
            return 0;
        }
    },

    mcSyncSaves: function () {
        if (typeof FS !== 'undefined') {
            FS.syncfs(false, function (err) {
                if (err) console.error('FS sync error:', err);
            });
        }
    }
});
