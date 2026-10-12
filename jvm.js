var JVM = (function () {
'use strict';

var TOP = { top: true };

function JObject(cls) { this.cls = cls; }
function JArray(cls, a) { this.cls = cls; this.a = a; }

function JavaThrow(obj) { this.obj = obj; }
JavaThrow.prototype.toString = function () { return 'JavaThrow(' + describeThrowable(this.obj) + ')'; };
function describeThrowable(o) {
	if (!o) return 'null';
	var m = o.$message;
	return (o.cls ? o.cls.name.replace(/[/]/g, '.') : '?') + (m != null ? ': ' + m : '');
}

var descCache = {};
function parseDesc(desc) {
	var c = descCache[desc];
	if (c) return c;
	var args = [], i = 1;
	if (desc[0] !== '(') throw new Error('not a method descriptor: ' + desc);
	while (desc[i] !== ')') {
		if (i >= desc.length) throw new Error('bad method descriptor: ' + desc);
		var s = i;
		while (desc[i] === '[') i++;
		if (desc[i] === 'L') i = desc.indexOf(';', i);
		i++;
		args.push(desc.substring(s, i));
	}
	var ret = desc.substring(i + 1);
	var slots = 0;
	for (var k = 0; k < args.length; k++) slots += (args[k] === 'J' || args[k] === 'D') ? 2 : 1;
	return (descCache[desc] = { args: args, ret: ret, slots: slots });
}
function isWide(t) { return t === 'J' || t === 'D'; }
function defaultOf(t) {
	switch (t[0]) {
	case 'J': return 0n;
	case 'L': case '[': return null;
	case 'V': return undefined;
	default: return 0;
	}
}
function typeToClassName(t) { return t[0] === 'L' ? t.substring(1, t.length - 1) : t; }

var ACC_PUBLIC = 0x0001, ACC_PRIVATE = 0x0002, ACC_STATIC = 0x0008, ACC_FINAL = 0x0010,
    ACC_SYNCHRONIZED = 0x0020, ACC_NATIVE = 0x0100, ACC_INTERFACE = 0x0200, ACC_ABSTRACT = 0x0400;

function JClass(vm, name) {
	this.vm = vm;
	this.name = name;
	this.superClass = null;
	this.interfaces = [];
	this.access = 0;
	this.methods = Object.create(null);
	this.fields = Object.create(null);
	this.statics = Object.create(null);
	this.initState = 0;
	this.absent = false;
	this.native = false;
	this.cf = null;
	this.vcache = Object.create(null);
	this.component = null;
	this.classObj = null;
	this.source = '';
}
JClass.prototype.isInterface = function () { return (this.access & ACC_INTERFACE) !== 0; };

JClass.prototype.findMethod = function (key) {
	var m = this.vcache[key];
	if (m !== undefined) return m;
	m = null;
	for (var c = this; c && !m; c = c.superClass) m = c.methods[key] || null;
	if (!m || (m.access & ACC_ABSTRACT)) {
		var q = [], seen = {};
		for (var c2 = this; c2; c2 = c2.superClass) q.push.apply(q, c2.interfaces);
		while (q.length) {
			var it = q.shift();
			if (seen[it.name]) continue;
			seen[it.name] = true;
			var im = it.methods[key];
			if (im && !(im.access & ACC_ABSTRACT)) { m = im; break; }
			if (im && !m) m = im;
			q.push.apply(q, it.interfaces);
		}
	}
	return (this.vcache[key] = m);
};
JClass.prototype.findDeclared = function (key) {
	for (var c = this; c; c = c.superClass) if (c.methods[key]) return c.methods[key];
	return this.findMethod(key);
};
JClass.prototype.findField = function (name) {
	for (var c = this; c; c = c.superClass) {
		if (c.fields[name]) return { owner: c, f: c.fields[name] };
		for (var i = 0; i < c.interfaces.length; i++) {
			var r = c.interfaces[i].findField(name);
			if (r) return r;
		}
	}
	return null;
};
JClass.prototype.isSubclassOf = function (other) {
	if (this === other) return true;
	if (other.name === 'java/lang/Object') return true;
	if (this.name[0] === '[') {
		if (other.name[0] !== '[') return other.name === 'java/lang/Cloneable' || other.name === 'java/io/Serializable';
		var a = this.component, b = other.component;
		if (a[0] === 'L' || a[0] === '[') {
			if (!(b[0] === 'L' || b[0] === '[')) return false;
			return this.vm.classFor(a).isSubclassOf(this.vm.classFor(b));
		}
		return a === b;
	}
	for (var c = this; c; c = c.superClass) {
		if (c === other) return true;
		for (var i = 0; i < c.interfaces.length; i++) if (c.interfaces[i].isSubclassOf(other)) return true;
	}
	return other.absent || this.absent;
};

function JMethod(cls, name, desc, access) {
	this.cls = cls;
	this.name = name;
	this.desc = desc;
	this.key = name + desc;
	this.access = access;
	this.isStatic = (access & ACC_STATIC) !== 0;
	this.sig = parseDesc(desc);
	this.code = null;
	this.fn = null;
}

function VM(opts) {
	opts = opts || {};
	this.classes = Object.create(null);
	this.sources = Object.create(null);
	this.natives = Object.create(null);
	this.log = opts.log || function () {};
	this.warned = {};
	this.mapClass = opts.mapClass || null;
	this.mapMember = opts.mapMember || null;
	this.depth = 0;
	this.hashSeq = 1;
	this.internTable = {};
	this.maxSteps = opts.maxSteps || 50000000;
	this.steps = 0;
	this.fs = opts.fs || null;
	this.resources = Object.create(null);
	JVM.installLang(this);
	JVM.installUtil(this);
	JVM.installIo(this);
	if (opts.install) opts.install(this);
}

VM.prototype.warnOnce = function (key, msg) {
	if (this.warned[key]) return;
	this.warned[key] = true;
	this.log('warn', msg);
};

VM.prototype.defineNative = function (name, spec) { this.natives[name] = spec; };

VM.prototype.classFor = function (t) {
	if (t.length > 1 && t[0] === 'L' && t[t.length - 1] === ';') t = t.substring(1, t.length - 1);
	return this.loadClass(t);
};

VM.prototype.loadClass = function (name) {
	var c = this.classes[name];
	if (c) return c;
	if (this.mapClass) {
		var m = this.mapClass(name);
		if (m && m !== name) {
			c = this.loadClass(m);
			this.classes[name] = c;
			return c;
		}
	}
	if (name[0] === '[') return this.arrayClass(name);
	if (name.length === 1) return this.primitiveClass(name);
	var src = this.sources[name];
	if (src) {
		delete this.sources[name];
		return this.defineFromBytes(name, src.bytes, src.source);
	}
	var spec = this.natives[name];
	if (spec) return this.defineNativeClass(name, spec);
	return this.absentClass(name);
};

VM.prototype.primitiveClass = function (t) {
	var c = new JClass(this, t);
	c.access = ACC_PUBLIC | ACC_FINAL | ACC_ABSTRACT;
	c.initState = 2;
	c.primitive = true;
	this.classes[t] = c;
	return c;
};

VM.prototype.arrayClass = function (name) {
	var c = new JClass(this, name);
	c.component = name.substring(1);
	c.superClass = this.loadClass('java/lang/Object');
	c.access = ACC_PUBLIC | ACC_FINAL;
	c.initState = 2;
	this.classes[name] = c;
	return c;
};

VM.prototype.absentClass = function (name) {
	var c = new JClass(this, name);
	c.absent = true;
	c.native = true;
	c.access = ACC_PUBLIC;
	c.initState = 2;
	if (name !== 'java/lang/Object') c.superClass = this.loadClass('java/lang/Object');
	this.classes[name] = c;
	this.warnOnce('class:' + name, 'not available here: ' + name.replace(/[/]/g, '.') + ' (left unplugged)');
	return c;
};

VM.prototype.defineNativeClass = function (name, spec) {
	var c = new JClass(this, name);
	c.native = true;
	c.access = spec.access != null ? spec.access : ACC_PUBLIC;
	this.classes[name] = c;
	if (name !== 'java/lang/Object') c.superClass = this.loadClass(spec.super || 'java/lang/Object');
	c.interfaces = (spec.interfaces || []).map(this.loadClass, this);
	var k, m;
	for (k in spec.methods || {}) {
		var p = k.indexOf('(');
		m = new JMethod(c, k.substring(0, p), k.substring(p), ACC_PUBLIC);
		m.fn = spec.methods[k];
		c.methods[k] = m;
	}
	for (k in spec.staticMethods || {}) {
		var p2 = k.indexOf('(');
		m = new JMethod(c, k.substring(0, p2), k.substring(p2), ACC_PUBLIC | ACC_STATIC);
		m.fn = spec.staticMethods[k];
		c.methods[k] = m;
	}
	for (k in spec.abstractMethods || {}) {
		var p3 = k.indexOf('(');
		m = new JMethod(c, k.substring(0, p3), k.substring(p3), ACC_PUBLIC | ACC_ABSTRACT);
		c.methods[k] = m;
	}
	for (k in spec.fields || {}) c.fields[k] = { name: k, desc: spec.fields[k], access: ACC_PUBLIC, static: false };
	for (k in spec.statics || {}) {
		c.fields[k] = { name: k, desc: '?', access: ACC_PUBLIC | ACC_STATIC, static: true };
		c.statics[k] = spec.statics[k];
	}
	c.spec = spec;
	c.initState = spec.clinit ? 0 : 2;
	return c;
};

VM.prototype.addClassFile = function (name, bytes, source) {
	if (this.classes[name] && !this.classes[name].absent) return;
	this.sources[name] = { bytes: bytes, source: source || '' };
};

VM.prototype.defineFromBytes = function (expectName, bytes, source) {
	var cf = JVM.parseClassFile(bytes);
	if (this.mapClass || this.mapMember) JVM.remapClassFile(this, cf);
	var name = cf.name;
	var c = new JClass(this, name);
	c.cf = cf;
	c.access = cf.access;
	c.source = source || '';
	this.classes[name] = c;
	if (expectName !== name) this.classes[expectName] = c;
	c.superClass = cf.superName ? this.loadClass(cf.superName) : null;
	c.interfaces = cf.interfaces.map(this.loadClass, this);
	for (var i = 0; i < cf.fields.length; i++) {
		var f = cf.fields[i];
		var st = (f.access & ACC_STATIC) !== 0;
		c.fields[f.name] = { name: f.name, desc: f.desc, access: f.access, static: st };
		if (st) c.statics[f.name] = f.constant !== undefined ? f.constant : defaultOf(f.desc);
	}
	for (var j = 0; j < cf.methods.length; j++) {
		var mi = cf.methods[j];
		var m = new JMethod(c, mi.name, mi.desc, mi.access);
		m.code = mi.code;
		c.methods[m.key] = m;
	}
	return c;
};

VM.prototype.initClass = function (c) {
	if (c.initState !== 0) return;
	c.initState = 1;
	if (c.superClass) this.initClass(c.superClass);
	if (c.native) {
		if (c.spec && c.spec.clinit) c.spec.clinit(this, c);
	} else {
		var m = c.methods['<clinit>()V'];
		if (m) this.invoke(m, null, []);
	}
	c.initState = 2;
};

VM.prototype.newObject = function (c) {
	if (c.initState !== 2) this.initClass(c);
	var o = new JObject(c);
	for (var k = c; k; k = k.superClass) {
		for (var n in k.fields) {
			var f = k.fields[n];
			if (!f.static && !((':' + n) in o)) o[':' + n] = defaultOf(f.desc);
		}
	}
	return o;
};

VM.prototype.newArray = function (type, n) {
	if (n < 0) this.throwNew('java/lang/NegativeArraySizeException', String(n));
	var a;
	switch (type) {
	case 'I': a = new Int32Array(n); break;
	case 'B': case 'Z': a = new Int8Array(n); break;
	case 'C': a = new Uint16Array(n); break;
	case 'S': a = new Int16Array(n); break;
	case 'F': a = new Float32Array(n); break;
	case 'D': a = new Float64Array(n); break;
	case 'J': a = new BigInt64Array(n); break;
	default: a = new Array(n); for (var i = 0; i < n; i++) a[i] = null;
	}
	return new JArray(this.loadClass('[' + type), a);
};

VM.prototype.classOf = function (v) {
	if (typeof v === 'string') return this.loadClass('java/lang/String');
	return v.cls;
};

VM.prototype.isInstance = function (v, c) {
	if (v === null || v === undefined) return false;
	return this.classOf(v).isSubclassOf(c);
};

VM.prototype.makeThrowable = function (cname, msg) {
	var c = this.loadClass(cname);
	var o = this.newObject(c);
	o.$message = msg != null ? String(msg) : null;
	o.$jsStack = this.currentTrace ? this.currentTrace() : null;
	return o;
};
VM.prototype.throwNew = function (cname, msg) {
	throw new JavaThrow(this.makeThrowable(cname, msg));
};

VM.prototype.toJava = function (e) {
	if (e instanceof JavaThrow) return e;
	if (e instanceof RangeError && /call stack/i.test(e.message)) return new JavaThrow(this.makeThrowable('java/lang/StackOverflowError', null));
	if (e instanceof TypeError && /null|undefined/.test(e.message)) return new JavaThrow(this.makeThrowable('java/lang/NullPointerException', e.message));
	if (e && e.vmStop) throw e;
	return new JavaThrow(this.makeThrowable('java/lang/Error', 'internal: ' + (e && e.message || e)));
};

VM.prototype.intern = function (s) { return s; };

VM.prototype.identityHash = function (o) {
	if (typeof o === 'string') return JVM.stringHash(o);
	if (o.$hash === undefined) o.$hash = (this.hashSeq = (Math.imul(this.hashSeq, 1103515245) + 12345) | 0) & 0x7fffffff;
	return o.$hash;
};

VM.prototype.classObject = function (c) {
	if (!c.classObj) {
		var o = new JObject(this.loadClass('java/lang/Class'));
		o.$cls = c;
		c.classObj = o;
	}
	return c.classObj;
};

VM.prototype.invoke = function (m, self, args) {
	if (m.fn) return m.fn(this, self, args);
	if (!m.code) {
		if (m.access & ACC_ABSTRACT) this.throwNew('java/lang/AbstractMethodError', m.cls.name + '.' + m.key);
		if (m.access & ACC_NATIVE) {
			this.warnOnce('native:' + m.cls.name + m.key, 'native method left unplugged: ' + m.cls.name.replace(/[/]/g, '.') + '.' + m.name);
			return defaultOf(m.sig.ret);
		}
		return defaultOf(m.sig.ret);
	}
	return JVM.interpret(this, m, self, args);
};

VM.prototype.callVirtual = function (obj, name, desc, args) {
	if (obj === null || obj === undefined) this.throwNew('java/lang/NullPointerException', name);
	var c = this.classOf(obj);
	var m = c.findMethod(name + desc);
	if (!m) return this.missingMethod(c, name, desc);
	return this.invoke(m, obj, args || []);
};
VM.prototype.callStatic = function (cname, name, desc, args) {
	var c = this.loadClass(cname);
	this.initClass(c);
	var m = c.findDeclared(name + desc);
	if (!m) return this.missingMethod(c, name, desc);
	return this.invoke(m, null, args || []);
};
VM.prototype.missingMethod = function (c, name, desc) {
	this.warnOnce('m:' + c.name + '.' + name + desc, 'not available here: ' + c.name.replace(/[/]/g, '.') + '.' + name + desc + ' (left unplugged)');
	return defaultOf(parseDesc(desc).ret);
};

VM.prototype.toJavaString = function (v) {
	if (v === null || v === undefined) return 'null';
	if (typeof v === 'string') return v;
	if (typeof v === 'bigint') return v.toString();
	if (typeof v === 'number') return String(v);
	var s = this.callVirtual(v, 'toString', '()Ljava/lang/String;', []);
	return s === null ? 'null' : s;
};

VM.prototype.charArray = function (s) {
	var a = this.newArray('C', s.length);
	for (var i = 0; i < s.length; i++) a.a[i] = s.charCodeAt(i);
	return a;
};
VM.prototype.stringFromChars = function (arr, off, len) {
	var a = arr.a, s = '';
	off = off || 0;
	len = len == null ? a.length - off : len;
	for (var i = 0; i < len; i += 8192) s += String.fromCharCode.apply(null, Array.prototype.slice.call(a, off + i, off + Math.min(len, i + 8192)));
	return s;
};

var api = {
	VM: VM, JClass: JClass, JMethod: JMethod, JObject: JObject, JArray: JArray, JavaThrow: JavaThrow,
	TOP: TOP, parseDesc: parseDesc, isWide: isWide, defaultOf: defaultOf, typeToClassName: typeToClassName,
	describeThrowable: describeThrowable,
	ACC_PUBLIC: ACC_PUBLIC, ACC_PRIVATE: ACC_PRIVATE, ACC_STATIC: ACC_STATIC, ACC_FINAL: ACC_FINAL,
	ACC_SYNCHRONIZED: ACC_SYNCHRONIZED, ACC_NATIVE: ACC_NATIVE, ACC_INTERFACE: ACC_INTERFACE,
	ACC_ABSTRACT: ACC_ABSTRACT,
	create: function (opts) { return new VM(opts); },
};
return api;
})();

(function () {
'use strict';

var CONSTANT_Utf8 = 1, CONSTANT_Integer = 3, CONSTANT_Float = 4, CONSTANT_Long = 5, CONSTANT_Double = 6,
    CONSTANT_Class = 7, CONSTANT_String = 8, CONSTANT_Fieldref = 9, CONSTANT_Methodref = 10,
    CONSTANT_InterfaceMethodref = 11, CONSTANT_NameAndType = 12, CONSTANT_MethodHandle = 15,
    CONSTANT_MethodType = 16, CONSTANT_Dynamic = 17, CONSTANT_InvokeDynamic = 18,
    CONSTANT_Module = 19, CONSTANT_Package = 20;

function Reader(bytes) {
	this.b = bytes;
	this.dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
	this.p = 0;
}
Reader.prototype.u1 = function () { return this.b[this.p++]; };
Reader.prototype.u2 = function () { var v = this.dv.getUint16(this.p); this.p += 2; return v; };
Reader.prototype.u4 = function () { var v = this.dv.getUint32(this.p); this.p += 4; return v; };
Reader.prototype.i4 = function () { var v = this.dv.getInt32(this.p); this.p += 4; return v; };
Reader.prototype.bytes = function (n) { var v = this.b.subarray(this.p, this.p + n); this.p += n; return v; };

function decodeMutf8(b) {
	var s = '', i = 0, n = b.length, chunk = [];
	while (i < n) {
		var c = b[i++];
		if (c < 0x80) chunk.push(c);
		else if ((c & 0xe0) === 0xc0) chunk.push(((c & 0x1f) << 6) | (b[i++] & 0x3f));
		else { var c2 = b[i++], c3 = b[i++]; chunk.push(((c & 0x0f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f)); }
		if (chunk.length >= 4096) { s += String.fromCharCode.apply(null, chunk); chunk.length = 0; }
	}
	return s + String.fromCharCode.apply(null, chunk);
}

function parseClassFile(bytes) {
	var r = new Reader(bytes);
	if (r.u4() !== 0xCAFEBABE) throw new Error('not a class file');
	var minor = r.u2(), major = r.u2();
	var n = r.u2();
	var cp = new Array(n);
	for (var i = 1; i < n; i++) {
		var tag = r.u1();
		switch (tag) {
		case CONSTANT_Utf8: cp[i] = { tag: tag, v: decodeMutf8(r.bytes(r.u2())) }; break;
		case CONSTANT_Integer: cp[i] = { tag: tag, v: r.i4() }; break;
		case CONSTANT_Float: { var f = r.dv.getFloat32(r.p); r.p += 4; cp[i] = { tag: tag, v: f }; break; }
		case CONSTANT_Long: { var l = r.dv.getBigInt64(r.p); r.p += 8; cp[i] = { tag: tag, v: l }; i++; break; }
		case CONSTANT_Double: { var d = r.dv.getFloat64(r.p); r.p += 8; cp[i] = { tag: tag, v: d }; i++; break; }
		case CONSTANT_Class: cp[i] = { tag: tag, name: r.u2() }; break;
		case CONSTANT_String: cp[i] = { tag: tag, str: r.u2() }; break;
		case CONSTANT_Fieldref: case CONSTANT_Methodref: case CONSTANT_InterfaceMethodref:
			cp[i] = { tag: tag, cls: r.u2(), nt: r.u2() }; break;
		case CONSTANT_NameAndType: cp[i] = { tag: tag, name: r.u2(), desc: r.u2() }; break;
		case CONSTANT_MethodHandle: cp[i] = { tag: tag, kind: r.u1(), ref: r.u2() }; break;
		case CONSTANT_MethodType: cp[i] = { tag: tag, desc: r.u2() }; break;
		case CONSTANT_Dynamic: case CONSTANT_InvokeDynamic: cp[i] = { tag: tag, bsm: r.u2(), nt: r.u2() }; break;
		case CONSTANT_Module: case CONSTANT_Package: cp[i] = { tag: tag, name: r.u2() }; break;
		default: throw new Error('bad constant pool tag ' + tag);
		}
	}
	function utf(k) { return cp[k].v; }
	for (var j = 1; j < n; j++) {
		var e = cp[j];
		if (!e) continue;
		switch (e.tag) {
		case CONSTANT_Class: e.v = utf(e.name); break;
		case CONSTANT_String: e.v = utf(e.str); break;
		case CONSTANT_NameAndType: e.n = utf(e.name); e.d = utf(e.desc); break;
		case CONSTANT_MethodType: e.d = utf(e.desc); break;
		}
	}
	for (var k = 1; k < n; k++) {
		var e2 = cp[k];
		if (!e2) continue;
		if (e2.tag === CONSTANT_Fieldref || e2.tag === CONSTANT_Methodref || e2.tag === CONSTANT_InterfaceMethodref) {
			e2.owner = cp[e2.cls].v;
			e2.name = cp[e2.nt].n;
			e2.desc = cp[e2.nt].d;
		} else if (e2.tag === CONSTANT_InvokeDynamic || e2.tag === CONSTANT_Dynamic) {
			e2.name = cp[e2.nt].n;
			e2.desc = cp[e2.nt].d;
		}
	}

	var cf = { major: major, minor: minor, cp: cp };
	cf.access = r.u2();
	cf.name = cp[r.u2()].v;
	var sup = r.u2();
	cf.superName = sup ? cp[sup].v : null;
	cf.interfaces = [];
	for (var ii = r.u2(); ii > 0; ii--) cf.interfaces.push(cp[r.u2()].v);

	cf.fields = [];
	for (var fc = r.u2(); fc > 0; fc--) {
		var fld = { access: r.u2(), name: utf(r.u2()), desc: utf(r.u2()) };
		readAttributes(r, cp, function (aname, len) {
			if (aname === 'ConstantValue') {
				var ce = cp[r.u2()];
				fld.constant = ce.tag === CONSTANT_String ? ce.v : ce.v;
				if (fld.desc === 'F') fld.constant = Math.fround(fld.constant);
				return true;
			}
			return false;
		});
		cf.fields.push(fld);
	}

	cf.methods = [];
	for (var mc = r.u2(); mc > 0; mc--) {
		var mt = { access: r.u2(), name: utf(r.u2()), desc: utf(r.u2()), code: null };
		readAttributes(r, cp, function (aname, len) {
			if (aname !== 'Code') return false;
			var code = { maxStack: r.u2(), maxLocals: r.u2() };
			code.bytes = r.bytes(r.u4());
			code.handlers = [];
			for (var h = r.u2(); h > 0; h--) {
				var start = r.u2(), end = r.u2(), handler = r.u2(), ct = r.u2();
				code.handlers.push({ start: start, end: end, handler: handler, type: ct ? cp[ct].v : null });
			}
			readAttributes(r, cp, function (an2) {
				if (an2 !== 'LineNumberTable') return false;
				var lines = [];
				for (var q = r.u2(); q > 0; q--) lines.push(r.u2(), r.u2());
				code.lines = lines;
				return true;
			});
			mt.code = code;
			return true;
		});
		cf.methods.push(mt);
	}

	cf.bootstrap = [];
	readAttributes(r, cp, function (aname) {
		if (aname === 'BootstrapMethods') {
			for (var b = r.u2(); b > 0; b--) {
				var bm = { ref: r.u2(), args: [] };
				for (var ba = r.u2(); ba > 0; ba--) bm.args.push(r.u2());
				cf.bootstrap.push(bm);
			}
			return true;
		}
		if (aname === 'SourceFile') { cf.sourceFile = utf(r.u2()); return true; }
		return false;
	});
	return cf;
}

function readAttributes(r, cp, fn) {
	for (var n = r.u2(); n > 0; n--) {
		var name = cp[r.u2()].v, len = r.u4(), end = r.p + len;
		if (!fn(name, len)) r.p = end;
		else r.p = end;
	}
}

function remapClassFile(vm, cf) {
	(vm.origParents || (vm.origParents = Object.create(null)))[cf.name] = [cf.superName].concat(cf.interfaces);
	var mc = vm.mapClass ? function (n) { var m = vm.mapClass(n); return m || n; } : function (n) { return n; };
	function mapDesc(d) {
		return d.replace(/L([^;]+);/g, function (all, n) { return 'L' + mc(n) + ';'; });
	}
	function mapType(t) { return t[0] === '[' ? mapDesc(t) : mc(t); }
	var cp = cf.cp;
	for (var i = 1; i < cp.length; i++) {
		var e = cp[i];
		if (!e) continue;
		if (e.tag === 7) e.v = mapType(e.v);
		else if (e.tag === 16) e.d = mapDesc(e.d);
		else if (e.tag === 9 || e.tag === 10 || e.tag === 11) {
			var ownerOrig = e.owner, nameOrig = e.name, descOrig = e.desc;
			e.owner = mapType(ownerOrig);
			if (vm.mapMember) e.name = vm.mapMember(ownerOrig, nameOrig, descOrig, e.tag !== 9) || nameOrig;
			e.desc = mapDesc(descOrig);
		} else if (e.tag === 18 || e.tag === 17) e.desc = mapDesc(e.desc);
	}
	var selfOrig = cf.name;
	cf.name = mc(cf.name);
	if (cf.superName) cf.superName = mc(cf.superName);
	cf.interfaces = cf.interfaces.map(mc);
	cf.fields.forEach(function (f) { f.desc = mapDesc(f.desc); });
	cf.methods.forEach(function (m) {
		if (vm.mapMember && m.name[0] !== '<') m.name = vm.mapMember(selfOrig, m.name, m.desc, true, true) || m.name;
		m.desc = mapDesc(m.desc);
		if (m.code) m.code.handlers.forEach(function (h) { if (h.type) h.type = mc(h.type); });
	});
}

JVM.parseClassFile = parseClassFile;
JVM.remapClassFile = remapClassFile;
JVM.decodeMutf8 = decodeMutf8;
})();

(function () {
'use strict';

var TOP = JVM.TOP, JavaThrow = JVM.JavaThrow, parseDesc = JVM.parseDesc, isWide = JVM.isWide,
    defaultOf = JVM.defaultOf, JArray = JVM.JArray;

var ARRAY_TYPES = { 4: 'Z', 5: 'C', 6: 'F', 7: 'D', 8: 'B', 9: 'S', 10: 'I', 11: 'J' };
var INT_MIN = -2147483648;

function f2i(v) {
	if (v !== v) return 0;
	if (v >= 2147483647) return 2147483647;
	if (v <= INT_MIN) return INT_MIN;
	return Math.trunc(v) | 0;
}
function f2l(v) {
	if (v !== v) return 0n;
	if (v >= 9223372036854775807) return 9223372036854775807n;
	if (v <= -9223372036854775808) return -9223372036854775808n;
	return BigInt(Math.trunc(v));
}
var L = function (v) { return BigInt.asIntN(64, v); };

function Frame(m) { this.m = m; this.pc = 0; }

function interpret(vm, m, self, args) {
	var code = m.code, bytes = code.bytes, cp = m.cls.cf.cp;
	var locals = new Array(code.maxLocals);
	var slot = 0;
	if (!m.isStatic) locals[slot++] = self;
	var at = m.sig.args;
	for (var ai = 0; ai < at.length; ai++) {
		locals[slot++] = args[ai];
		if (isWide(at[ai])) locals[slot++] = TOP;
	}
	var stack = [];
	var pc = 0;
	var frame = new Frame(m);
	var frames = vm.frames || (vm.frames = []);
	frames.push(frame);
	try {
		for (;;) {
			try {
				return run();
			} catch (e) {
				if (e && e.vmStop) throw e;
				var je = vm.toJava(e);
				var h = findHandler(vm, code, frame.pc, je.obj);
				if (h < 0) throw je;
				stack.length = 0;
				stack.push(je.obj);
				pc = h;
			}
		}
	} finally {
		frames.pop();
	}

	function run() {
		var a, b, c, v, e, i, n, o, idx, arr, off;
		for (;;) {
			frame.pc = pc;
			var op = bytes[pc];
			switch (op) {
			case 0x00: pc++; break;
			case 0x01: stack.push(null); pc++; break;
			case 0x02: case 0x03: case 0x04: case 0x05: case 0x06: case 0x07: case 0x08:
				stack.push(op - 3); pc++; break;
			case 0x09: case 0x0a: stack.push(BigInt(op - 9), TOP); pc++; break;
			case 0x0b: case 0x0c: case 0x0d: stack.push(op - 0x0b); pc++; break;
			case 0x0e: case 0x0f: stack.push(op - 0x0e, TOP); pc++; break;
			case 0x10: stack.push((bytes[pc + 1] << 24) >> 24); pc += 2; break;
			case 0x11: stack.push(((bytes[pc + 1] << 24) >> 16) | bytes[pc + 2]); pc += 3; break;
			case 0x12: ldc(bytes[pc + 1]); pc += 2; break;
			case 0x13: ldc((bytes[pc + 1] << 8) | bytes[pc + 2]); pc += 3; break;
			case 0x14: e = cp[(bytes[pc + 1] << 8) | bytes[pc + 2]]; stack.push(e.v, TOP); pc += 3; break;
			case 0x15: case 0x17: case 0x19: stack.push(locals[bytes[pc + 1]]); pc += 2; break;
			case 0x16: case 0x18: stack.push(locals[bytes[pc + 1]], TOP); pc += 2; break;
			case 0x1a: case 0x1b: case 0x1c: case 0x1d: stack.push(locals[op - 0x1a]); pc++; break;
			case 0x1e: case 0x1f: case 0x20: case 0x21: stack.push(locals[op - 0x1e], TOP); pc++; break;
			case 0x22: case 0x23: case 0x24: case 0x25: stack.push(locals[op - 0x22]); pc++; break;
			case 0x26: case 0x27: case 0x28: case 0x29: stack.push(locals[op - 0x26], TOP); pc++; break;
			case 0x2a: case 0x2b: case 0x2c: case 0x2d: stack.push(locals[op - 0x2a]); pc++; break;
			case 0x2e: case 0x30: case 0x32: case 0x33: case 0x34: case 0x35:
				i = stack.pop(); arr = stack.pop(); checkIndex(arr, i); stack.push(arr.a[i]); pc++; break;
			case 0x2f: case 0x31:
				i = stack.pop(); arr = stack.pop(); checkIndex(arr, i); stack.push(arr.a[i], TOP); pc++; break;
			case 0x36: case 0x38: case 0x3a: locals[bytes[pc + 1]] = stack.pop(); pc += 2; break;
			case 0x37: case 0x39: stack.pop(); idx = bytes[pc + 1]; locals[idx] = stack.pop(); locals[idx + 1] = TOP; pc += 2; break;
			case 0x3b: case 0x3c: case 0x3d: case 0x3e: locals[op - 0x3b] = stack.pop(); pc++; break;
			case 0x3f: case 0x40: case 0x41: case 0x42: stack.pop(); locals[op - 0x3f] = stack.pop(); locals[op - 0x3f + 1] = TOP; pc++; break;
			case 0x43: case 0x44: case 0x45: case 0x46: locals[op - 0x43] = stack.pop(); pc++; break;
			case 0x47: case 0x48: case 0x49: case 0x4a: stack.pop(); locals[op - 0x47] = stack.pop(); locals[op - 0x47 + 1] = TOP; pc++; break;
			case 0x4b: case 0x4c: case 0x4d: case 0x4e: locals[op - 0x4b] = stack.pop(); pc++; break;
			case 0x4f: case 0x51: case 0x53: case 0x54: case 0x55: case 0x56:
				v = stack.pop(); i = stack.pop(); arr = stack.pop(); checkIndex(arr, i);
				if (op === 0x54 && arr.cls.name === '[Z') v = v ? 1 : 0;
				arr.a[i] = v; pc++; break;
			case 0x50: case 0x52:
				stack.pop(); v = stack.pop(); i = stack.pop(); arr = stack.pop(); checkIndex(arr, i); arr.a[i] = v; pc++; break;
			case 0x57: stack.pop(); pc++; break;
			case 0x58: stack.pop(); stack.pop(); pc++; break;
			case 0x59: stack.push(stack[stack.length - 1]); pc++; break;
			case 0x5a: a = stack.pop(); b = stack.pop(); stack.push(a, b, a); pc++; break;
			case 0x5b: a = stack.pop(); b = stack.pop(); c = stack.pop(); stack.push(a, c, b, a); pc++; break;
			case 0x5c: a = stack[stack.length - 2]; b = stack[stack.length - 1]; stack.push(a, b); pc++; break;
			case 0x5d: a = stack.pop(); b = stack.pop(); c = stack.pop(); stack.push(b, a, c, b, a); pc++; break;
			case 0x5e: a = stack.pop(); b = stack.pop(); c = stack.pop(); var d4 = stack.pop(); stack.push(b, a, d4, c, b, a); pc++; break;
			case 0x5f: a = stack.pop(); b = stack.pop(); stack.push(a, b); pc++; break;
			case 0x60: b = stack.pop(); a = stack.pop(); stack.push((a + b) | 0); pc++; break;
			case 0x64: b = stack.pop(); a = stack.pop(); stack.push((a - b) | 0); pc++; break;
			case 0x68: b = stack.pop(); a = stack.pop(); stack.push(Math.imul(a, b)); pc++; break;
			case 0x6c: b = stack.pop(); a = stack.pop(); if (b === 0) vm.throwNew('java/lang/ArithmeticException', '/ by zero');
				stack.push((a / b) | 0); pc++; break;
			case 0x70: b = stack.pop(); a = stack.pop(); if (b === 0) vm.throwNew('java/lang/ArithmeticException', '/ by zero');
				stack.push((a % b) | 0); pc++; break;
			case 0x74: stack.push((-stack.pop()) | 0); pc++; break;
			case 0x78: b = stack.pop(); a = stack.pop(); stack.push(a << (b & 31)); pc++; break;
			case 0x7a: b = stack.pop(); a = stack.pop(); stack.push(a >> (b & 31)); pc++; break;
			case 0x7c: b = stack.pop(); a = stack.pop(); stack.push((a >>> (b & 31)) | 0); pc++; break;
			case 0x7e: b = stack.pop(); a = stack.pop(); stack.push(a & b); pc++; break;
			case 0x80: b = stack.pop(); a = stack.pop(); stack.push(a | b); pc++; break;
			case 0x82: b = stack.pop(); a = stack.pop(); stack.push(a ^ b); pc++; break;
			case 0x61: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(L(a + b), TOP); pc++; break;
			case 0x65: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(L(a - b), TOP); pc++; break;
			case 0x69: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(L(a * b), TOP); pc++; break;
			case 0x6d: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); if (b === 0n) vm.throwNew('java/lang/ArithmeticException', '/ by zero');
				stack.push(L(a / b), TOP); pc++; break;
			case 0x71: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); if (b === 0n) vm.throwNew('java/lang/ArithmeticException', '/ by zero');
				stack.push(L(a % b), TOP); pc++; break;
			case 0x75: stack.pop(); a = stack.pop(); stack.push(L(-a), TOP); pc++; break;
			case 0x79: b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(L(a << BigInt(b & 63)), TOP); pc++; break;
			case 0x7b: b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(a >> BigInt(b & 63), TOP); pc++; break;
			case 0x7d: b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(L(BigInt.asUintN(64, a) >> BigInt(b & 63)), TOP); pc++; break;
			case 0x7f: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(a & b, TOP); pc++; break;
			case 0x81: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(a | b, TOP); pc++; break;
			case 0x83: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(a ^ b, TOP); pc++; break;
			case 0x62: b = stack.pop(); a = stack.pop(); stack.push(Math.fround(a + b)); pc++; break;
			case 0x66: b = stack.pop(); a = stack.pop(); stack.push(Math.fround(a - b)); pc++; break;
			case 0x6a: b = stack.pop(); a = stack.pop(); stack.push(Math.fround(a * b)); pc++; break;
			case 0x6e: b = stack.pop(); a = stack.pop(); stack.push(Math.fround(a / b)); pc++; break;
			case 0x72: b = stack.pop(); a = stack.pop(); stack.push(Math.fround(a % b)); pc++; break;
			case 0x76: stack.push(-stack.pop()); pc++; break;
			case 0x63: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(a + b, TOP); pc++; break;
			case 0x67: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(a - b, TOP); pc++; break;
			case 0x6b: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(a * b, TOP); pc++; break;
			case 0x6f: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(a / b, TOP); pc++; break;
			case 0x73: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(a % b, TOP); pc++; break;
			case 0x77: stack.pop(); a = stack.pop(); stack.push(-a, TOP); pc++; break;
			case 0x84:
				locals[bytes[pc + 1]] = (locals[bytes[pc + 1]] + ((bytes[pc + 2] << 24) >> 24)) | 0; pc += 3; break;
			case 0x85: stack.push(BigInt(stack.pop()), TOP); pc++; break;
			case 0x86: stack.push(Math.fround(stack.pop())); pc++; break;
			case 0x87: stack.push(stack.pop(), TOP); pc++; break;
			case 0x88: stack.pop(); stack.push(Number(BigInt.asIntN(32, stack.pop()))); pc++; break;
			case 0x89: stack.pop(); stack.push(Math.fround(Number(stack.pop()))); pc++; break;
			case 0x8a: stack.pop(); stack.push(Number(stack.pop()), TOP); pc++; break;
			case 0x8b: stack.push(f2i(stack.pop())); pc++; break;
			case 0x8c: stack.push(f2l(stack.pop()), TOP); pc++; break;
			case 0x8d: stack.push(stack.pop(), TOP); pc++; break;
			case 0x8e: stack.pop(); stack.push(f2i(stack.pop())); pc++; break;
			case 0x8f: stack.pop(); stack.push(f2l(stack.pop()), TOP); pc++; break;
			case 0x90: stack.pop(); stack.push(Math.fround(stack.pop())); pc++; break;
			case 0x91: stack.push((stack.pop() << 24) >> 24); pc++; break;
			case 0x92: stack.push(stack.pop() & 0xffff); pc++; break;
			case 0x93: stack.push((stack.pop() << 16) >> 16); pc++; break;
			case 0x94: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop(); stack.push(a > b ? 1 : a < b ? -1 : 0); pc++; break;
			case 0x95: case 0x96: b = stack.pop(); a = stack.pop();
				stack.push(a > b ? 1 : a < b ? -1 : a === b ? 0 : (op === 0x95 ? -1 : 1)); pc++; break;
			case 0x97: case 0x98: stack.pop(); b = stack.pop(); stack.pop(); a = stack.pop();
				stack.push(a > b ? 1 : a < b ? -1 : a === b ? 0 : (op === 0x97 ? -1 : 1)); pc++; break;
			case 0x99: v = stack.pop(); pc = v === 0 ? jump() : pc + 3; break;
			case 0x9a: v = stack.pop(); pc = v !== 0 ? jump() : pc + 3; break;
			case 0x9b: v = stack.pop(); pc = v < 0 ? jump() : pc + 3; break;
			case 0x9c: v = stack.pop(); pc = v >= 0 ? jump() : pc + 3; break;
			case 0x9d: v = stack.pop(); pc = v > 0 ? jump() : pc + 3; break;
			case 0x9e: v = stack.pop(); pc = v <= 0 ? jump() : pc + 3; break;
			case 0x9f: b = stack.pop(); a = stack.pop(); pc = a === b ? jump() : pc + 3; break;
			case 0xa0: b = stack.pop(); a = stack.pop(); pc = a !== b ? jump() : pc + 3; break;
			case 0xa1: b = stack.pop(); a = stack.pop(); pc = a < b ? jump() : pc + 3; break;
			case 0xa2: b = stack.pop(); a = stack.pop(); pc = a >= b ? jump() : pc + 3; break;
			case 0xa3: b = stack.pop(); a = stack.pop(); pc = a > b ? jump() : pc + 3; break;
			case 0xa4: b = stack.pop(); a = stack.pop(); pc = a <= b ? jump() : pc + 3; break;
			case 0xa5: b = stack.pop(); a = stack.pop(); pc = a === b ? jump() : pc + 3; break;
			case 0xa6: b = stack.pop(); a = stack.pop(); pc = a !== b ? jump() : pc + 3; break;
			case 0xa7: pc = jump(); break;
			case 0xa8: stack.push(pc + 3); pc = jump(); break;
			case 0xa9: pc = locals[bytes[pc + 1]]; break;
			case 0xaa: {
				i = stack.pop();
				off = (pc + 4) & ~3;
				var def = s4(off), lo = s4(off + 4), hi = s4(off + 8);
				pc = (i < lo || i > hi) ? pc + def : pc + s4(off + 12 + (i - lo) * 4);
				backCheck();
				break;
			}
			case 0xab: {
				i = stack.pop();
				off = (pc + 4) & ~3;
				var dflt = s4(off), np = s4(off + 4), target = dflt;
				for (n = 0; n < np; n++) if (s4(off + 8 + n * 8) === i) { target = s4(off + 12 + n * 8); break; }
				pc += target;
				backCheck();
				break;
			}
			case 0xac: case 0xae: case 0xb0: return stack.pop();
			case 0xad: case 0xaf: stack.pop(); return stack.pop();
			case 0xb1: return undefined;
			case 0xb2: case 0xb3: {
				e = cp[u2()];
				var fr = e.$f || (e.$f = resolveStatic(vm, e));
				if (fr.owner.initState !== 2) vm.initClass(fr.owner);
				if (op === 0xb2) {
					v = fr.missing ? defaultOf(e.desc) : fr.owner.statics[e.name];
					stack.push(v);
					if (isWide(e.desc)) stack.push(TOP);
				} else {
					if (isWide(e.desc)) stack.pop();
					v = stack.pop();
					if (!fr.missing) fr.owner.statics[e.name] = v;
				}
				pc += 3;
				break;
			}
			case 0xb4: {
				e = cp[u2()];
				o = stack.pop();
				if (o === null || o === undefined) vm.throwNew('java/lang/NullPointerException', 'reading ' + e.name);
				v = o[':' + e.name];
				if (v === undefined) v = typeof o === 'string' ? stringField(o, e.name) : defaultOf(e.desc);
				stack.push(v);
				if (isWide(e.desc)) stack.push(TOP);
				pc += 3;
				break;
			}
			case 0xb5: {
				e = cp[u2()];
				if (isWide(e.desc)) stack.pop();
				v = stack.pop();
				o = stack.pop();
				if (o === null || o === undefined) vm.throwNew('java/lang/NullPointerException', 'writing ' + e.name);
				if (e.desc === 'Z') v = v ? 1 : 0;
				o[':' + e.name] = v;
				pc += 3;
				break;
			}
			case 0xb6: case 0xb7: case 0xb8: case 0xb9: {
				e = cp[u2()];
				var sig = parseDesc(e.desc);
				var cargs = popArgs(sig);
				var target, recv = null;
				if (op === 0xb8) {
					target = e.$m || (e.$m = resolveStaticMethod(vm, e));
					if (target !== MISSING && target.cls.initState !== 2) vm.initClass(target.cls);
				} else {
					recv = stack.pop();
					if (recv === null || recv === undefined) vm.throwNew('java/lang/NullPointerException', 'calling ' + e.name);
					if (op === 0xb7) target = e.$m || (e.$m = resolveSpecial(vm, e));
					else {
						var rc = typeof recv === 'string' ? vm.loadClass('java/lang/String') : recv.cls;
						target = rc.findMethod(e.name + e.desc) || missing(vm, rc, e);
					}
				}
				v = target === MISSING ? defaultOf(sig.ret) : vm.invoke(target, recv, cargs);
				if (op === 0xb7 && recv !== null && typeof recv === 'object' && recv.$str !== undefined && recv.cls && recv.cls.name === 'java/lang/String') {
					var sv = recv.$str;
					for (var si = 0; si < stack.length; si++) if (stack[si] === recv) stack[si] = sv;
					for (var li = 0; li < locals.length; li++) if (locals[li] === recv) locals[li] = sv;
				}
				if (sig.ret !== 'V') {
					if (sig.ret === 'Z' && typeof v === 'boolean') v = v ? 1 : 0;
					stack.push(v === undefined ? defaultOf(sig.ret) : v);
					if (isWide(sig.ret)) stack.push(TOP);
				}
				pc += op === 0xb9 ? 5 : 3;
				break;
			}
			case 0xba: {
				e = cp[u2()];
				var site = (code.indy || (code.indy = {}))[pc] || (code.indy[pc] = JVM.linkIndy(vm, m.cls, e));
				var dsig = parseDesc(e.desc);
				var dargs = popArgs(dsig);
				v = site(dargs);
				if (dsig.ret !== 'V') {
					stack.push(v);
					if (isWide(dsig.ret)) stack.push(TOP);
				}
				pc += 5;
				break;
			}
			case 0xbb: {
				e = cp[u2()];
				var nc = e.$c || (e.$c = vm.loadClass(e.v));
				stack.push(vm.newObject(nc));
				pc += 3;
				break;
			}
			case 0xbc: n = stack.pop(); stack.push(vm.newArray(ARRAY_TYPES[bytes[pc + 1]], n)); pc += 2; break;
			case 0xbd: {
				e = cp[u2()];
				n = stack.pop();
				stack.push(vm.newArray(e.v[0] === '[' ? e.v : 'L' + e.v + ';', n));
				pc += 3;
				break;
			}
			case 0xbe: arr = stack.pop(); if (arr === null) vm.throwNew('java/lang/NullPointerException', 'array length'); stack.push(arr.a.length); pc++; break;
			case 0xbf: v = stack.pop(); if (v === null) vm.throwNew('java/lang/NullPointerException', 'throw null'); throw new JavaThrow(v);
			case 0xc0: {
				e = cp[u2()];
				v = stack[stack.length - 1];
				if (v !== null && v !== undefined) {
					var cc = e.$c || (e.$c = vm.loadClass(e.v));
					if (!vm.isInstance(v, cc)) vm.throwNew('java/lang/ClassCastException', vm.classOf(v).name.replace(/[/]/g, '.') + ' cannot be cast to ' + cc.name.replace(/[/]/g, '.'));
				}
				pc += 3;
				break;
			}
			case 0xc1: {
				e = cp[u2()];
				v = stack.pop();
				var ic = e.$c || (e.$c = vm.loadClass(e.v));
				stack.push(vm.isInstance(v, ic) ? 1 : 0);
				pc += 3;
				break;
			}
			case 0xc2: case 0xc3: stack.pop(); pc++; break;
			case 0xc4: {
				var wop = bytes[pc + 1];
				idx = (bytes[pc + 2] << 8) | bytes[pc + 3];
				switch (wop) {
				case 0x15: case 0x17: case 0x19: stack.push(locals[idx]); break;
				case 0x16: case 0x18: stack.push(locals[idx], TOP); break;
				case 0x36: case 0x38: case 0x3a: locals[idx] = stack.pop(); break;
				case 0x37: case 0x39: stack.pop(); locals[idx] = stack.pop(); locals[idx + 1] = TOP; break;
				case 0xa9: pc = locals[idx]; continue;
				case 0x84: locals[idx] = (locals[idx] + (((bytes[pc + 4] << 24) >> 16) | bytes[pc + 5])) | 0; pc += 6; continue;
				}
				pc += 4;
				break;
			}
			case 0xc5: {
				e = cp[u2()];
				var dims = bytes[pc + 3], counts = [];
				for (n = 0; n < dims; n++) counts.unshift(stack.pop());
				stack.push(multiArray(vm, e.v, counts, 0));
				pc += 4;
				break;
			}
			case 0xc6: v = stack.pop(); pc = (v === null || v === undefined) ? jump() : pc + 3; break;
			case 0xc7: v = stack.pop(); pc = (v !== null && v !== undefined) ? jump() : pc + 3; break;
			case 0xc8: pc += s4(pc + 1); backCheck(); break;
			case 0xc9: stack.push(pc + 5); pc += s4(pc + 1); break;
			default:
				vm.throwNew('java/lang/VerifyError', 'unknown opcode 0x' + op.toString(16) + ' in ' + m.cls.name + '.' + m.name);
			}
		}

		function u2() { return (bytes[pc + 1] << 8) | bytes[pc + 2]; }
		function s4(p) { return (bytes[p] << 24) | (bytes[p + 1] << 16) | (bytes[p + 2] << 8) | bytes[p + 3]; }
		function jump() {
			var t = pc + (((bytes[pc + 1] << 24) >> 16) | bytes[pc + 2]);
			if (t <= pc) backCheck();
			return t;
		}
		function backCheck() {
			if (++vm.steps > vm.maxSteps) { var err = new Error('stopped: ran too long'); err.vmStop = true; throw err; }
		}
		function popArgs(sig) {
			var t = sig.args, out = new Array(t.length);
			for (var k = t.length - 1; k >= 0; k--) {
				if (isWide(t[k])) stack.pop();
				out[k] = stack.pop();
			}
			return out;
		}
		function ldc(k) {
			var ce = cp[k];
			switch (ce.tag) {
			case 3: case 4: case 8: stack.push(ce.v); break;
			case 7: stack.push(vm.classObject(ce.$c || (ce.$c = vm.loadClass(ce.v)))); break;
			case 16: stack.push(JVM.methodType(vm, ce.d)); break;
			case 15: stack.push(JVM.methodHandle(vm, m.cls, ce)); break;
			default: stack.push(null);
			}
		}
	}

	function checkIndex(arr, i) {
		if (arr === null || arr === undefined) vm.throwNew('java/lang/NullPointerException', 'array access');
		if (i < 0 || i >= arr.a.length) vm.throwNew('java/lang/ArrayIndexOutOfBoundsException', 'Index ' + i + ' out of bounds for length ' + arr.a.length);
	}
}

function stringField(s, name) { return name === 'count' ? s.length : null; }

function multiArray(vm, type, counts, d) {
	var arr = vm.newArray(type.substring(1), counts[d]);
	if (d + 1 < counts.length) for (var i = 0; i < counts[d]; i++) arr.a[i] = multiArray(vm, type.substring(1), counts, d + 1);
	return arr;
}

function findHandler(vm, code, pc, ex) {
	var hs = code.handlers;
	for (var i = 0; i < hs.length; i++) {
		var h = hs[i];
		if (pc < h.start || pc >= h.end) continue;
		if (!h.type) return h.handler;
		var hc = h.$c || (h.$c = vm.loadClass(h.type));
		if (vm.isInstance(ex, hc)) return h.handler;
	}
	return -1;
}

var MISSING = { missing: true };
function missing(vm, c, e) {
	vm.missingMethod(c, e.name, e.desc);
	return MISSING;
}

function resolveStatic(vm, e) {
	var c = vm.loadClass(e.owner);
	var r = c.findField(e.name);
	if (r && r.f.static) return { owner: r.owner };
	if (!c.absent) vm.warnOnce('f:' + e.owner + '.' + e.name, 'not available here: ' + e.owner.replace(/[/]/g, '.') + '.' + e.name + ' (left unplugged)');
	if (c.absent) { c.fields[e.name] = { name: e.name, desc: e.desc, static: true }; c.statics[e.name] = defaultOf(e.desc); return { owner: c }; }
	return { owner: c, missing: true };
}
function resolveStaticMethod(vm, e) {
	var c = vm.loadClass(e.owner);
	return c.findDeclared(e.name + e.desc) || missing(vm, c, e);
}
function resolveSpecial(vm, e) {
	var c = vm.loadClass(e.owner);
	var m = c.findDeclared(e.name + e.desc);
	if (m) return m;
	if (e.name === '<init>') return NOOP_INIT;
	return missing(vm, c, e);
}
var NOOP_INIT = new JVM.JMethod({ name: '?' }, '<init>', '()V', JVM.ACC_PUBLIC);
NOOP_INIT.fn = function () { return undefined; };

function methodHandle(vm, fromCls, ce) {
	var cp = fromCls.cf.cp, ref = cp[ce.ref];
	var h = { kind: ce.kind, owner: ref.owner, name: ref.name, desc: ref.desc };
	var mh = new JVM.JObject(vm.loadClass('java/lang/invoke/MethodHandle'));
	mh.$h = h;
	var isField = ce.kind >= 1 && ce.kind <= 4;
	h.call = function (args) {
		var c = vm.loadClass(h.owner), sig = isField ? null : parseDesc(h.desc), m;
		switch (h.kind) {
		case 1: case 3: { var r = c.findField(h.name); vm.initClass(r ? r.owner : c); return r ? args[0][':' + h.name] : null; }
		case 2: case 4: { var r2 = c.findField(h.name); vm.initClass(r2 ? r2.owner : c); return r2 ? r2.owner.statics[h.name] : null; }
		case 6: vm.initClass(c); m = c.findDeclared(h.name + h.desc); return m ? vm.invoke(m, null, adapt(vm, args, sig)) : vm.missingMethod(c, h.name, h.desc);
		case 7: m = c.findDeclared(h.name + h.desc); return m ? vm.invoke(m, args[0], adapt(vm, args.slice(1), sig)) : vm.missingMethod(c, h.name, h.desc);
		case 8: {
			var o = vm.newObject(c);
			m = c.findDeclared('<init>' + h.desc);
			if (m) vm.invoke(m, o, adapt(vm, args, sig));
			return o;
		}
		default: {
			var recv = args[0];
			if (recv === null || recv === undefined) vm.throwNew('java/lang/NullPointerException', h.name);
			m = vm.classOf(recv).findMethod(h.name + h.desc);
			return m ? vm.invoke(m, recv, adapt(vm, args.slice(1), sig)) : vm.missingMethod(c, h.name, h.desc);
		}
		}
	};
	h.returns = isField ? ref.desc : parseDesc(ref.desc).ret;
	return mh;
}
function adapt(vm, args, sig) {
	var out = args.slice();
	for (var i = 0; i < sig.args.length && i < out.length; i++) {
		var t = sig.args[i], v = out[i];
		if (t.length === 1 && v !== null && typeof v === 'object' && v.$box !== undefined) out[i] = v.$box;
		else if (t.length !== 1 && (typeof v === 'number' || typeof v === 'bigint')) out[i] = JVM.box(vm, v, null);
	}
	return out;
}
function methodType(vm, desc) {
	var o = new JVM.JObject(vm.loadClass('java/lang/invoke/MethodType'));
	o.$desc = desc;
	return o;
}

function linkIndy(vm, cls, e) {
	var cf = cls.cf, cp = cf.cp;
	var bm = cf.bootstrap[e.bsm];
	var bref = cp[cp[bm.ref].ref];
	var owner = bref.owner, bname = bref.name;
	var bargs = bm.args.map(function (k) { return cp[k]; });
	var sig = parseDesc(e.desc);

	if (owner === 'java/lang/invoke/LambdaMetafactory') {
		var samDesc = bargs[0].d;
		var impl = methodHandle(vm, cls, bargs[1]).$h;
		var iface = vm.loadClass(JVM.typeToClassName(sig.ret));
		var extraIfaces = [], bridges = [];
		if (bname === 'altMetafactory' && bargs.length > 3) {
			var flags = bargs[3].v, k = 4;
			if (flags & 2) { var nm = bargs[k++].v; for (var q = 0; q < nm; q++) extraIfaces.push(vm.loadClass(bargs[k++].v)); }
			if (flags & 4) { var nb = bargs[k++].v; for (var q2 = 0; q2 < nb; q2++) bridges.push(bargs[k++].d); }
		}
		var lc = new JVM.JClass(vm, cls.name + '$$Lambda$' + e.name);
		lc.native = true;
		lc.initState = 2;
		lc.superClass = vm.loadClass('java/lang/Object');
		lc.interfaces = [iface].concat(extraIfaces);
		var samSig = parseDesc(samDesc);
		var callImpl = function (vm2, self, args) {
			var all = self.$captured.concat(args);
			var r = impl.call(all);
			if (samSig.ret.length !== 1 && impl.returns.length === 1 && impl.returns !== 'V' && r !== undefined) r = JVM.box(vm, r, impl.returns);
			else if (samSig.ret.length === 1 && r !== null && typeof r === 'object' && r.$box !== undefined) r = r.$box;
			return r;
		};
		[samDesc].concat(bridges).forEach(function (d) {
			var mm = new JVM.JMethod(lc, e.name, d, JVM.ACC_PUBLIC);
			mm.fn = callImpl;
			lc.methods[mm.key] = mm;
		});
		return function (args) {
			var o = new JVM.JObject(lc);
			o.$captured = args;
			return o;
		};
	}

	if (owner === 'java/lang/invoke/StringConcatFactory') {
		var types = sig.args;
		if (bname === 'makeConcatWithConstants') {
			var recipe = bargs[0].v, consts = bargs.slice(1).map(function (c) { return c.v; });
			return function (args) {
				var s = '', ai = 0, ci = 0;
				for (var i = 0; i < recipe.length; i++) {
					var ch = recipe.charCodeAt(i);
					if (ch === 1) { s += JVM.stringOf(vm, args[ai], types[ai]); ai++; }
					else if (ch === 2) s += JVM.stringOf(vm, consts[ci++], null);
					else s += recipe[i];
				}
				return s;
			};
		}
		return function (args) {
			var s = '';
			for (var i = 0; i < args.length; i++) s += JVM.stringOf(vm, args[i], types[i]);
			return s;
		};
	}

	if (owner === 'java/lang/runtime/ObjectMethods') {
		var names = bargs[1].v ? bargs[1].v.split(';') : [];
		var getters = bargs.slice(2).map(function (b) { return methodHandle(vm, cls, b).$h; });
		var simple = cls.name.substring(cls.name.lastIndexOf('/') + 1);
		simple = simple.substring(simple.lastIndexOf('$') + 1);
		if (e.name === 'toString') return function (args) {
			var r = args[0];
			return simple + '[' + names.map(function (nm, i) { return nm + '=' + JVM.stringOf(vm, getters[i].call([r]), getters[i].returns); }).join(', ') + ']';
		};
		if (e.name === 'hashCode') return function (args) {
			var h = 0, r = args[0];
			for (var i = 0; i < getters.length; i++) h = (Math.imul(h, 31) + JVM.hashOf(vm, getters[i].call([r]))) | 0;
			return h;
		};
		if (e.name === 'equals') return function (args) {
			var a = args[0], b = args[1];
			if (a === b) return 1;
			if (!b || b.cls !== a.cls) return 0;
			for (var i = 0; i < getters.length; i++) if (!JVM.equalsOf(vm, getters[i].call([a]), getters[i].call([b]))) return 0;
			return 1;
		};
	}

	vm.warnOnce('indy:' + owner + '.' + bname, 'not available here: invokedynamic ' + owner.replace(/[/]/g, '.') + '.' + bname + ' (left unplugged)');
	return function () { return defaultOf(sig.ret); };
}

JVM.interpret = interpret;
JVM.linkIndy = linkIndy;
JVM.methodHandle = methodHandle;
JVM.methodType = methodType;
JVM.f2i = f2i;
JVM.f2l = f2l;
})();

(function () {
'use strict';

var JObject = JVM.JObject, JArray = JVM.JArray, JavaThrow = JVM.JavaThrow;

function stringHash(s) {
	var h = 0;
	for (var i = 0; i < s.length; i++) h = (Math.imul(h, 31) + s.charCodeAt(i)) | 0;
	return h;
}

function javaDouble(d, isFloat) {
	if (d !== d) return 'NaN';
	if (d === Infinity) return 'Infinity';
	if (d === -Infinity) return '-Infinity';
	if (d === 0) return 1 / d < 0 ? '-0.0' : '0.0';
	var s;
	if (isFloat) {
		for (var p = 1; p <= 9; p++) { s = d.toPrecision(p); if (Math.fround(parseFloat(s)) === d) break; }
		d = parseFloat(s);
	}
	var a = Math.abs(d);
	if (a >= 1e-3 && a < 1e7) {
		s = String(d);
		if (s.indexOf('e') >= 0) s = d.toFixed(20).replace(/0+$/, '');
		if (s.indexOf('.') < 0) s += '.0';
		return s;
	}
	s = d.toExponential();
	var m = s.split('e'), mant = m[0], ex = parseInt(m[1], 10);
	if (mant.indexOf('.') < 0) mant += '.0';
	return mant + 'E' + ex;
}

function stringOf(vm, v, t) {
	if (t === 'C') return String.fromCharCode(v);
	if (t === 'Z') return v ? 'true' : 'false';
	if (t === 'F') return javaDouble(v, true);
	if (t === 'D') return javaDouble(v, false);
	if (v === null || v === undefined) return 'null';
	if (typeof v === 'string') return v;
	if (typeof v === 'bigint') return v.toString();
	if (typeof v === 'number') return String(v);
	return vm.toJavaString(v);
}

function hashOf(vm, v) {
	if (v === null || v === undefined) return 0;
	if (typeof v === 'string') return stringHash(v);
	if (typeof v === 'number') return v | 0;
	if (typeof v === 'bigint') return Number(BigInt.asIntN(32, v ^ (v >> 32n)));
	return vm.callVirtual(v, 'hashCode', '()I', []) | 0;
}
function equalsOf(vm, a, b) {
	if (a === b) return true;
	if (a === null || a === undefined || b === null || b === undefined) return false;
	if (typeof a === 'string' || typeof a !== 'object') return a === b;
	return !!vm.callVirtual(a, 'equals', '(Ljava/lang/Object;)Z', [b]);
}

var BOX_CLASS = { I: 'java/lang/Integer', J: 'java/lang/Long', F: 'java/lang/Float', D: 'java/lang/Double',
                  Z: 'java/lang/Boolean', C: 'java/lang/Character', S: 'java/lang/Short', B: 'java/lang/Byte' };
function box(vm, v, t) {
	if (!t) t = typeof v === 'bigint' ? 'J' : (Number.isInteger(v) && v >= -2147483648 && v <= 2147483647 ? 'I' : 'D');
	var cname = BOX_CLASS[t];
	if (!cname) return v;
	var cache = vm.boxCache || (vm.boxCache = {});
	var small = (t === 'I' || t === 'S' || t === 'B' || t === 'J' || t === 'C') && v >= -128 && v <= 127 || t === 'Z';
	var key = t + v;
	if (small && cache[key]) return cache[key];
	var o = new JObject(vm.loadClass(cname));
	o.$box = t === 'Z' ? (v ? 1 : 0) : v;
	if (small) cache[key] = o;
	return o;
}
function unbox(v) { return v !== null && typeof v === 'object' && v.$box !== undefined ? v.$box : v; }

function javaArray(vm, elemDesc, values) {
	var a = vm.newArray(elemDesc, values.length);
	for (var i = 0; i < values.length; i++) a.a[i] = values[i];
	return a;
}

var reCache = {};
function javaRegex(p, flags) {
	var key = p + '/' + (flags || '');
	if (reCache[key]) return reCache[key];
	var js = p.replace(/\\p\{Alpha\}/g, '[A-Za-z]').replace(/\\p\{Digit\}/g, '[0-9]').replace(/\\p\{Alnum\}/g, '[A-Za-z0-9]')
	          .replace(/\\p\{Upper\}/g, '[A-Z]').replace(/\\p\{Lower\}/g, '[a-z]').replace(/\\p\{Punct\}/g, '[!-\\/:-@\\[-`{-~]')
	          .replace(/\\p\{Space\}/g, '\\s').replace(/([*+?}])\+/g, '$1').replace(/\(\?>/g, '(?:');
	return (reCache[key] = new RegExp(js, flags || ''));
}
function javaSplit(s, regex, limit) {
	var parts;
	if (regex.length === 1 && '.$|()[{^?*+\\'.indexOf(regex) < 0) parts = s.split(regex);
	else parts = s.split(javaRegex(regex, 'g'));
	if (limit > 0 && parts.length > limit) {
		var re = javaRegex(regex, 'g'), out = [], last = 0, mm, count = 0;
		while (count < limit - 1 && (mm = re.exec(s))) {
			if (mm[0].length === 0 && mm.index === 0) { re.lastIndex++; continue; }
			out.push(s.substring(last, mm.index)); last = mm.index + mm[0].length; count++;
			if (mm[0].length === 0) re.lastIndex++;
		}
		out.push(s.substring(last));
		return out;
	}
	if (parts.length > 1 && parts[0] === '' && s.length > 0) {
		var z = javaRegex(regex, '').exec(s);
		if (z && z.index === 0 && z[0].length === 0) parts.shift();
	}
	if (!limit) while (parts.length > 1 && parts[parts.length - 1] === '') parts.pop();
	if (s === '') return [''];
	return parts;
}

function javaFormat(vm, fmt, args) {
	var ai = 0;
	return fmt.replace(/%(\d+\$)?([-#+ 0,(]*)(\d+)?(\.\d+)?([a-zA-Z%])/g, function (all, pos, flags, width, prec, conv) {
		if (conv === '%') return '%';
		if (conv === 'n') return '\n';
		var v = pos ? args[parseInt(pos, 10) - 1] : args[ai++];
		if (v !== null && typeof v === 'object' && v.cls && (v.cls.name === 'java/lang/Boolean' || v.cls.name === 'java/lang/Character') && conv.toLowerCase() !== 'c')
			v = v.cls.name === 'java/lang/Boolean' ? (v.$box ? 'true' : 'false') : String.fromCharCode(v.$box);
		v = unbox(v);
		var s;
		switch (conv.toLowerCase()) {
		case 'd':
			s = typeof v === 'bigint' ? v.toString() : String(Math.trunc(Number(v)));
			if (flags.indexOf(',') >= 0) s = s.replace(/\B(?=(\d{3})+(?!\d))/g, ',');
			if (flags.indexOf('+') >= 0 && s[0] !== '-') s = '+' + s;
			break;
		case 'f': s = Number(v).toFixed(prec ? parseInt(prec.substring(1), 10) : 6); break;
		case 'e': s = Number(v).toExponential(prec ? parseInt(prec.substring(1), 10) : 6).replace(/e([+-])(\d)$/, 'e$10$2'); break;
		case 'x': s = (typeof v === 'bigint' ? BigInt.asUintN(64, v) : (Number(v) >>> 0)).toString(16); break;
		case 'o': s = (Number(v) >>> 0).toString(8); break;
		case 'c': s = typeof v === 'number' ? String.fromCharCode(v) : stringOf(vm, v, null); break;
		case 'b': s = v === null || v === undefined ? 'false' : (typeof v === 'number' ? (v ? 'true' : 'false') : 'true'); break;
		default: s = stringOf(vm, v, null); if (prec) s = s.substring(0, parseInt(prec.substring(1), 10));
		}
		if (conv !== conv.toLowerCase()) s = s.toUpperCase();
		if (width) {
			var w = parseInt(width, 10);
			while (s.length < w) s = flags.indexOf('-') >= 0 ? s + ' ' : (flags.indexOf('0') >= 0 && /[dfx]/i.test(conv) ? (s[0] === '-' ? '-0' + s.substring(1) : '0' + s) : ' ' + s);
		}
		return s;
	});
}

function utf8Bytes(vm, s) {
	var u = new TextEncoder().encode(s);
	var a = vm.newArray('B', u.length);
	a.a.set(new Int8Array(u.buffer, u.byteOffset, u.length));
	return a;
}
function utf8String(arr, off, len) {
	var b = new Uint8Array(arr.a.buffer, arr.a.byteOffset + (off || 0), len == null ? arr.a.length - (off || 0) : len);
	return new TextDecoder().decode(b);
}

function npe(vm, what) { vm.throwNew('java/lang/NullPointerException', what); }
function str(vm, v) { return v === null || v === undefined ? 'null' : stringOf(vm, v, null); }

function installLang(vm) {
	var def = function (n, s) { vm.defineNative(n, s); };
	var I = JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC;

	def('java/lang/Object', {
		methods: {
			'<init>()V': function () {},
			'hashCode()I': function (vm, self) { return vm.identityHash(self); },
			'equals(Ljava/lang/Object;)Z': function (vm, self, a) { return self === a[0] ? 1 : 0; },
			'toString()Ljava/lang/String;': function (vm, self) {
				return vm.classOf(self).name.replace(/[/]/g, '.') + '@' + (vm.callVirtual(self, 'hashCode', '()I', []) >>> 0).toString(16);
			},
			'getClass()Ljava/lang/Class;': function (vm, self) { return vm.classObject(vm.classOf(self)); },
			'clone()Ljava/lang/Object;': function (vm, self) {
				if (self instanceof JArray) return new JArray(self.cls, self.a.slice());
				var o = new JObject(self.cls);
				for (var k in self) if (k !== '$hash' && Object.prototype.hasOwnProperty.call(self, k)) o[k] = self[k];
				return o;
			},
			'notify()V': function () {}, 'notifyAll()V': function () {}, 'wait()V': function () {},
			'wait(J)V': function () {}, 'wait(JI)V': function () {}, 'finalize()V': function () {},
		},
	});

	['java/lang/Runnable:run()V', 'java/lang/Comparable:compareTo(Ljava/lang/Object;)I',
	 'java/lang/Iterable:iterator()Ljava/util/Iterator;', 'java/lang/AutoCloseable:close()V',
	 'java/lang/Cloneable:', 'java/io/Serializable:', 'java/lang/Appendable:',
	 'java/lang/CharSequence:length()I'].forEach(function (s) {
		var p = s.split(':'), abs = {};
		if (p[1]) abs[p[1]] = true;
		def(p[0], { access: I, abstractMethods: abs, super: 'java/lang/Object' });
	});

	var S = function (f) { return function (vm, self, a) { return f(self, a, vm); }; };
	def('java/lang/String', {
		interfaces: ['java/lang/CharSequence', 'java/lang/Comparable', 'java/io/Serializable'],
		methods: {
			'<init>()V': function (vm, self) { self.$str = ''; },
			'<init>(Ljava/lang/String;)V': function (vm, self, a) { self.$str = a[0]; },
			'<init>([C)V': function (vm, self, a) { self.$str = vm.stringFromChars(a[0]); },
			'<init>([CII)V': function (vm, self, a) { self.$str = vm.stringFromChars(a[0], a[1], a[2]); },
			'<init>([B)V': function (vm, self, a) { self.$str = utf8String(a[0]); },
			'<init>([BII)V': function (vm, self, a) { self.$str = utf8String(a[0], a[1], a[2]); },
			'<init>([BLjava/lang/String;)V': function (vm, self, a) { self.$str = utf8String(a[0]); },
			'<init>([BLjava/nio/charset/Charset;)V': function (vm, self, a) { self.$str = utf8String(a[0]); },
			'<init>(Ljava/lang/StringBuilder;)V': function (vm, self, a) { self.$str = a[0].$s; },
			'<init>(Ljava/lang/StringBuffer;)V': function (vm, self, a) { self.$str = a[0].$s; },
			'length()I': S(function (s) { return s.length; }),
			'isEmpty()Z': S(function (s) { return s.length === 0 ? 1 : 0; }),
			'isBlank()Z': S(function (s) { return s.trim().length === 0 ? 1 : 0; }),
			'charAt(I)C': S(function (s, a, vm) {
				if (a[0] < 0 || a[0] >= s.length) vm.throwNew('java/lang/StringIndexOutOfBoundsException', 'index ' + a[0]);
				return s.charCodeAt(a[0]);
			}),
			'codePointAt(I)I': S(function (s, a) { return s.codePointAt(a[0]); }),
			'equals(Ljava/lang/Object;)Z': S(function (s, a) { return s === a[0] ? 1 : 0; }),
			'equalsIgnoreCase(Ljava/lang/String;)Z': S(function (s, a) { return a[0] !== null && s.toLowerCase() === a[0].toLowerCase() ? 1 : 0; }),
			'hashCode()I': S(function (s) { return stringHash(s); }),
			'compareTo(Ljava/lang/String;)I': S(compareStrings),
			'compareTo(Ljava/lang/Object;)I': S(compareStrings),
			'compareToIgnoreCase(Ljava/lang/String;)I': S(function (s, a) { return compareStrings(s.toLowerCase(), [a[0].toLowerCase()]); }),
			'indexOf(I)I': S(function (s, a) { return s.indexOf(String.fromCharCode(a[0])); }),
			'indexOf(II)I': S(function (s, a) { return s.indexOf(String.fromCharCode(a[0]), Math.max(0, a[1])); }),
			'indexOf(Ljava/lang/String;)I': S(function (s, a) { return s.indexOf(a[0]); }),
			'indexOf(Ljava/lang/String;I)I': S(function (s, a) { return s.indexOf(a[0], Math.max(0, a[1])); }),
			'lastIndexOf(I)I': S(function (s, a) { return s.lastIndexOf(String.fromCharCode(a[0])); }),
			'lastIndexOf(II)I': S(function (s, a) { return s.lastIndexOf(String.fromCharCode(a[0]), a[1]); }),
			'lastIndexOf(Ljava/lang/String;)I': S(function (s, a) { return s.lastIndexOf(a[0]); }),
			'lastIndexOf(Ljava/lang/String;I)I': S(function (s, a) { return s.lastIndexOf(a[0], a[1]); }),
			'substring(I)Ljava/lang/String;': S(function (s, a, vm) {
				if (a[0] < 0 || a[0] > s.length) vm.throwNew('java/lang/StringIndexOutOfBoundsException', 'begin ' + a[0] + ', length ' + s.length);
				return s.substring(a[0]);
			}),
			'substring(II)Ljava/lang/String;': S(function (s, a, vm) {
				if (a[0] < 0 || a[1] > s.length || a[0] > a[1]) vm.throwNew('java/lang/StringIndexOutOfBoundsException', 'begin ' + a[0] + ', end ' + a[1] + ', length ' + s.length);
				return s.substring(a[0], a[1]);
			}),
			'subSequence(II)Ljava/lang/CharSequence;': S(function (s, a) { return s.substring(a[0], a[1]); }),
			'startsWith(Ljava/lang/String;)Z': S(function (s, a) { return s.startsWith(a[0]) ? 1 : 0; }),
			'startsWith(Ljava/lang/String;I)Z': S(function (s, a) { return s.startsWith(a[0], a[1]) ? 1 : 0; }),
			'endsWith(Ljava/lang/String;)Z': S(function (s, a) { return s.endsWith(a[0]) ? 1 : 0; }),
			'contains(Ljava/lang/CharSequence;)Z': S(function (s, a, vm) { return s.indexOf(str(vm, a[0])) >= 0 ? 1 : 0; }),
			'replace(CC)Ljava/lang/String;': S(function (s, a) { return s.split(String.fromCharCode(a[0])).join(String.fromCharCode(a[1])); }),
			'replace(Ljava/lang/CharSequence;Ljava/lang/CharSequence;)Ljava/lang/String;': S(function (s, a, vm) { return s.split(str(vm, a[0])).join(str(vm, a[1])); }),
			'replaceAll(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;': S(function (s, a) { return s.replace(javaRegex(a[0], 'g'), a[1].replace(/\$(\d)/g, '$$$1')); }),
			'replaceFirst(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;': S(function (s, a) { return s.replace(javaRegex(a[0], ''), a[1]); }),
			'matches(Ljava/lang/String;)Z': S(function (s, a) { return javaRegex('^(?:' + a[0] + ')$', '').test(s) ? 1 : 0; }),
			'split(Ljava/lang/String;)[Ljava/lang/String;': S(function (s, a, vm) { return javaArray(vm, 'Ljava/lang/String;', javaSplit(s, a[0], 0)); }),
			'split(Ljava/lang/String;I)[Ljava/lang/String;': S(function (s, a, vm) { return javaArray(vm, 'Ljava/lang/String;', javaSplit(s, a[0], a[1])); }),
			'toLowerCase()Ljava/lang/String;': S(function (s) { return s.toLowerCase(); }),
			'toLowerCase(Ljava/util/Locale;)Ljava/lang/String;': S(function (s) { return s.toLowerCase(); }),
			'toUpperCase()Ljava/lang/String;': S(function (s) { return s.toUpperCase(); }),
			'toUpperCase(Ljava/util/Locale;)Ljava/lang/String;': S(function (s) { return s.toUpperCase(); }),
			'trim()Ljava/lang/String;': S(function (s) { return s.replace(/^[\x00-\x20]+|[\x00-\x20]+$/g, ''); }),
			'strip()Ljava/lang/String;': S(function (s) { return s.trim(); }),
			'concat(Ljava/lang/String;)Ljava/lang/String;': S(function (s, a) { return s + a[0]; }),
			'repeat(I)Ljava/lang/String;': S(function (s, a) { return s.repeat(a[0]); }),
			'toCharArray()[C': S(function (s, a, vm) { return vm.charArray(s); }),
			'getBytes()[B': S(function (s, a, vm) { return utf8Bytes(vm, s); }),
			'getBytes(Ljava/lang/String;)[B': S(function (s, a, vm) { return utf8Bytes(vm, s); }),
			'getBytes(Ljava/nio/charset/Charset;)[B': S(function (s, a, vm) { return utf8Bytes(vm, s); }),
			'getChars(II[CI)V': S(function (s, a) { for (var i = a[0]; i < a[1]; i++) a[2].a[a[3] + i - a[0]] = s.charCodeAt(i); }),
			'toString()Ljava/lang/String;': S(function (s) { return s; }),
			'intern()Ljava/lang/String;': S(function (s) { return s; }),
		},
		staticMethods: {
			'valueOf(Ljava/lang/Object;)Ljava/lang/String;': function (vm, n, a) { return str(vm, a[0]); },
			'valueOf(I)Ljava/lang/String;': function (vm, n, a) { return String(a[0]); },
			'valueOf(J)Ljava/lang/String;': function (vm, n, a) { return a[0].toString(); },
			'valueOf(F)Ljava/lang/String;': function (vm, n, a) { return javaDouble(a[0], true); },
			'valueOf(D)Ljava/lang/String;': function (vm, n, a) { return javaDouble(a[0], false); },
			'valueOf(Z)Ljava/lang/String;': function (vm, n, a) { return a[0] ? 'true' : 'false'; },
			'valueOf(C)Ljava/lang/String;': function (vm, n, a) { return String.fromCharCode(a[0]); },
			'valueOf([C)Ljava/lang/String;': function (vm, n, a) { return vm.stringFromChars(a[0]); },
			'copyValueOf([C)Ljava/lang/String;': function (vm, n, a) { return vm.stringFromChars(a[0]); },
			'format(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;': function (vm, n, a) { return javaFormat(vm, a[0], a[1] ? Array.prototype.slice.call(a[1].a) : []); },
			'format(Ljava/util/Locale;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;': function (vm, n, a) { return javaFormat(vm, a[1], a[2] ? Array.prototype.slice.call(a[2].a) : []); },
			'join(Ljava/lang/CharSequence;[Ljava/lang/CharSequence;)Ljava/lang/String;': function (vm, n, a) {
				return Array.prototype.map.call(a[1].a, function (x) { return str(vm, x); }).join(str(vm, a[0]));
			},
			'join(Ljava/lang/CharSequence;Ljava/lang/Iterable;)Ljava/lang/String;': function (vm, n, a) {
				return JVM.iterate(vm, a[1]).map(function (x) { return str(vm, x); }).join(str(vm, a[0]));
			},
		},
	});
	function compareStrings(s, a) {
		var t = a[0], n = Math.min(s.length, t.length);
		for (var i = 0; i < n; i++) { var d = s.charCodeAt(i) - t.charCodeAt(i); if (d) return d; }
		return s.length - t.length;
	}

	var sbAppend = function (conv) { return function (vm, self, a) { self.$s += conv(vm, a); return self; }; };
	var sbSpec = function () {
		return {
			interfaces: ['java/lang/CharSequence', 'java/lang/Appendable'],
			methods: {
				'<init>()V': function (vm, self) { self.$s = ''; },
				'<init>(I)V': function (vm, self) { self.$s = ''; },
				'<init>(Ljava/lang/String;)V': function (vm, self, a) { self.$s = a[0] === null ? npe(vm, 'StringBuilder') : a[0]; },
				'<init>(Ljava/lang/CharSequence;)V': function (vm, self, a) { self.$s = str(vm, a[0]); },
				'append(Ljava/lang/String;)': null,
				'length()I': function (vm, self) { return self.$s.length; },
				'charAt(I)C': function (vm, self, a) { return self.$s.charCodeAt(a[0]); },
				'toString()Ljava/lang/String;': function (vm, self) { return self.$s; },
				'setLength(I)V': function (vm, self, a) { var s = self.$s; self.$s = a[0] <= s.length ? s.substring(0, a[0]) : s + '\0'.repeat(a[0] - s.length); },
				'setCharAt(IC)V': function (vm, self, a) { var s = self.$s; self.$s = s.substring(0, a[0]) + String.fromCharCode(a[1]) + s.substring(a[0] + 1); },
				'indexOf(Ljava/lang/String;)I': function (vm, self, a) { return self.$s.indexOf(a[0]); },
				'lastIndexOf(Ljava/lang/String;)I': function (vm, self, a) { return self.$s.lastIndexOf(a[0]); },
				'substring(I)Ljava/lang/String;': function (vm, self, a) { return self.$s.substring(a[0]); },
				'substring(II)Ljava/lang/String;': function (vm, self, a) { return self.$s.substring(a[0], a[1]); },
				'capacity()I': function (vm, self) { return self.$s.length + 16; },
				'ensureCapacity(I)V': function () {},
				'trimToSize()V': function () {},
			},
		};
	};
	['java/lang/StringBuilder', 'java/lang/StringBuffer'].forEach(function (name) {
		var spec = sbSpec(), m = spec.methods, R = 'L' + name + ';';
		delete m['append(Ljava/lang/String;)'];
		m['append(Ljava/lang/String;)' + R] = sbAppend(function (vm, a) { return str(vm, a[0]); });
		m['append(Ljava/lang/Object;)' + R] = sbAppend(function (vm, a) { return str(vm, a[0]); });
		m['append(Ljava/lang/CharSequence;)' + R] = sbAppend(function (vm, a) { return str(vm, a[0]); });
		m['append(Ljava/lang/CharSequence;II)' + R] = sbAppend(function (vm, a) { return str(vm, a[0]).substring(a[1], a[2]); });
		m['append(Ljava/lang/StringBuffer;)' + R] = sbAppend(function (vm, a) { return str(vm, a[0]); });
		m['append(I)' + R] = sbAppend(function (vm, a) { return String(a[0]); });
		m['append(J)' + R] = sbAppend(function (vm, a) { return a[0].toString(); });
		m['append(F)' + R] = sbAppend(function (vm, a) { return javaDouble(a[0], true); });
		m['append(D)' + R] = sbAppend(function (vm, a) { return javaDouble(a[0], false); });
		m['append(C)' + R] = sbAppend(function (vm, a) { return String.fromCharCode(a[0]); });
		m['append(Z)' + R] = sbAppend(function (vm, a) { return a[0] ? 'true' : 'false'; });
		m['append([C)' + R] = sbAppend(function (vm, a) { return vm.stringFromChars(a[0]); });
		m['append([CII)' + R] = sbAppend(function (vm, a) { return vm.stringFromChars(a[0], a[1], a[2]); });
		m['append(C)Ljava/lang/Appendable;'] = m['append(C)' + R];
		m['append(Ljava/lang/CharSequence;)Ljava/lang/Appendable;'] = m['append(Ljava/lang/CharSequence;)' + R];
		var ins = function (conv) { return function (vm, self, a) { var s = self.$s; self.$s = s.substring(0, a[0]) + conv(vm, a[1]) + s.substring(a[0]); return self; }; };
		m['insert(ILjava/lang/String;)' + R] = ins(function (vm, v) { return str(vm, v); });
		m['insert(ILjava/lang/Object;)' + R] = ins(function (vm, v) { return str(vm, v); });
		m['insert(IC)' + R] = ins(function (vm, v) { return String.fromCharCode(v); });
		m['insert(II)' + R] = ins(function (vm, v) { return String(v); });
		m['reverse()' + R] = function (vm, self) { self.$s = self.$s.split('').reverse().join(''); return self; };
		m['deleteCharAt(I)' + R] = function (vm, self, a) { var s = self.$s; self.$s = s.substring(0, a[0]) + s.substring(a[0] + 1); return self; };
		m['delete(II)' + R] = function (vm, self, a) { var s = self.$s; self.$s = s.substring(0, a[0]) + s.substring(Math.min(a[1], s.length)); return self; };
		m['replace(IILjava/lang/String;)' + R] = function (vm, self, a) { var s = self.$s; self.$s = s.substring(0, a[0]) + a[2] + s.substring(Math.min(a[1], s.length)); return self; };
		def(name, spec);
	});

	var numBox = function (cname, t, extra) {
		var m = {
			['<init>(' + t + ')V']: function (vm, self, a) { self.$box = a[0]; },
			'intValue()I': function (vm, self) { return typeof self.$box === 'bigint' ? Number(BigInt.asIntN(32, self.$box)) : JVM.f2i(self.$box); },
			'longValue()J': function (vm, self) { return typeof self.$box === 'bigint' ? self.$box : JVM.f2l(self.$box); },
			'floatValue()F': function (vm, self) { return Math.fround(Number(self.$box)); },
			'doubleValue()D': function (vm, self) { return Number(self.$box); },
			'shortValue()S': function (vm, self) { return (Number(self.$box) << 16) >> 16; },
			'byteValue()B': function (vm, self) { return (Number(self.$box) << 24) >> 24; },
			'hashCode()I': function (vm, self) { return hashOf(vm, self.$box); },
			'equals(Ljava/lang/Object;)Z': function (vm, self, a) { return a[0] && a[0].cls === self.cls && (a[0].$box === self.$box || (self.$box !== self.$box && a[0].$box !== a[0].$box)) ? 1 : 0; },
			'toString()Ljava/lang/String;': function (vm, self) { return stringOf(vm, self.$box, t); },
			'compareTo(Ljava/lang/Object;)I': function (vm, self, a) { return self.$box < a[0].$box ? -1 : self.$box > a[0].$box ? 1 : 0; },
		};
		m['compareTo(L' + cname + ';)I'] = m['compareTo(Ljava/lang/Object;)I'];
		var st = {};
		st['valueOf(' + t + ')L' + cname + ';'] = function (vm, n, a) { return box(vm, a[0], t); };
		st['toString(' + t + ')Ljava/lang/String;'] = function (vm, n, a) { return stringOf(vm, a[0], t); };
		st['compare(' + t + t + ')I'] = function (vm, n, a) { return a[0] < a[1] ? -1 : a[0] > a[1] ? 1 : 0; };
		for (var k in extra || {}) st[k] = extra[k];
		def(cname, { super: 'java/lang/Number', interfaces: ['java/lang/Comparable'], methods: m, staticMethods: st, fields: {} });
	};
	def('java/lang/Number', { access: JVM.ACC_PUBLIC | JVM.ACC_ABSTRACT, methods: { '<init>()V': function () {} } });
	var parseIntJ = function (vm, s, radix) {
		if (s === null) vm.throwNew('java/lang/NumberFormatException', 'null');
		var t = s.trim() === s ? s : null;
		var re = radix === 16 ? /^[+-]?[0-9a-fA-F]+$/ : radix === 2 ? /^[+-]?[01]+$/ : radix === 8 ? /^[+-]?[0-7]+$/ : /^[+-]?\d+$/;
		if (t === null || !re.test(s)) vm.throwNew('java/lang/NumberFormatException', 'For input string: "' + s + '"');
		return parseInt(s, radix || 10);
	};
	numBox('java/lang/Integer', 'I', {
		'parseInt(Ljava/lang/String;)I': function (vm, n, a) {
			var v = parseIntJ(vm, a[0], 10);
			if (v > 2147483647 || v < -2147483648) vm.throwNew('java/lang/NumberFormatException', 'For input string: "' + a[0] + '"');
			return v;
		},
		'parseInt(Ljava/lang/String;I)I': function (vm, n, a) { return parseIntJ(vm, a[0], a[1]) | 0; },
		'valueOf(Ljava/lang/String;)Ljava/lang/Integer;': function (vm, n, a) { return box(vm, parseIntJ(vm, a[0], 10) | 0, 'I'); },
		'valueOf(Ljava/lang/String;I)Ljava/lang/Integer;': function (vm, n, a) { return box(vm, parseIntJ(vm, a[0], a[1]) | 0, 'I'); },
		'toHexString(I)Ljava/lang/String;': function (vm, n, a) { return (a[0] >>> 0).toString(16); },
		'toBinaryString(I)Ljava/lang/String;': function (vm, n, a) { return (a[0] >>> 0).toString(2); },
		'toOctalString(I)Ljava/lang/String;': function (vm, n, a) { return (a[0] >>> 0).toString(8); },
		'toString(II)Ljava/lang/String;': function (vm, n, a) { return a[0].toString(a[1]); },
		'bitCount(I)I': function (vm, n, a) { var v = a[0] >>> 0, c = 0; while (v) { c += v & 1; v >>>= 1; } return c; },
		'numberOfLeadingZeros(I)I': function (vm, n, a) { return Math.clz32(a[0]); },
		'numberOfTrailingZeros(I)I': function (vm, n, a) { var v = a[0]; if (v === 0) return 32; var c = 0; while (!(v & 1)) { v >>>= 1; c++; } return c; },
		'highestOneBit(I)I': function (vm, n, a) { return a[0] === 0 ? 0 : (0x80000000 >>> Math.clz32(a[0])) | 0; },
		'signum(I)I': function (vm, n, a) { return a[0] > 0 ? 1 : a[0] < 0 ? -1 : 0; },
		'reverse(I)I': function (vm, n, a) { var v = a[0], r = 0; for (var i = 0; i < 32; i++) { r = (r << 1) | (v & 1); v >>>= 1; } return r | 0; },
		'max(II)I': function (vm, n, a) { return Math.max(a[0], a[1]); },
		'min(II)I': function (vm, n, a) { return Math.min(a[0], a[1]); },
		'sum(II)I': function (vm, n, a) { return (a[0] + a[1]) | 0; },
		'hashCode(I)I': function (vm, n, a) { return a[0]; },
	});
	numBox('java/lang/Long', 'J', {
		'parseLong(Ljava/lang/String;)J': function (vm, n, a) {
			if (a[0] === null || !/^[+-]?\d+$/.test(a[0])) vm.throwNew('java/lang/NumberFormatException', 'For input string: "' + a[0] + '"');
			return BigInt.asIntN(64, BigInt(a[0]));
		},
		'valueOf(Ljava/lang/String;)Ljava/lang/Long;': function (vm, n, a) { return box(vm, BigInt.asIntN(64, BigInt(a[0])), 'J'); },
		'toHexString(J)Ljava/lang/String;': function (vm, n, a) { return BigInt.asUintN(64, a[0]).toString(16); },
		'hashCode(J)I': function (vm, n, a) { return hashOf(vm, a[0]); },
	});
	numBox('java/lang/Short', 'S', { 'parseShort(Ljava/lang/String;)S': function (vm, n, a) { return (parseIntJ(vm, a[0], 10) << 16) >> 16; } });
	numBox('java/lang/Byte', 'B', { 'parseByte(Ljava/lang/String;)B': function (vm, n, a) { return (parseIntJ(vm, a[0], 10) << 24) >> 24; } });
	var parseFloatJ = function (vm, s) {
		var t = s === null ? '' : s.trim().replace(/[fFdD]$/, '');
		if (!/^[+-]?(NaN|Infinity|(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?)$/.test(t)) vm.throwNew('java/lang/NumberFormatException', 'For input string: "' + s + '"');
		return parseFloat(t);
	};
	numBox('java/lang/Float', 'F', {
		'parseFloat(Ljava/lang/String;)F': function (vm, n, a) { return Math.fround(parseFloatJ(vm, a[0])); },
		'valueOf(Ljava/lang/String;)Ljava/lang/Float;': function (vm, n, a) { return box(vm, Math.fround(parseFloatJ(vm, a[0])), 'F'); },
		'isNaN(F)Z': function (vm, n, a) { return a[0] !== a[0] ? 1 : 0; },
		'isInfinite(F)Z': function (vm, n, a) { return Math.abs(a[0]) === Infinity ? 1 : 0; },
		'floatToIntBits(F)I': function (vm, n, a) { var dv = new DataView(new ArrayBuffer(4)); dv.setFloat32(0, a[0]); return dv.getInt32(0); },
		'floatToRawIntBits(F)I': function (vm, n, a) { var dv = new DataView(new ArrayBuffer(4)); dv.setFloat32(0, a[0]); return dv.getInt32(0); },
		'intBitsToFloat(I)F': function (vm, n, a) { var dv = new DataView(new ArrayBuffer(4)); dv.setInt32(0, a[0]); return dv.getFloat32(0); },
		'max(FF)F': function (vm, n, a) { return Math.max(a[0], a[1]); },
		'min(FF)F': function (vm, n, a) { return Math.min(a[0], a[1]); },
	});
	numBox('java/lang/Double', 'D', {
		'parseDouble(Ljava/lang/String;)D': function (vm, n, a) { return parseFloatJ(vm, a[0]); },
		'valueOf(Ljava/lang/String;)Ljava/lang/Double;': function (vm, n, a) { return box(vm, parseFloatJ(vm, a[0]), 'D'); },
		'isNaN(D)Z': function (vm, n, a) { return a[0] !== a[0] ? 1 : 0; },
		'isInfinite(D)Z': function (vm, n, a) { return Math.abs(a[0]) === Infinity ? 1 : 0; },
		'doubleToLongBits(D)J': function (vm, n, a) { var dv = new DataView(new ArrayBuffer(8)); dv.setFloat64(0, a[0]); return dv.getBigInt64(0); },
		'doubleToRawLongBits(D)J': function (vm, n, a) { var dv = new DataView(new ArrayBuffer(8)); dv.setFloat64(0, a[0]); return dv.getBigInt64(0); },
		'longBitsToDouble(J)D': function (vm, n, a) { var dv = new DataView(new ArrayBuffer(8)); dv.setBigInt64(0, a[0]); return dv.getFloat64(0); },
	});
	def('java/lang/Boolean', {
		interfaces: ['java/lang/Comparable'],
		methods: {
			'<init>(Z)V': function (vm, self, a) { self.$box = a[0] ? 1 : 0; },
			'booleanValue()Z': function (vm, self) { return self.$box; },
			'hashCode()I': function (vm, self) { return self.$box ? 1231 : 1237; },
			'equals(Ljava/lang/Object;)Z': function (vm, self, a) { return a[0] && a[0].cls === self.cls && a[0].$box === self.$box ? 1 : 0; },
			'toString()Ljava/lang/String;': function (vm, self) { return self.$box ? 'true' : 'false'; },
		},
		staticMethods: {
			'valueOf(Z)Ljava/lang/Boolean;': function (vm, n, a) { return box(vm, a[0], 'Z'); },
			'valueOf(Ljava/lang/String;)Ljava/lang/Boolean;': function (vm, n, a) { return box(vm, a[0] !== null && a[0].toLowerCase() === 'true' ? 1 : 0, 'Z'); },
			'parseBoolean(Ljava/lang/String;)Z': function (vm, n, a) { return a[0] !== null && a[0].toLowerCase() === 'true' ? 1 : 0; },
			'toString(Z)Ljava/lang/String;': function (vm, n, a) { return a[0] ? 'true' : 'false'; },
		},
		clinit: function (vm, c) { c.statics.TRUE = box(vm, 1, 'Z'); c.statics.FALSE = box(vm, 0, 'Z'); },
		statics: { TRUE: null, FALSE: null },
	});
	var ch = function (f) { return function (vm, n, a) { return f(String.fromCharCode(a[0]), a[0]) ? 1 : 0; }; };
	def('java/lang/Character', {
		interfaces: ['java/lang/Comparable'],
		methods: {
			'<init>(C)V': function (vm, self, a) { self.$box = a[0]; },
			'charValue()C': function (vm, self) { return self.$box; },
			'hashCode()I': function (vm, self) { return self.$box; },
			'equals(Ljava/lang/Object;)Z': function (vm, self, a) { return a[0] && a[0].cls === self.cls && a[0].$box === self.$box ? 1 : 0; },
			'toString()Ljava/lang/String;': function (vm, self) { return String.fromCharCode(self.$box); },
			'compareTo(Ljava/lang/Object;)I': function (vm, self, a) { return self.$box - a[0].$box; },
		},
		staticMethods: {
			'valueOf(C)Ljava/lang/Character;': function (vm, n, a) { return box(vm, a[0], 'C'); },
			'toString(C)Ljava/lang/String;': function (vm, n, a) { return String.fromCharCode(a[0]); },
			'isDigit(C)Z': ch(function (c) { return /\d/.test(c); }),
			'isLetter(C)Z': ch(function (c) { return c.toLowerCase() !== c.toUpperCase() || /[a-zA-Z]/.test(c); }),
			'isLetterOrDigit(C)Z': ch(function (c) { return /\d/.test(c) || c.toLowerCase() !== c.toUpperCase(); }),
			'isWhitespace(C)Z': ch(function (c) { return /\s/.test(c); }),
			'isSpaceChar(C)Z': ch(function (c) { return /\s/.test(c); }),
			'isUpperCase(C)Z': ch(function (c) { return c !== c.toLowerCase(); }),
			'isLowerCase(C)Z': ch(function (c) { return c !== c.toUpperCase(); }),
			'toUpperCase(C)C': function (vm, n, a) { return String.fromCharCode(a[0]).toUpperCase().charCodeAt(0); },
			'toLowerCase(C)C': function (vm, n, a) { return String.fromCharCode(a[0]).toLowerCase().charCodeAt(0); },
			'digit(CI)I': function (vm, n, a) { var v = parseInt(String.fromCharCode(a[0]), a[1]); return v !== v ? -1 : v; },
			'forDigit(II)C': function (vm, n, a) { return a[0].toString(a[1]).charCodeAt(0); },
			'getNumericValue(C)I': function (vm, n, a) { var v = parseInt(String.fromCharCode(a[0]), 36); return v !== v ? -1 : v; },
			'isDigit(I)Z': ch(function (c) { return /\d/.test(c); }),
			'isLetter(I)Z': ch(function (c) { return c.toLowerCase() !== c.toUpperCase(); }),
			'isWhitespace(I)Z': ch(function (c) { return /\s/.test(c); }),
		},
	});

	var M1 = function (f) { return function (vm, n, a) { return f(a[0]); }; };
	var M2 = function (f) { return function (vm, n, a) { return f(a[0], a[1]); }; };
	var mathSpec = { staticMethods: {
		'abs(I)I': M1(function (x) { return x < 0 ? (-x) | 0 : x; }),
		'abs(J)J': M1(function (x) { return x < 0n ? BigInt.asIntN(64, -x) : x; }),
		'abs(F)F': M1(Math.abs), 'abs(D)D': M1(Math.abs),
		'max(II)I': M2(Math.max), 'max(FF)F': M2(Math.max), 'max(DD)D': M2(Math.max),
		'max(JJ)J': M2(function (a, b) { return a > b ? a : b; }),
		'min(II)I': M2(Math.min), 'min(FF)F': M2(Math.min), 'min(DD)D': M2(Math.min),
		'min(JJ)J': M2(function (a, b) { return a < b ? a : b; }),
		'sqrt(D)D': M1(Math.sqrt), 'cbrt(D)D': M1(Math.cbrt), 'pow(DD)D': M2(Math.pow), 'exp(D)D': M1(Math.exp),
		'log(D)D': M1(Math.log), 'log10(D)D': M1(Math.log10), 'sin(D)D': M1(Math.sin), 'cos(D)D': M1(Math.cos),
		'tan(D)D': M1(Math.tan), 'asin(D)D': M1(Math.asin), 'acos(D)D': M1(Math.acos), 'atan(D)D': M1(Math.atan),
		'atan2(DD)D': M2(Math.atan2), 'sinh(D)D': M1(Math.sinh), 'cosh(D)D': M1(Math.cosh), 'tanh(D)D': M1(Math.tanh),
		'hypot(DD)D': M2(Math.hypot), 'floor(D)D': M1(Math.floor), 'ceil(D)D': M1(Math.ceil),
		'rint(D)D': M1(function (x) { var r = Math.round(x); return (Math.abs(x % 1) === 0.5 && r % 2 !== 0) ? r - 1 : r; }),
		'round(F)I': M1(function (x) { return JVM.f2i(Math.floor(x + 0.5)); }),
		'round(D)J': M1(function (x) { return JVM.f2l(Math.floor(x + 0.5)); }),
		'random()D': function () { return Math.random(); },
		'signum(D)D': M1(Math.sign), 'signum(F)F': M1(Math.sign),
		'toRadians(D)D': M1(function (x) { return x / 180 * Math.PI; }), 'toDegrees(D)D': M1(function (x) { return x * 180 / Math.PI; }),
		'floorDiv(II)I': M2(function (a, b) { return Math.floor(a / b) | 0; }),
		'floorMod(II)I': M2(function (a, b) { return ((a % b) + b) % b; }),
		'log1p(D)D': M1(Math.log1p), 'expm1(D)D': M1(Math.expm1),
		'ulp(D)D': M1(function (x) { return Math.abs(x) * 2.220446049250313e-16; }),
		'clamp(DDD)D': function (vm, n, a) { return Math.min(Math.max(a[0], a[1]), a[2]); },
	}, statics: { PI: Math.PI, E: Math.E } };
	def('java/lang/Math', mathSpec);
	def('java/lang/StrictMath', mathSpec);

	var printSpec = function (dest) {
		var w = function (vm, self, s) {
			var buf = (self.$line || '') + s, i;
			while ((i = buf.indexOf('\n')) >= 0) { vm.log(dest, buf.substring(0, i)); buf = buf.substring(i + 1); }
			self.$line = buf;
		};
		var m = {
			'flush()V': function (vm, self) { if (self.$line) { vm.log(dest, self.$line); self.$line = ''; } },
			'close()V': function () {},
			'println()V': function (vm, self) { w(vm, self, '\n'); },
			'printf(Ljava/lang/String;[Ljava/lang/Object;)Ljava/io/PrintStream;': function (vm, self, a) { w(vm, self, javaFormat(vm, a[0], a[1] ? Array.prototype.slice.call(a[1].a) : [])); return self; },
			'format(Ljava/lang/String;[Ljava/lang/Object;)Ljava/io/PrintStream;': function (vm, self, a) { w(vm, self, javaFormat(vm, a[0], a[1] ? Array.prototype.slice.call(a[1].a) : [])); return self; },
		};
		['Ljava/lang/String;', 'Ljava/lang/Object;', 'I', 'J', 'F', 'D', 'C', 'Z', '[C'].forEach(function (t) {
			var conv = t === '[C' ? function (vm, v) { return vm.stringFromChars(v); } : function (vm, v) { return stringOf(vm, v, t.length === 1 ? t : null); };
			m['print(' + t + ')V'] = function (vm, self, a) { w(vm, self, conv(vm, a[0])); };
			m['println(' + t + ')V'] = function (vm, self, a) { w(vm, self, conv(vm, a[0]) + '\n'); };
		});
		return m;
	};
	def('java/io/OutputStream', { methods: { '<init>()V': function () {}, 'flush()V': function () {}, 'close()V': function () {} } });
	def('java/io/PrintStream', { super: 'java/io/OutputStream', methods: printSpec('out') });
	def('java/lang/System', {
		statics: { out: null, err: null, in: null },
		clinit: function (vm, c) {
			var out = vm.newObject(vm.loadClass('java/io/PrintStream'));
			var err = vm.newObject(vm.loadClass('java/io/PrintStream'));
			err.$err = true;
			c.statics.out = out;
			c.statics.err = err;
		},
		staticMethods: {
			'currentTimeMillis()J': function () { return BigInt(Date.now()); },
			'nanoTime()J': function () { return BigInt(Math.floor((typeof performance !== 'undefined' ? performance.now() : Date.now()) * 1e6)); },
			'arraycopy(Ljava/lang/Object;ILjava/lang/Object;II)V': function (vm, n, a) {
				var src = a[0], sp = a[1], dst = a[2], dp = a[3], len = a[4];
				if (!src || !dst) npe(vm, 'arraycopy');
				if (sp < 0 || dp < 0 || len < 0 || sp + len > src.a.length || dp + len > dst.a.length)
					vm.throwNew('java/lang/ArrayIndexOutOfBoundsException', 'arraycopy: last source index ' + (sp + len) + ' out of bounds for length ' + src.a.length);
				if (src.a.copyWithin && src === dst) src.a.copyWithin(dp, sp, sp + len);
				else if (dst.a.set && src.a.subarray) dst.a.set(src.a.subarray(sp, sp + len), dp);
				else { var tmp = Array.prototype.slice.call(src.a, sp, sp + len); for (var i = 0; i < len; i++) dst.a[dp + i] = tmp[i]; }
			},
			'identityHashCode(Ljava/lang/Object;)I': function (vm, n, a) { return a[0] === null ? 0 : vm.identityHash(a[0]); },
			'getProperty(Ljava/lang/String;)Ljava/lang/String;': function (vm, n, a) { return SYS_PROPS[a[0]] !== undefined ? SYS_PROPS[a[0]] : null; },
			'getProperty(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;': function (vm, n, a) { return SYS_PROPS[a[0]] !== undefined ? SYS_PROPS[a[0]] : a[1]; },
			'setProperty(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;': function (vm, n, a) { var o = SYS_PROPS[a[0]]; SYS_PROPS[a[0]] = a[1]; return o === undefined ? null : o; },
			'lineSeparator()Ljava/lang/String;': function () { return '\n'; },
			'getenv(Ljava/lang/String;)Ljava/lang/String;': function () { return null; },
			'exit(I)V': function (vm) { vm.warnOnce('exit', 'a mod asked to quit the game (System.exit) - ignored'); },
			'gc()V': function () {},
			'setOut(Ljava/io/PrintStream;)V': function () {}, 'setErr(Ljava/io/PrintStream;)V': function () {},
		},
	});
	var SYS_PROPS = { 'line.separator': '\n', 'file.separator': '/', 'path.separator': ':', 'java.version': '1.8.0',
		'os.name': 'Linux', 'user.dir': '/sdcard', 'user.home': '/sdcard', 'java.io.tmpdir': '/sdcard/tmp',
		'file.encoding': 'UTF-8', 'java.vendor': 'MCRE' };
	def('java/lang/Runtime', {
		staticMethods: { 'getRuntime()Ljava/lang/Runtime;': function (vm) { return vm.runtimeObj || (vm.runtimeObj = vm.newObject(vm.loadClass('java/lang/Runtime'))); } },
		methods: {
			'availableProcessors()I': function () { return 1; },
			'maxMemory()J': function () { return 1073741824n; }, 'totalMemory()J': function () { return 268435456n; },
			'freeMemory()J': function () { return 134217728n; }, 'gc()V': function () {},
			'addShutdownHook(Ljava/lang/Thread;)V': function () {},
		},
	});

	def('java/lang/Thread', {
		interfaces: ['java/lang/Runnable'],
		methods: {
			'<init>()V': function () {}, '<init>(Ljava/lang/Runnable;)V': function (vm, self, a) { self.$target = a[0]; },
			'<init>(Ljava/lang/Runnable;Ljava/lang/String;)V': function (vm, self, a) { self.$target = a[0]; self.$name = a[1]; },
			'<init>(Ljava/lang/String;)V': function (vm, self, a) { self.$name = a[0]; },
			'start()V': function (vm, self) { vm.warnOnce('thread', 'a mod started a background thread - not run here (left unplugged)'); },
			'run()V': function (vm, self) { if (self.$target) vm.callVirtual(self.$target, 'run', '()V', []); },
			'setDaemon(Z)V': function () {}, 'setName(Ljava/lang/String;)V': function (vm, self, a) { self.$name = a[0]; },
			'getName()Ljava/lang/String;': function (vm, self) { return self.$name || 'main'; },
			'interrupt()V': function () {}, 'isAlive()Z': function () { return 0; }, 'join()V': function () {},
			'setPriority(I)V': function () {}, 'isInterrupted()Z': function () { return 0; },
			'getContextClassLoader()Ljava/lang/ClassLoader;': function (vm) { return JVM.classLoaderObj(vm); },
			'getStackTrace()[Ljava/lang/StackTraceElement;': function (vm) { return vm.newArray('Ljava/lang/StackTraceElement;', 0); },
		},
		staticMethods: {
			'currentThread()Ljava/lang/Thread;': function (vm) { return vm.mainThread || (vm.mainThread = vm.newObject(vm.loadClass('java/lang/Thread'))); },
			'sleep(J)V': function () {}, 'yield()V': function () {}, 'interrupted()Z': function () { return 0; },
		},
	});
	def('java/lang/ThreadLocal', {
		methods: {
			'<init>()V': function () {},
			'get()Ljava/lang/Object;': function (vm, self) {
				if (!('$v' in self)) self.$v = vm.callVirtual(self, 'initialValue', '()Ljava/lang/Object;', []);
				return self.$v;
			},
			'set(Ljava/lang/Object;)V': function (vm, self, a) { self.$v = a[0]; },
			'remove()V': function (vm, self) { delete self.$v; },
			'initialValue()Ljava/lang/Object;': function () { return null; },
		},
	});

	def('java/lang/Throwable', {
		interfaces: ['java/io/Serializable'],
		methods: {
			'<init>()V': function (vm, self) { self.$jsStack = vm.currentTrace(); },
			'<init>(Ljava/lang/String;)V': function (vm, self, a) { self.$message = a[0]; self.$jsStack = vm.currentTrace(); },
			'<init>(Ljava/lang/String;Ljava/lang/Throwable;)V': function (vm, self, a) { self.$message = a[0]; self.$cause = a[1]; self.$jsStack = vm.currentTrace(); },
			'<init>(Ljava/lang/Throwable;)V': function (vm, self, a) { self.$cause = a[0]; self.$message = a[0] ? vm.toJavaString(a[0]) : null; self.$jsStack = vm.currentTrace(); },
			'<init>(Ljava/lang/String;Ljava/lang/Throwable;ZZ)V': function (vm, self, a) { self.$message = a[0]; self.$cause = a[1]; self.$jsStack = vm.currentTrace(); },
			'getMessage()Ljava/lang/String;': function (vm, self) { return self.$message != null ? self.$message : null; },
			'getLocalizedMessage()Ljava/lang/String;': function (vm, self) { return vm.callVirtual(self, 'getMessage', '()Ljava/lang/String;', []); },
			'getCause()Ljava/lang/Throwable;': function (vm, self) { return self.$cause || null; },
			'initCause(Ljava/lang/Throwable;)Ljava/lang/Throwable;': function (vm, self, a) { self.$cause = a[0]; return self; },
			'toString()Ljava/lang/String;': function (vm, self) {
				var m = vm.callVirtual(self, 'getLocalizedMessage', '()Ljava/lang/String;', []);
				return self.cls.name.replace(/[/]/g, '.') + (m !== null ? ': ' + m : '');
			},
			'printStackTrace()V': function (vm, self) { vm.log('err', vm.toJavaString(self)); },
			'printStackTrace(Ljava/io/PrintStream;)V': function (vm, self) { vm.log('err', vm.toJavaString(self)); },
			'fillInStackTrace()Ljava/lang/Throwable;': function (vm, self) { return self; },
			'getStackTrace()[Ljava/lang/StackTraceElement;': function (vm) { return vm.newArray('Ljava/lang/StackTraceElement;', 0); },
			'setStackTrace([Ljava/lang/StackTraceElement;)V': function () {},
			'addSuppressed(Ljava/lang/Throwable;)V': function () {},
			'getSuppressed()[Ljava/lang/Throwable;': function (vm) { return vm.newArray('Ljava/lang/Throwable;', 0); },
		},
	});
	[['java/lang/Exception', 'java/lang/Throwable'], ['java/lang/Error', 'java/lang/Throwable'],
	 ['java/lang/RuntimeException', 'java/lang/Exception'],
	 ['java/lang/NullPointerException', 'java/lang/RuntimeException'],
	 ['java/lang/ArithmeticException', 'java/lang/RuntimeException'],
	 ['java/lang/IndexOutOfBoundsException', 'java/lang/RuntimeException'],
	 ['java/lang/ArrayIndexOutOfBoundsException', 'java/lang/IndexOutOfBoundsException'],
	 ['java/lang/StringIndexOutOfBoundsException', 'java/lang/IndexOutOfBoundsException'],
	 ['java/lang/ClassCastException', 'java/lang/RuntimeException'],
	 ['java/lang/IllegalArgumentException', 'java/lang/RuntimeException'],
	 ['java/lang/NumberFormatException', 'java/lang/IllegalArgumentException'],
	 ['java/lang/IllegalStateException', 'java/lang/RuntimeException'],
	 ['java/lang/UnsupportedOperationException', 'java/lang/RuntimeException'],
	 ['java/lang/NegativeArraySizeException', 'java/lang/RuntimeException'],
	 ['java/lang/ArrayStoreException', 'java/lang/RuntimeException'],
	 ['java/lang/SecurityException', 'java/lang/RuntimeException'],
	 ['java/lang/CloneNotSupportedException', 'java/lang/Exception'],
	 ['java/lang/InterruptedException', 'java/lang/Exception'],
	 ['java/lang/ReflectiveOperationException', 'java/lang/Exception'],
	 ['java/lang/ClassNotFoundException', 'java/lang/ReflectiveOperationException'],
	 ['java/lang/NoSuchMethodException', 'java/lang/ReflectiveOperationException'],
	 ['java/lang/NoSuchFieldException', 'java/lang/ReflectiveOperationException'],
	 ['java/lang/InstantiationException', 'java/lang/ReflectiveOperationException'],
	 ['java/lang/IllegalAccessException', 'java/lang/ReflectiveOperationException'],
	 ['java/lang/LinkageError', 'java/lang/Error'],
	 ['java/lang/NoClassDefFoundError', 'java/lang/LinkageError'],
	 ['java/lang/VerifyError', 'java/lang/LinkageError'],
	 ['java/lang/IncompatibleClassChangeError', 'java/lang/LinkageError'],
	 ['java/lang/AbstractMethodError', 'java/lang/IncompatibleClassChangeError'],
	 ['java/lang/NoSuchMethodError', 'java/lang/IncompatibleClassChangeError'],
	 ['java/lang/NoSuchFieldError', 'java/lang/IncompatibleClassChangeError'],
	 ['java/lang/ExceptionInInitializerError', 'java/lang/LinkageError'],
	 ['java/lang/VirtualMachineError', 'java/lang/Error'],
	 ['java/lang/StackOverflowError', 'java/lang/VirtualMachineError'],
	 ['java/lang/OutOfMemoryError', 'java/lang/VirtualMachineError'],
	 ['java/lang/AssertionError', 'java/lang/Error'],
	 ['java/util/NoSuchElementException', 'java/lang/RuntimeException'],
	 ['java/util/ConcurrentModificationException', 'java/lang/RuntimeException'],
	 ['java/util/EmptyStackException', 'java/lang/RuntimeException'],
	 ['java/util/MissingResourceException', 'java/lang/RuntimeException'],
	 ['java/io/IOException', 'java/lang/Exception'],
	 ['java/io/FileNotFoundException', 'java/io/IOException'],
	 ['java/io/EOFException', 'java/io/IOException'],
	 ['java/io/UncheckedIOException', 'java/lang/RuntimeException'],
	].forEach(function (p) { def(p[0], { super: p[1] }); });
	vm.natives['java/lang/AssertionError'].methods = { '<init>(Ljava/lang/Object;)V': function (vm, self, a) { self.$message = str(vm, a[0]); } };

	def('java/lang/Class', {
		methods: {
			'getName()Ljava/lang/String;': function (vm, self) { return self.$cls.name.replace(/[/]/g, '.'); },
			'getSimpleName()Ljava/lang/String;': function (vm, self) { var n = self.$cls.name; n = n.substring(n.lastIndexOf('/') + 1); return n.substring(n.lastIndexOf('$') + 1); },
			'getCanonicalName()Ljava/lang/String;': function (vm, self) { return self.$cls.name.replace(/[\/$]/g, '.'); },
			'toString()Ljava/lang/String;': function (vm, self) { return (self.$cls.isInterface() ? 'interface ' : 'class ') + self.$cls.name.replace(/[/]/g, '.'); },
			'isInstance(Ljava/lang/Object;)Z': function (vm, self, a) { return vm.isInstance(a[0], self.$cls) ? 1 : 0; },
			'isAssignableFrom(Ljava/lang/Class;)Z': function (vm, self, a) { return a[0].$cls.isSubclassOf(self.$cls) ? 1 : 0; },
			'getSuperclass()Ljava/lang/Class;': function (vm, self) { return self.$cls.superClass ? vm.classObject(self.$cls.superClass) : null; },
			'isArray()Z': function (vm, self) { return self.$cls.name[0] === '[' ? 1 : 0; },
			'isInterface()Z': function (vm, self) { return self.$cls.isInterface() ? 1 : 0; },
			'isPrimitive()Z': function (vm, self) { return self.$cls.primitive ? 1 : 0; },
			'isEnum()Z': function (vm, self) { return self.$cls.superClass && self.$cls.superClass.name === 'java/lang/Enum' ? 1 : 0; },
			'getComponentType()Ljava/lang/Class;': function (vm, self) { return self.$cls.component ? vm.classObject(vm.classFor(self.$cls.component)) : null; },
			'desiredAssertionStatus()Z': function () { return 0; },
			'getModifiers()I': function (vm, self) { return self.$cls.access; },
			'cast(Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { return a[0]; },
			'hashCode()I': function (vm, self) { return vm.identityHash(self); },
			'getClassLoader()Ljava/lang/ClassLoader;': function (vm) { return JVM.classLoaderObj(vm); },
			'newInstance()Ljava/lang/Object;': function (vm, self) {
				var o = vm.newObject(self.$cls);
				var m = self.$cls.findDeclared('<init>()V');
				if (m) vm.invoke(m, o, []);
				return o;
			},
			'getEnumConstants()[Ljava/lang/Object;': function (vm, self) {
				var m = self.$cls.methods['values()[L' + self.$cls.name + ';'];
				return m ? (vm.initClass(self.$cls), vm.invoke(m, null, [])) : null;
			},
			'getResourceAsStream(Ljava/lang/String;)Ljava/io/InputStream;': function (vm, self, a) { return JVM.resourceStream(vm, a[0], self.$cls); },
			'getResource(Ljava/lang/String;)Ljava/net/URL;': function () { return null; },
			'getPackage()Ljava/lang/Package;': function () { return null; },
			'getAnnotation(Ljava/lang/Class;)Ljava/lang/annotation/Annotation;': function () { return null; },
			'isAnnotationPresent(Ljava/lang/Class;)Z': function () { return 0; },
			'getDeclaredFields()[Ljava/lang/reflect/Field;': function (vm) { return vm.newArray('Ljava/lang/reflect/Field;', 0); },
			'getFields()[Ljava/lang/reflect/Field;': function (vm) { return vm.newArray('Ljava/lang/reflect/Field;', 0); },
			'getDeclaredMethods()[Ljava/lang/reflect/Method;': function (vm) { return vm.newArray('Ljava/lang/reflect/Method;', 0); },
			'getMethods()[Ljava/lang/reflect/Method;': function (vm) { return vm.newArray('Ljava/lang/reflect/Method;', 0); },
			'getInterfaces()[Ljava/lang/Class;': function (vm, self) { return javaArray(vm, 'Ljava/lang/Class;', self.$cls.interfaces.map(function (c) { return vm.classObject(c); })); },
		},
		staticMethods: {
			'forName(Ljava/lang/String;)Ljava/lang/Class;': function (vm, n, a) { return JVM.forName(vm, a[0]); },
			'forName(Ljava/lang/String;ZLjava/lang/ClassLoader;)Ljava/lang/Class;': function (vm, n, a) { return JVM.forName(vm, a[0]); },
		},
	});
	def('java/lang/ClassLoader', {
		methods: {
			'loadClass(Ljava/lang/String;)Ljava/lang/Class;': function (vm, self, a) { return JVM.forName(vm, a[0]); },
			'getResourceAsStream(Ljava/lang/String;)Ljava/io/InputStream;': function (vm, self, a) { return JVM.resourceStream(vm, a[0], null); },
			'getResource(Ljava/lang/String;)Ljava/net/URL;': function () { return null; },
			'getParent()Ljava/lang/ClassLoader;': function () { return null; },
		},
		staticMethods: { 'getSystemClassLoader()Ljava/lang/ClassLoader;': function (vm) { return JVM.classLoaderObj(vm); } },
	});

	def('java/lang/Enum', {
		interfaces: ['java/lang/Comparable', 'java/io/Serializable'],
		methods: {
			'<init>(Ljava/lang/String;I)V': function (vm, self, a) { self.$name = a[0]; self.$ordinal = a[1]; },
			'name()Ljava/lang/String;': function (vm, self) { return self.$name; },
			'ordinal()I': function (vm, self) { return self.$ordinal; },
			'toString()Ljava/lang/String;': function (vm, self) { return self.$name; },
			'compareTo(Ljava/lang/Enum;)I': function (vm, self, a) { return self.$ordinal - a[0].$ordinal; },
			'compareTo(Ljava/lang/Object;)I': function (vm, self, a) { return self.$ordinal - a[0].$ordinal; },
			'getDeclaringClass()Ljava/lang/Class;': function (vm, self) {
				var c = self.cls;
				while (c.superClass && c.superClass.name !== 'java/lang/Enum') c = c.superClass;
				return vm.classObject(c);
			},
			'hashCode()I': function (vm, self) { return vm.identityHash(self); },
			'equals(Ljava/lang/Object;)Z': function (vm, self, a) { return self === a[0] ? 1 : 0; },
		},
		staticMethods: {
			'valueOf(Ljava/lang/Class;Ljava/lang/String;)Ljava/lang/Enum;': function (vm, n, a) {
				var c = a[0].$cls, m = c.methods['values()[L' + c.name + ';'];
				if (m) {
					vm.initClass(c);
					var vals = vm.invoke(m, null, []).a;
					for (var i = 0; i < vals.length; i++) if (vals[i].$name === a[1]) return vals[i];
				}
				vm.throwNew('java/lang/IllegalArgumentException', 'No enum constant ' + c.name.replace(/[/]/g, '.') + '.' + a[1]);
			},
		},
	});

	def('java/lang/ref/Reference', { methods: {
		'<init>(Ljava/lang/Object;)V': function (vm, self, a) { self.$ref = a[0]; },
		'get()Ljava/lang/Object;': function (vm, self) { return self.$ref === undefined ? null : self.$ref; },
		'clear()V': function (vm, self) { self.$ref = null; },
	} });
	def('java/lang/ref/WeakReference', { super: 'java/lang/ref/Reference', methods: { '<init>(Ljava/lang/Object;)V': function (vm, self, a) { self.$ref = a[0]; } } });
	def('java/lang/ref/SoftReference', { super: 'java/lang/ref/Reference', methods: { '<init>(Ljava/lang/Object;)V': function (vm, self, a) { self.$ref = a[0]; } } });
	def('java/lang/invoke/MethodHandle', { methods: {
		'invoke([Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { return self.$h.call(Array.prototype.slice.call(a[0].a)); },
		'invokeWithArguments([Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { return self.$h.call(Array.prototype.slice.call(a[0].a)); },
	} });
	def('java/lang/invoke/MethodType', {});
	def('java/lang/StackTraceElement', {});
	def('java/lang/Record', { access: JVM.ACC_PUBLIC | JVM.ACC_ABSTRACT, methods: { '<init>()V': function () {} } });
	var fnI = function (n, sam, extra) { var abs = {}; abs[sam] = true; def('java/util/function/' + n, { access: I, abstractMethods: abs, methods: extra || {} }); };
	var O = 'Ljava/lang/Object;';
	fnI('Function', 'apply(' + O + ')' + O, {
		'andThen(Ljava/util/function/Function;)Ljava/util/function/Function;': function (vm, self, a) { return JVM.jsFunction(vm, 'java/util/function/Function', 'apply(' + O + ')' + O, function (x) { return vm.callVirtual(a[0], 'apply', '(' + O + ')' + O, [vm.callVirtual(self, 'apply', '(' + O + ')' + O, [x])]); }); },
		'compose(Ljava/util/function/Function;)Ljava/util/function/Function;': function (vm, self, a) { return JVM.jsFunction(vm, 'java/util/function/Function', 'apply(' + O + ')' + O, function (x) { return vm.callVirtual(self, 'apply', '(' + O + ')' + O, [vm.callVirtual(a[0], 'apply', '(' + O + ')' + O, [x])]); }); },
	});
	fnI('BiFunction', 'apply(' + O + O + ')' + O);
	fnI('UnaryOperator', 'apply(' + O + ')' + O);
	fnI('BinaryOperator', 'apply(' + O + O + ')' + O);
	fnI('Supplier', 'get()' + O);
	fnI('Consumer', 'accept(' + O + ')V', {
		'andThen(Ljava/util/function/Consumer;)Ljava/util/function/Consumer;': function (vm, self, a) { return JVM.jsFunction(vm, 'java/util/function/Consumer', 'accept(' + O + ')V', function (x) { vm.callVirtual(self, 'accept', '(' + O + ')V', [x]); vm.callVirtual(a[0], 'accept', '(' + O + ')V', [x]); }); },
	});
	fnI('BiConsumer', 'accept(' + O + O + ')V');
	fnI('Predicate', 'test(' + O + ')Z', {
		'negate()Ljava/util/function/Predicate;': function (vm, self) { return JVM.jsFunction(vm, 'java/util/function/Predicate', 'test(' + O + ')Z', function (x) { return vm.callVirtual(self, 'test', '(' + O + ')Z', [x]) ? 0 : 1; }); },
		'and(Ljava/util/function/Predicate;)Ljava/util/function/Predicate;': function (vm, self, a) { return JVM.jsFunction(vm, 'java/util/function/Predicate', 'test(' + O + ')Z', function (x) { return vm.callVirtual(self, 'test', '(' + O + ')Z', [x]) && vm.callVirtual(a[0], 'test', '(' + O + ')Z', [x]) ? 1 : 0; }); },
		'or(Ljava/util/function/Predicate;)Ljava/util/function/Predicate;': function (vm, self, a) { return JVM.jsFunction(vm, 'java/util/function/Predicate', 'test(' + O + ')Z', function (x) { return vm.callVirtual(self, 'test', '(' + O + ')Z', [x]) || vm.callVirtual(a[0], 'test', '(' + O + ')Z', [x]) ? 1 : 0; }); },
	});
	fnI('BiPredicate', 'test(' + O + O + ')Z');
	fnI('IntFunction', 'apply(I)' + O);
	fnI('IntPredicate', 'test(I)Z');
	fnI('IntConsumer', 'accept(I)V');
	fnI('IntSupplier', 'getAsInt()I');
	fnI('IntUnaryOperator', 'applyAsInt(I)I');
	fnI('IntBinaryOperator', 'applyAsInt(II)I');
	fnI('ToIntFunction', 'applyAsInt(' + O + ')I');
	fnI('ToDoubleFunction', 'applyAsDouble(' + O + ')D');
	fnI('ToLongFunction', 'applyAsLong(' + O + ')J');
	fnI('BooleanSupplier', 'getAsBoolean()Z');
	fnI('DoubleSupplier', 'getAsDouble()D');
	fnI('LongSupplier', 'getAsLong()J');
	def('java/lang/Void', {});
	def('java/lang/Iterable', { access: I, abstractMethods: { 'iterator()Ljava/util/Iterator;': true },
		methods: { 'forEach(Ljava/util/function/Consumer;)V': function (vm, self, a) {
			JVM.iterate(vm, self).forEach(function (x) { vm.callVirtual(a[0], 'accept', '(Ljava/lang/Object;)V', [x]); });
		} } });
}

JVM.forName = function (vm, name) {
	var n = name.replace(/\./g, '/');
	var c = vm.classes[n];
	if (!c || c.absent) {
		var real = vm.sources[n] || vm.natives[n] || (vm.mapClass && vm.mapClass(n) && vm.mapClass(n) !== n);
		if (!real && !(c && !c.absent)) vm.throwNew('java/lang/ClassNotFoundException', name);
		c = vm.loadClass(n);
	}
	vm.initClass(c);
	return vm.classObject(c);
};
JVM.jsFunction = function (vm, iface, key, fn) {
	var cname = 'mcre/Fn$' + iface.replace(/[/]/g, '_');
	if (!vm.classes[cname]) {
		var methods = {};
		methods[key] = function (vm, self, a) { return self.$fn.apply(null, a); };
		vm.defineNative(cname, { interfaces: [iface], methods: methods });
	}
	var o = new JObject(vm.loadClass(cname));
	o.$fn = fn;
	return o;
};
JVM.classLoaderObj = function (vm) {
	return vm.loaderObj || (vm.loaderObj = vm.newObject(vm.loadClass('java/lang/ClassLoader')));
};

JVM.stringHash = stringHash;
JVM.javaDouble = javaDouble;
JVM.stringOf = stringOf;
JVM.hashOf = hashOf;
JVM.equalsOf = equalsOf;
JVM.box = box;
JVM.unbox = unbox;
JVM.javaArray = javaArray;
JVM.javaFormat = javaFormat;
JVM.javaRegex = javaRegex;
JVM.utf8Bytes = utf8Bytes;
JVM.utf8String = utf8String;
JVM.installLang = installLang;
})();

(function () {
'use strict';

var JObject = JVM.JObject, JArray = JVM.JArray;
var OBJ = 'Ljava/lang/Object;', COL = 'Ljava/util/Collection;';

function JMap(vm, identity) {
	this.vm = vm;
	this.identity = !!identity;
	this.buckets = new Map();
	this.list = [];
	this.size = 0;
	this.dead = 0;
}
JMap.prototype.hash = function (k) {
	if (this.identity) return k === null ? 0 : (typeof k === 'object' ? this.vm.identityHash(k) : JVM.hashOf(this.vm, k));
	return JVM.hashOf(this.vm, k);
};
JMap.prototype.eq = function (a, b) { return this.identity ? a === b : JVM.equalsOf(this.vm, a, b); };
JMap.prototype.find = function (k) {
	var b = this.buckets.get(this.hash(k));
	if (b) for (var i = 0; i < b.length; i++) if (this.eq(b[i].k, k)) return b[i];
	return null;
};
JMap.prototype.get = function (k) { var e = this.find(k); return e ? e.v : null; };
JMap.prototype.has = function (k) { return this.find(k) !== null; };
JMap.prototype.put = function (k, v) {
	var h = this.hash(k), b = this.buckets.get(h);
	if (b) for (var i = 0; i < b.length; i++) if (this.eq(b[i].k, k)) { var old = b[i].v; b[i].v = v; return old; }
	var e = { k: k, v: v, dead: false };
	if (b) b.push(e); else this.buckets.set(h, [e]);
	this.list.push(e);
	this.size++;
	return null;
};
JMap.prototype.remove = function (k) {
	var h = this.hash(k), b = this.buckets.get(h);
	if (!b) return undefined;
	for (var i = 0; i < b.length; i++) if (this.eq(b[i].k, k)) {
		var e = b[i];
		b.splice(i, 1);
		if (!b.length) this.buckets.delete(h);
		e.dead = true;
		this.size--;
		if (++this.dead > 32 && this.dead > this.list.length / 2) { this.list = this.list.filter(function (x) { return !x.dead; }); this.dead = 0; }
		return e;
	}
	return undefined;
};
JMap.prototype.clear = function () { this.buckets.clear(); this.list.forEach(function (e) { e.dead = true; }); this.list = []; this.size = 0; this.dead = 0; };
JMap.prototype.entries = function () {
	var out = this.list.filter(function (e) { return !e.dead; });
	if (this.sorted) {
		var vm = this.vm, cmp = this.comparator;
		out.sort(function (a, b) { return compare(vm, a.k, b.k, cmp); });
	}
	return out;
};

function compare(vm, a, b, cmp) {
	if (cmp) return vm.callVirtual(cmp, 'compare', '(' + OBJ + OBJ + ')I', [a, b]);
	if (typeof a === 'string' && typeof b === 'string') return a < b ? -1 : a > b ? 1 : 0;
	var ua = JVM.unbox(a), ub = JVM.unbox(b);
	if ((typeof ua === 'number' || typeof ua === 'bigint') && (typeof ub === 'number' || typeof ub === 'bigint')) return ua < ub ? -1 : ua > ub ? 1 : 0;
	return vm.callVirtual(a, 'compareTo', '(' + OBJ + ')I', [b]);
}

function iterate(vm, c) {
	if (c === null || c === undefined) vm.throwNew('java/lang/NullPointerException', 'iterate');
	if (c.$list) return c.$list.slice();
	if (c.$m && c.$set) return c.$m.entries().map(function (e) { return e.k; });
	if (c.$view) return viewItems(c);
	if (c instanceof JArray) return Array.prototype.slice.call(c.a);
	var out = [], it = vm.callVirtual(c, 'iterator', '()Ljava/util/Iterator;', []);
	while (vm.callVirtual(it, 'hasNext', '()Z', [])) out.push(vm.callVirtual(it, 'next', '()' + OBJ, []));
	return out;
}
function viewItems(v) {
	var es = v.$view.entries();
	if (v.$kind === 'k') return es.map(function (e) { return e.k; });
	if (v.$kind === 'v') return es.map(function (e) { return e.v; });
	return es.map(function (e) { return entryObj(v.vm, e); });
}

function makeIterator(vm, items, onRemove) {
	var it = new JObject(vm.loadClass('mcre/Iterator'));
	it.$items = items; it.$i = 0; it.$remove = onRemove || null;
	return it;
}
function entryObj(vm, e) {
	var o = new JObject(vm.loadClass('mcre/MapEntry'));
	o.$e = e;
	return o;
}
function toStr(vm, v) { return JVM.stringOf(vm, v, null); }

function installUtil(vm) {
	var def = function (n, s) { vm.defineNative(n, s); };
	var I = JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC;
	var iface = function (n, abs, sup, extra) {
		var a = {};
		(abs || []).forEach(function (k) { a[k] = true; });
		def(n, { access: I, interfaces: sup || [], abstractMethods: a, methods: extra || {} });
	};
	iface('java/util/Iterator', ['hasNext()Z', 'next()' + OBJ], [], { 'remove()V': function (vm) { vm.throwNew('java/lang/UnsupportedOperationException', 'remove'); } });
	iface('java/util/ListIterator', [], ['java/util/Iterator']);
	iface('java/util/Enumeration', ['hasMoreElements()Z', 'nextElement()' + OBJ]);
	iface('java/util/Collection', ['size()I', 'iterator()Ljava/util/Iterator;'], ['java/lang/Iterable']);
	var ofStatics = function (maker) {
		var st = {};
		for (var n = 0; n <= 10; n++) st['of(' + 'Ljava/lang/Object;'.repeat(n) + ')' + maker.ret] = function (vm, x, a) { return maker.fn(vm, a); };
		st['of([Ljava/lang/Object;)' + maker.ret] = function (vm, x, a) { return maker.fn(vm, Array.prototype.slice.call(a[0].a)); };
		st['copyOf(Ljava/util/Collection;)' + maker.ret] = function (vm, x, a) { return maker.fn(vm, iterate(vm, a[0])); };
		return st;
	};
	def('java/util/List', { access: I, interfaces: ['java/util/Collection'], staticMethods: ofStatics({ ret: 'Ljava/util/List;', fn: function (vm, a) { return newList(vm, a.slice()); } }) });
	def('java/util/Set', { access: I, interfaces: ['java/util/Collection'], staticMethods: ofStatics({ ret: 'Ljava/util/Set;', fn: function (vm, a) { return newSet(vm, 'java/util/LinkedHashSet', a); } }) });
	iface('java/util/SortedSet', [], ['java/util/Set']);
	iface('java/util/NavigableSet', [], ['java/util/SortedSet']);
	iface('java/util/Queue', [], ['java/util/Collection']);
	iface('java/util/Deque', [], ['java/util/Queue']);
	iface('java/util/RandomAccess', []);
	var mapOf = {};
	for (var mn = 0; mn <= 10; mn++) mapOf['of(' + 'Ljava/lang/Object;'.repeat(mn * 2) + ')Ljava/util/Map;'] = function (vm, x, a) { var m = newMap(vm); for (var i = 0; i + 1 < a.length; i += 2) m.$m.put(a[i], a[i + 1]); return m; };
	mapOf['copyOf(Ljava/util/Map;)Ljava/util/Map;'] = function (vm, x, a) { var m = newMap(vm); mapEntries(vm, a[0]).forEach(function (e) { m.$m.put(e.k, e.v); }); return m; };
	mapOf['entry(Ljava/lang/Object;Ljava/lang/Object;)Ljava/util/Map$Entry;'] = function (vm, x, a) { return entryObj(vm, { k: a[0], v: a[1] }); };
	def('java/util/Map', { access: I, abstractMethods: { 'size()I': true }, staticMethods: mapOf });
	iface('java/util/SortedMap', [], ['java/util/Map']);
	iface('java/util/NavigableMap', [], ['java/util/SortedMap']);
	iface('java/util/Map$Entry', ['getKey()' + OBJ, 'getValue()' + OBJ]);
	iface('java/util/Comparator', ['compare(' + OBJ + OBJ + ')I'], [], {
		'reversed()Ljava/util/Comparator;': function (vm, self) { return comparatorFn(vm, function (a, b) { return -compare(vm, a, b, self); }); },
		'thenComparing(Ljava/util/Comparator;)Ljava/util/Comparator;': function (vm, self, a) {
			return comparatorFn(vm, function (x, y) { var r = compare(vm, x, y, self); return r !== 0 ? r : compare(vm, x, y, a[0]); });
		},
	});
	iface('java/util/EventListener', []);

	def('mcre/Iterator', {
		interfaces: ['java/util/Iterator', 'java/util/ListIterator', 'java/util/Enumeration'],
		methods: {
			'hasNext()Z': function (vm, self) { return self.$i < self.$items.length ? 1 : 0; },
			'next()Ljava/lang/Object;': function (vm, self) {
				if (self.$i >= self.$items.length) vm.throwNew('java/util/NoSuchElementException', null);
				return self.$items[self.$i++];
			},
			'remove()V': function (vm, self) {
				if (!self.$remove) vm.throwNew('java/lang/UnsupportedOperationException', 'remove');
				self.$remove(self.$items[self.$i - 1], self.$i - 1);
				self.$removed = (self.$removed || 0) + 1;
			},
			'hasMoreElements()Z': function (vm, self) { return self.$i < self.$items.length ? 1 : 0; },
			'nextElement()Ljava/lang/Object;': function (vm, self) { return self.$items[self.$i++]; },
			'hasPrevious()Z': function (vm, self) { return self.$i > 0 ? 1 : 0; },
			'previous()Ljava/lang/Object;': function (vm, self) { return self.$items[--self.$i]; },
			'nextIndex()I': function (vm, self) { return self.$i; },
			'forEachRemaining(Ljava/util/function/Consumer;)V': function (vm, self, a) {
				while (self.$i < self.$items.length) vm.callVirtual(a[0], 'accept', '(' + OBJ + ')V', [self.$items[self.$i++]]);
			},
		},
	});
	def('mcre/MapEntry', {
		interfaces: ['java/util/Map$Entry'],
		methods: {
			'getKey()Ljava/lang/Object;': function (vm, self) { return self.$e.k; },
			'getValue()Ljava/lang/Object;': function (vm, self) { return self.$e.v; },
			'setValue(Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { var o = self.$e.v; self.$e.v = a[0]; return o; },
			'hashCode()I': function (vm, self) { return JVM.hashOf(vm, self.$e.k) ^ JVM.hashOf(vm, self.$e.v); },
			'equals(Ljava/lang/Object;)Z': function (vm, self, a) { return a[0] && a[0].$e && JVM.equalsOf(vm, a[0].$e.k, self.$e.k) && JVM.equalsOf(vm, a[0].$e.v, self.$e.v) ? 1 : 0; },
			'toString()Ljava/lang/String;': function (vm, self) { return toStr(vm, self.$e.k) + '=' + toStr(vm, self.$e.v); },
		},
	});
	def('java/util/AbstractMap$SimpleEntry', { super: 'mcre/MapEntry', methods: {
		'<init>(Ljava/lang/Object;Ljava/lang/Object;)V': function (vm, self, a) { self.$e = { k: a[0], v: a[1] }; },
	} });

	var listMethods = {
		'<init>()V': function (vm, self) { self.$list = []; },
		'<init>(I)V': function (vm, self) { self.$list = []; },
		'<init>(Ljava/util/Collection;)V': function (vm, self, a) { self.$list = iterate(vm, a[0]); },
		'size()I': function (vm, self) { return self.$list.length; },
		'isEmpty()Z': function (vm, self) { return self.$list.length ? 0 : 1; },
		'get(I)Ljava/lang/Object;': function (vm, self, a) { idx(vm, self, a[0], 0); return self.$list[a[0]]; },
		'set(ILjava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { idx(vm, self, a[0], 0); var o = self.$list[a[0]]; self.$list[a[0]] = a[1]; return o; },
		'add(Ljava/lang/Object;)Z': function (vm, self, a) { self.$list.push(a[0]); return 1; },
		'add(ILjava/lang/Object;)V': function (vm, self, a) { idx(vm, self, a[0], 1); self.$list.splice(a[0], 0, a[1]); },
		'remove(I)Ljava/lang/Object;': function (vm, self, a) { idx(vm, self, a[0], 0); return self.$list.splice(a[0], 1)[0]; },
		'remove(Ljava/lang/Object;)Z': function (vm, self, a) { var i = indexIn(vm, self.$list, a[0]); if (i < 0) return 0; self.$list.splice(i, 1); return 1; },
		'contains(Ljava/lang/Object;)Z': function (vm, self, a) { return indexIn(vm, self.$list, a[0]) >= 0 ? 1 : 0; },
		'indexOf(Ljava/lang/Object;)I': function (vm, self, a) { return indexIn(vm, self.$list, a[0]); },
		'lastIndexOf(Ljava/lang/Object;)I': function (vm, self, a) { for (var i = self.$list.length - 1; i >= 0; i--) if (JVM.equalsOf(vm, self.$list[i], a[0])) return i; return -1; },
		'clear()V': function (vm, self) { self.$list.length = 0; },
		'addAll(Ljava/util/Collection;)Z': function (vm, self, a) { var x = iterate(vm, a[0]); Array.prototype.push.apply(self.$list, x); return x.length ? 1 : 0; },
		'addAll(ILjava/util/Collection;)Z': function (vm, self, a) { var x = iterate(vm, a[1]); Array.prototype.splice.apply(self.$list, [a[0], 0].concat(x)); return x.length ? 1 : 0; },
		'removeAll(Ljava/util/Collection;)Z': function (vm, self, a) { var x = iterate(vm, a[0]), n = self.$list.length; self.$list = self.$list.filter(function (v) { return indexIn(vm, x, v) < 0; }); return n !== self.$list.length ? 1 : 0; },
		'retainAll(Ljava/util/Collection;)Z': function (vm, self, a) { var x = iterate(vm, a[0]), n = self.$list.length; self.$list = self.$list.filter(function (v) { return indexIn(vm, x, v) >= 0; }); return n !== self.$list.length ? 1 : 0; },
		'containsAll(Ljava/util/Collection;)Z': function (vm, self, a) { var l = self.$list; return iterate(vm, a[0]).every(function (v) { return indexIn(vm, l, v) >= 0; }) ? 1 : 0; },
		'iterator()Ljava/util/Iterator;': function (vm, self) { return listIter(vm, self); },
		'listIterator()Ljava/util/ListIterator;': function (vm, self) { return listIter(vm, self); },
		'toArray()[Ljava/lang/Object;': function (vm, self) { return JVM.javaArray(vm, OBJ, self.$list); },
		'toArray([Ljava/lang/Object;)[Ljava/lang/Object;': function (vm, self, a) {
			var t = a[0], l = self.$list;
			if (t.a.length >= l.length) { for (var i = 0; i < l.length; i++) t.a[i] = l[i]; if (t.a.length > l.length) t.a[l.length] = null; return t; }
			return JVM.javaArray(vm, t.cls.component, l);
		},
		'subList(II)Ljava/util/List;': function (vm, self, a) { return newList(vm, self.$list.slice(a[0], a[1])); },
		'sort(Ljava/util/Comparator;)V': function (vm, self, a) { stableSort(vm, self.$list, a[0]); },
		'forEach(Ljava/util/function/Consumer;)V': function (vm, self, a) { self.$list.slice().forEach(function (x) { vm.callVirtual(a[0], 'accept', '(' + OBJ + ')V', [x]); }); },
		'removeIf(Ljava/util/function/Predicate;)Z': function (vm, self, a) { var n = self.$list.length; self.$list = self.$list.filter(function (x) { return !vm.callVirtual(a[0], 'test', '(' + OBJ + ')Z', [x]); }); return n !== self.$list.length ? 1 : 0; },
		'equals(Ljava/lang/Object;)Z': function (vm, self, a) {
			var o = a[0];
			if (!o || !o.$list || o.$list.length !== self.$list.length) return 0;
			for (var i = 0; i < o.$list.length; i++) if (!JVM.equalsOf(vm, o.$list[i], self.$list[i])) return 0;
			return 1;
		},
		'hashCode()I': function (vm, self) { var h = 1; self.$list.forEach(function (x) { h = (Math.imul(31, h) + JVM.hashOf(vm, x)) | 0; }); return h; },
		'toString()Ljava/lang/String;': function (vm, self) { return '[' + self.$list.map(function (x) { return x === self ? '(this Collection)' : toStr(vm, x); }).join(', ') + ']'; },
		'ensureCapacity(I)V': function () {}, 'trimToSize()V': function () {},
		'clone()Ljava/lang/Object;': function (vm, self) { var o = vm.newObject(self.cls); o.$list = self.$list.slice(); return o; },
		'addFirst(Ljava/lang/Object;)V': function (vm, self, a) { self.$list.unshift(a[0]); },
		'addLast(Ljava/lang/Object;)V': function (vm, self, a) { self.$list.push(a[0]); },
		'offer(Ljava/lang/Object;)Z': function (vm, self, a) { self.$list.push(a[0]); return 1; },
		'offerFirst(Ljava/lang/Object;)Z': function (vm, self, a) { self.$list.unshift(a[0]); return 1; },
		'offerLast(Ljava/lang/Object;)Z': function (vm, self, a) { self.$list.push(a[0]); return 1; },
		'removeFirst()Ljava/lang/Object;': function (vm, self) { if (!self.$list.length) vm.throwNew('java/util/NoSuchElementException', null); return self.$list.shift(); },
		'removeLast()Ljava/lang/Object;': function (vm, self) { if (!self.$list.length) vm.throwNew('java/util/NoSuchElementException', null); return self.$list.pop(); },
		'remove()Ljava/lang/Object;': function (vm, self) { if (!self.$list.length) vm.throwNew('java/util/NoSuchElementException', null); return self.$list.shift(); },
		'poll()Ljava/lang/Object;': function (vm, self) { return self.$list.length ? self.$list.shift() : null; },
		'pollFirst()Ljava/lang/Object;': function (vm, self) { return self.$list.length ? self.$list.shift() : null; },
		'pollLast()Ljava/lang/Object;': function (vm, self) { return self.$list.length ? self.$list.pop() : null; },
		'peekFirst()Ljava/lang/Object;': function (vm, self) { return self.$list.length ? self.$list[0] : null; },
		'peekLast()Ljava/lang/Object;': function (vm, self) { return self.$list.length ? self.$list[self.$list.length - 1] : null; },
		'getFirst()Ljava/lang/Object;': function (vm, self) { if (!self.$list.length) vm.throwNew('java/util/NoSuchElementException', null); return self.$list[0]; },
		'getLast()Ljava/lang/Object;': function (vm, self) { if (!self.$list.length) vm.throwNew('java/util/NoSuchElementException', null); return self.$list[self.$list.length - 1]; },
		'element()Ljava/lang/Object;': function (vm, self) { if (!self.$list.length) vm.throwNew('java/util/NoSuchElementException', null); return self.$list[0]; },
		'descendingIterator()Ljava/util/Iterator;': function (vm, self) { return makeIterator(vm, self.$list.slice().reverse(), null); },
		'push(Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { self.$list.push(a[0]); return a[0]; },
		'pop()Ljava/lang/Object;': function (vm, self) { if (!self.$list.length) vm.throwNew('java/util/EmptyStackException', null); return self.$list.pop(); },
		'peek()Ljava/lang/Object;': function (vm, self) { return self.$list.length ? self.$list[self.$list.length - 1] : null; },
		'empty()Z': function (vm, self) { return self.$list.length ? 0 : 1; },
		'addElement(Ljava/lang/Object;)V': function (vm, self, a) { self.$list.push(a[0]); },
		'elementAt(I)Ljava/lang/Object;': function (vm, self, a) { return self.$list[a[0]]; },
		'elements()Ljava/util/Enumeration;': function (vm, self) { return makeIterator(vm, self.$list.slice(), null); },
		'removeAllElements()V': function (vm, self) { self.$list.length = 0; },
		'firstElement()Ljava/lang/Object;': function (vm, self) { return self.$list[0]; },
		'lastElement()Ljava/lang/Object;': function (vm, self) { return self.$list[self.$list.length - 1]; },
	};
	var listIfaces = ['java/util/List', 'java/util/Deque', 'java/util/RandomAccess', 'java/lang/Cloneable', 'java/io/Serializable'];
	def('java/util/AbstractCollection', { interfaces: ['java/util/Collection'], methods: { '<init>()V': function (vm, self) { if (!self.$list) self.$list = []; } } });
	def('java/util/AbstractList', { super: 'java/util/AbstractCollection', interfaces: ['java/util/List'], methods: { '<init>()V': function () {} } });
	def('java/util/ArrayList', { super: 'java/util/AbstractList', interfaces: listIfaces, methods: listMethods });
	var linked = Object.assign({}, listMethods, {
		'push(Ljava/lang/Object;)V': function (vm, self, a) { self.$list.unshift(a[0]); },
		'pop()Ljava/lang/Object;': function (vm, self) { if (!self.$list.length) vm.throwNew('java/util/NoSuchElementException', null); return self.$list.shift(); },
		'peek()Ljava/lang/Object;': function (vm, self) { return self.$list.length ? self.$list[0] : null; },
	});
	def('java/util/LinkedList', { super: 'java/util/AbstractList', interfaces: listIfaces, methods: linked });
	def('java/util/ArrayDeque', { super: 'java/util/AbstractCollection', interfaces: ['java/util/Deque'], methods: linked });
	def('java/util/Vector', { super: 'java/util/AbstractList', interfaces: listIfaces, methods: listMethods });
	def('java/util/Stack', { super: 'java/util/Vector', methods: { '<init>()V': function (vm, self) { self.$list = []; } } });
	def('java/util/concurrent/CopyOnWriteArrayList', { super: 'java/util/ArrayList', methods: {} });
	def('java/util/PriorityQueue', { super: 'java/util/AbstractCollection', interfaces: ['java/util/Queue'], methods: {
		'<init>()V': function (vm, self) { self.$list = []; },
		'<init>(I)V': function (vm, self) { self.$list = []; },
		'<init>(ILjava/util/Comparator;)V': function (vm, self, a) { self.$list = []; self.$cmp = a[1]; },
		'<init>(Ljava/util/Comparator;)V': function (vm, self, a) { self.$list = []; self.$cmp = a[0]; },
		'add(Ljava/lang/Object;)Z': function (vm, self, a) { pqAdd(vm, self, a[0]); return 1; },
		'offer(Ljava/lang/Object;)Z': function (vm, self, a) { pqAdd(vm, self, a[0]); return 1; },
		'poll()Ljava/lang/Object;': function (vm, self) { return self.$list.length ? self.$list.shift() : null; },
		'peek()Ljava/lang/Object;': function (vm, self) { return self.$list.length ? self.$list[0] : null; },
		'size()I': listMethods['size()I'], 'isEmpty()Z': listMethods['isEmpty()Z'], 'clear()V': listMethods['clear()V'],
		'iterator()Ljava/util/Iterator;': listMethods['iterator()Ljava/util/Iterator;'],
		'contains(Ljava/lang/Object;)Z': listMethods['contains(Ljava/lang/Object;)Z'],
		'remove(Ljava/lang/Object;)Z': listMethods['remove(Ljava/lang/Object;)Z'],
	} });
	function pqAdd(vm, self, v) {
		var l = self.$list, i = 0;
		while (i < l.length && compare(vm, l[i], v, self.$cmp) <= 0) i++;
		l.splice(i, 0, v);
	}

	var mapMethods = function (sorted, identity) {
		var init = function (vm, self) { self.$m = new JMap(vm, identity); if (sorted) self.$m.sorted = true; };
		return {
			'<init>()V': init,
			'<init>(I)V': init,
			'<init>(IF)V': init,
			'<init>(Ljava/util/Map;)V': function (vm, self, a) { init(vm, self); mapEntries(vm, a[0]).forEach(function (e) { self.$m.put(e.k, e.v); }); },
			'<init>(Ljava/util/Comparator;)V': function (vm, self, a) { init(vm, self); self.$m.comparator = a[0]; },
			'<init>(Ljava/lang/Class;)V': init,
			'size()I': function (vm, self) { return self.$m.size; },
			'isEmpty()Z': function (vm, self) { return self.$m.size ? 0 : 1; },
			'get(Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { return self.$m.get(a[0]); },
			'getOrDefault(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { var e = self.$m.find(a[0]); return e ? e.v : a[1]; },
			'put(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { return self.$m.put(a[0], a[1]); },
			'putIfAbsent(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { var e = self.$m.find(a[0]); if (e && e.v !== null) return e.v; self.$m.put(a[0], a[1]); return null; },
			'remove(Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { var e = self.$m.remove(a[0]); return e ? e.v : null; },
			'containsKey(Ljava/lang/Object;)Z': function (vm, self, a) { return self.$m.has(a[0]) ? 1 : 0; },
			'containsValue(Ljava/lang/Object;)Z': function (vm, self, a) { return self.$m.entries().some(function (e) { return JVM.equalsOf(vm, e.v, a[0]); }) ? 1 : 0; },
			'clear()V': function (vm, self) { self.$m.clear(); },
			'putAll(Ljava/util/Map;)V': function (vm, self, a) { mapEntries(vm, a[0]).forEach(function (e) { self.$m.put(e.k, e.v); }); },
			'keySet()Ljava/util/Set;': function (vm, self) { return mapView(vm, self.$m, 'k'); },
			'values()Ljava/util/Collection;': function (vm, self) { return mapView(vm, self.$m, 'v'); },
			'entrySet()Ljava/util/Set;': function (vm, self) { return mapView(vm, self.$m, 'e'); },
			'computeIfAbsent(Ljava/lang/Object;Ljava/util/function/Function;)Ljava/lang/Object;': function (vm, self, a) {
				var e = self.$m.find(a[0]);
				if (e && e.v !== null) return e.v;
				var v = vm.callVirtual(a[1], 'apply', '(' + OBJ + ')' + OBJ, [a[0]]);
				if (v !== null) self.$m.put(a[0], v);
				return v;
			},
			'merge(Ljava/lang/Object;Ljava/lang/Object;Ljava/util/function/BiFunction;)Ljava/lang/Object;': function (vm, self, a) {
				var e = self.$m.find(a[0]);
				var v = e && e.v !== null ? vm.callVirtual(a[2], 'apply', '(' + OBJ + OBJ + ')' + OBJ, [e.v, a[1]]) : a[1];
				if (v === null) self.$m.remove(a[0]); else self.$m.put(a[0], v);
				return v;
			},
			'forEach(Ljava/util/function/BiConsumer;)V': function (vm, self, a) { self.$m.entries().forEach(function (e) { vm.callVirtual(a[0], 'accept', '(' + OBJ + OBJ + ')V', [e.k, e.v]); }); },
			'equals(Ljava/lang/Object;)Z': function (vm, self, a) {
				var o = a[0];
				if (!o || !o.$m || o.$m.size !== self.$m.size) return 0;
				return self.$m.entries().every(function (e) { var f = o.$m.find(e.k); return f && JVM.equalsOf(vm, f.v, e.v); }) ? 1 : 0;
			},
			'hashCode()I': function (vm, self) { var h = 0; self.$m.entries().forEach(function (e) { h = (h + (JVM.hashOf(vm, e.k) ^ JVM.hashOf(vm, e.v))) | 0; }); return h; },
			'toString()Ljava/lang/String;': function (vm, self) { return '{' + self.$m.entries().map(function (e) { return toStr(vm, e.k) + '=' + toStr(vm, e.v); }).join(', ') + '}'; },
			'clone()Ljava/lang/Object;': function (vm, self) { var o = vm.newObject(self.cls); init(vm, o); self.$m.entries().forEach(function (e) { o.$m.put(e.k, e.v); }); return o; },
			'firstKey()Ljava/lang/Object;': function (vm, self) { var es = self.$m.entries(); if (!es.length) vm.throwNew('java/util/NoSuchElementException', null); return es[0].k; },
			'lastKey()Ljava/lang/Object;': function (vm, self) { var es = self.$m.entries(); if (!es.length) vm.throwNew('java/util/NoSuchElementException', null); return es[es.length - 1].k; },
			'keys()Ljava/util/Enumeration;': function (vm, self) { return makeIterator(vm, self.$m.entries().map(function (e) { return e.k; }), null); },
			'elements()Ljava/util/Enumeration;': function (vm, self) { return makeIterator(vm, self.$m.entries().map(function (e) { return e.v; }), null); },
		};
	};
	def('java/util/AbstractMap', { interfaces: ['java/util/Map'], methods: { '<init>()V': function (vm, self) { if (!self.$m) self.$m = new JMap(vm); } } });
	def('java/util/HashMap', { super: 'java/util/AbstractMap', interfaces: ['java/util/Map', 'java/lang/Cloneable', 'java/io/Serializable'], methods: mapMethods(false) });
	def('java/util/LinkedHashMap', { super: 'java/util/HashMap', methods: mapMethods(false) });
	def('java/util/TreeMap', { super: 'java/util/AbstractMap', interfaces: ['java/util/NavigableMap'], methods: mapMethods(true) });
	def('java/util/Hashtable', { super: 'java/util/AbstractMap', interfaces: ['java/util/Map'], methods: mapMethods(false) });
	def('java/util/IdentityHashMap', { super: 'java/util/AbstractMap', interfaces: ['java/util/Map'], methods: mapMethods(false, true) });
	def('java/util/WeakHashMap', { super: 'java/util/AbstractMap', interfaces: ['java/util/Map'], methods: mapMethods(false, true) });
	def('java/util/EnumMap', { super: 'java/util/AbstractMap', interfaces: ['java/util/Map'], methods: mapMethods(false, true) });
	def('java/util/concurrent/ConcurrentHashMap', { super: 'java/util/AbstractMap', interfaces: ['java/util/Map'], methods: mapMethods(false) });

	var setMethods = function (sorted, identity) {
		var init = function (vm, self) { self.$m = new JMap(vm, identity); self.$set = true; if (sorted) self.$m.sorted = true; };
		return {
			'<init>()V': init, '<init>(I)V': init, '<init>(IF)V': init,
			'<init>(Ljava/util/Collection;)V': function (vm, self, a) { init(vm, self); iterate(vm, a[0]).forEach(function (x) { self.$m.put(x, true); }); },
			'<init>(Ljava/util/Comparator;)V': function (vm, self, a) { init(vm, self); self.$m.comparator = a[0]; },
			'size()I': function (vm, self) { return self.$m.size; },
			'isEmpty()Z': function (vm, self) { return self.$m.size ? 0 : 1; },
			'add(Ljava/lang/Object;)Z': function (vm, self, a) { if (self.$m.has(a[0])) return 0; self.$m.put(a[0], true); return 1; },
			'remove(Ljava/lang/Object;)Z': function (vm, self, a) { return self.$m.remove(a[0]) ? 1 : 0; },
			'contains(Ljava/lang/Object;)Z': function (vm, self, a) { return self.$m.has(a[0]) ? 1 : 0; },
			'clear()V': function (vm, self) { self.$m.clear(); },
			'iterator()Ljava/util/Iterator;': function (vm, self) { var m = self.$m; return makeIterator(vm, m.entries().map(function (e) { return e.k; }), function (k) { m.remove(k); }); },
			'addAll(Ljava/util/Collection;)Z': function (vm, self, a) { var ch = 0; iterate(vm, a[0]).forEach(function (x) { if (!self.$m.has(x)) { self.$m.put(x, true); ch = 1; } }); return ch; },
			'removeAll(Ljava/util/Collection;)Z': function (vm, self, a) { var ch = 0; iterate(vm, a[0]).forEach(function (x) { if (self.$m.remove(x)) ch = 1; }); return ch; },
			'retainAll(Ljava/util/Collection;)Z': function (vm, self, a) { var keep = iterate(vm, a[0]), ch = 0; self.$m.entries().forEach(function (e) { if (indexIn(vm, keep, e.k) < 0) { self.$m.remove(e.k); ch = 1; } }); return ch; },
			'containsAll(Ljava/util/Collection;)Z': function (vm, self, a) { return iterate(vm, a[0]).every(function (x) { return self.$m.has(x); }) ? 1 : 0; },
			'toArray()[Ljava/lang/Object;': function (vm, self) { return JVM.javaArray(vm, OBJ, self.$m.entries().map(function (e) { return e.k; })); },
			'toArray([Ljava/lang/Object;)[Ljava/lang/Object;': function (vm, self, a) { return JVM.javaArray(vm, a[0].cls.component, self.$m.entries().map(function (e) { return e.k; })); },
			'forEach(Ljava/util/function/Consumer;)V': function (vm, self, a) { self.$m.entries().forEach(function (e) { vm.callVirtual(a[0], 'accept', '(' + OBJ + ')V', [e.k]); }); },
			'removeIf(Ljava/util/function/Predicate;)Z': function (vm, self, a) { var ch = 0; self.$m.entries().forEach(function (e) { if (vm.callVirtual(a[0], 'test', '(' + OBJ + ')Z', [e.k])) { self.$m.remove(e.k); ch = 1; } }); return ch; },
			'equals(Ljava/lang/Object;)Z': function (vm, self, a) { var o = a[0]; if (!o || !o.$m || o.$m.size !== self.$m.size) return 0; return self.$m.entries().every(function (e) { return o.$m.has(e.k); }) ? 1 : 0; },
			'hashCode()I': function (vm, self) { var h = 0; self.$m.entries().forEach(function (e) { h = (h + JVM.hashOf(vm, e.k)) | 0; }); return h; },
			'toString()Ljava/lang/String;': function (vm, self) { return '[' + self.$m.entries().map(function (e) { return toStr(vm, e.k); }).join(', ') + ']'; },
			'first()Ljava/lang/Object;': function (vm, self) { var es = self.$m.entries(); if (!es.length) vm.throwNew('java/util/NoSuchElementException', null); return es[0].k; },
			'last()Ljava/lang/Object;': function (vm, self) { var es = self.$m.entries(); if (!es.length) vm.throwNew('java/util/NoSuchElementException', null); return es[es.length - 1].k; },
			'clone()Ljava/lang/Object;': function (vm, self) { var o = vm.newObject(self.cls); init(vm, o); self.$m.entries().forEach(function (e) { o.$m.put(e.k, true); }); return o; },
		};
	};
	def('java/util/AbstractSet', { super: 'java/util/AbstractCollection', interfaces: ['java/util/Set'], methods: { '<init>()V': function () {} } });
	def('java/util/HashSet', { super: 'java/util/AbstractSet', interfaces: ['java/util/Set', 'java/lang/Cloneable', 'java/io/Serializable'], methods: setMethods(false) });
	def('java/util/LinkedHashSet', { super: 'java/util/HashSet', methods: setMethods(false) });
	def('java/util/TreeSet', { super: 'java/util/AbstractSet', interfaces: ['java/util/NavigableSet'], methods: setMethods(true) });
	def('java/util/EnumSet', { super: 'java/util/AbstractSet', interfaces: ['java/util/Set'], methods: setMethods(false, true), staticMethods: {
		'noneOf(Ljava/lang/Class;)Ljava/util/EnumSet;': function (vm) { return newSet(vm, 'java/util/EnumSet', []); },
		'allOf(Ljava/lang/Class;)Ljava/util/EnumSet;': function (vm, n, a) { var v = vm.callVirtual(a[0], 'getEnumConstants', '()[Ljava/lang/Object;', []); return newSet(vm, 'java/util/EnumSet', v ? Array.prototype.slice.call(v.a) : []); },
		'of(Ljava/lang/Enum;)Ljava/util/EnumSet;': function (vm, n, a) { return newSet(vm, 'java/util/EnumSet', a); },
		'of(Ljava/lang/Enum;Ljava/lang/Enum;)Ljava/util/EnumSet;': function (vm, n, a) { return newSet(vm, 'java/util/EnumSet', a); },
		'of(Ljava/lang/Enum;Ljava/lang/Enum;Ljava/lang/Enum;)Ljava/util/EnumSet;': function (vm, n, a) { return newSet(vm, 'java/util/EnumSet', a); },
	} });

	def('mcre/MapView', {
		super: 'java/util/AbstractSet', interfaces: ['java/util/Set'],
		methods: {
			'size()I': function (vm, self) { return self.$view.size; },
			'isEmpty()Z': function (vm, self) { return self.$view.size ? 0 : 1; },
			'iterator()Ljava/util/Iterator;': function (vm, self) {
				var m = self.$view, es = m.entries(), kind = self.$kind;
				var items = es.map(function (e) { return kind === 'k' ? e.k : kind === 'v' ? e.v : entryObj(vm, e); });
				return makeIterator(vm, items, function (x, i) { m.remove(es[i].k); });
			},
			'contains(Ljava/lang/Object;)Z': function (vm, self, a) {
				if (self.$kind === 'k') return self.$view.has(a[0]) ? 1 : 0;
				return viewItems(self).some(function (x) { return JVM.equalsOf(vm, x, a[0]); }) ? 1 : 0;
			},
			'remove(Ljava/lang/Object;)Z': function (vm, self, a) {
				if (self.$kind === 'k') return self.$view.remove(a[0]) ? 1 : 0;
				var es = self.$view.entries();
				for (var i = 0; i < es.length; i++) if (JVM.equalsOf(vm, self.$kind === 'v' ? es[i].v : entryObj(vm, es[i]), a[0])) { self.$view.remove(es[i].k); return 1; }
				return 0;
			},
			'clear()V': function (vm, self) { self.$view.clear(); },
			'toArray()[Ljava/lang/Object;': function (vm, self) { return JVM.javaArray(vm, OBJ, viewItems(self)); },
			'toArray([Ljava/lang/Object;)[Ljava/lang/Object;': function (vm, self, a) { return JVM.javaArray(vm, a[0].cls.component, viewItems(self)); },
			'forEach(Ljava/util/function/Consumer;)V': function (vm, self, a) { viewItems(self).forEach(function (x) { vm.callVirtual(a[0], 'accept', '(' + OBJ + ')V', [x]); }); },
			'toString()Ljava/lang/String;': function (vm, self) { return '[' + viewItems(self).map(function (x) { return toStr(vm, x); }).join(', ') + ']'; },
			'containsAll(Ljava/util/Collection;)Z': function (vm, self, a) { var items = viewItems(self); return iterate(vm, a[0]).every(function (x) { return indexIn(vm, items, x) >= 0; }) ? 1 : 0; },
			'removeIf(Ljava/util/function/Predicate;)Z': function (vm, self, a) {
				var ch = 0, m = self.$view, kind = self.$kind;
				m.entries().forEach(function (e) {
					var x = kind === 'k' ? e.k : kind === 'v' ? e.v : entryObj(vm, e);
					if (vm.callVirtual(a[0], 'test', '(' + OBJ + ')Z', [x])) { m.remove(e.k); ch = 1; }
				});
				return ch;
			},
		},
	});

	def('java/util/Collections', {
		statics: { EMPTY_LIST: null, EMPTY_MAP: null, EMPTY_SET: null },
		clinit: function (vm, c) { c.statics.EMPTY_LIST = newList(vm, []); c.statics.EMPTY_MAP = newMap(vm); c.statics.EMPTY_SET = newSet(vm, 'java/util/HashSet', []); },
		staticMethods: {
			'emptyList()Ljava/util/List;': function (vm) { return newList(vm, []); },
			'emptyMap()Ljava/util/Map;': function (vm) { return newMap(vm); },
			'emptySet()Ljava/util/Set;': function (vm) { return newSet(vm, 'java/util/HashSet', []); },
			'emptyIterator()Ljava/util/Iterator;': function (vm) { return makeIterator(vm, [], null); },
			'singletonList(Ljava/lang/Object;)Ljava/util/List;': function (vm, n, a) { return newList(vm, [a[0]]); },
			'singleton(Ljava/lang/Object;)Ljava/util/Set;': function (vm, n, a) { return newSet(vm, 'java/util/HashSet', [a[0]]); },
			'singletonMap(Ljava/lang/Object;Ljava/lang/Object;)Ljava/util/Map;': function (vm, n, a) { var m = newMap(vm); m.$m.put(a[0], a[1]); return m; },
			'unmodifiableList(Ljava/util/List;)Ljava/util/List;': function (vm, n, a) { return a[0]; },
			'unmodifiableSet(Ljava/util/Set;)Ljava/util/Set;': function (vm, n, a) { return a[0]; },
			'unmodifiableMap(Ljava/util/Map;)Ljava/util/Map;': function (vm, n, a) { return a[0]; },
			'unmodifiableCollection(Ljava/util/Collection;)Ljava/util/Collection;': function (vm, n, a) { return a[0]; },
			'synchronizedList(Ljava/util/List;)Ljava/util/List;': function (vm, n, a) { return a[0]; },
			'synchronizedMap(Ljava/util/Map;)Ljava/util/Map;': function (vm, n, a) { return a[0]; },
			'synchronizedSet(Ljava/util/Set;)Ljava/util/Set;': function (vm, n, a) { return a[0]; },
			'sort(Ljava/util/List;)V': function (vm, n, a) { sortList(vm, a[0], null); },
			'sort(Ljava/util/List;Ljava/util/Comparator;)V': function (vm, n, a) { sortList(vm, a[0], a[1]); },
			'reverse(Ljava/util/List;)V': function (vm, n, a) { if (a[0].$list) a[0].$list.reverse(); },
			'shuffle(Ljava/util/List;)V': function (vm, n, a) { shuffle(a[0].$list, function (k) { return Math.floor(Math.random() * k); }); },
			'shuffle(Ljava/util/List;Ljava/util/Random;)V': function (vm, n, a) { shuffle(a[0].$list, function (k) { return vm.callVirtual(a[1], 'nextInt', '(I)I', [k]); }); },
			'swap(Ljava/util/List;II)V': function (vm, n, a) { var l = a[0].$list, t = l[a[1]]; l[a[1]] = l[a[2]]; l[a[2]] = t; },
			'addAll(Ljava/util/Collection;[Ljava/lang/Object;)Z': function (vm, n, a) {
				Array.prototype.forEach.call(a[1].a, function (x) { vm.callVirtual(a[0], 'add', '(' + OBJ + ')Z', [x]); });
				return a[1].a.length ? 1 : 0;
			},
			'max(Ljava/util/Collection;)Ljava/lang/Object;': function (vm, n, a) { return iterate(vm, a[0]).reduce(function (m, x) { return compare(vm, x, m, null) > 0 ? x : m; }); },
			'min(Ljava/util/Collection;)Ljava/lang/Object;': function (vm, n, a) { return iterate(vm, a[0]).reduce(function (m, x) { return compare(vm, x, m, null) < 0 ? x : m; }); },
			'frequency(Ljava/util/Collection;Ljava/lang/Object;)I': function (vm, n, a) { return iterate(vm, a[0]).filter(function (x) { return JVM.equalsOf(vm, x, a[1]); }).length; },
			'nCopies(ILjava/lang/Object;)Ljava/util/List;': function (vm, n, a) { var l = []; for (var i = 0; i < a[0]; i++) l.push(a[1]); return newList(vm, l); },
			'reverseOrder()Ljava/util/Comparator;': function (vm) { return comparatorFn(vm, function (x, y) { return -compare(vm, x, y, null); }); },
		},
	});
	var arraysStatics = {
		'asList([Ljava/lang/Object;)Ljava/util/List;': function (vm, n, a) { return newList(vm, Array.prototype.slice.call(a[0].a)); },
		'sort([Ljava/lang/Object;)V': function (vm, n, a) { var x = Array.prototype.slice.call(a[0].a); stableSort(vm, x, null); x.forEach(function (v, i) { a[0].a[i] = v; }); },
		'sort([Ljava/lang/Object;Ljava/util/Comparator;)V': function (vm, n, a) { var x = Array.prototype.slice.call(a[0].a); stableSort(vm, x, a[1]); x.forEach(function (v, i) { a[0].a[i] = v; }); },
		'sort([Ljava/lang/Object;IILjava/util/Comparator;)V': function (vm, n, a) { var x = Array.prototype.slice.call(a[0].a, a[1], a[2]); stableSort(vm, x, a[3]); x.forEach(function (v, i) { a[0].a[a[1] + i] = v; }); },
		'toString([Ljava/lang/Object;)Ljava/lang/String;': function (vm, n, a) { return a[0] === null ? 'null' : '[' + Array.prototype.map.call(a[0].a, function (x) { return toStr(vm, x); }).join(', ') + ']'; },
		'deepToString([Ljava/lang/Object;)Ljava/lang/String;': function (vm, n, a) { return deepStr(vm, a[0]); },
		'equals([Ljava/lang/Object;[Ljava/lang/Object;)Z': function (vm, n, a) { return arrEq(vm, a[0], a[1], true) ? 1 : 0; },
		'hashCode([Ljava/lang/Object;)I': function (vm, n, a) { var h = 1; if (!a[0]) return 0; Array.prototype.forEach.call(a[0].a, function (x) { h = (Math.imul(31, h) + JVM.hashOf(vm, x)) | 0; }); return h; },
		'fill([Ljava/lang/Object;Ljava/lang/Object;)V': function (vm, n, a) { a[0].a.fill(a[1]); },
		'fill([Ljava/lang/Object;IILjava/lang/Object;)V': function (vm, n, a) { a[0].a.fill(a[3], a[1], a[2]); },
		'copyOf([Ljava/lang/Object;I)[Ljava/lang/Object;': function (vm, n, a) { return copyOf(vm, a[0], 0, a[1]); },
		'copyOfRange([Ljava/lang/Object;II)[Ljava/lang/Object;': function (vm, n, a) { return copyOf(vm, a[0], a[1], a[2]); },
		'stream([Ljava/lang/Object;)Ljava/util/stream/Stream;': function (vm, n, a) { vm.warnOnce('stream', 'java.util.stream is not available here (left unplugged)'); return null; },
	};
	'IJFDBCSZ'.split('').forEach(function (t) {
		arraysStatics['fill([' + t + t + ')V'] = function (vm, n, a) { a[0].a.fill(a[1]); };
		arraysStatics['fill([' + t + 'II' + t + ')V'] = function (vm, n, a) { a[0].a.fill(a[3], a[1], a[2]); };
		arraysStatics['copyOf([' + t + 'I)[' + t] = function (vm, n, a) { return copyOf(vm, a[0], 0, a[1]); };
		arraysStatics['copyOfRange([' + t + 'II)[' + t] = function (vm, n, a) { return copyOf(vm, a[0], a[1], a[2]); };
		arraysStatics['equals([' + t + '[' + t + ')Z'] = function (vm, n, a) { return arrEq(vm, a[0], a[1], false) ? 1 : 0; };
		arraysStatics['hashCode([' + t + ')I'] = function (vm, n, a) { var h = 1; if (!a[0]) return 0; Array.prototype.forEach.call(a[0].a, function (x) { h = (Math.imul(31, h) + JVM.hashOf(vm, x)) | 0; }); return h; };
		arraysStatics['toString([' + t + ')Ljava/lang/String;'] = function (vm, n, a) { return a[0] === null ? 'null' : '[' + Array.prototype.map.call(a[0].a, function (x) { return JVM.stringOf(vm, x, t); }).join(', ') + ']'; };
		if (t !== 'Z') {
			arraysStatics['sort([' + t + ')V'] = function (vm, n, a) { numSort(a[0].a, 0, a[0].a.length); };
			arraysStatics['sort([' + t + 'II)V'] = function (vm, n, a) { numSort(a[0].a, a[1], a[2]); };
			arraysStatics['binarySearch([' + t + t + ')I'] = function (vm, n, a) { var x = a[0].a, lo = 0, hi = x.length - 1; while (lo <= hi) { var mid = (lo + hi) >>> 1; if (x[mid] < a[1]) lo = mid + 1; else if (x[mid] > a[1]) hi = mid - 1; else return mid; } return -(lo + 1); };
		}
	});
	def('java/util/Arrays', { staticMethods: arraysStatics });
	def('java/util/Objects', { staticMethods: {
		'equals(Ljava/lang/Object;Ljava/lang/Object;)Z': function (vm, n, a) { return JVM.equalsOf(vm, a[0], a[1]) ? 1 : 0; },
		'hashCode(Ljava/lang/Object;)I': function (vm, n, a) { return JVM.hashOf(vm, a[0]); },
		'hash([Ljava/lang/Object;)I': function (vm, n, a) { var h = 1; Array.prototype.forEach.call(a[0].a, function (x) { h = (Math.imul(31, h) + JVM.hashOf(vm, x)) | 0; }); return h; },
		'toString(Ljava/lang/Object;)Ljava/lang/String;': function (vm, n, a) { return toStr(vm, a[0]); },
		'toString(Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/String;': function (vm, n, a) { return a[0] === null ? a[1] : toStr(vm, a[0]); },
		'isNull(Ljava/lang/Object;)Z': function (vm, n, a) { return a[0] === null ? 1 : 0; },
		'nonNull(Ljava/lang/Object;)Z': function (vm, n, a) { return a[0] !== null ? 1 : 0; },
		'requireNonNull(Ljava/lang/Object;)Ljava/lang/Object;': function (vm, n, a) { if (a[0] === null) vm.throwNew('java/lang/NullPointerException', null); return a[0]; },
		'requireNonNull(Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/Object;': function (vm, n, a) { if (a[0] === null) vm.throwNew('java/lang/NullPointerException', a[1]); return a[0]; },
		'requireNonNullElse(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;': function (vm, n, a) { return a[0] !== null ? a[0] : a[1]; },
	} });

	var MULT = 0x5DEECE66Dn, MASK = (1n << 48n) - 1n;
	var next = function (self, bits) {
		self.$seed = (self.$seed * MULT + 0xBn) & MASK;
		return Number(BigInt.asIntN(32, self.$seed >> BigInt(48 - bits)));
	};
	var seedUniq = 8682522807148012n;
	def('java/util/Random', {
		methods: {
			'<init>()V': function (vm, self) { seedUniq = BigInt.asIntN(64, seedUniq * 181783497276652981n); self.$seed = (BigInt.asIntN(64, seedUniq ^ BigInt(Date.now()) * 1000000n) ^ MULT) & MASK; },
			'<init>(J)V': function (vm, self, a) { self.$seed = (a[0] ^ MULT) & MASK; self.$gauss = undefined; },
			'setSeed(J)V': function (vm, self, a) { self.$seed = (a[0] ^ MULT) & MASK; self.$gauss = undefined; },
			'next(I)I': function (vm, self, a) { return next(self, a[0]); },
			'nextInt()I': function (vm, self) { return next(self, 32); },
			'nextInt(I)I': function (vm, self, a) {
				var bound = a[0];
				if (bound <= 0) vm.throwNew('java/lang/IllegalArgumentException', 'bound must be positive');
				if ((bound & -bound) === bound) return Number((BigInt(bound) * BigInt(next(self, 31))) >> 31n);
				var bits, val;
				do { bits = next(self, 31); val = bits % bound; } while (bits - val + (bound - 1) > 2147483647);
				return val;
			},
			'nextInt(II)I': function (vm, self, a) { return a[0] + vm.callVirtual(self, 'nextInt', '(I)I', [a[1] - a[0]]); },
			'nextLong()J': function (vm, self) { return BigInt.asIntN(64, (BigInt(next(self, 32)) << 32n) + BigInt(next(self, 32))); },
			'nextBoolean()Z': function (vm, self) { return next(self, 1) !== 0 ? 1 : 0; },
			'nextFloat()F': function (vm, self) { return next(self, 24) / 16777216; },
			'nextDouble()D': function (vm, self) { return (next(self, 26) * 134217728 + next(self, 27)) / 9007199254740992; },
			'nextGaussian()D': function (vm, self) {
				if (self.$gauss !== undefined) { var g = self.$gauss; self.$gauss = undefined; return g; }
				var v1, v2, s;
				do {
					v1 = 2 * ((next(self, 26) * 134217728 + next(self, 27)) / 9007199254740992) - 1;
					v2 = 2 * ((next(self, 26) * 134217728 + next(self, 27)) / 9007199254740992) - 1;
					s = v1 * v1 + v2 * v2;
				} while (s >= 1 || s === 0);
				var mul = Math.sqrt(-2 * Math.log(s) / s);
				self.$gauss = v2 * mul;
				return v1 * mul;
			},
			'nextBytes([B)V': function (vm, self, a) { var b = a[0].a; for (var i = 0; i < b.length;) for (var r = next(self, 32), n = Math.min(b.length - i, 4); n-- > 0; r >>= 8) b[i++] = (r << 24) >> 24; },
		},
	});

	def('java/util/StringTokenizer', { interfaces: ['java/util/Enumeration'], methods: {
		'<init>(Ljava/lang/String;)V': function (vm, self, a) { tok(self, a[0], ' \t\n\r\f'); },
		'<init>(Ljava/lang/String;Ljava/lang/String;)V': function (vm, self, a) { tok(self, a[0], a[1]); },
		'<init>(Ljava/lang/String;Ljava/lang/String;Z)V': function (vm, self, a) { tok(self, a[0], a[1]); },
		'hasMoreTokens()Z': function (vm, self) { return self.$i < self.$t.length ? 1 : 0; },
		'hasMoreElements()Z': function (vm, self) { return self.$i < self.$t.length ? 1 : 0; },
		'nextToken()Ljava/lang/String;': function (vm, self) { if (self.$i >= self.$t.length) vm.throwNew('java/util/NoSuchElementException', null); return self.$t[self.$i++]; },
		'nextElement()Ljava/lang/Object;': function (vm, self) { return self.$t[self.$i++]; },
		'countTokens()I': function (vm, self) { return self.$t.length - self.$i; },
	} });
	function tok(self, s, delims) { var re = new RegExp('[' + delims.replace(/[\\\]^-]/g, '\\$&') + ']+'); self.$t = s.split(re).filter(function (x) { return x.length; }); self.$i = 0; }
	def('java/util/Locale', {
		statics: { ROOT: null, ENGLISH: null, US: null, UK: null },
		clinit: function (vm, c) { ['ROOT', 'ENGLISH', 'US', 'UK'].forEach(function (k) { var o = vm.newObject(c); o.$tag = k === 'ROOT' ? '' : 'en'; c.statics[k] = o; }); },
		staticMethods: { 'getDefault()Ljava/util/Locale;': function (vm) { var c = vm.loadClass('java/util/Locale'); vm.initClass(c); return c.statics.US; } },
		methods: { 'toString()Ljava/lang/String;': function (vm, self) { return self.$tag || ''; }, 'getLanguage()Ljava/lang/String;': function () { return 'en'; } },
	});
	def('java/util/UUID', {
		methods: {
			'<init>(JJ)V': function (vm, self, a) { self.$hi = a[0]; self.$lo = a[1]; },
			'toString()Ljava/lang/String;': function (vm, self) { return uuidStr(self); },
			'hashCode()I': function (vm, self) { var x = self.$hi ^ self.$lo; return Number(BigInt.asIntN(32, (x >> 32n) ^ x)); },
			'equals(Ljava/lang/Object;)Z': function (vm, self, a) { return a[0] && a[0].$hi === self.$hi && a[0].$lo === self.$lo ? 1 : 0; },
			'getMostSignificantBits()J': function (vm, self) { return self.$hi; },
			'getLeastSignificantBits()J': function (vm, self) { return self.$lo; },
		},
		staticMethods: {
			'randomUUID()Ljava/util/UUID;': function (vm) {
				var o = vm.newObject(vm.loadClass('java/util/UUID')), r = function () { return BigInt(Math.floor(Math.random() * 4294967296)); };
				o.$hi = BigInt.asIntN(64, ((r() << 32n) | r()) & ~0xF000n | 0x4000n);
				o.$lo = BigInt.asIntN(64, ((r() << 32n) | r()) & 0x3FFFFFFFFFFFFFFFn | (1n << 63n));
				return o;
			},
			'fromString(Ljava/lang/String;)Ljava/util/UUID;': function (vm, n, a) {
				var h = a[0].replace(/-/g, ''), o = vm.newObject(vm.loadClass('java/util/UUID'));
				o.$hi = BigInt.asIntN(64, BigInt('0x' + h.substring(0, 16))); o.$lo = BigInt.asIntN(64, BigInt('0x' + h.substring(16, 32)));
				return o;
			},
			'nameUUIDFromBytes([B)Ljava/util/UUID;': function (vm, n, a) {
				var o = vm.newObject(vm.loadClass('java/util/UUID')), h = 0n;
				Array.prototype.forEach.call(a[0].a, function (b) { h = BigInt.asIntN(64, h * 31n + BigInt(b)); });
				o.$hi = h; o.$lo = BigInt.asIntN(64, h * 0x9E3779B97F4A7C15n);
				return o;
			},
		},
	});
	function uuidStr(u) {
		var h = BigInt.asUintN(64, u.$hi).toString(16).padStart(16, '0') + BigInt.asUintN(64, u.$lo).toString(16).padStart(16, '0');
		return h.substring(0, 8) + '-' + h.substring(8, 12) + '-' + h.substring(12, 16) + '-' + h.substring(16, 20) + '-' + h.substring(20);
	}
	def('java/util/Optional', {
		methods: {
			'isPresent()Z': function (vm, self) { return self.$v !== null ? 1 : 0; },
			'isEmpty()Z': function (vm, self) { return self.$v === null ? 1 : 0; },
			'get()Ljava/lang/Object;': function (vm, self) { if (self.$v === null) vm.throwNew('java/util/NoSuchElementException', 'No value present'); return self.$v; },
			'orElse(Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { return self.$v !== null ? self.$v : a[0]; },
			'orElseGet(Ljava/util/function/Supplier;)Ljava/lang/Object;': function (vm, self, a) { return self.$v !== null ? self.$v : vm.callVirtual(a[0], 'get', '()' + OBJ, []); },
			'ifPresent(Ljava/util/function/Consumer;)V': function (vm, self, a) { if (self.$v !== null) vm.callVirtual(a[0], 'accept', '(' + OBJ + ')V', [self.$v]); },
			'map(Ljava/util/function/Function;)Ljava/util/Optional;': function (vm, self, a) { return optional(vm, self.$v === null ? null : vm.callVirtual(a[0], 'apply', '(' + OBJ + ')' + OBJ, [self.$v])); },
		},
		staticMethods: {
			'of(Ljava/lang/Object;)Ljava/util/Optional;': function (vm, n, a) { return optional(vm, a[0]); },
			'ofNullable(Ljava/lang/Object;)Ljava/util/Optional;': function (vm, n, a) { return optional(vm, a[0]); },
			'empty()Ljava/util/Optional;': function (vm) { return optional(vm, null); },
		},
	});
	function optional(vm, v) { var o = vm.newObject(vm.loadClass('java/util/Optional')); o.$v = v === undefined ? null : v; return o; }
	var atomic = function (name, t, def0) {
		var m = {
			'<init>()V': function (vm, self) { self.$v = def0; },
			['<init>(' + t + ')V']: function (vm, self, a) { self.$v = a[0]; },
			['get()' + t]: function (vm, self) { return self.$v; },
			['set(' + t + ')V']: function (vm, self, a) { self.$v = a[0]; },
			['getAndSet(' + t + ')' + t]: function (vm, self, a) { var o = self.$v; self.$v = a[0]; return o; },
			['compareAndSet(' + t + t + ')Z']: function (vm, self, a) { if (self.$v !== a[0]) return 0; self.$v = a[1]; return 1; },
			'toString()Ljava/lang/String;': function (vm, self) { return toStr(vm, self.$v); },
		};
		if (t === 'I' || t === 'J') {
			var one = t === 'I' ? 1 : 1n, fix = t === 'I' ? function (x) { return x | 0; } : function (x) { return BigInt.asIntN(64, x); };
			m['incrementAndGet()' + t] = function (vm, self) { return (self.$v = fix(self.$v + one)); };
			m['decrementAndGet()' + t] = function (vm, self) { return (self.$v = fix(self.$v - one)); };
			m['getAndIncrement()' + t] = function (vm, self) { var o = self.$v; self.$v = fix(o + one); return o; };
			m['getAndDecrement()' + t] = function (vm, self) { var o = self.$v; self.$v = fix(o - one); return o; };
			m['addAndGet(' + t + ')' + t] = function (vm, self, a) { return (self.$v = fix(self.$v + a[0])); };
			m['getAndAdd(' + t + ')' + t] = function (vm, self, a) { var o = self.$v; self.$v = fix(o + a[0]); return o; };
			m['intValue()I'] = function (vm, self) { return Number(self.$v) | 0; };
		}
		def(name, { super: t === OBJ ? 'java/lang/Object' : 'java/lang/Number', methods: m });
	};
	atomic('java/util/concurrent/atomic/AtomicInteger', 'I', 0);
	atomic('java/util/concurrent/atomic/AtomicLong', 'J', 0n);
	atomic('java/util/concurrent/atomic/AtomicBoolean', 'Z', 0);
	atomic('java/util/concurrent/atomic/AtomicReference', OBJ, null);
	def('java/util/Properties', { super: 'java/util/Hashtable', methods: Object.assign(mapMethods(false), {
		'getProperty(Ljava/lang/String;)Ljava/lang/String;': function (vm, self, a) { return self.$m.get(a[0]); },
		'getProperty(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;': function (vm, self, a) { var v = self.$m.get(a[0]); return v === null ? a[1] : v; },
		'setProperty(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/Object;': function (vm, self, a) { return self.$m.put(a[0], a[1]); },
		'load(Ljava/io/InputStream;)V': function (vm, self, a) { loadProps(vm, self, JVM.readAllText(vm, a[0])); },
		'load(Ljava/io/Reader;)V': function (vm, self, a) { loadProps(vm, self, JVM.readAllText(vm, a[0])); },
		'store(Ljava/io/OutputStream;Ljava/lang/String;)V': function (vm, self, a) { JVM.writeAllText(vm, a[0], propsText(vm, self, a[1])); },
		'store(Ljava/io/Writer;Ljava/lang/String;)V': function (vm, self, a) { JVM.writeAllText(vm, a[0], propsText(vm, self, a[1])); },
		'stringPropertyNames()Ljava/util/Set;': function (vm, self) { return newSet(vm, 'java/util/HashSet', self.$m.entries().map(function (e) { return e.k; })); },
	}) });
	function loadProps(vm, self, text) {
		if (!self.$m) self.$m = new JMap(vm);
		text.split(/\r?\n/).forEach(function (line) {
			line = line.replace(/^\s+/, '');
			if (!line || line[0] === '#' || line[0] === '!') return;
			var m = /^((?:\\.|[^=:\s])*)\s*[=:\s]\s*(.*)$/.exec(line);
			if (m) self.$m.put(m[1].replace(/\\(.)/g, '$1'), m[2]);
			else self.$m.put(line, '');
		});
	}
	function propsText(vm, self, comment) {
		var s = (comment ? '#' + comment + '\n' : '') + '#' + new Date().toString() + '\n';
		self.$m.entries().forEach(function (e) { s += toStr(vm, e.k) + '=' + toStr(vm, e.v) + '\n'; });
		return s;
	}
}

function idx(vm, self, i, extra) {
	if (i < 0 || i >= self.$list.length + extra) vm.throwNew('java/lang/IndexOutOfBoundsException', 'Index: ' + i + ', Size: ' + self.$list.length);
}
function indexIn(vm, arr, v) {
	for (var i = 0; i < arr.length; i++) if (JVM.equalsOf(vm, arr[i], v)) return i;
	return -1;
}
function listIter(vm, self) {
	var l = self.$list;
	var it = makeIterator(vm, l.slice(), function (x, i) { var k = i - (it.$removed || 0); if (self.$list[k] === x) self.$list.splice(k, 1); else { var j = self.$list.indexOf(x); if (j >= 0) self.$list.splice(j, 1); } });
	return it;
}
function newList(vm, items) { var o = vm.newObject(vm.loadClass('java/util/ArrayList')); o.$list = items; return o; }
function newMap(vm) { var o = vm.newObject(vm.loadClass('java/util/HashMap')); o.$m = new JMap(vm); return o; }
function newSet(vm, cname, items) {
	var o = vm.newObject(vm.loadClass(cname));
	o.$m = new JMap(vm, cname === 'java/util/EnumSet');
	o.$set = true;
	items.forEach(function (x) { o.$m.put(x, true); });
	return o;
}
function mapView(vm, m, kind) {
	var o = new JObject(vm.loadClass('mcre/MapView'));
	o.$view = m; o.$kind = kind; o.vm = vm;
	return o;
}
function mapEntries(vm, map) {
	if (map.$m) return map.$m.entries();
	return iterate(vm, vm.callVirtual(map, 'entrySet', '()Ljava/util/Set;', [])).map(function (e) {
		return { k: vm.callVirtual(e, 'getKey', '()' + OBJ, []), v: vm.callVirtual(e, 'getValue', '()' + OBJ, []) };
	});
}
function stableSort(vm, arr, cmp) {
	var idxd = arr.map(function (v, i) { return [v, i]; });
	idxd.sort(function (x, y) { return compare(vm, x[0], y[0], cmp) || x[1] - y[1]; });
	for (var i = 0; i < arr.length; i++) arr[i] = idxd[i][0];
}
function sortList(vm, list, cmp) {
	if (list.$list) { stableSort(vm, list.$list, cmp); return; }
	vm.callVirtual(list, 'sort', '(Ljava/util/Comparator;)V', [cmp]);
}
function numSort(a, from, to) {
	var part = Array.prototype.slice.call(a, from, to);
	part.sort(function (x, y) { return x < y ? -1 : x > y ? 1 : 0; });
	for (var i = 0; i < part.length; i++) a[from + i] = part[i];
}
function shuffle(l, rnd) {
	for (var i = l.length; i > 1; i--) { var j = rnd(i), t = l[i - 1]; l[i - 1] = l[j]; l[j] = t; }
}
function copyOf(vm, arr, from, to) {
	var n = to - from, out = vm.newArray(arr.cls.component, n);
	for (var i = 0; i < n && from + i < arr.a.length; i++) out.a[i] = arr.a[from + i];
	return out;
}
function arrEq(vm, a, b, deep) {
	if (a === b) return true;
	if (!a || !b || a.a.length !== b.a.length) return false;
	for (var i = 0; i < a.a.length; i++) if (deep ? !JVM.equalsOf(vm, a.a[i], b.a[i]) : a.a[i] !== b.a[i]) return false;
	return true;
}
function deepStr(vm, a) {
	if (a === null) return 'null';
	return '[' + Array.prototype.map.call(a.a, function (x) { return x instanceof JArray ? deepStr(vm, x) : JVM.stringOf(vm, x, a.cls.component.length === 1 ? a.cls.component : null); }).join(', ') + ']';
}
function comparatorFn(vm, f) {
	var c = vm.classes['mcre/FnComparator'];
	if (!c) {
		vm.defineNative('mcre/FnComparator', { interfaces: ['java/util/Comparator'], methods: {
			'compare(Ljava/lang/Object;Ljava/lang/Object;)I': function (vm, self, a) { return self.$f(a[0], a[1]); },
		} });
		c = vm.loadClass('mcre/FnComparator');
	}
	var o = new JObject(c);
	o.$f = f;
	return o;
}

JVM.JMap = JMap;
JVM.iterate = iterate;
JVM.compare = compare;
JVM.newList = newList;
JVM.newMap = newMap;
JVM.installUtil = installUtil;
})();

(function () {
'use strict';

var JObject = JVM.JObject;

function fsOf(vm) { return vm.fs || NULL_FS; }
var NULL_FS = { read: function () { return null; }, write: function () {}, exists: function () { return false; },
	isDir: function () { return false; }, list: function () { return []; }, mkdirs: function () {}, remove: function () {} };
function norm(p) {
	p = String(p || '').replace(/\\/g, '/');
	var parts = [], segs = p.split('/');
	for (var i = 0; i < segs.length; i++) {
		var s = segs[i];
		if (!s || s === '.') continue;
		if (s === '..') parts.pop(); else parts.push(s);
	}
	return parts.join('/');
}

function bytesStream(vm, bytes, cname) {
	var o = vm.newObject(vm.loadClass(cname || 'java/io/ByteArrayInputStream'));
	o.$buf = bytes || new Uint8Array(0);
	o.$pos = 0;
	return o;
}
function readAllBytes(vm, s) {
	if (s === null) vm.throwNew('java/lang/NullPointerException', 'stream');
	if (s.$buf) { var b = s.$buf.subarray(s.$pos); s.$pos = s.$buf.length; return b; }
	if (s.$in) return readAllBytes(vm, s.$in);
	if (s.$text !== undefined) { var t = new TextEncoder().encode(s.$text.substring(s.$tpos || 0)); s.$tpos = s.$text.length; return t; }
	var out = [], v;
	while ((v = vm.callVirtual(s, 'read', '()I', [])) >= 0) out.push(v);
	return Uint8Array.from(out);
}
JVM.readAllText = function (vm, s) {
	if (s && s.$text !== undefined) { var t = s.$text.substring(s.$tpos || 0); s.$tpos = s.$text.length; return t; }
	if (s && s.$reader) return JVM.readAllText(vm, s.$reader);
	return new TextDecoder().decode(readAllBytes(vm, s));
};
JVM.writeAllText = function (vm, w, text) {
	var b = new TextEncoder().encode(text);
	sink(vm, w, b);
	vm.callVirtual(w, 'flush', '()V', []);
};
function sink(vm, w, bytes) {
	if (w.$sink) { w.$sink(bytes); return; }
	if (w.$out) { sink(vm, w.$out, bytes); return; }
	for (var i = 0; i < bytes.length; i++) vm.callVirtual(w, 'write', '(I)V', [bytes[i]]);
}
function fileSink(vm, self, path, append) {
	var fs = fsOf(vm), chunks = [];
	if (append) { var old = fs.read(path); if (old) chunks.push(old); }
	var flush = function () {
		var n = 0; chunks.forEach(function (c) { n += c.length; });
		var all = new Uint8Array(n), o = 0;
		chunks.forEach(function (c) { all.set(c, o); o += c.length; });
		fs.write(path, all);
	};
	self.$sink = function (b) { chunks.push(b.slice ? b.slice() : b); };
	self.$flush = flush;
	flush();
}

JVM.resourceStream = function (vm, name, cls) {
	if (name === null) return null;
	var n = String(name);
	if (n[0] === '/') n = n.substring(1);
	else if (cls) { var pk = cls.name.substring(0, cls.name.lastIndexOf('/') + 1); n = pk + n; }
	var r = vm.resources && vm.resources[n];
	return r ? bytesStream(vm, r) : null;
};
JVM.bytesStream = bytesStream;
JVM.readAllBytes = readAllBytes;

function installIo(vm) {
	var def = function (n, s) { vm.defineNative(n, s); };
	var I = JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC;
	def('java/io/Closeable', { access: I, interfaces: ['java/lang/AutoCloseable'], abstractMethods: { 'close()V': true } });
	def('java/io/Flushable', { access: I, abstractMethods: { 'flush()V': true } });
	def('java/io/DataInput', { access: I });
	def('java/io/DataOutput', { access: I });

	var inMethods = {
		'<init>()V': function () {},
		'read()I': function (vm, self) {
			if (self.$in) return vm.callVirtual(self.$in, 'read', '()I', []);
			if (!self.$buf || self.$pos >= self.$buf.length) return -1;
			return self.$buf[self.$pos++];
		},
		'read([B)I': function (vm, self, a) { return readInto(vm, self, a[0], 0, a[0].a.length); },
		'read([BII)I': function (vm, self, a) { return readInto(vm, self, a[0], a[1], a[2]); },
		'available()I': function (vm, self) { return self.$buf ? self.$buf.length - self.$pos : (self.$in ? vm.callVirtual(self.$in, 'available', '()I', []) : 0); },
		'skip(J)J': function (vm, self, a) { var n = Math.min(Number(a[0]), self.$buf ? self.$buf.length - self.$pos : 0); if (self.$buf) self.$pos += n; return BigInt(n); },
		'close()V': function () {},
		'mark(I)V': function (vm, self) { self.$mark = self.$pos; },
		'reset()V': function (vm, self) { self.$pos = self.$mark || 0; },
		'markSupported()Z': function (vm, self) { return self.$buf ? 1 : 0; },
		'readAllBytes()[B': function (vm, self) { var b = readAllBytes(vm, self), a = vm.newArray('B', b.length); a.a.set(new Int8Array(b.buffer, b.byteOffset, b.length)); return a; },
	};
	function readInto(vm, self, arr, off, len) {
		if (self.$in && !self.$buf) {
			var n = 0, v;
			while (n < len && (v = vm.callVirtual(self.$in, 'read', '()I', [])) >= 0) arr.a[off + n++] = (v << 24) >> 24;
			return n === 0 && len > 0 ? -1 : n;
		}
		var left = self.$buf.length - self.$pos;
		if (left <= 0) return len === 0 ? 0 : -1;
		var k = Math.min(len, left);
		for (var i = 0; i < k; i++) arr.a[off + i] = (self.$buf[self.$pos + i] << 24) >> 24;
		self.$pos += k;
		return k;
	}
	def('java/io/InputStream', { interfaces: ['java/io/Closeable'], methods: inMethods });
	def('java/io/ByteArrayInputStream', { super: 'java/io/InputStream', methods: {
		'<init>([B)V': function (vm, self, a) { self.$buf = new Uint8Array(a[0].a.buffer, a[0].a.byteOffset, a[0].a.length); self.$pos = 0; },
		'<init>([BII)V': function (vm, self, a) { self.$buf = new Uint8Array(a[0].a.buffer, a[0].a.byteOffset + a[1], a[2]); self.$pos = 0; },
	} });
	def('java/io/FileInputStream', { super: 'java/io/InputStream', methods: {
		'<init>(Ljava/lang/String;)V': function (vm, self, a) { openIn(vm, self, norm(a[0])); },
		'<init>(Ljava/io/File;)V': function (vm, self, a) { openIn(vm, self, a[0].$path); },
	} });
	function openIn(vm, self, path) {
		var b = fsOf(vm).read(path);
		if (!b) vm.throwNew('java/io/FileNotFoundException', path + ' (No such file or directory)');
		self.$buf = b; self.$pos = 0;
	}
	var wrapIn = { '<init>(Ljava/io/InputStream;)V': function (vm, self, a) { self.$in = a[0]; if (a[0] && a[0].$buf) { self.$buf = a[0].$buf; self.$pos = a[0].$pos; self.$shared = a[0]; } } };
	def('java/io/FilterInputStream', { super: 'java/io/InputStream', methods: wrapIn });
	def('java/io/BufferedInputStream', { super: 'java/io/FilterInputStream', methods: Object.assign({ '<init>(Ljava/io/InputStream;I)V': wrapIn['<init>(Ljava/io/InputStream;)V'] }, wrapIn) });
	var din = Object.assign({}, wrapIn, {
		'readByte()B': function (vm, self) { return (rb(vm, self) << 24) >> 24; },
		'readUnsignedByte()I': function (vm, self) { return rb(vm, self); },
		'readBoolean()Z': function (vm, self) { return rb(vm, self) ? 1 : 0; },
		'readShort()S': function (vm, self) { return ((rb(vm, self) << 8 | rb(vm, self)) << 16) >> 16; },
		'readUnsignedShort()I': function (vm, self) { return rb(vm, self) << 8 | rb(vm, self); },
		'readChar()C': function (vm, self) { return rb(vm, self) << 8 | rb(vm, self); },
		'readInt()I': function (vm, self) { return (rb(vm, self) << 24) | (rb(vm, self) << 16) | (rb(vm, self) << 8) | rb(vm, self); },
		'readLong()J': function (vm, self) { var v = 0n; for (var i = 0; i < 8; i++) v = (v << 8n) | BigInt(rb(vm, self)); return BigInt.asIntN(64, v); },
		'readFloat()F': function (vm, self) { var dv = new DataView(new ArrayBuffer(4)); for (var i = 0; i < 4; i++) dv.setUint8(i, rb(vm, self)); return dv.getFloat32(0); },
		'readDouble()D': function (vm, self) { var dv = new DataView(new ArrayBuffer(8)); for (var i = 0; i < 8; i++) dv.setUint8(i, rb(vm, self)); return dv.getFloat64(0); },
		'readUTF()Ljava/lang/String;': function (vm, self) {
			var n = rb(vm, self) << 8 | rb(vm, self), b = new Uint8Array(n);
			for (var i = 0; i < n; i++) b[i] = rb(vm, self);
			return JVM.decodeMutf8(b);
		},
		'readFully([B)V': function (vm, self, a) { for (var i = 0; i < a[0].a.length; i++) a[0].a[i] = (rb(vm, self) << 24) >> 24; },
		'readFully([BII)V': function (vm, self, a) { for (var i = 0; i < a[2]; i++) a[0].a[a[1] + i] = (rb(vm, self) << 24) >> 24; },
		'skipBytes(I)I': function (vm, self, a) { for (var i = 0; i < a[0]; i++) rb(vm, self); return a[0]; },
	});
	function rb(vm, self) {
		var v = self.$buf ? (self.$pos < self.$buf.length ? self.$buf[self.$pos++] : -1) : vm.callVirtual(self.$in, 'read', '()I', []);
		if (self.$shared) self.$shared.$pos = self.$pos;
		if (v < 0) vm.throwNew('java/io/EOFException', null);
		return v;
	}
	def('java/io/DataInputStream', { super: 'java/io/FilterInputStream', interfaces: ['java/io/DataInput'], methods: din });

	var outMethods = {
		'<init>()V': function () {},
		'write(I)V': function (vm, self, a) { sink(vm, self, Uint8Array.of(a[0] & 255)); },
		'write([B)V': function (vm, self, a) { sink(vm, self, new Uint8Array(a[0].a.buffer, a[0].a.byteOffset, a[0].a.length)); },
		'write([BII)V': function (vm, self, a) { sink(vm, self, new Uint8Array(a[0].a.buffer, a[0].a.byteOffset + a[1], a[2])); },
		'flush()V': function (vm, self) { if (self.$flush) self.$flush(); else if (self.$out) vm.callVirtual(self.$out, 'flush', '()V', []); },
		'close()V': function (vm, self) { vm.callVirtual(self, 'flush', '()V', []); },
	};
	def('java/io/OutputStream', { interfaces: ['java/io/Closeable', 'java/io/Flushable'], methods: outMethods });
	def('java/io/ByteArrayOutputStream', { super: 'java/io/OutputStream', methods: {
		'<init>()V': function (vm, self) { baos(self); }, '<init>(I)V': function (vm, self) { baos(self); },
		'toByteArray()[B': function (vm, self) { var b = baosBytes(self), a = vm.newArray('B', b.length); a.a.set(new Int8Array(b.buffer, b.byteOffset, b.length)); return a; },
		'size()I': function (vm, self) { return baosBytes(self).length; },
		'toString()Ljava/lang/String;': function (vm, self) { return new TextDecoder().decode(baosBytes(self)); },
		'reset()V': function (vm, self) { baos(self); },
	} });
	function baos(self) { self.$chunks = []; self.$sink = function (b) { self.$chunks.push(b.slice()); }; }
	function baosBytes(self) { var n = 0; self.$chunks.forEach(function (c) { n += c.length; }); var all = new Uint8Array(n), o = 0; self.$chunks.forEach(function (c) { all.set(c, o); o += c.length; }); return all; }
	def('java/io/FileOutputStream', { super: 'java/io/OutputStream', methods: {
		'<init>(Ljava/lang/String;)V': function (vm, self, a) { fileSink(vm, self, norm(a[0]), false); },
		'<init>(Ljava/lang/String;Z)V': function (vm, self, a) { fileSink(vm, self, norm(a[0]), a[1]); },
		'<init>(Ljava/io/File;)V': function (vm, self, a) { fileSink(vm, self, a[0].$path, false); },
		'<init>(Ljava/io/File;Z)V': function (vm, self, a) { fileSink(vm, self, a[0].$path, a[1]); },
	} });
	var wrapOut = { '<init>(Ljava/io/OutputStream;)V': function (vm, self, a) { self.$out = a[0]; } };
	def('java/io/FilterOutputStream', { super: 'java/io/OutputStream', methods: wrapOut });
	def('java/io/BufferedOutputStream', { super: 'java/io/FilterOutputStream', methods: Object.assign({ '<init>(Ljava/io/OutputStream;I)V': wrapOut['<init>(Ljava/io/OutputStream;)V'] }, wrapOut) });
	var w = function (vm, self, bytes) { sink(vm, self, Uint8Array.from(bytes)); };
	def('java/io/DataOutputStream', { super: 'java/io/FilterOutputStream', interfaces: ['java/io/DataOutput'], methods: Object.assign({}, wrapOut, {
		'writeByte(I)V': function (vm, self, a) { w(vm, self, [a[0] & 255]); },
		'writeBoolean(Z)V': function (vm, self, a) { w(vm, self, [a[0] ? 1 : 0]); },
		'writeShort(I)V': function (vm, self, a) { w(vm, self, [(a[0] >> 8) & 255, a[0] & 255]); },
		'writeChar(I)V': function (vm, self, a) { w(vm, self, [(a[0] >> 8) & 255, a[0] & 255]); },
		'writeInt(I)V': function (vm, self, a) { w(vm, self, [(a[0] >>> 24) & 255, (a[0] >> 16) & 255, (a[0] >> 8) & 255, a[0] & 255]); },
		'writeLong(J)V': function (vm, self, a) { var b = []; for (var i = 7; i >= 0; i--) b.push(Number((a[0] >> BigInt(i * 8)) & 255n)); w(vm, self, b); },
		'writeFloat(F)V': function (vm, self, a) { var dv = new DataView(new ArrayBuffer(4)); dv.setFloat32(0, a[0]); w(vm, self, new Uint8Array(dv.buffer)); },
		'writeDouble(D)V': function (vm, self, a) { var dv = new DataView(new ArrayBuffer(8)); dv.setFloat64(0, a[0]); w(vm, self, new Uint8Array(dv.buffer)); },
		'writeUTF(Ljava/lang/String;)V': function (vm, self, a) { var b = new TextEncoder().encode(a[0]); w(vm, self, [(b.length >> 8) & 255, b.length & 255]); sink(vm, self, b); },
		'writeBytes(Ljava/lang/String;)V': function (vm, self, a) { var s = a[0], b = []; for (var i = 0; i < s.length; i++) b.push(s.charCodeAt(i) & 255); w(vm, self, b); },
		'writeChars(Ljava/lang/String;)V': function (vm, self, a) { var s = a[0], b = []; for (var i = 0; i < s.length; i++) b.push(s.charCodeAt(i) >> 8, s.charCodeAt(i) & 255); w(vm, self, b); },
	}) });

	var rdr = {
		'<init>()V': function () {},
		'<init>(Ljava/io/InputStream;)V': function (vm, self, a) { self.$text = JVM.readAllText(vm, a[0]); self.$tpos = 0; },
		'<init>(Ljava/io/InputStream;Ljava/lang/String;)V': function (vm, self, a) { self.$text = JVM.readAllText(vm, a[0]); self.$tpos = 0; },
		'<init>(Ljava/io/InputStream;Ljava/nio/charset/Charset;)V': function (vm, self, a) { self.$text = JVM.readAllText(vm, a[0]); self.$tpos = 0; },
		'<init>(Ljava/io/Reader;)V': function (vm, self, a) { self.$text = JVM.readAllText(vm, a[0]); self.$tpos = 0; },
		'<init>(Ljava/io/Reader;I)V': function (vm, self, a) { self.$text = JVM.readAllText(vm, a[0]); self.$tpos = 0; },
		'<init>(Ljava/lang/String;)V': function (vm, self, a) { self.$text = a[0]; self.$tpos = 0; },
		'read()I': function (vm, self) { return self.$tpos < self.$text.length ? self.$text.charCodeAt(self.$tpos++) : -1; },
		'read([C)I': function (vm, self, a) { return readChars(self, a[0], 0, a[0].a.length); },
		'read([CII)I': function (vm, self, a) { return readChars(self, a[0], a[1], a[2]); },
		'readLine()Ljava/lang/String;': function (vm, self) {
			var t = self.$text, p = self.$tpos;
			if (p >= t.length) return null;
			var e = t.indexOf('\n', p);
			if (e < 0) e = t.length;
			self.$tpos = e + 1;
			var line = t.substring(p, e);
			return line.endsWith('\r') ? line.substring(0, line.length - 1) : line;
		},
		'ready()Z': function (vm, self) { return self.$tpos < self.$text.length ? 1 : 0; },
		'skip(J)J': function (vm, self, a) { var n = Math.min(Number(a[0]), self.$text.length - self.$tpos); self.$tpos += n; return BigInt(n); },
		'close()V': function () {},
		'lines()Ljava/util/stream/Stream;': function (vm) { vm.warnOnce('stream', 'java.util.stream is not available here (left unplugged)'); return null; },
	};
	function readChars(self, arr, off, len) {
		var left = self.$text.length - self.$tpos;
		if (left <= 0) return -1;
		var k = Math.min(len, left);
		for (var i = 0; i < k; i++) arr.a[off + i] = self.$text.charCodeAt(self.$tpos + i);
		self.$tpos += k;
		return k;
	}
	def('java/io/Reader', { interfaces: ['java/io/Closeable'], methods: rdr });
	['java/io/InputStreamReader', 'java/io/BufferedReader', 'java/io/StringReader', 'java/io/LineNumberReader'].forEach(function (n) { def(n, { super: 'java/io/Reader', methods: {} }); });
	def('java/io/FileReader', { super: 'java/io/InputStreamReader', methods: {
		'<init>(Ljava/lang/String;)V': function (vm, self, a) { var b = fsOf(vm).read(norm(a[0])); if (!b) vm.throwNew('java/io/FileNotFoundException', a[0]); self.$text = new TextDecoder().decode(b); self.$tpos = 0; },
		'<init>(Ljava/io/File;)V': function (vm, self, a) { var b = fsOf(vm).read(a[0].$path); if (!b) vm.throwNew('java/io/FileNotFoundException', a[0].$path); self.$text = new TextDecoder().decode(b); self.$tpos = 0; },
	} });
	var wtr = {
		'<init>()V': function () {},
		'<init>(Ljava/io/OutputStream;)V': function (vm, self, a) { self.$out = a[0]; },
		'<init>(Ljava/io/OutputStream;Ljava/lang/String;)V': function (vm, self, a) { self.$out = a[0]; },
		'<init>(Ljava/io/OutputStream;Ljava/nio/charset/Charset;)V': function (vm, self, a) { self.$out = a[0]; },
		'<init>(Ljava/io/Writer;)V': function (vm, self, a) { self.$out = a[0]; },
		'<init>(Ljava/io/Writer;I)V': function (vm, self, a) { self.$out = a[0]; },
		'<init>(Ljava/io/OutputStream;Z)V': function (vm, self, a) { self.$out = a[0]; },
		'<init>(Ljava/io/Writer;Z)V': function (vm, self, a) { self.$out = a[0]; },
		'write(I)V': function (vm, self, a) { txt(vm, self, String.fromCharCode(a[0])); },
		'write(Ljava/lang/String;)V': function (vm, self, a) { txt(vm, self, a[0]); },
		'write(Ljava/lang/String;II)V': function (vm, self, a) { txt(vm, self, a[0].substring(a[1], a[1] + a[2])); },
		'write([C)V': function (vm, self, a) { txt(vm, self, vm.stringFromChars(a[0])); },
		'write([CII)V': function (vm, self, a) { txt(vm, self, vm.stringFromChars(a[0], a[1], a[2])); },
		'append(Ljava/lang/CharSequence;)Ljava/io/Writer;': function (vm, self, a) { txt(vm, self, JVM.stringOf(vm, a[0], null)); return self; },
		'append(C)Ljava/io/Writer;': function (vm, self, a) { txt(vm, self, String.fromCharCode(a[0])); return self; },
		'newLine()V': function (vm, self) { txt(vm, self, '\n'); },
		'flush()V': function (vm, self) { if (self.$flush) self.$flush(); else if (self.$out) vm.callVirtual(self.$out, 'flush', '()V', []); },
		'close()V': function (vm, self) { vm.callVirtual(self, 'flush', '()V', []); },
		'toString()Ljava/lang/String;': function (vm, self) { return self.$acc || ''; },
		'getBuffer()Ljava/lang/StringBuffer;': function (vm, self) { var sb = vm.newObject(vm.loadClass('java/lang/StringBuffer')); sb.$s = self.$acc || ''; return sb; },
	};
	function txt(vm, self, s) {
		if (self.$out || self.$sink) sink(vm, self, new TextEncoder().encode(s));
		else self.$acc = (self.$acc || '') + s;
	}
	var pw = Object.assign({}, wtr, {
		'<init>(Ljava/lang/String;)V': function (vm, self, a) { fileSink(vm, self, norm(a[0]), false); },
		'<init>(Ljava/io/File;)V': function (vm, self, a) { fileSink(vm, self, a[0].$path, false); },
		'println()V': function (vm, self) { txt(vm, self, '\n'); },
		'printf(Ljava/lang/String;[Ljava/lang/Object;)Ljava/io/PrintWriter;': function (vm, self, a) { txt(vm, self, JVM.javaFormat(vm, a[0], a[1] ? Array.prototype.slice.call(a[1].a) : [])); return self; },
		'format(Ljava/lang/String;[Ljava/lang/Object;)Ljava/io/PrintWriter;': function (vm, self, a) { txt(vm, self, JVM.javaFormat(vm, a[0], a[1] ? Array.prototype.slice.call(a[1].a) : [])); return self; },
	});
	['Ljava/lang/String;', 'Ljava/lang/Object;', 'I', 'J', 'F', 'D', 'C', 'Z'].forEach(function (t) {
		pw['print(' + t + ')V'] = function (vm, self, a) { txt(vm, self, JVM.stringOf(vm, a[0], t.length === 1 ? t : null)); };
		pw['println(' + t + ')V'] = function (vm, self, a) { txt(vm, self, JVM.stringOf(vm, a[0], t.length === 1 ? t : null) + '\n'); };
	});
	def('java/io/Writer', { interfaces: ['java/io/Closeable', 'java/io/Flushable', 'java/lang/Appendable'], methods: wtr });
	['java/io/OutputStreamWriter', 'java/io/BufferedWriter', 'java/io/StringWriter'].forEach(function (n) { def(n, { super: 'java/io/Writer', methods: {} }); });
	def('java/io/PrintWriter', { super: 'java/io/Writer', methods: pw });
	def('java/io/FileWriter', { super: 'java/io/OutputStreamWriter', methods: {
		'<init>(Ljava/lang/String;)V': function (vm, self, a) { fileSink(vm, self, norm(a[0]), false); },
		'<init>(Ljava/lang/String;Z)V': function (vm, self, a) { fileSink(vm, self, norm(a[0]), a[1]); },
		'<init>(Ljava/io/File;)V': function (vm, self, a) { fileSink(vm, self, a[0].$path, false); },
		'<init>(Ljava/io/File;Z)V': function (vm, self, a) { fileSink(vm, self, a[0].$path, a[1]); },
	} });

	def('java/io/File', {
		interfaces: ['java/lang/Comparable'],
		statics: { separator: '/', separatorChar: 47, pathSeparator: ':', pathSeparatorChar: 58 },
		methods: {
			'<init>(Ljava/lang/String;)V': function (vm, self, a) { self.$path = norm(a[0]); },
			'<init>(Ljava/lang/String;Ljava/lang/String;)V': function (vm, self, a) { self.$path = norm((a[0] || '') + '/' + a[1]); },
			'<init>(Ljava/io/File;Ljava/lang/String;)V': function (vm, self, a) { self.$path = norm((a[0] ? a[0].$path : '') + '/' + a[1]); },
			'getName()Ljava/lang/String;': function (vm, self) { return self.$path.substring(self.$path.lastIndexOf('/') + 1); },
			'getPath()Ljava/lang/String;': function (vm, self) { return self.$path; },
			'getAbsolutePath()Ljava/lang/String;': function (vm, self) { return '/' + self.$path; },
			'getCanonicalPath()Ljava/lang/String;': function (vm, self) { return '/' + self.$path; },
			'toString()Ljava/lang/String;': function (vm, self) { return self.$path; },
			'getAbsoluteFile()Ljava/io/File;': function (vm, self) { return self; },
			'getCanonicalFile()Ljava/io/File;': function (vm, self) { return self; },
			'getParent()Ljava/lang/String;': function (vm, self) { var i = self.$path.lastIndexOf('/'); return i < 0 ? null : self.$path.substring(0, i); },
			'getParentFile()Ljava/io/File;': function (vm, self) { var i = self.$path.lastIndexOf('/'); return i < 0 ? null : fileObj(vm, self.$path.substring(0, i)); },
			'exists()Z': function (vm, self) { return fsOf(vm).exists(self.$path) ? 1 : 0; },
			'isFile()Z': function (vm, self) { return fsOf(vm).exists(self.$path) && !fsOf(vm).isDir(self.$path) ? 1 : 0; },
			'isDirectory()Z': function (vm, self) { return fsOf(vm).isDir(self.$path) ? 1 : 0; },
			'canRead()Z': function (vm, self) { return fsOf(vm).exists(self.$path) ? 1 : 0; },
			'canWrite()Z': function () { return 1; },
			'length()J': function (vm, self) { var b = fsOf(vm).read(self.$path); return BigInt(b ? b.length : 0); },
			'lastModified()J': function () { return 0n; },
			'mkdir()Z': function (vm, self) { fsOf(vm).mkdirs(self.$path); return 1; },
			'mkdirs()Z': function (vm, self) { fsOf(vm).mkdirs(self.$path); return 1; },
			'createNewFile()Z': function (vm, self) { if (fsOf(vm).exists(self.$path)) return 0; fsOf(vm).write(self.$path, new Uint8Array(0)); return 1; },
			'delete()Z': function (vm, self) { fsOf(vm).remove(self.$path); return 1; },
			'deleteOnExit()V': function () {},
			'renameTo(Ljava/io/File;)Z': function (vm, self, a) { var b = fsOf(vm).read(self.$path); if (!b) return 0; fsOf(vm).write(a[0].$path, b); fsOf(vm).remove(self.$path); return 1; },
			'list()[Ljava/lang/String;': function (vm, self) { return JVM.javaArray(vm, 'Ljava/lang/String;', fsOf(vm).list(self.$path)); },
			'listFiles()[Ljava/io/File;': function (vm, self) { return JVM.javaArray(vm, 'Ljava/io/File;', fsOf(vm).list(self.$path).map(function (n) { return fileObj(vm, self.$path + '/' + n); })); },
			'equals(Ljava/lang/Object;)Z': function (vm, self, a) { return a[0] && a[0].$path === self.$path ? 1 : 0; },
			'hashCode()I': function (vm, self) { return JVM.stringHash(self.$path) ^ 1234321; },
			'compareTo(Ljava/lang/Object;)I': function (vm, self, a) { return self.$path < a[0].$path ? -1 : self.$path > a[0].$path ? 1 : 0; },
			'toURI()Ljava/net/URI;': function () { return null; },
		},
	});
	function fileObj(vm, path) { var f = vm.newObject(vm.loadClass('java/io/File')); f.$path = norm(path); return f; }
}

JVM.installIo = installIo;
})();

(function () {
'use strict';

function inflateRaw(bytes) {
	return new Response(new Blob([bytes]).stream().pipeThrough(new DecompressionStream('deflate-raw')))
		.arrayBuffer().then(function (b) { return new Uint8Array(b); });
}

function readZip(bytes) {
	var dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
	var eocd = -1;
	for (var i = bytes.length - 22; i >= Math.max(0, bytes.length - 65557); i--) {
		if (dv.getUint32(i, true) === 0x06054b50) { eocd = i; break; }
	}
	if (eocd < 0) return Promise.reject(new Error('not a zip / jar file'));
	var count = dv.getUint16(eocd + 10, true), cdOff = dv.getUint32(eocd + 16, true);
	var entries = [], p = cdOff;
	var dec = new TextDecoder();
	for (var n = 0; n < count; n++) {
		if (dv.getUint32(p, true) !== 0x02014b50) break;
		var method = dv.getUint16(p + 10, true), csize = dv.getUint32(p + 20, true);
		var nlen = dv.getUint16(p + 28, true), xlen = dv.getUint16(p + 30, true), clen = dv.getUint16(p + 32, true);
		var lho = dv.getUint32(p + 42, true);
		var name = dec.decode(bytes.subarray(p + 46, p + 46 + nlen));
		p += 46 + nlen + xlen + clen;
		if (name.endsWith('/')) continue;
		var lnlen = dv.getUint16(lho + 26, true), lxlen = dv.getUint16(lho + 28, true);
		var start = lho + 30 + lnlen + lxlen;
		entries.push({ name: name, method: method, data: bytes.subarray(start, start + csize) });
	}
	return Promise.all(entries.map(function (e) {
		if (e.method === 0) return Promise.resolve({ name: e.name, bytes: e.data.slice() });
		if (e.method === 8) return inflateRaw(e.data).then(function (b) { return { name: e.name, bytes: b }; }, function () { return null; });
		return Promise.resolve(null);
	})).then(function (list) { return list.filter(Boolean); });
}

JVM.readZip = readZip;
})();

(function () {
'use strict';

var SRC = 'net/minecraft/src/';
var MODLOADER_CLASSES = ['BaseMod', 'ModLoader', 'MLProp', 'EntityRendererProxy', 'ModTextureStatic',
	'ModTextureAnimation', 'TradeEntry', 'ModLoaderMp', 'BaseModMp', 'ModLoaderPacket'];

function loadMap(vm, text) {
	var cls = Object.create(null);
	var rev = Object.create(null);
	var fld = Object.create(null);
	var mth = Object.create(null);
	var srg = Object.create(null);
	var lines = text.split('\n');
	for (var i = 0; i < lines.length; i++) {
		var p = lines[i].split('\t');
		if (p[0] === 'C') { cls[p[1]] = p[2]; rev[p[2]] = p[1]; }
		else if (p[0] === 'F') { fld[p[1] + '.' + p[2]] = p[4]; srg[p[3]] = p[4]; }
		else if (p[0] === 'M') { mth[p[1] + '.' + p[2] + p[3]] = p[5]; srg[p[4]] = p[5]; }
	}
	MODLOADER_CLASSES.forEach(function (n) { cls[n] = SRC + n; rev[SRC + n] = n; });
	var map = { cls: cls, rev: rev, fld: fld, mth: mth, srg: srg };
	vm.nameMap = map;
	var prevClass = vm.mapClass;
	vm.mapClass = function (n) {
		var m = cls[n];
		if (m) return m;
		if (n.indexOf('net/minecraft/') === 0 && n.indexOf(SRC) !== 0) {
			var simple = n.substring(n.lastIndexOf('/') + 1);
			if (rev[SRC + simple] !== undefined || vm.natives[SRC + simple]) return SRC + simple;
		}
		return prevClass ? prevClass(n) : null;
	};
	vm.mapMember = function (owner, name, desc, isMethod) {
		if (srg[name]) return srg[name];
		var q = [owner], seen = Object.create(null);
		while (q.length) {
			var c = q.shift();
			if (!c || seen[c]) continue;
			seen[c] = true;
			var key = c + '.' + name + (isMethod ? desc : '');
			var r = isMethod ? mth[key] : fld[key];
			if (r) return r;
			var ps = parentsOf(vm, c);
			for (var k = 0; k < ps.length; k++) q.push(ps[k]);
		}
		return name;
	};
	return map;
}

function parentsOf(vm, name) {
	var h = vm.origParents && vm.origParents[name];
	if (h) return h;
	var src = vm.sources[name];
	if (src) {
		if (!src.header) src.header = JVM.classHeader(src.bytes);
		return [src.header.superName].concat(src.header.interfaces);
	}
	var map = vm.nameMap, mcp = map && map.cls[name];
	if (mcp) {
		var spec = vm.natives[mcp];
		if (!spec) return [];
		var out = [];
		if (spec.super) out.push(map.rev[spec.super] || spec.super);
		(spec.interfaces || []).forEach(function (i) { out.push(map.rev[i] || i); });
		return out;
	}
	return [];
}

function classHeader(bytes) {
	var dv = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength), p = 8;
	var n = dv.getUint16(p); p += 2;
	var utf = [], clsRef = [];
	for (var i = 1; i < n; i++) {
		var tag = bytes[p++];
		switch (tag) {
		case 1: { var len = dv.getUint16(p); utf[i] = JVM.decodeMutf8(bytes.subarray(p + 2, p + 2 + len)); p += 2 + len; break; }
		case 7: clsRef[i] = dv.getUint16(p); p += 2; break;
		case 8: case 16: case 19: case 20: p += 2; break;
		case 3: case 4: case 9: case 10: case 11: case 12: case 17: case 18: p += 4; break;
		case 5: case 6: p += 8; i++; break;
		case 15: p += 3; break;
		default: return { name: null, superName: null, interfaces: [] };
		}
	}
	p += 2;
	var self = dv.getUint16(p), sup = dv.getUint16(p + 2), ni = dv.getUint16(p + 4), ifs = [];
	for (var k = 0; k < ni; k++) ifs.push(utf[clsRef[dv.getUint16(p + 6 + k * 2)]]);
	return { name: utf[clsRef[self]], superName: sup ? utf[clsRef[sup]] : null, interfaces: ifs };
}

JVM.loadMap = loadMap;
JVM.classHeader = classHeader;
})();

(function () {
'use strict';

var JObject = JVM.JObject, SRC = 'net/minecraft/src/';
var L = function (n) { return 'L' + SRC + n + ';'; };

var VANILLA_BLOCKS = 'stone 1,grass 2,dirt 3,cobblestone 4,planks 5,sapling 6,bedrock 7,waterMoving 8,waterStill 9,lavaMoving 10,lavaStill 11,sand 12,gravel 13,oreGold 14,oreIron 15,oreCoal 16,wood 17,leaves 18,sponge 19,glass 20,oreLapis 21,blockLapis 22,dispenser 23,sandStone 24,music 25,bed 26,railPowered 27,railDetector 28,pistonStickyBase 29,web 30,tallGrass 31,deadBush 32,pistonBase 33,pistonExtension 34,cloth 35,pistonMoving 36,plantYellow 37,plantRed 38,mushroomBrown 39,mushroomRed 40,blockGold 41,blockIron 42,stoneDoubleSlab 43,stoneSingleSlab 44,brick 45,tnt 46,bookShelf 47,cobblestoneMossy 48,obsidian 49,torchWood 50,fire 51,mobSpawner 52,stairsWoodOak 53,chest 54,redstoneWire 55,oreDiamond 56,blockDiamond 57,workbench 58,crops 59,tilledField 60,furnaceIdle 61,furnaceBurning 62,signPost 63,doorWood 64,ladder 65,rail 66,stairsCobblestone 67,signWall 68,lever 69,pressurePlateStone 70,doorIron 71,pressurePlatePlanks 72,oreRedstone 73,oreRedstoneGlowing 74,torchRedstoneIdle 75,torchRedstoneActive 76,stoneButton 77,snow 78,ice 79,blockSnow 80,cactus 81,blockClay 82,reed 83,jukebox 84,fence 85,pumpkin 86,netherrack 87,slowSand 88,glowStone 89,portal 90,pumpkinLantern 91,cake 92,redstoneRepeaterIdle 93,redstoneRepeaterActive 94,lockedChest 95,trapdoor 96,silverfish 97,stoneBrick 98,mushroomCapBrown 99,mushroomCapRed 100,fenceIron 101,thinGlass 102,melon 103,pumpkinStem 104,melonStem 105,vine 106,fenceGate 107,stairsBrick 108,stairsStoneBrick 109,mycelium 110,waterlily 111,netherBrick 112,netherFence 113,stairsNetherBrick 114,netherStalk 115,enchantmentTable 116,brewingStand 117,cauldron 118,endPortal 119,endPortalFrame 120,whiteStone 121,dragonEgg 122,redstoneLampIdle 123,redstoneLampActive 124,woodDoubleSlab 125,woodSingleSlab 126,cocoaPlant 127,stairsSandStone 128,oreEmerald 129,enderChest 130,tripWireSource 131,tripWire 132,blockEmerald 133,stairsWoodSpruce 134,stairsWoodBirch 135,stairsWoodJungle 136,commandBlock 137,beacon 138,cobblestoneWall 139,flowerPot 140,carrot 141,potato 142,woodenButton 143,skull 144,anvil 145,chestTrapped 146,pressurePlateGold 147,pressurePlateIron 148,redstoneComparatorIdle 149,redstoneComparatorActive 150,daylightSensor 151,blockRedstone 152,oreNetherQuartz 153,hopperBlock 154,blockNetherQuartz 155,stairsNetherQuartz 156,railActivator 157,dropper 158';
var VANILLA_ITEMS = 'shovelIron 256,pickaxeIron 257,axeIron 258,flintAndSteel 259,appleRed 260,bow 261,arrow 262,coal 263,diamond 264,ingotIron 265,ingotGold 266,swordIron 267,swordWood 268,shovelWood 269,pickaxeWood 270,axeWood 271,swordStone 272,shovelStone 273,pickaxeStone 274,axeStone 275,swordDiamond 276,shovelDiamond 277,pickaxeDiamond 278,axeDiamond 279,stick 280,bowlEmpty 281,bowlSoup 282,swordGold 283,shovelGold 284,pickaxeGold 285,axeGold 286,silk 287,feather 288,gunpowder 289,hoeWood 290,hoeStone 291,hoeIron 292,hoeDiamond 293,hoeGold 294,seeds 295,wheat 296,bread 297,helmetLeather 298,plateLeather 299,legsLeather 300,bootsLeather 301,helmetChain 302,plateChain 303,legsChain 304,bootsChain 305,helmetIron 306,plateIron 307,legsIron 308,bootsIron 309,helmetDiamond 310,plateDiamond 311,legsDiamond 312,bootsDiamond 313,helmetGold 314,plateGold 315,legsGold 316,bootsGold 317,flint 318,porkRaw 319,porkCooked 320,painting 321,appleGold 322,sign 323,doorWood 324,bucketEmpty 325,bucketWater 326,bucketLava 327,minecartEmpty 328,saddle 329,doorIron 330,redstone 331,snowball 332,boat 333,leather 334,bucketMilk 335,brick 336,clay 337,reed 338,paper 339,book 340,slimeBall 341,minecartCrate 342,minecartPowered 343,egg 344,compass 345,fishingRod 346,pocketSundial 347,lightStoneDust 348,fishRaw 349,fishCooked 350,dyePowder 351,bone 352,sugar 353,cake 354,bed 355,redstoneRepeater 356,cookie 357,map 358,shears 359,melon 360,pumpkinSeeds 361,melonSeeds 362,beefRaw 363,beefCooked 364,chickenRaw 365,chickenCooked 366,rottenFlesh 367,enderPearl 368,blazeRod 369,ghastTear 370,goldNugget 371,netherStalkSeeds 372,potion 373,glassBottle 374,spiderEye 375,fermentedSpiderEye 376,blazePowder 377,magmaCream 378,brewingStand 379,cauldron 380,eyeOfEnder 381,speckledMelon 382,monsterPlacer 383,expBottle 384,fireballCharge 385,writableBook 386,writtenBook 387,emerald 388,itemFrame 389,flowerPot 390,carrot 391,potato 392,bakedPotato 393,poisonousPotato 394,emptyMap 395,goldenCarrot 396,skull 397,carrotOnAStick 398,netherStar 399,pumpkinPie 400,firework 401,fireworkCharge 402,enchantedBook 403,comparator 404,netherrackBrick 405,netherQuartz 406,tntMinecart 407,hopperMinecart 408,record13 2256,recordCat 2257,recordBlocks 2258,recordChirp 2259,recordFar 2260,recordMall 2261,recordMellohi 2262,recordStal 2263,recordStrad 2264,recordWard 2265,record11 2266,recordWait 2267';
var MATERIALS = ['air', 'grass', 'ground', 'wood', 'rock', 'iron', 'anvil', 'water', 'lava', 'leaves', 'plants', 'vine',
	'sponge', 'cloth', 'fire', 'sand', 'circuits', 'glass', 'redstoneLight', 'tnt', 'coral', 'ice', 'snow', 'craftedSnow',
	'cactus', 'clay', 'pumpkin', 'dragonEgg', 'portal', 'cake', 'web', 'piston'];
var SOUNDS = { soundPowderFootstep: 'stone', soundWoodFootstep: 'wood', soundGravelFootstep: 'gravel', soundGrassFootstep: 'grass',
	soundStoneFootstep: 'stone', soundMetalFootstep: 'metal', soundGlassFootstep: 'glass', soundClothFootstep: 'cloth',
	soundSandFootstep: 'sand', soundSnowFootstep: 'cloth', soundLadderFootstep: 'wood', soundAnvilFootstep: 'metal' };
var TABS = ['tabBlock', 'tabDecorations', 'tabRedstone', 'tabTransport', 'tabMisc', 'tabAllSearch', 'tabFood', 'tabTools',
	'tabCombat', 'tabBrewing', 'tabMaterials', 'tabInventory'];
var TOOL_MATS = { WOOD: [0, 59, 2, 0, 15], STONE: [1, 131, 4, 1, 5], IRON: [2, 250, 6, 2, 14], EMERALD: [3, 1561, 8, 3, 10], GOLD: [0, 32, 12, 0, 22] };
var ARMOR_MATS = { CLOTH: [5, [1, 3, 2, 1], 15], CHAIN: [15, [2, 5, 4, 1], 12], IRON: [15, [2, 6, 5, 2], 9], GOLD: [7, [2, 5, 3, 1], 25], DIAMOND: [33, [3, 8, 6, 3], 10] };

function reg(vm) { return vm.mcReg || (vm.mcReg = { blocks: {}, items: {}, recipes: [], smelting: [], names: {}, lang: {}, tickMods: [], mods: [], vanilla: true }); }
function op(vm) { var g = vm.game; return g && g.mode === 'run' && g.op ? g.op.apply(null, Array.prototype.slice.call(arguments, 1)) : undefined; }
function F(o, n) { return o[':' + n]; }

function installMc152(vm) {
	var def = function (n, s) { vm.defineNative(SRC + n, s); };
	var I = JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC;

	def('BaseMod', {
		access: JVM.ACC_PUBLIC | JVM.ACC_ABSTRACT,
		abstractMethods: { 'getVersion()Ljava/lang/String;': true, 'load()V': true },
		methods: {
			'<init>()V': function (vm, self) { reg(vm).mods.push(self); },
			'getName()Ljava/lang/String;': function (vm, self) { return self.cls.name.substring(self.cls.name.lastIndexOf('/') + 1); },
			'getPriorities()Ljava/lang/String;': function () { return ''; },
			'toString()Ljava/lang/String;': function (vm, self) { return vm.callVirtual(self, 'getName', '()Ljava/lang/String;', []) + ' ' + vm.callVirtual(self, 'getVersion', '()Ljava/lang/String;', []); },
			'modsLoaded()V': function () {},
			'onTickInGame(FLnet/minecraft/client/Minecraft;)Z': function () { return 1; },
			'onTickInGUI(FLnet/minecraft/client/Minecraft;Lnet/minecraft/src/GuiScreen;)Z': function () { return 1; },
			'generateSurface(Lnet/minecraft/src/World;Ljava/util/Random;II)V': function () {},
			'generateNether(Lnet/minecraft/src/World;Ljava/util/Random;II)V': function () {},
			'takenFromCrafting(Lnet/minecraft/src/EntityPlayer;Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/IInventory;)V': function () {},
			'takenFromFurnace(Lnet/minecraft/src/EntityPlayer;Lnet/minecraft/src/ItemStack;)V': function () {},
			'onItemPickup(Lnet/minecraft/src/EntityPlayer;Lnet/minecraft/src/ItemStack;)V': function () {},
			'addRenderer(Ljava/util/Map;)V': function () {},
			'registerAnimation(Lnet/minecraft/client/Minecraft;)V': function () {},
			'keyboardEvent(Lnet/minecraft/src/KeyBinding;)V': function () {},
			'clientChat(Ljava/lang/String;)V': function () {},
			'serverChat(Lnet/minecraft/src/NetServerHandler;Ljava/lang/String;)V': function () {},
			'addSeeds?': null,
		},
	});
	delete vm.natives[SRC + 'BaseMod'].methods['addSeeds?'];
	var unplugged = function (what, ret) { return function (vm) { vm.warnOnce('ml:' + what, 'ModLoader.' + what + ' is not available here (left unplugged)'); return ret === undefined ? undefined : ret; }; };
	var nameOf = function (vm, o) {
		if (!o) return null;
		if (vm.isInstance(o, vm.loadClass(SRC + 'ItemStack'))) return vm.callVirtual(o, 'getItemName', '()Ljava/lang/String;', []);
		if (vm.isInstance(o, vm.loadClass(SRC + 'Block'))) return vm.callVirtual(o, 'getUnlocalizedName', '()Ljava/lang/String;', []);
		if (vm.isInstance(o, vm.loadClass(SRC + 'Item'))) return vm.callVirtual(o, 'getUnlocalizedName', '()Ljava/lang/String;', []);
		return null;
	};
	def('ModLoader', {
		staticMethods: {
			'addName(Ljava/lang/Object;Ljava/lang/String;)V': function (vm, n, a) { var k = nameOf(vm, a[0]); if (k) reg(vm).lang[k + '.name'] = a[1]; },
			'addName(Ljava/lang/Object;Ljava/lang/String;Ljava/lang/String;)V': function (vm, n, a) { var k = nameOf(vm, a[0]); if (k && /^en_/i.test(a[1])) reg(vm).lang[k + '.name'] = a[2]; },
			'addLocalization(Ljava/lang/String;Ljava/lang/String;)V': function (vm, n, a) { reg(vm).lang[a[0]] = a[1]; },
			'addLocalization(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V': function (vm, n, a) { if (/^en_/i.test(a[1])) reg(vm).lang[a[0]] = a[2]; },
			'addRecipe(Lnet/minecraft/src/ItemStack;[Ljava/lang/Object;)V': function (vm, n, a) { reg(vm).recipes.push({ mod: vm.currentMod, shaped: true, out: a[0], args: Array.prototype.slice.call(a[1].a) }); },
			'addShapelessRecipe(Lnet/minecraft/src/ItemStack;[Ljava/lang/Object;)V': function (vm, n, a) { reg(vm).recipes.push({ mod: vm.currentMod, shaped: false, out: a[0], args: Array.prototype.slice.call(a[1].a) }); },
			'addSmelting(ILnet/minecraft/src/ItemStack;F)V': function (vm, n, a) { reg(vm).smelting.push({ mod: vm.currentMod, input: a[0], out: a[1] }); },
			'addSmelting(ILnet/minecraft/src/ItemStack;)V': function (vm, n, a) { reg(vm).smelting.push({ mod: vm.currentMod, input: a[0], out: a[1] }); },
			'registerBlock(Lnet/minecraft/src/Block;)V': function (vm, n, a) { if (a[0]) a[0].$registered = true; },
			'registerBlock(Lnet/minecraft/src/Block;Ljava/lang/Class;)V': function (vm, n, a) { if (a[0]) a[0].$registered = true; },
			'setInGameHook(Lnet/minecraft/src/BaseMod;ZZ)V': function (vm, n, a) { var t = reg(vm).tickMods; if (a[1] && t.indexOf(a[0]) < 0) t.push(a[0]); if (!a[1]) t.splice(t.indexOf(a[0]) >>> 0, 1); },
			'setInGUIHook(Lnet/minecraft/src/BaseMod;ZZ)V': function () {},
			'getMinecraftInstance()Lnet/minecraft/client/Minecraft;': function (vm) { return minecraftObj(vm); },
			'isModLoaded(Ljava/lang/String;)Z': function (vm, n, a) { return reg(vm).mods.some(function (m) { return vm.callVirtual(m, 'getName', '()Ljava/lang/String;', []) === a[0]; }) ? 1 : 0; },
			'getLoadedMods()Ljava/util/List;': function (vm) { return JVM.newList(vm, reg(vm).mods.slice()); },
			'getLogger()Ljava/util/logging/Logger;': function (vm) { return loggerObj(vm); },
			'isGUIOpen(Ljava/lang/Class;)Z': function () { return 0; },
			'getUniqueEntityId()I': function (vm) { return (vm.mcEntityIds = (vm.mcEntityIds || 200) + 1); },
			'getUniqueBlockModelID(Lnet/minecraft/src/BaseMod;Z)I': function (vm) { return (vm.mcModelIds = (vm.mcModelIds || 1000) + 1); },
			'addArmor(Ljava/lang/String;)I': function (vm) { return (vm.mcArmorIdx = (vm.mcArmorIdx || 5) + 1); },
			'registerEntityID(Ljava/lang/Class;Ljava/lang/String;I)V': unplugged('registerEntityID'),
			'registerEntityID(Ljava/lang/Class;Ljava/lang/String;III)V': unplugged('registerEntityID'),
			'registerTileEntity(Ljava/lang/Class;Ljava/lang/String;)V': unplugged('registerTileEntity'),
			'registerTileEntity(Ljava/lang/Class;Ljava/lang/String;Lnet/minecraft/src/TileEntitySpecialRenderer;)V': unplugged('registerTileEntity'),
			'addSpawn(Ljava/lang/Class;IIILnet/minecraft/src/EnumCreatureType;)V': unplugged('addSpawn'),
			'addSpawn(Ljava/lang/Class;IIILnet/minecraft/src/EnumCreatureType;[Lnet/minecraft/src/BiomeGenBase;)V': unplugged('addSpawn'),
			'addBiome(Lnet/minecraft/src/BiomeGenBase;)V': unplugged('addBiome'),
			'addEntityRenderer?': null,
			'registerKey(Lnet/minecraft/src/BaseMod;Lnet/minecraft/src/KeyBinding;Z)V': unplugged('registerKey'),
			'addAchievementDesc(Lnet/minecraft/src/Achievement;Ljava/lang/String;Ljava/lang/String;)V': unplugged('addAchievementDesc'),
			'getPrivateValue(Ljava/lang/Class;Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/Object;': unplugged('getPrivateValue', null),
			'getPrivateValue(Ljava/lang/Class;Ljava/lang/Object;I)Ljava/lang/Object;': unplugged('getPrivateValue', null),
			'setPrivateValue(Ljava/lang/Class;Ljava/lang/Object;Ljava/lang/String;Ljava/lang/Object;)V': unplugged('setPrivateValue'),
			'setPrivateValue(Ljava/lang/Class;Ljava/lang/Object;ILjava/lang/Object;)V': unplugged('setPrivateValue'),
			'openGUI(Lnet/minecraft/src/EntityPlayer;Lnet/minecraft/src/GuiScreen;)V': unplugged('openGUI'),
			'addCommand(Lnet/minecraft/src/ICommand;)V': unplugged('addCommand'),
			'genericContainerRemoval(Lnet/minecraft/src/World;IIILnet/minecraft/src/IInventory;)V': unplugged('genericContainerRemoval'),
		},
	});
	delete vm.natives[SRC + 'ModLoader'].staticMethods['addEntityRenderer?'];
	function minecraftObj(vm) {
		var mc = vm.mcInstance || (vm.mcInstance = vm.newObject(vm.loadClass('net/minecraft/client/Minecraft')));
		if (vm.game && vm.game.mode === 'run') { mc[':theWorld'] = worldObj(vm); mc[':thePlayer'] = playerObj(vm, null); }
		return mc;
	}
	vm.defineNative('net/minecraft/client/Minecraft', { methods: { 'isSingleplayer()Z': function () { return 1; } } });
	vm.defineNative('java/util/logging/Logger', { methods: (function () {
		var m = {};
		['info', 'warning', 'severe', 'fine', 'finer', 'finest', 'config'].forEach(function (k) {
			m[k + '(Ljava/lang/String;)V'] = function (vm, self, a) { vm.log(k === 'warning' || k === 'severe' ? 'warn' : 'out', a[0]); };
		});
		m['log(Ljava/util/logging/Level;Ljava/lang/String;)V'] = function (vm, self, a) { vm.log('out', a[1]); };
		m['log(Ljava/util/logging/Level;Ljava/lang/String;Ljava/lang/Throwable;)V'] = function (vm, self, a) { vm.log('warn', a[1]); };
		return m;
	})(), staticMethods: { 'getLogger(Ljava/lang/String;)Ljava/util/logging/Logger;': function (vm) { return loggerObj(vm); } } });
	function loggerObj(vm) { return vm.mcLogger || (vm.mcLogger = vm.newObject(vm.loadClass('java/util/logging/Logger'))); }
	vm.defineNative('java/util/logging/Level', { statics: { INFO: null, WARNING: null, SEVERE: null, FINE: null, FINEST: null } });

	def('MapColor', { statics: {}, methods: { '<init>(II)V': function () {} } });
	def('Material', {
		statics: (function () { var s = {}; MATERIALS.forEach(function (n) { s[n] = null; }); return s; })(),
		clinit: function (vm, c) { MATERIALS.forEach(function (n) { var o = vm.newObject(c); o.$name = n; c.statics[n] = o; }); },
		methods: {
			'<init>(Lnet/minecraft/src/MapColor;)V': function (vm, self) { self.$name = self.$name || 'custom'; },
			'isSolid()Z': function (vm, self) { return ['air', 'water', 'lava', 'plants', 'vine', 'fire', 'circuits', 'snow', 'portal', 'web'].indexOf(self.$name) < 0 ? 1 : 0; },
			'isLiquid()Z': function (vm, self) { return self.$name === 'water' || self.$name === 'lava' ? 1 : 0; },
			'isOpaque()Z': function (vm, self) { return ['glass', 'leaves', 'ice', 'air'].indexOf(self.$name) < 0 ? 1 : 0; },
			'getCanBurn()Z': function (vm, self) { return ['wood', 'leaves', 'cloth', 'tnt', 'plants', 'vine'].indexOf(self.$name) >= 0 ? 1 : 0; },
			'setRequiresTool()Lnet/minecraft/src/Material;': function (vm, self) { self.$tool = true; return self; },
			'isToolNotRequired()Z': function (vm, self) { return self.$name === 'rock' || self.$name === 'iron' ? 0 : 1; },
		},
	});
	def('StepSound', {
		methods: {
			'<init>(Ljava/lang/String;FF)V': function (vm, self, a) { self.$name = a[0]; self[':stepSoundName'] = a[0]; self[':stepSoundVolume'] = a[1]; self[':stepSoundPitch'] = a[2]; },
			'getVolume()F': function (vm, self) { return self[':stepSoundVolume']; },
			'getPitch()F': function (vm, self) { return self[':stepSoundPitch']; },
			'getBreakSound()Ljava/lang/String;': function (vm, self) { return 'dig.' + self.$name; },
			'getStepSound()Ljava/lang/String;': function (vm, self) { return 'step.' + self.$name; },
		},
	});
	def('CreativeTabs', {
		statics: (function () { var s = {}; TABS.forEach(function (n) { s[n] = null; }); s.creativeTabArray = null; return s; })(),
		clinit: function (vm, c) {
			TABS.forEach(function (n, i) { var o = vm.newObject(c); o.$label = n.substring(3).toLowerCase(); o.$index = i; c.statics[n] = o; });
			c.statics.creativeTabArray = JVM.javaArray(vm, L('CreativeTabs'), TABS.map(function (n) { return c.statics[n]; }));
		},
		methods: {
			'<init>(ILjava/lang/String;)V': function (vm, self, a) { self.$label = a[1]; self.$index = a[0]; },
			'<init>(Ljava/lang/String;)V': function (vm, self, a) { self.$label = a[0]; },
			'getTabLabel()Ljava/lang/String;': function (vm, self) { return self.$label; },
			'getTabIconItemIndex()I': function () { return 1; },
		},
	});
	var enumStatics = function (names, init) {
		return {
			statics: (function () { var s = {}; names.forEach(function (n) { s[n] = null; }); return s; })(),
			clinit: function (vm, c) {
				var all = names.map(function (n, i) { var o = vm.newObject(c); o.$name = n; o.$ordinal = i; init(o, n); c.statics[n] = o; return o; });
				c.$values = all;
			},
		};
	};
	def('EnumToolMaterial', Object.assign({ super: 'java/lang/Enum' }, enumStatics(Object.keys(TOOL_MATS), function (o, n) { o.$m = TOOL_MATS[n]; }), {
		methods: {
			'getHarvestLevel()I': function (vm, self) { return self.$m[0]; },
			'getMaxUses()I': function (vm, self) { return self.$m[1]; },
			'getEfficiencyOnProperMaterial()F': function (vm, self) { return self.$m[2]; },
			'getDamageVsEntity()I': function (vm, self) { return self.$m[3]; },
			'getEnchantability()I': function (vm, self) { return self.$m[4]; },
			'getToolCraftingMaterial()I': function (vm, self) { return { WOOD: 5, STONE: 4, IRON: 265, EMERALD: 264, GOLD: 266 }[self.$name]; },
		},
		staticMethods: { 'values()[Lnet/minecraft/src/EnumToolMaterial;': function (vm) { var c = vm.loadClass(SRC + 'EnumToolMaterial'); vm.initClass(c); return JVM.javaArray(vm, L('EnumToolMaterial'), c.$values); } },
	}));
	def('EnumArmorMaterial', Object.assign({ super: 'java/lang/Enum' }, enumStatics(Object.keys(ARMOR_MATS), function (o, n) { o.$m = ARMOR_MATS[n]; }), {
		methods: {
			'getDurability(I)I': function (vm, self, a) { return [11, 16, 15, 13][a[0]] * self.$m[0]; },
			'getDamageReductionAmount(I)I': function (vm, self, a) { return self.$m[1][a[0]]; },
			'getEnchantability()I': function (vm, self) { return self.$m[2]; },
		},
	}));
	vm.natives[SRC + 'EnumToolMaterial'].methods = Object.assign({}, vm.natives[SRC + 'EnumToolMaterial'].methods);

	def('Icon', { access: I, abstractMethods: { 'getIconName()Ljava/lang/String;': true } });
	def('IconRegister', { access: I, abstractMethods: { 'registerIcon(Ljava/lang/String;)Lnet/minecraft/src/Icon;': true } });
	vm.defineNative('mcre/Icon', { interfaces: [SRC + 'Icon'], methods: {
		'getIconName()Ljava/lang/String;': function (vm, self) { return self.$name; },
		'getOriginX()I': function () { return 0; }, 'getOriginY()I': function () { return 0; },
		'getMinU()F': function () { return 0; }, 'getMaxU()F': function () { return 1; },
		'getMinV()F': function () { return 0; }, 'getMaxV()F': function () { return 1; },
		'getInterpolatedU(D)F': function (vm, s, a) { return a[0] / 16; }, 'getInterpolatedV(D)F': function (vm, s, a) { return a[0] / 16; },
		'getSheetWidth()I': function () { return 16; }, 'getSheetHeight()I': function () { return 16; },
	} });
	vm.defineNative('mcre/IconRegister', { interfaces: [SRC + 'IconRegister'], methods: {
		'registerIcon(Ljava/lang/String;)Lnet/minecraft/src/Icon;': function (vm, self, a) { return iconObj(vm, a[0]); },
	} });

	var blockMethods = {
		'<init>(ILnet/minecraft/src/Material;)V': function (vm, self, a) { initBlock(vm, self, a[0], a[1]); },
		'setHardness(F)Lnet/minecraft/src/Block;': function (vm, self, a) { self[':blockHardness'] = a[0]; if (self[':blockResistance'] < a[0] * 5) self[':blockResistance'] = a[0] * 5; return self; },
		'setResistance(F)Lnet/minecraft/src/Block;': function (vm, self, a) { self[':blockResistance'] = a[0] * 3; return self; },
		'setBlockUnbreakable()Lnet/minecraft/src/Block;': function (vm, self) { self[':blockHardness'] = -1; return self; },
		'setStepSound(Lnet/minecraft/src/StepSound;)Lnet/minecraft/src/Block;': function (vm, self, a) { self[':stepSound'] = a[0]; return self; },
		'setLightValue(F)Lnet/minecraft/src/Block;': function (vm, self, a) { self.$light = Math.round(15 * a[0]); return self; },
		'setLightOpacity(I)Lnet/minecraft/src/Block;': function (vm, self, a) { self.$opacity = a[0]; return self; },
		'setTickRandomly(Z)Lnet/minecraft/src/Block;': function (vm, self, a) { self[':needsRandomTick'] = a[0]; return self; },
		'setUnlocalizedName(Ljava/lang/String;)Lnet/minecraft/src/Block;': function (vm, self, a) { self[':unlocalizedName'] = a[0]; return self; },
		'setCreativeTab(Lnet/minecraft/src/CreativeTabs;)Lnet/minecraft/src/Block;': function (vm, self, a) { self.$tab = a[0]; return self; },
		'disableStats()Lnet/minecraft/src/Block;': function (vm, self) { return self; },
		'setBlockBounds(FFFFFF)V': function (vm, self, a) { ['minX', 'minY', 'minZ', 'maxX', 'maxY', 'maxZ'].forEach(function (k, i) { self[':' + k] = a[i]; }); },
		'getUnlocalizedName()Ljava/lang/String;': function (vm, self) { return 'tile.' + (self[':unlocalizedName'] || 'null'); },
		'getLocalizedName()Ljava/lang/String;': function (vm, self) { var k = vm.callVirtual(self, 'getUnlocalizedName', '()Ljava/lang/String;', []); return reg(vm).lang[k + '.name'] || k; },
		'registerIcons(Lnet/minecraft/src/IconRegister;)V': function (vm, self, a) { self[':blockIcon'] = vm.callVirtual(a[0], 'registerIcon', '(Ljava/lang/String;)Lnet/minecraft/src/Icon;', [self[':unlocalizedName'] || 'stone']); },
		'getIcon(II)Lnet/minecraft/src/Icon;': function (vm, self) { return self[':blockIcon']; },
		'getBlockTextureFromSide(I)Lnet/minecraft/src/Icon;': function (vm, self, a) { return vm.callVirtual(self, 'getIcon', '(II)Lnet/minecraft/src/Icon;', [a[0], 0]); },
		'idDropped(ILjava/util/Random;I)I': function (vm, self) { return self[':blockID']; },
		'quantityDropped(Ljava/util/Random;)I': function () { return 1; },
		'quantityDroppedWithBonus(ILjava/util/Random;)I': function (vm, self, a) { return vm.callVirtual(self, 'quantityDropped', '(Ljava/util/Random;)I', [a[1]]); },
		'damageDropped(I)I': function () { return 0; },
		'isOpaqueCube()Z': function (vm, self) { return 1; },
		'renderAsNormalBlock()Z': function () { return 1; },
		'getRenderType()I': function () { return 0; },
		'tickRate(Lnet/minecraft/src/World;)I': function () { return 10; },
		'getBlockHardness(Lnet/minecraft/src/World;III)F': function (vm, self) { return self[':blockHardness']; },
		'onBlockActivated(Lnet/minecraft/src/World;IIILnet/minecraft/src/EntityPlayer;IFFF)Z': function () { return 0; },
		'onBlockAdded(Lnet/minecraft/src/World;III)V': function () {},
		'breakBlock(Lnet/minecraft/src/World;IIIII)V': function () {},
		'onBlockDestroyedByPlayer(Lnet/minecraft/src/World;IIII)V': function () {},
		'onNeighborBlockChange(Lnet/minecraft/src/World;IIII)V': function () {},
		'updateTick(Lnet/minecraft/src/World;IIILjava/util/Random;)V': function () {},
		'randomDisplayTick(Lnet/minecraft/src/World;IIILjava/util/Random;)V': function () {},
		'onEntityWalking(Lnet/minecraft/src/World;IIILnet/minecraft/src/Entity;)V': function () {},
		'onEntityCollidedWithBlock(Lnet/minecraft/src/World;IIILnet/minecraft/src/Entity;)V': function () {},
		'onBlockPlacedBy(Lnet/minecraft/src/World;IIILnet/minecraft/src/EntityLiving;Lnet/minecraft/src/ItemStack;)V': function () {},
		'onBlockClicked(Lnet/minecraft/src/World;IIILnet/minecraft/src/EntityPlayer;)V': function () {},
		'canPlaceBlockAt(Lnet/minecraft/src/World;III)Z': function () { return 1; },
		'dropBlockAsItem_do(Lnet/minecraft/src/World;IIILnet/minecraft/src/ItemStack;)V': function (vm, self, a) { dropStack(vm, a[1] + 0.5, a[2] + 0.5, a[3] + 0.5, a[4]); },
		'dropBlockAsItem(Lnet/minecraft/src/World;IIIII)V': function () {},
		'getCollisionBoundingBoxFromPool(Lnet/minecraft/src/World;III)Lnet/minecraft/src/AxisAlignedBB;': function () { return null; },
		'isCollidable()Z': function () { return 1; },
		'getMobilityFlag()I': function () { return 0; },
		'getEnableStats()Z': function () { return 1; },
		'getBlockColor()I': function () { return 0xffffff; },
		'getRenderColor(I)I': function () { return 0xffffff; },
		'colorMultiplier(Lnet/minecraft/src/IBlockAccess;III)I': function () { return 0xffffff; },
		'setBlockBoundsForItemRender()V': function () {},
		'harvestBlock(Lnet/minecraft/src/World;Lnet/minecraft/src/EntityPlayer;IIII)V': function () {},
		'getRenderBlockPass()I': function () { return 0; },
		'hasTileEntity()Z?': null,
	};
	delete blockMethods['hasTileEntity()Z?'];
	var blockStatics = { blocksList: null, opaqueCubeLookup: null, lightOpacity: null, lightValue: null, canBlockGrass: null, useNeighborBrightness: null };
	Object.keys(SOUNDS).forEach(function (k) { blockStatics[k] = null; });
	VANILLA_BLOCKS.split(',').forEach(function (kv) { blockStatics[kv.split(' ')[0]] = null; });
	def('Block', {
		statics: blockStatics,
		methods: blockMethods,
		clinit: function (vm, c) {
			var r = reg(vm);
			c.statics.blocksList = vm.newArray(L('Block'), 4096);
			c.statics.lightValue = vm.newArray('I', 4096);
			c.statics.lightOpacity = vm.newArray('I', 4096);
			c.statics.opaqueCubeLookup = vm.newArray('Z', 4096);
			c.statics.canBlockGrass = vm.newArray('Z', 4096);
			c.statics.useNeighborBrightness = vm.newArray('Z', 4096);
			var ss = vm.loadClass(SRC + 'StepSound');
			Object.keys(SOUNDS).forEach(function (k) { var o = vm.newObject(ss); o.$name = SOUNDS[k]; o[':stepSoundName'] = SOUNDS[k]; o[':stepSoundVolume'] = 1; o[':stepSoundPitch'] = 1; c.statics[k] = o; });
			var rock = vm.loadClass(SRC + 'Material'); vm.initClass(rock);
			r.vanilla = true;
			VANILLA_BLOCKS.split(',').forEach(function (kv) {
				var p = kv.split(' '), b = vm.newObject(c);
				initBlock(vm, b, +p[1], rock.statics.rock);
				b.$vanilla = true;
				b[':unlocalizedName'] = p[0];
				c.statics[p[0]] = b;
			});
			r.vanilla = false;
		},
	});
	function initBlock(vm, self, id, material) {
		var c = vm.loadClass(SRC + 'Block');
		if (c.initState !== 2) vm.initClass(c);
		self[':blockID'] = id;
		self[':blockMaterial'] = material;
		self[':blockHardness'] = 0;
		self[':blockResistance'] = 0;
		self[':slipperiness'] = 0.6;
		self[':blockParticleGravity'] = 1;
		self[':stepSound'] = c.statics.soundPowderFootstep;
		self[':minX'] = 0; self[':minY'] = 0; self[':minZ'] = 0; self[':maxX'] = 1; self[':maxY'] = 1; self[':maxZ'] = 1;
		self[':enableStats'] = 1;
		self[':isBlockContainer'] = 0;
		if (id < 0 || id >= 4096) return;
		var list = c.statics.blocksList.a;
		if (list[id] && !list[id].$vanilla && !reg(vm).vanilla) vm.log('warn', 'block id ' + id + ' is used twice');
		list[id] = self;
		if (!reg(vm).vanilla) { reg(vm).blocks[id] = self; self.$mod = vm.currentMod || ''; }
	}

	var itemMethods = {
		'<init>(I)V': function (vm, self, a) { initItem(vm, self, 256 + a[0]); },
		'setMaxStackSize(I)Lnet/minecraft/src/Item;': function (vm, self, a) { self[':maxStackSize'] = a[0]; return self; },
		'setMaxDamage(I)Lnet/minecraft/src/Item;': function (vm, self, a) { self[':maxDamage'] = a[0]; return self; },
		'setHasSubtypes(Z)Lnet/minecraft/src/Item;': function (vm, self, a) { self[':hasSubtypes'] = a[0]; return self; },
		'setUnlocalizedName(Ljava/lang/String;)Lnet/minecraft/src/Item;': function (vm, self, a) { self[':unlocalizedName'] = a[0]; return self; },
		'setCreativeTab(Lnet/minecraft/src/CreativeTabs;)Lnet/minecraft/src/Item;': function (vm, self, a) { self.$tab = a[0]; return self; },
		'setFull3D()Lnet/minecraft/src/Item;': function (vm, self) { self[':bFull3D'] = 1; return self; },
		'setContainerItem(Lnet/minecraft/src/Item;)Lnet/minecraft/src/Item;': function (vm, self, a) { self[':containerItem'] = a[0]; return self; },
		'setPotionEffect(Ljava/lang/String;)Lnet/minecraft/src/Item;': function (vm, self) { return self; },
		'getUnlocalizedName()Ljava/lang/String;': function (vm, self) { return 'item.' + (self[':unlocalizedName'] || 'null'); },
		'getUnlocalizedName(Lnet/minecraft/src/ItemStack;)Ljava/lang/String;': function (vm, self) { return vm.callVirtual(self, 'getUnlocalizedName', '()Ljava/lang/String;', []); },
		'getItemDisplayName(Lnet/minecraft/src/ItemStack;)Ljava/lang/String;': function (vm, self, a) { var k = vm.callVirtual(self, 'getUnlocalizedName', '(Lnet/minecraft/src/ItemStack;)Ljava/lang/String;', [a[0]]); return reg(vm).lang[k + '.name'] || k; },
		'getItemStackLimit()I': function (vm, self) { return self[':maxStackSize']; },
		'getMaxDamage()I': function (vm, self) { return self[':maxDamage']; },
		'isDamageable()Z': function (vm, self) { return self[':maxDamage'] > 0 && !self[':hasSubtypes'] ? 1 : 0; },
		'getHasSubtypes()Z': function (vm, self) { return self[':hasSubtypes']; },
		'registerIcons(Lnet/minecraft/src/IconRegister;)V': function (vm, self, a) { self[':itemIcon'] = vm.callVirtual(a[0], 'registerIcon', '(Ljava/lang/String;)Lnet/minecraft/src/Icon;', [self[':unlocalizedName'] || 'stick']); },
		'getIconFromDamage(I)Lnet/minecraft/src/Icon;': function (vm, self) { return self[':itemIcon']; },
		'getIconIndex(Lnet/minecraft/src/ItemStack;)Lnet/minecraft/src/Icon;': function (vm, self, a) { return vm.callVirtual(self, 'getIconFromDamage', '(I)Lnet/minecraft/src/Icon;', [a[0] ? a[0][':itemDamage'] : 0]); },
		'onItemUse(Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/EntityPlayer;Lnet/minecraft/src/World;IIIIFFF)Z': function () { return 0; },
		'onItemRightClick(Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/World;Lnet/minecraft/src/EntityPlayer;)Lnet/minecraft/src/ItemStack;': function (vm, self, a) { return a[0]; },
		'onEaten(Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/World;Lnet/minecraft/src/EntityPlayer;)Lnet/minecraft/src/ItemStack;': function (vm, self, a) { return a[0]; },
		'hitEntity(Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/EntityLiving;Lnet/minecraft/src/EntityLiving;)Z': function () { return 0; },
		'onBlockDestroyed(Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/World;IIIILnet/minecraft/src/EntityLiving;)Z': function () { return 0; },
		'onUpdate(Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/World;Lnet/minecraft/src/Entity;IZ)V': function () {},
		'onCreated(Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/World;Lnet/minecraft/src/EntityPlayer;)V': function () {},
		'getStrVsBlock(Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/Block;)F': function () { return 1; },
		'getDamageVsEntity(Lnet/minecraft/src/Entity;)I': function () { return 1; },
		'canHarvestBlock(Lnet/minecraft/src/Block;)Z': function () { return 0; },
		'hasEffect(Lnet/minecraft/src/ItemStack;)Z': function () { return 0; },
		'getMaxItemUseDuration(Lnet/minecraft/src/ItemStack;)I': function () { return 0; },
		'isFull3D()Z': function (vm, self) { return self[':bFull3D']; },
		'getColorFromItemStack(Lnet/minecraft/src/ItemStack;I)I': function () { return 0xffffff; },
		'getContainerItem()Lnet/minecraft/src/Item;': function (vm, self) { return self[':containerItem'] || null; },
		'getItemEnchantability()I': function () { return 0; },
	};
	var itemStatics = { itemsList: null, itemRand: null };
	VANILLA_ITEMS.split(',').forEach(function (kv) { itemStatics[kv.split(' ')[0]] = null; });
	def('Item', {
		statics: itemStatics,
		methods: itemMethods,
		clinit: function (vm, c) {
			var r = reg(vm);
			c.statics.itemsList = vm.newArray(L('Item'), 32000);
			c.statics.itemRand = vm.newObject(vm.loadClass('java/util/Random'));
			vm.callVirtual(c.statics.itemRand, '<init>', '()V', []);
			r.vanilla = true;
			VANILLA_ITEMS.split(',').forEach(function (kv) {
				var p = kv.split(' '), it = vm.newObject(c);
				initItem(vm, it, +p[1]);
				it.$vanilla = true;
				it[':unlocalizedName'] = p[0];
				c.statics[p[0]] = it;
			});
			r.vanilla = false;
			var bc = vm.loadClass(SRC + 'Block'); vm.initClass(bc);
		},
	});
	function initItem(vm, self, id) {
		var c = vm.loadClass(SRC + 'Item');
		if (c.initState !== 2) vm.initClass(c);
		self[':itemID'] = id;
		self[':maxStackSize'] = 64;
		self[':maxDamage'] = 0;
		self[':hasSubtypes'] = 0;
		self[':bFull3D'] = 0;
		if (id < 0 || id >= 32000) return;
		var list = c.statics.itemsList.a;
		if (list[id] && !list[id].$vanilla && !reg(vm).vanilla && !list[id].$blockItem) vm.log('warn', 'item id ' + id + ' is used twice');
		list[id] = self;
		if (!reg(vm).vanilla && !self.$blockItem) { reg(vm).items[id] = self; self.$mod = vm.currentMod || ''; }
	}
	def('ItemBlock', { super: SRC + 'Item', methods: {
		'<init>(I)V': function (vm, self, a) { self.$blockItem = true; initItem(vm, self, a[0] + 256); self[':blockID'] = a[0] + 256; },
		'getBlockID()I': function (vm, self) { return self[':blockID']; },
	} });
	def('ItemFood', { super: SRC + 'Item', methods: {
		'<init>(IIFZ)V': function (vm, self, a) { initItem(vm, self, 256 + a[0]); self.$food = [a[1], a[2]]; self[':healAmount'] = a[1]; self[':saturationModifier'] = a[2]; self[':isWolfsFavoriteMeat'] = a[3]; },
		'<init>(IIZ)V': function (vm, self, a) { initItem(vm, self, 256 + a[0]); self.$food = [a[1], 0.6]; self[':healAmount'] = a[1]; self[':saturationModifier'] = 0.6; self[':isWolfsFavoriteMeat'] = a[2]; },
		'getHealAmount()I': function (vm, self) { return self.$food[0]; },
		'getSaturationModifier()F': function (vm, self) { return self.$food[1]; },
		'setAlwaysEdible()Lnet/minecraft/src/ItemFood;': function (vm, self) { self.$alwaysEdible = true; return self; },
		'setPotionEffect(IIIF)Lnet/minecraft/src/ItemFood;': function (vm, self) { return self; },
	} });
	var toolInit = function (kind) { return function (vm, self, a) { initItem(vm, self, 256 + a[0]); self.$tool = kind; self.$toolMat = a[1]; self[':toolMaterial'] = a[1]; self[':maxStackSize'] = 1; self[':maxDamage'] = a[1] ? a[1].$m[1] : 0; }; };
	def('ItemTool', { super: SRC + 'Item', methods: { '<init>(IILnet/minecraft/src/EnumToolMaterial;[Lnet/minecraft/src/Block;)V': function (vm, self, a) { toolInit('tool')(vm, self, [a[0], a[2]]); } } });
	def('ItemSword', { super: SRC + 'Item', methods: { '<init>(ILnet/minecraft/src/EnumToolMaterial;)V': toolInit('sword') } });
	def('ItemPickaxe', { super: SRC + 'ItemTool', methods: { '<init>(ILnet/minecraft/src/EnumToolMaterial;)V': toolInit('pickaxe') } });
	def('ItemAxe', { super: SRC + 'ItemTool', methods: { '<init>(ILnet/minecraft/src/EnumToolMaterial;)V': toolInit('axe') } });
	def('ItemSpade', { super: SRC + 'ItemTool', methods: { '<init>(ILnet/minecraft/src/EnumToolMaterial;)V': toolInit('shovel') } });
	def('ItemHoe', { super: SRC + 'Item', methods: { '<init>(ILnet/minecraft/src/EnumToolMaterial;)V': toolInit('hoe') } });
	def('ItemArmor', { super: SRC + 'Item', methods: {
		'<init>(ILnet/minecraft/src/EnumArmorMaterial;II)V': function (vm, self, a) {
			initItem(vm, self, 256 + a[0]);
			self.$armor = { mat: a[1], slot: a[3] };
			self[':armorType'] = a[3]; self[':renderIndex'] = a[2]; self[':maxStackSize'] = 1;
			self[':maxDamage'] = a[1] ? [11, 16, 15, 13][a[3]] * a[1].$m[0] : 0;
			self[':damageReduceAmount'] = a[1] ? a[1].$m[1][a[3]] : 0;
		},
	} });

	var stackInit = function (vm, self, id, n, dmg) { self[':itemID'] = id; self[':stackSize'] = n; self[':itemDamage'] = dmg; };
	def('ItemStack', { methods: {
		'<init>(Lnet/minecraft/src/Block;)V': function (vm, self, a) { stackInit(vm, self, a[0][':blockID'], 1, 0); },
		'<init>(Lnet/minecraft/src/Block;I)V': function (vm, self, a) { stackInit(vm, self, a[0][':blockID'], a[1], 0); },
		'<init>(Lnet/minecraft/src/Block;II)V': function (vm, self, a) { stackInit(vm, self, a[0][':blockID'], a[1], a[2]); },
		'<init>(Lnet/minecraft/src/Item;)V': function (vm, self, a) { stackInit(vm, self, a[0][':itemID'], 1, 0); },
		'<init>(Lnet/minecraft/src/Item;I)V': function (vm, self, a) { stackInit(vm, self, a[0][':itemID'], a[1], 0); },
		'<init>(Lnet/minecraft/src/Item;II)V': function (vm, self, a) { stackInit(vm, self, a[0][':itemID'], a[1], a[2]); },
		'<init>(III)V': function (vm, self, a) { stackInit(vm, self, a[0], a[1], a[2]); },
		'getItem()Lnet/minecraft/src/Item;': function (vm, self) { return itemById(vm, self[':itemID']); },
		'getItemDamage()I': function (vm, self) { return self[':itemDamage']; },
		'setItemDamage(I)V': function (vm, self, a) { self[':itemDamage'] = a[0]; },
		'getMaxStackSize()I': function (vm, self) { var it = itemById(vm, self[':itemID']); return it ? it[':maxStackSize'] : 64; },
		'isStackable()Z': function (vm, self) { var it = itemById(vm, self[':itemID']); return !it || it[':maxStackSize'] > 1 ? 1 : 0; },
		'copy()Lnet/minecraft/src/ItemStack;': function (vm, self) { return newStack(vm, self[':itemID'], self[':stackSize'], self[':itemDamage']); },
		'isItemEqual(Lnet/minecraft/src/ItemStack;)Z': function (vm, self, a) { return a[0] && a[0][':itemID'] === self[':itemID'] && a[0][':itemDamage'] === self[':itemDamage'] ? 1 : 0; },
		'getItemName()Ljava/lang/String;': function (vm, self) { var it = itemById(vm, self[':itemID']); return it ? vm.callVirtual(it, 'getUnlocalizedName', '(Lnet/minecraft/src/ItemStack;)Ljava/lang/String;', [self]) : 'item.null'; },
		'getDisplayName()Ljava/lang/String;': function (vm, self) { var k = vm.callVirtual(self, 'getItemName', '()Ljava/lang/String;', []); return reg(vm).lang[k + '.name'] || k; },
		'toString()Ljava/lang/String;': function (vm, self) { return self[':stackSize'] + 'x' + vm.callVirtual(self, 'getItemName', '()Ljava/lang/String;', []) + '@' + self[':itemDamage']; },
		'damageItem(ILnet/minecraft/src/EntityLiving;)V': function (vm, self, a) { self[':itemDamage'] += a[0]; },
		'splitStack(I)Lnet/minecraft/src/ItemStack;': function (vm, self, a) { self[':stackSize'] -= a[0]; return newStack(vm, self[':itemID'], a[0], self[':itemDamage']); },
		'hasTagCompound()Z': function () { return 0; },
		'getTagCompound()Lnet/minecraft/src/NBTTagCompound;': function () { return null; },
	} });
	function itemById(vm, id) { var c = vm.loadClass(SRC + 'Item'); vm.initClass(c); return c.statics.itemsList.a[id] || null; }
	function newStack(vm, id, n, d) { var s = vm.newObject(vm.loadClass(SRC + 'ItemStack')); stackInit(vm, s, id, n, d); return s; }

	installWorld(vm, def);
}

function iconObj(vm, name) { var o = new JObject(vm.loadClass('mcre/Icon')); o.$name = String(name); return o; }
function dropStack(vm, x, y, z, stack) {
	if (!stack) return;
	op(vm, 'drop', x, y, z, vm.game ? vm.game.itemToGame(stack[':itemID']) : stack[':itemID'], stack[':stackSize'], stack[':itemDamage']);
}

function worldObj(vm) {
	if (!vm.mcWorld) {
		var w = vm.newObject(vm.loadClass(SRC + 'World'));
		w[':isRemote'] = 0;
		var rnd = vm.newObject(vm.loadClass('java/util/Random'));
		vm.callVirtual(rnd, '<init>', '()V', []);
		w[':rand'] = rnd;
		vm.mcWorld = w;
	}
	return vm.mcWorld;
}
function playerObj(vm, info) {
	var p = vm.mcPlayer || (vm.mcPlayer = vm.newObject(vm.loadClass(SRC + 'EntityClientPlayerMP')));
	var i = info || op(vm, 'player') || {};
	p[':posX'] = +i.x || 0; p[':posY'] = +i.y || 0; p[':posZ'] = +i.z || 0;
	p[':rotationYaw'] = +i.yaw || 0; p[':rotationPitch'] = +i.pitch || 0;
	p[':username'] = i.name || 'Player';
	p[':worldObj'] = worldObj(vm);
	p[':onGround'] = i.onGround ? 1 : 0;
	p.$info = i;
	if (!p[':inventory']) p[':inventory'] = vm.newObject(vm.loadClass(SRC + 'InventoryPlayer'));
	p[':inventory'].$player = p;
	if (!p[':capabilities']) p[':capabilities'] = vm.newObject(vm.loadClass(SRC + 'PlayerCapabilities'));
	p[':capabilities'][':isCreativeMode'] = i.creative ? 1 : 0;
	p[':capabilities'][':allowFlying'] = i.creative ? 1 : 0;
	p[':capabilities'][':isFlying'] = i.flying ? 1 : 0;
	return p;
}
function heldStack(vm) {
	var h = op(vm, 'held');
	if (!h || !h.id) return null;
	return (function () { var s = vm.newObject(vm.loadClass(SRC + 'ItemStack')); s[':itemID'] = vm.game.itemToJava(h.id); s[':stackSize'] = h.count; s[':itemDamage'] = h.data || 0; return s; })();
}

function installWorld(vm, def) {
	var g = function (vm) { return vm.game || { blockToGame: function (x) { return x; }, blockToJava: function (x) { return x; }, itemToGame: function (x) { return x; }, itemToJava: function (x) { return x; } }; };
	var tile = function (vm, x, y, z) { var t = op(vm, 'tile', x, y, z); return t ? t : { id: 0, data: 0 }; };
	def('IBlockAccess', { access: JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC });
	def('World', { interfaces: [SRC + 'IBlockAccess'], methods: {
		'getBlockId(III)I': function (vm, self, a) { return g(vm).blockToJava(tile(vm, a[0], a[1], a[2]).id); },
		'getBlockMetadata(III)I': function (vm, self, a) { return tile(vm, a[0], a[1], a[2]).data; },
		'isAirBlock(III)Z': function (vm, self, a) { return tile(vm, a[0], a[1], a[2]).id === 0 ? 1 : 0; },
		'setBlock(IIII)Z': function (vm, self, a) { op(vm, 'settile', a[0], a[1], a[2], g(vm).blockToGame(a[3]), 0); return 1; },
		'setBlock(IIIIII)Z': function (vm, self, a) { op(vm, 'settile', a[0], a[1], a[2], g(vm).blockToGame(a[3]), a[4]); return 1; },
		'setBlockToAir(III)Z': function (vm, self, a) { op(vm, 'settile', a[0], a[1], a[2], 0, 0); return 1; },
		'setBlockMetadataWithNotify(IIIII)Z': function (vm, self, a) { op(vm, 'setdata', a[0], a[1], a[2], a[3]); return 1; },
		'destroyBlock(IIIZ)Z': function (vm, self, a) { op(vm, 'destroy', a[0], a[1], a[2], a[3] ? 1 : 0); return 1; },
		'playSoundEffect(DDDLjava/lang/String;FF)V': function (vm, self, a) { op(vm, 'sound', a[0], a[1], a[2], a[3], a[4], a[5]); },
		'playSoundAtEntity(Lnet/minecraft/src/Entity;Ljava/lang/String;FF)V': function (vm, self, a) { op(vm, 'sound', a[0][':posX'], a[0][':posY'], a[0][':posZ'], a[1], a[2], a[3]); },
		'spawnParticle(Ljava/lang/String;DDDDDD)V': function (vm, self, a) { op(vm, 'particle', a[0], a[1], a[2], a[3], a[4], a[5], a[6]); },
		'spawnEntityInWorld(Lnet/minecraft/src/Entity;)Z': function (vm, self, a) {
			var e = a[0];
			if (e && e.$stack) { dropStack(vm, e[':posX'], e[':posY'], e[':posZ'], e.$stack); return 1; }
			vm.warnOnce('spawn:' + (e && e.cls.name), 'spawning ' + (e ? e.cls.name.replace(/[/]/g, '.') : 'null') + ' is not available here (left unplugged)');
			return 0;
		},
		'createExplosion(Lnet/minecraft/src/Entity;DDDFZ)Lnet/minecraft/src/Explosion;': function (vm, self, a) { op(vm, 'explode', a[1], a[2], a[3], a[4], a[5] ? 1 : 0); return null; },
		'getWorldTime()J': function (vm) { return BigInt(op(vm, 'time') || 0); },
		'getTotalWorldTime()J': function (vm) { return BigInt(op(vm, 'time') || 0); },
		'setWorldTime(J)V': function (vm, self, a) { op(vm, 'settime', Number(a[0])); },
		'isDaytime()Z': function (vm) { var t = (op(vm, 'time') || 0) % 24000; return t < 12000 ? 1 : 0; },
		'getHeightValue(II)I': function (vm, self, a) { var y = 127; while (y > 0 && tile(vm, a[0], y, a[1]).id === 0) y--; return y + 1; },
		'getTopSolidOrLiquidBlock(II)I': function (vm, self, a) { var y = 127; while (y > 0 && tile(vm, a[0], y, a[1]).id === 0) y--; return y + 1; },
		'markBlockForUpdate(III)V': function () {},
		'notifyBlocksOfNeighborChange(IIII)V': function () {},
		'scheduleBlockUpdate(IIIII)V': function () {},
		'getClosestPlayer(DDDD)Lnet/minecraft/src/EntityPlayer;': function (vm) { return playerObj(vm, null); },
		'getClosestPlayerToEntity(Lnet/minecraft/src/Entity;D)Lnet/minecraft/src/EntityPlayer;': function (vm) { return playerObj(vm, null); },
		'isBlockIndirectlyGettingPowered(III)Z': function () { return 0; },
		'getBlockMaterial(III)Lnet/minecraft/src/Material;': function (vm, self, a) {
			var id = g(vm).blockToJava(tile(vm, a[0], a[1], a[2]).id), bc = vm.loadClass(SRC + 'Block'); vm.initClass(bc);
			var b = bc.statics.blocksList.a[id];
			var mc = vm.loadClass(SRC + 'Material'); vm.initClass(mc);
			return b ? b[':blockMaterial'] : mc.statics.air;
		},
	} });
	var ent = { methods: {
		'<init>(Lnet/minecraft/src/World;)V': function (vm, self, a) { self[':worldObj'] = a[0]; },
		'setPosition(DDD)V': function (vm, self, a) { self[':posX'] = a[0]; self[':posY'] = a[1]; self[':posZ'] = a[2]; },
		'setLocationAndAngles(DDDFF)V': function (vm, self, a) { self[':posX'] = a[0]; self[':posY'] = a[1]; self[':posZ'] = a[2]; },
		'setDead()V': function () {},
		'isSneaking()Z': function (vm, self) { return self.$info && self.$info.sneaking ? 1 : 0; },
		'getDistanceToEntity(Lnet/minecraft/src/Entity;)F': function (vm, self, a) { var dx = self[':posX'] - a[0][':posX'], dy = self[':posY'] - a[0][':posY'], dz = self[':posZ'] - a[0][':posZ']; return Math.sqrt(dx * dx + dy * dy + dz * dz); },
		'getDistance(DDD)D': function (vm, self, a) { var dx = self[':posX'] - a[0], dy = self[':posY'] - a[1], dz = self[':posZ'] - a[2]; return Math.sqrt(dx * dx + dy * dy + dz * dz); },
	} };
	def('Entity', ent);
	def('EntityLiving', { super: SRC + 'Entity', methods: {
		'heal(I)V': function (vm, self, a) { op(vm, 'heal', a[0]); },
		'getHealth()I': function (vm, self) { var i = op(vm, 'player'); return i ? i.health : 20; },
		'setEntityHealth(I)V': function (vm, self, a) { op(vm, 'sethealth', a[0]); },
		'getHeldItem()Lnet/minecraft/src/ItemStack;': function (vm) { return heldStack(vm); },
	} });
	def('EntityPlayer', { super: SRC + 'EntityLiving', methods: {
		'addChatMessage(Ljava/lang/String;)V': function (vm, self, a) { op(vm, 'msg', a[0]); },
		'sendChatToPlayer(Ljava/lang/String;)V': function (vm, self, a) { op(vm, 'msg', a[0]); },
		'getCurrentEquippedItem()Lnet/minecraft/src/ItemStack;': function (vm) { return heldStack(vm); },
		'dropPlayerItem(Lnet/minecraft/src/ItemStack;)Lnet/minecraft/src/EntityItem;': function (vm, self, a) { dropStack(vm, self[':posX'], self[':posY'], self[':posZ'], a[0]); return null; },
		'getFoodStats()Lnet/minecraft/src/FoodStats;': function (vm, self) { return self.$food || (self.$food = vm.newObject(vm.loadClass(SRC + 'FoodStats'))); },
		'getCommandSenderName()Ljava/lang/String;': function (vm, self) { return self[':username']; },
		'getEntityName()Ljava/lang/String;': function (vm, self) { return self[':username']; },
		'setPositionAndUpdate(DDD)V': function (vm, self, a) { op(vm, 'setpos', a[0], a[1], a[2]); },
		'canPlayerEdit(IIIILnet/minecraft/src/ItemStack;)Z': function () { return 1; },
		'addExperience(I)V': function (vm, self, a) { op(vm, 'xp', a[0]); },
	} });
	def('EntityPlayerSP', { super: SRC + 'EntityPlayer', methods: {} });
	def('EntityClientPlayerMP', { super: SRC + 'EntityPlayerSP', methods: {} });
	def('EntityPlayerMP', { super: SRC + 'EntityPlayer', methods: {} });
	def('PlayerCapabilities', { methods: { '<init>()V': function () {} } });
	def('FoodStats', { methods: {
		'addStats(IF)V': function (vm, self, a) { op(vm, 'feed', a[0], a[1]); },
		'getFoodLevel()I': function (vm) { var i = op(vm, 'player'); return i ? i.food : 20; },
	} });
	def('InventoryPlayer', { methods: {
		'addItemStackToInventory(Lnet/minecraft/src/ItemStack;)Z': function (vm, self, a) {
			var s = a[0];
			if (!s) return 0;
			op(vm, 'give', g(vm).itemToGame(s[':itemID']), s[':stackSize'], s[':itemDamage']);
			s[':stackSize'] = 0;
			return 1;
		},
		'getCurrentItem()Lnet/minecraft/src/ItemStack;': function (vm) { return heldStack(vm); },
		'hasItem(I)Z': function (vm, self, a) { return op(vm, 'hasitem', g(vm).itemToGame(a[0])) ? 1 : 0; },
		'consumeInventoryItem(I)Z': function (vm, self, a) { return op(vm, 'takeitem', g(vm).itemToGame(a[0]), 1) ? 1 : 0; },
	} });
	def('EntityItem', { super: SRC + 'Entity', methods: {
		'<init>(Lnet/minecraft/src/World;DDDLnet/minecraft/src/ItemStack;)V': function (vm, self, a) { self[':worldObj'] = a[0]; self[':posX'] = a[1]; self[':posY'] = a[2]; self[':posZ'] = a[3]; self.$stack = a[4]; },
		'getEntityItem()Lnet/minecraft/src/ItemStack;': function (vm, self) { return self.$stack; },
	} });
}

JVM.collectContent = function (vm, modId) {
	modId = modId || '';
	var r = reg(vm), out = { blocks: {}, items: {}, recipes: [], lang: {}, textures: {}, scripted: { blocks: {}, items: {} } };
	var bc = vm.loadClass(SRC + 'Block'), ic = vm.loadClass(SRC + 'Item');
	vm.initClass(bc); vm.initClass(ic);
	var icons = vm.newObject(vm.loadClass('mcre/IconRegister'));
	var safe = function (fn, dflt) { var res = JVM.run(vm, fn); return res.ok ? res.value : dflt; };
	var langOf = function (o) {
		var k = safe(function () { return vm.callVirtual(o, 'getUnlocalizedName', '()Ljava/lang/String;', []); }, null);
		return k ? (r.lang[k + '.name'] || null) : null;
	};
	var overrides = function (o, keys) { return keys.some(function (k) { var m = o.cls.findMethod(k); return m && !m.cls.native; }); };
	var ref = function (id, data) {
		var o = r.blocks[id] ? r.blocks[id] : r.items[id];
		if (o) return (o.$mod === modId ? '' : o.$mod + ':') + (r.blocks[id] ? 'b' : 'i') + id;
		return 'minecraft:' + id + (data ? ':' + data : '');
	};
	var tex = function (icon) {
		if (!icon || !icon.$name) return null;
		var n = icon.$name, p = n.indexOf(':');
		return p >= 0 ? { mod: n.substring(0, p), name: n.substring(p + 1) } : { mod: null, name: n };
	};
	var BLOCK_SCRIPTED = ['onBlockActivated(Lnet/minecraft/src/World;IIILnet/minecraft/src/EntityPlayer;IFFF)Z',
		'updateTick(Lnet/minecraft/src/World;IIILjava/util/Random;)V', 'onEntityWalking(Lnet/minecraft/src/World;IIILnet/minecraft/src/Entity;)V',
		'onBlockAdded(Lnet/minecraft/src/World;III)V', 'breakBlock(Lnet/minecraft/src/World;IIIII)V',
		'onBlockPlacedBy(Lnet/minecraft/src/World;IIILnet/minecraft/src/EntityLiving;Lnet/minecraft/src/ItemStack;)V',
		'onBlockDestroyedByPlayer(Lnet/minecraft/src/World;IIII)V', 'onBlockClicked(Lnet/minecraft/src/World;IIILnet/minecraft/src/EntityPlayer;)V'];
	var ITEM_SCRIPTED = ['onItemRightClick(Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/World;Lnet/minecraft/src/EntityPlayer;)Lnet/minecraft/src/ItemStack;',
		'onItemUse(Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/EntityPlayer;Lnet/minecraft/src/World;IIIIFFF)Z'];
	var SOUND_OF = { stone: 'stone', wood: 'wood', gravel: 'gravel', grass: 'grass', metal: 'metal', glass: 'glass', cloth: 'cloth', sand: 'sand' };
	var TOOL_OF = { rock: 'pickaxe', iron: 'pickaxe', anvil: 'pickaxe', wood: 'axe', pumpkin: 'axe', ground: 'shovel', grass: 'shovel', sand: 'shovel', clay: 'shovel', snow: 'shovel', craftedSnow: 'shovel' };

	Object.keys(r.blocks).forEach(function (idS) {
		var b = r.blocks[idS], id = +idS;
		if (b.$mod !== modId) return;
		safe(function () { vm.callVirtual(b, 'registerIcons', '(Lnet/minecraft/src/IconRegister;)V', [icons]); });
		var faces = {}, FACE = ['down', 'up', 'north', 'south', 'west', 'east'];
		for (var s = 0; s < 6; s++) {
			var t = tex(safe(function () { return vm.callVirtual(b, 'getIcon', '(II)Lnet/minecraft/src/Icon;', [s, 0]); }, null));
			if (t) { faces[FACE[s]] = t.name; out.textures['blocks/' + t.name] = t; }
		}
		var uniq = Object.keys(faces).map(function (k) { return faces[k]; }).filter(function (v, i, a) { return a.indexOf(v) === i; });
		var json = { name: langOf(b) || ('Block ' + id), texture: uniq.length === 1 ? uniq[0] : faces };
		json.hardness = b[':blockHardness'];
		var mat = b[':blockMaterial'] && b[':blockMaterial'].$name;
		json.tool = TOOL_OF[mat] || 'none';
		var snd = b[':stepSound'] && b[':stepSound'].$name;
		if (SOUND_OF[snd]) json.sound = SOUND_OF[snd];
		if (b.$light) json.light = b.$light;
		var opaque = safe(function () { return vm.callVirtual(b, 'isOpaqueCube', '()Z', []); }, 1);
		if (!opaque) json.transparent = true;
		var rnd = vm.newObject(vm.loadClass('java/util/Random')); vm.callVirtual(rnd, '<init>', '(J)V', [0n]);
		var drop = safe(function () { return vm.callVirtual(b, 'idDropped', '(ILjava/util/Random;I)I', [0, rnd, 0]); }, id);
		var cnt = safe(function () { return vm.callVirtual(b, 'quantityDropped', '(Ljava/util/Random;)I', [rnd]); }, 1);
		if (drop <= 0) json.drops = 'none';
		else if (drop !== id) json.drops = ref(drop, safe(function () { return vm.callVirtual(b, 'damageDropped', '(I)I', [0]); }, 0));
		if (cnt !== 1 && drop > 0) json.drop_count = cnt;
		var box = ['minX', 'minY', 'minZ', 'maxX', 'maxY', 'maxZ'].map(function (k) { return Math.round(b[':' + k] * 16); });
		if (box.join() !== '0,0,0,16,16,16') json.shape = box;
		if (b[':slipperiness'] !== 0.6) json.friction = b[':slipperiness'];
		if (mat === 'wood' || mat === 'cloth' || mat === 'leaves') json.flammable = true;
		if (overrides(b, BLOCK_SCRIPTED)) out.scripted.blocks[id] = true;
		if (overrides(b, BLOCK_SCRIPTED.slice(0, 3)) || b[':needsRandomTick'] || overrides(b, [BLOCK_SCRIPTED[7]])) json.scripted = true;
		out.blocks['b' + id] = json;
	});
	Object.keys(r.items).forEach(function (idS) {
		var it = r.items[idS], id = +idS;
		if (it.$mod !== modId) return;
		safe(function () { vm.callVirtual(it, 'registerIcons', '(Lnet/minecraft/src/IconRegister;)V', [icons]); });
		var t = tex(safe(function () { return vm.callVirtual(it, 'getIconFromDamage', '(I)Lnet/minecraft/src/Icon;', [0]); }, null));
		if (t) out.textures['items/' + t.name] = t;
		var json = { name: langOf(it) || ('Item ' + id), texture: t ? t.name : 'stick', stack: it[':maxStackSize'] };
		if (it.$food) json.food = { hunger: it.$food[0], saturation: it.$food[1] };
		if (it.$tool && it.$toolMat) json.tool = { type: it.$tool, level: it.$toolMat.$m[0], uses: it.$toolMat.$m[1], speed: it.$toolMat.$m[2], damage: it.$toolMat.$m[3] };
		if (it.$armor) json.armor = { slot: ['head', 'chest', 'legs', 'feet'][it.$armor.slot], protection: it[':damageReduceAmount'], durability: it[':maxDamage'] };
		if (overrides(it, ITEM_SCRIPTED)) { json.scripted = true; out.scripted.items[id] = true; }
		out.items['i' + id] = json;
	});
	var stackRef = function (o) {
		if (!o) return null;
		if (vm.isInstance(o, vm.loadClass(SRC + 'ItemStack'))) return ref(o[':itemID'], o[':itemDamage'] === -1 || o[':itemDamage'] === 32767 ? 0 : o[':itemDamage']);
		if (vm.isInstance(o, vm.loadClass(SRC + 'Block'))) return ref(o[':blockID'], 0);
		if (vm.isInstance(o, vm.loadClass(SRC + 'Item'))) return ref(o[':itemID'], 0);
		return null;
	};
	r.recipes.forEach(function (rc) {
		if ((rc.mod || '') !== modId) return;
		var res = stackRef(rc.out), count = rc.out ? rc.out[':stackSize'] : 1;
		if (!res) return;
		if (rc.shaped) {
			var rows = [], key = {}, args = rc.args, i = 0;
			if (args[0] instanceof JVM.JArray) { rows = Array.prototype.slice.call(args[0].a); i = 1; }
			else while (typeof args[i] === 'string') rows.push(args[i++]);
			for (; i + 1 < args.length; i += 2) {
				var ch = args[i] && args[i].$box !== undefined ? String.fromCharCode(args[i].$box) : String(args[i]);
				var it2 = stackRef(args[i + 1]);
				if (it2) key[ch] = it2;
			}
			out.recipes.push({ type: 'shaped', pattern: rows, key: key, result: res, count: count });
		} else {
			var ing = rc.args.map(stackRef).filter(Boolean);
			out.recipes.push({ type: 'shapeless', ingredients: ing, result: res, count: count });
		}
	});
	r.smelting.forEach(function (s) {
		if ((s.mod || '') !== modId) return;
		var res = stackRef(s.out);
		if (res) out.recipes.push({ type: 'smelting', input: ref(s.input, 0), result: res, count: s.out[':stackSize'] });
	});
	Object.keys(r.lang).forEach(function (k) { out.lang[k] = r.lang[k]; });
	return out;
};

JVM.installMc152 = installMc152;
JVM.mc152 = { worldObj: worldObj, playerObj: playerObj, heldStack: heldStack, reg: reg, newStack: function (vm, id, n, d) { var s = vm.newObject(vm.loadClass(SRC + 'ItemStack')); s[':itemID'] = id; s[':stackSize'] = n; s[':itemDamage'] = d; return s; } };
})();

(function () {
'use strict';

JVM.loadJar = function (vm, bytes, source) {
	return JVM.readZip(bytes).then(function (entries) {
		var info = { source: source, classes: [], resources: [], kind: 'plain', modClasses: [], fabric: null, mcmod: null };
		entries.forEach(function (e) {
			if (e.name.endsWith('.class')) {
				var cname = e.name.substring(0, e.name.length - 6);
				if (cname === 'module-info' || cname.endsWith('/module-info') || cname.endsWith('package-info')) return;
				vm.addClassFile(cname, e.bytes, source);
				info.classes.push(cname);
			} else {
				vm.resources[e.name] = e.bytes;
				info.resources.push(e.name);
			}
		});
		var text = function (n) { var b = vm.resources[n]; return b ? new TextDecoder().decode(b) : null; };
		try { var fj = text('fabric.mod.json'); if (fj) info.fabric = JSON.parse(fj); } catch (e) { vm.log('warn', source + ': fabric.mod.json could not be read'); }
		try { var mi = text('mcmod.info'); if (mi) info.mcmod = JSON.parse(mi); } catch (e2) { info.mcmod = []; }
		info.modClasses = info.classes.filter(function (c) { return /(^|\/)mod_[^\/$]+$/.test(c); });
		if (info.fabric) {
			var dep = info.fabric.depends && info.fabric.depends.minecraft;
			info.kind = (typeof dep === 'string' && /b1\.7|beta.?7|1\.0\.0-beta/.test(dep)) || (info.fabric.depends && (info.fabric.depends.stationapi || info.fabric.depends['station-api'])) ? 'babric' : 'fabric';
		} else if (info.mcmod) info.kind = 'forge';
		else if (info.modClasses.length) info.kind = 'modloader';
		return info;
	});
};

JVM.run = function (vm, fn) {
	vm.steps = 0;
	var frames = vm.frames || (vm.frames = []);
	var depth = frames.length;
	try {
		return { ok: true, value: fn() };
	} catch (e) {
		var trace = frames.slice(depth).map(function (f) { return f.m.cls.name + '.' + f.m.name; });
		frames.length = depth;
		if (e instanceof JVM.JavaThrow) trace = (e.obj && e.obj.$jsStack) || trace;
		trace = trace.map(function (t) { return t.replace(/[/]/g, '.'); }).reverse();
		if (e instanceof JVM.JavaThrow) vm.log('error', 'uncaught ' + JVM.describeThrowable(e.obj) + traceText(e, trace));
		else if (e && e.vmStop) vm.log('error', 'a mod ran too long and was stopped' + traceText(e, trace));
		else vm.log('error', 'internal error: ' + (e && e.stack || e));
		return { ok: false };
	}
};
function traceText(e, frames) { return frames.length ? '\n    at ' + frames.slice(0, 12).join('\n    at ') : ''; }

JVM.VM.prototype.currentTrace = function () {
	return (this.frames || []).map(function (f) { return f.m.cls.name + '.' + f.m.name; });
};
})();

if (typeof module !== 'undefined' && module.exports) module.exports = JVM;
