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
	return this.isSubclassStrict(other) || other.absent || this.absent;
};
JClass.prototype.isSubclassStrict = function (other) {
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
		for (var i = 0; i < c.interfaces.length; i++) if (c.interfaces[i].isSubclassStrict(other)) return true;
	}
	return false;
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
	JVM.installReflect(this);
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
		return this.defineFromBytes(name, src.bytes, src.source, src.parsed);
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
	this.classes[name] = c;
	var ps = this.mcpParents ? this.mcpParents(name) : null;
	if (ps && ps.length) {
		c.superClass = this.loadClass(ps[0]);
		c.interfaces = ps.slice(1).map(this.loadClass, this);
		this.warnOnce('class:' + name, 'no stand-in for ' + name.replace(/[/]/g, '.') + ' - it works as its ' + c.superClass.name.replace(/[/]/g, '.') + ' part');
	} else {
		if (name !== 'java/lang/Object') c.superClass = this.loadClass('java/lang/Object');
		this.warnOnce('class:' + name, 'not available here: ' + name.replace(/[/]/g, '.') + ' (left unplugged)');
	}
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

VM.prototype.defineFromBytes = function (expectName, bytes, source, parsed) {
	var cf = parsed || JVM.parseClassFile(bytes);
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
		c.fields[f.name] = { name: f.name, desc: f.desc, access: f.access, static: st, annotations: f.annotations || null };
		if (st) c.statics[f.name] = f.constant !== undefined ? f.constant : defaultOf(f.desc);
	}
	for (var j = 0; j < cf.methods.length; j++) {
		var mi = cf.methods[j];
		var m = new JMethod(c, mi.name, mi.desc, mi.access);
		m.code = mi.code;
		m.annotations = mi.annotations || null;
		if (mi.annotationDefault) m.annotationDefault = mi.annotationDefault;
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
			return this.unpluggedValue(m.sig.ret);
		}
		return this.unpluggedValue(m.sig.ret);
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
	return this.unpluggedValue(parseDesc(desc).ret);
};
var EMPTY_OF = {
	'Ljava/util/List;': 'java/util/ArrayList', 'Ljava/util/ArrayList;': 'java/util/ArrayList', 'Ljava/util/Collection;': 'java/util/ArrayList',
	'Ljava/lang/Iterable;': 'java/util/ArrayList', 'Ljava/util/LinkedList;': 'java/util/LinkedList',
	'Ljava/util/Set;': 'java/util/HashSet', 'Ljava/util/HashSet;': 'java/util/HashSet',
	'Ljava/util/Map;': 'java/util/HashMap', 'Ljava/util/HashMap;': 'java/util/HashMap',
};
VM.prototype.unpluggedValue = function (t) {
	if (t === 'Ljava/lang/String;') return '';
	if (t[0] === '[') return this.newArray(t.substring(1), 0);
	var cn = EMPTY_OF[t];
	if (cn) { var o = this.newObject(this.loadClass(cn)); this.callVirtual(o, '<init>', '()V', []); return o; }
	return defaultOf(t);
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
			if (aname === 'RuntimeVisibleAnnotations') { fld.annotations = readAnnotations(r, cp); return true; }
			return false;
		});
		cf.fields.push(fld);
	}

	cf.methods = [];
	for (var mc = r.u2(); mc > 0; mc--) {
		var mt = { access: r.u2(), name: utf(r.u2()), desc: utf(r.u2()), code: null };
		readAttributes(r, cp, function (aname, len) {
			if (aname === 'RuntimeVisibleAnnotations') { mt.annotations = readAnnotations(r, cp); return true; }
			if (aname === 'AnnotationDefault') { mt.annotationDefault = readElement(r, cp); return true; }
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
		if (aname === 'RuntimeVisibleAnnotations') { cf.annotations = readAnnotations(r, cp); return true; }
		return false;
	});
	return cf;
}

function readAnnotations(r, cp) {
	var out = [];
	for (var n = r.u2(); n > 0; n--) out.push(readAnnotation(r, cp));
	return out;
}
function readAnnotation(r, cp) {
	var a = { type: cp[r.u2()].v, values: {} };
	for (var k = r.u2(); k > 0; k--) { var name = cp[r.u2()].v; a.values[name] = readElement(r, cp); }
	return a;
}
function readElement(r, cp) {
	var t = String.fromCharCode(r.u1());
	switch (t) {
	case 'e': return { t: t, type: cp[r.u2()].v, name: cp[r.u2()].v };
	case 'c': return { t: t, desc: cp[r.u2()].v };
	case '@': return { t: t, ann: readAnnotation(r, cp) };
	case '[': { var items = []; for (var n = r.u2(); n > 0; n--) items.push(readElement(r, cp)); return { t: t, items: items }; }
	default: { var v = cp[r.u2()].v; if (t === 'F') v = Math.fround(v); return { t: t, v: v }; }
	}
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
	var mapAnn = function (list) {
		(list || []).forEach(function (a) {
			a.type = mapDesc(a.type);
			Object.keys(a.values).forEach(function (k) { mapEl(a.values[k]); });
		});
	};
	var mapEl = function (e) {
		if (e.t === 'e') e.type = mapDesc(e.type);
		else if (e.t === 'c') e.desc = mapDesc(e.desc);
		else if (e.t === '@') mapAnn([e.ann]);
		else if (e.t === '[') e.items.forEach(mapEl);
	};
	mapAnn(cf.annotations);
	cf.origFields = cf.fields.map(function (f) { return f.name; });
	var vanilla = vm.nameMap && vm.nameMap.cls[selfOrig] !== undefined;
	cf.fields.forEach(function (f) {
		if (vanilla) { var mf = vm.nameMap.fld[selfOrig + '.' + f.name]; if (mf) f.name = mf; }
		f.desc = mapDesc(f.desc); mapAnn(f.annotations);
	});
	cf.methods.forEach(function (m) { mapAnn(m.annotations); if (m.annotationDefault) mapEl(m.annotationDefault); });
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
				v = target === MISSING ? vm.unpluggedValue(sig.ret) : vm.invoke(target, recv, cargs);
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
	if (e.name === '<init>') {
		for (var k = c; k; k = k.superClass) {
			var spec = k.native && vm.natives[k.name];
			if (spec && spec.anyInit) {
				var am = new JVM.JMethod(k, '<init>', e.desc, JVM.ACC_PUBLIC);
				am.fn = (function (f, d) { return function (vm2, self, args) { return f(vm2, self, args, d); }; })(spec.anyInit, e.desc);
				return am;
			}
		}
		return NOOP_INIT;
	}
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

var JObject = JVM.JObject;
var PRIM = { I: 1, J: 1, F: 1, D: 1, Z: 1, C: 1, S: 1, B: 1 };

function descOf(c) {
	if (c.primitive) return c.name;
	if (c.name[0] === '[') return c.name;
	return 'L' + c.name + ';';
}
function typeClass(vm, desc) {
	if (!desc || desc === '?') return vm.loadClass('java/lang/Object');
	if (desc.length === 1) return vm.loadClass(desc);
	return vm.classFor(desc);
}
function boxAs(vm, v, t) {
	if (t === 'V') return null;
	if (PRIM[t]) return JVM.box(vm, t === 'J' ? BigInt(v || 0) : v, t);
	return v === undefined ? null : v;
}
function unboxAs(v, t) {
	var u = JVM.unbox(v);
	switch (t) {
	case 'J': return typeof u === 'bigint' ? u : BigInt(Math.trunc(+u || 0));
	case 'Z': return u ? 1 : 0;
	case 'F': return Math.fround(typeof u === 'bigint' ? Number(u) : +u || 0);
	case 'D': return typeof u === 'bigint' ? Number(u) : +u || 0;
	case 'I': case 'S': case 'B': case 'C': return typeof u === 'bigint' ? Number(BigInt.asIntN(32, u)) : (u | 0);
	default: return v;
	}
}

function elementValue(vm, el, desc) {
	if (el === undefined || el === null) {
		if (desc === 'Ljava/lang/String;') return '';
		if (desc[0] === '[') return vm.newArray(desc.substring(1), 0);
		return JVM.defaultOf(desc);
	}
	if (desc[0] === '[' && el.t !== '[') el = { t: '[', items: [el] };
	switch (el.t) {
	case '[': {
		var comp = desc[0] === '[' ? desc.substring(1) : 'Ljava/lang/Object;';
		var arr = vm.newArray(comp, el.items.length);
		for (var i = 0; i < el.items.length; i++) arr.a[i] = elementValue(vm, el.items[i], comp);
		return arr;
	}
	case 'e': {
		var ec = vm.classFor(el.type);
		vm.initClass(ec);
		var v = ec.statics[el.name];
		if (v === undefined) {
			var vals = vm.callVirtual(vm.classObject(ec), 'getEnumConstants', '()[Ljava/lang/Object;', []);
			v = vals ? Array.prototype.slice.call(vals.a).filter(function (x) { return x && x.$name === el.name; })[0] || null : null;
		}
		return v;
	}
	case 'c': return vm.classObject(typeClass(vm, el.desc));
	case '@': return annotationObject(vm, el.ann);
	case 's': return String(el.v);
	case 'Z': return el.v ? 1 : 0;
	case 'J': return BigInt(el.v);
	default:
		if (PRIM[desc]) return desc === 'J' ? BigInt(el.v) : el.v;
		return boxAs(vm, el.v, el.t);
	}
}

function annotationClass(vm, type) {
	var cache = vm.annClasses || (vm.annClasses = Object.create(null));
	if (cache[type]) return cache[type];
	var iface = typeClass(vm, type);
	var c = new JVM.JClass(vm, 'mcre/annotation/' + JVM.typeToClassName(type));
	c.native = true;
	c.initState = 2;
	c.access = JVM.ACC_PUBLIC | JVM.ACC_FINAL;
	c.superClass = vm.loadClass('java/lang/Object');
	c.interfaces = [vm.loadClass('java/lang/annotation/Annotation'), iface];
	var base = JVM.JClass.prototype.findMethod;
	var mk = function (key, fn) {
		var p = key.indexOf('(');
		var m = new JVM.JMethod(c, key.substring(0, p), key.substring(p), JVM.ACC_PUBLIC);
		m.fn = fn;
		return m;
	};
	c.findMethod = function (key) {
		var hit = this.vcache[key];
		if (hit !== undefined) return hit;
		var m = null;
		if (key === 'annotationType()Ljava/lang/Class;') m = mk(key, function (vm) { return vm.classObject(iface); });
		else if (key === 'toString()Ljava/lang/String;') m = mk(key, function (vm, self) {
			var vs = self.$ann.values;
			return '@' + iface.name.replace(/[/]/g, '.') + '(' + Object.keys(vs).map(function (k) { return k + '=' + (vs[k].v !== undefined ? vs[k].v : vs[k].name || '...'); }).join(', ') + ')';
		});
		else if (key === 'hashCode()I') m = mk(key, function (vm, self) { return vm.identityHash(self); });
		else if (key === 'equals(Ljava/lang/Object;)Z') m = mk(key, function (vm, self, a) { return a[0] === self || (a[0] && a[0].$ann === self.$ann) ? 1 : 0; });
		else {
			var g = /^(\w+)\(\)(.+)$/.exec(key), found = g && base.call(this, key);
			if (g && (!found || (found.access & JVM.ACC_ABSTRACT))) {
				var name = g[1], ret = g[2], dflt = found ? found.annotationDefault : undefined;
				m = mk(key, function (vm, self) { var v = self.$ann.values[name]; return elementValue(vm, v !== undefined ? v : dflt, ret); });
			}
		}
		if (!m) m = base.call(this, key);
		return (this.vcache[key] = m);
	};
	return (cache[type] = c);
}
function annotationObject(vm, ann) {
	var o = new JObject(annotationClass(vm, ann.type));
	o.$ann = ann;
	return o;
}
function annotationArray(vm, list) {
	return JVM.javaArray(vm, 'Ljava/lang/annotation/Annotation;', (list || []).map(function (a) { return annotationObject(vm, a); }));
}
function findAnnotation(vm, list, annCls) {
	if (!list || !annCls) return null;
	for (var i = 0; i < list.length; i++) if (typeClass(vm, list[i].type) === annCls) return list[i];
	return null;
}
function classAnnotations(c) { return c.cf && c.cf.annotations || null; }
JVM.annotation = function (vm, list, typeName) {
	if (!list) return null;
	for (var i = 0; i < list.length; i++) {
		var t = list[i].type;
		if (t === 'L' + typeName + ';' || typeClass(vm, t).name === typeName) return list[i];
	}
	return null;
};
JVM.classAnnotations = classAnnotations;
JVM.annotationObject = annotationObject;
JVM.elementValue = elementValue;

function fieldObj(vm, owner, f) {
	var cache = owner.fieldObjs || (owner.fieldObjs = Object.create(null));
	if (cache[f.name]) return cache[f.name];
	var o = new JObject(vm.loadClass('java/lang/reflect/Field'));
	o.$owner = owner; o.$f = f;
	return (cache[f.name] = o);
}
function methodObj(vm, m) {
	if (m.reflObj) return m.reflObj;
	var o = new JObject(vm.loadClass(m.name === '<init>' ? 'java/lang/reflect/Constructor' : 'java/lang/reflect/Method'));
	o.$m = m;
	return (m.reflObj = o);
}
function declaredFields(c) { return Object.keys(c.fields).map(function (k) { return c.fields[k]; }); }
function declaredMethods(c, ctors) {
	return Object.keys(c.methods).map(function (k) { return c.methods[k]; }).filter(function (m) {
		return ctors ? m.name === '<init>' : m.name[0] !== '<';
	});
}
function paramsMatch(vm, m, classes) {
	var want = classes ? Array.prototype.slice.call(classes.a) : [];
	if (want.length !== m.sig.args.length) return false;
	for (var i = 0; i < want.length; i++) if (!want[i] || descOf(want[i].$cls) !== m.sig.args[i]) {
		if (!want[i] || typeClass(vm, m.sig.args[i]) !== want[i].$cls) return false;
	}
	return true;
}
function allPublicFields(c) {
	var out = [], seen = Object.create(null);
	(function walk(k) {
		if (!k) return;
		declaredFields(k).forEach(function (f) { if ((f.access & JVM.ACC_PUBLIC) && !seen[f.name]) { seen[f.name] = 1; out.push({ owner: k, f: f }); } });
		k.interfaces.forEach(walk);
		walk(k.superClass);
	})(c);
	return out;
}
function allPublicMethods(c) {
	var out = [], seen = Object.create(null);
	(function walk(k) {
		if (!k) return;
		declaredMethods(k).forEach(function (m) { if ((m.access & JVM.ACC_PUBLIC) && !seen[m.key]) { seen[m.key] = 1; out.push(m); } });
		walk(k.superClass);
		k.interfaces.forEach(walk);
	})(c);
	return out;
}
function staticOwner(vm, owner) { if (owner.initState !== 2) vm.initClass(owner); return owner; }
function fieldGet(vm, self, obj) {
	var f = self.$f;
	if (f.static) return staticOwner(vm, self.$owner).statics[f.name];
	if (obj === null || obj === undefined) vm.throwNew('java/lang/NullPointerException', f.name);
	var v = obj[':' + f.name];
	return v === undefined ? JVM.defaultOf(f.desc === '?' ? 'L;' : f.desc) : v;
}
function fieldSet(vm, self, obj, v) {
	var f = self.$f;
	if (f.static) staticOwner(vm, self.$owner).statics[f.name] = v;
	else {
		if (obj === null || obj === undefined) vm.throwNew('java/lang/NullPointerException', f.name);
		obj[':' + f.name] = v;
	}
}
function reflectInvoke(vm, m, recv, argArr) {
	var args = argArr ? Array.prototype.slice.call(argArr.a) : [];
	var cargs = m.sig.args.map(function (t, i) { return unboxAs(args[i], t); });
	var target = m;
	if (m.isStatic) staticOwner(vm, m.cls);
	else {
		if (recv === null || recv === undefined) vm.throwNew('java/lang/NullPointerException', m.name);
		if (m.name !== '<init>') target = vm.classOf(recv).findMethod(m.key) || m;
	}
	try {
		return vm.invoke(target, recv, cargs);
	} catch (e) {
		if (e instanceof JVM.JavaThrow) {
			var w = vm.makeThrowable('java/lang/reflect/InvocationTargetException', null);
			w.$cause = e.obj; w[':target'] = e.obj;
			throw new JVM.JavaThrow(w);
		}
		throw e;
	}
}

function installReflect(vm) {
	var def = function (n, s) { vm.defineNative(n, s); };
	var add = function (name, methods, statics) {
		var spec = vm.natives[name];
		spec.methods = Object.assign({}, spec.methods || {}, methods || {});
		spec.staticMethods = Object.assign({}, spec.staticMethods || {}, statics || {});
	};
	def('java/lang/annotation/Annotation', { access: JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC });
	def('java/lang/reflect/AccessibleObject', { methods: {
		'setAccessible(Z)V': function () {},
		'isAccessible()Z': function () { return 1; },
		'trySetAccessible()Z': function () { return 1; },
	} });
	def('java/lang/reflect/InvocationTargetException', { super: 'java/lang/ReflectiveOperationException', methods: {
		'getTargetException()Ljava/lang/Throwable;': function (vm, self) { return self.$cause || null; },
		'getCause()Ljava/lang/Throwable;': function (vm, self) { return self.$cause || null; },
	} });
	var annMethods = function (listOf) {
		return {
			'getAnnotation(Ljava/lang/Class;)Ljava/lang/annotation/Annotation;': function (vm, self, a) { var r = findAnnotation(vm, listOf(self), a[0] && a[0].$cls); return r ? annotationObject(vm, r) : null; },
			'isAnnotationPresent(Ljava/lang/Class;)Z': function (vm, self, a) { return findAnnotation(vm, listOf(self), a[0] && a[0].$cls) ? 1 : 0; },
			'getAnnotations()[Ljava/lang/annotation/Annotation;': function (vm, self) { return annotationArray(vm, listOf(self)); },
			'getDeclaredAnnotations()[Ljava/lang/annotation/Annotation;': function (vm, self) { return annotationArray(vm, listOf(self)); },
		};
	};
	def('java/lang/reflect/Field', { super: 'java/lang/reflect/AccessibleObject', methods: Object.assign(annMethods(function (s) { return s.$f.annotations; }), {
		'getName()Ljava/lang/String;': function (vm, self) { return self.$f.name; },
		'getType()Ljava/lang/Class;': function (vm, self) { return vm.classObject(typeClass(vm, self.$f.desc)); },
		'getGenericType()Ljava/lang/reflect/Type;': function (vm, self) { return vm.classObject(typeClass(vm, self.$f.desc)); },
		'getModifiers()I': function (vm, self) { return self.$f.access | (self.$f.static ? JVM.ACC_STATIC : 0); },
		'getDeclaringClass()Ljava/lang/Class;': function (vm, self) { return vm.classObject(self.$owner); },
		'isEnumConstant()Z': function (vm, self) { return self.$f.access & 0x4000 ? 1 : 0; },
		'isSynthetic()Z': function (vm, self) { return self.$f.access & 0x1000 ? 1 : 0; },
		'toString()Ljava/lang/String;': function (vm, self) { return self.$owner.name.replace(/[/]/g, '.') + '.' + self.$f.name; },
		'hashCode()I': function (vm, self) { return JVM.stringHash(self.$owner.name) ^ JVM.stringHash(self.$f.name); },
		'equals(Ljava/lang/Object;)Z': function (vm, self, a) { return a[0] === self ? 1 : 0; },
		'get(Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { return boxAs(vm, fieldGet(vm, self, a[0]), self.$f.desc); },
		'set(Ljava/lang/Object;Ljava/lang/Object;)V': function (vm, self, a) { fieldSet(vm, self, a[0], unboxAs(a[1], self.$f.desc)); },
	}, (function () {
		var m = {};
		[['Int', 'I'], ['Boolean', 'Z'], ['Float', 'F'], ['Double', 'D'], ['Long', 'J'], ['Short', 'S'], ['Byte', 'B'], ['Char', 'C']].forEach(function (p) {
			m['get' + p[0] + '(Ljava/lang/Object;)' + p[1]] = function (vm, self, a) { return unboxAs(fieldGet(vm, self, a[0]), p[1]); };
			m['set' + p[0] + '(Ljava/lang/Object;' + p[1] + ')V'] = function (vm, self, a) { fieldSet(vm, self, a[0], unboxAs(a[1], self.$f.desc === '?' ? p[1] : self.$f.desc)); };
		});
		return m;
	})()) });
	var execMethods = Object.assign(annMethods(function (s) { return s.$m.annotations; }), {
		'getName()Ljava/lang/String;': function (vm, self) { return self.$m.name === '<init>' ? self.$m.cls.name.replace(/[/]/g, '.') : self.$m.name; },
		'getModifiers()I': function (vm, self) { return self.$m.access; },
		'getDeclaringClass()Ljava/lang/Class;': function (vm, self) { return vm.classObject(self.$m.cls); },
		'getParameterTypes()[Ljava/lang/Class;': function (vm, self) { return JVM.javaArray(vm, 'Ljava/lang/Class;', self.$m.sig.args.map(function (t) { return vm.classObject(typeClass(vm, t)); })); },
		'getGenericParameterTypes()[Ljava/lang/reflect/Type;': function (vm, self) { return JVM.javaArray(vm, 'Ljava/lang/reflect/Type;', self.$m.sig.args.map(function (t) { return vm.classObject(typeClass(vm, t)); })); },
		'getParameterCount()I': function (vm, self) { return self.$m.sig.args.length; },
		'getExceptionTypes()[Ljava/lang/Class;': function (vm) { return vm.newArray('Ljava/lang/Class;', 0); },
		'getParameterAnnotations()[[Ljava/lang/annotation/Annotation;': function (vm, self) {
			var n = self.$m.sig.args.length, arr = vm.newArray('[Ljava/lang/annotation/Annotation;', n);
			for (var i = 0; i < n; i++) arr.a[i] = vm.newArray('Ljava/lang/annotation/Annotation;', 0);
			return arr;
		},
		'isVarArgs()Z': function (vm, self) { return self.$m.access & 0x80 ? 1 : 0; },
		'isSynthetic()Z': function (vm, self) { return self.$m.access & 0x1000 ? 1 : 0; },
		'toString()Ljava/lang/String;': function (vm, self) { return self.$m.cls.name.replace(/[/]/g, '.') + '.' + self.$m.name + self.$m.desc; },
		'hashCode()I': function (vm, self) { return JVM.stringHash(self.$m.cls.name) ^ JVM.stringHash(self.$m.key); },
		'equals(Ljava/lang/Object;)Z': function (vm, self, a) { return a[0] === self ? 1 : 0; },
	});
	def('java/lang/reflect/Method', { super: 'java/lang/reflect/AccessibleObject', methods: Object.assign({}, execMethods, {
		'getReturnType()Ljava/lang/Class;': function (vm, self) { return vm.classObject(typeClass(vm, self.$m.sig.ret)); },
		'getGenericReturnType()Ljava/lang/reflect/Type;': function (vm, self) { return vm.classObject(typeClass(vm, self.$m.sig.ret)); },
		'invoke(Ljava/lang/Object;[Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { return boxAs(vm, reflectInvoke(vm, self.$m, a[0], a[1]), self.$m.sig.ret); },
		'isDefault()Z': function () { return 0; },
	}) });
	def('java/lang/reflect/Constructor', { super: 'java/lang/reflect/AccessibleObject', methods: Object.assign({}, execMethods, {
		'newInstance([Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) {
			var o = vm.newObject(self.$m.cls);
			reflectInvoke(vm, self.$m, o, a[0]);
			return o;
		},
	}) });
	def('java/lang/reflect/Modifier', { staticMethods: (function () {
		var m = {};
		[['isPublic', 0x1], ['isPrivate', 0x2], ['isProtected', 0x4], ['isStatic', 0x8], ['isFinal', 0x10], ['isSynchronized', 0x20],
		 ['isVolatile', 0x40], ['isTransient', 0x80], ['isNative', 0x100], ['isInterface', 0x200], ['isAbstract', 0x400]].forEach(function (p) {
			m[p[0] + '(I)Z'] = function (vm, n, a) { return a[0] & p[1] ? 1 : 0; };
		});
		m['toString(I)Ljava/lang/String;'] = function (vm, n, a) { return [[1, 'public'], [2, 'private'], [4, 'protected'], [8, 'static'], [16, 'final']].filter(function (p) { return a[0] & p[0]; }).map(function (p) { return p[1]; }).join(' '); };
		return m;
	})(), statics: { PUBLIC: 1, PRIVATE: 2, PROTECTED: 4, STATIC: 8, FINAL: 16, SYNCHRONIZED: 32, VOLATILE: 64, TRANSIENT: 128, NATIVE: 256, INTERFACE: 512, ABSTRACT: 1024 } });

	var PNAME = { I: 'int', J: 'long', F: 'float', D: 'double', Z: 'boolean', C: 'char', S: 'short', B: 'byte', V: 'void' };
	[['java/lang/Integer', 'I'], ['java/lang/Long', 'J'], ['java/lang/Float', 'F'], ['java/lang/Double', 'D'], ['java/lang/Boolean', 'Z'],
	 ['java/lang/Character', 'C'], ['java/lang/Short', 'S'], ['java/lang/Byte', 'B'], ['java/lang/Void', 'V']].forEach(function (p) {
		var spec = vm.natives[p[0]];
		if (!spec) { def(p[0], {}); spec = vm.natives[p[0]]; }
		spec.statics = Object.assign({}, spec.statics || {}, { TYPE: null });
		var prev = spec.clinit;
		spec.clinit = function (vm, c) { if (prev) prev(vm, c); c.statics.TYPE = vm.classObject(vm.loadClass(p[1])); };
	});
	var jname = function (c) { return c.primitive ? PNAME[c.name] : c.name.replace(/[/]/g, '.'); };
	var noSuch = function (vm, kind, c, name) { vm.throwNew('java/lang/NoSuch' + kind + 'Exception', c.name.replace(/[/]/g, '.') + '.' + name); };
	add('java/lang/Class', Object.assign(annMethods(function (s) { return classAnnotations(s.$cls); }), {
		'getName()Ljava/lang/String;': function (vm, self) { return jname(self.$cls); },
		'getSimpleName()Ljava/lang/String;': function (vm, self) {
			if (self.$cls.primitive) return PNAME[self.$cls.name];
			if (self.$cls.name[0] === '[') return vm.callVirtual(vm.classObject(vm.classFor(self.$cls.component)), 'getSimpleName', '()Ljava/lang/String;', []) + '[]';
			var n = self.$cls.name; n = n.substring(n.lastIndexOf('/') + 1); return n.substring(n.lastIndexOf('$') + 1);
		},
		'toString()Ljava/lang/String;': function (vm, self) { return self.$cls.primitive ? PNAME[self.$cls.name] : (self.$cls.isInterface() ? 'interface ' : 'class ') + jname(self.$cls); },
		'getDeclaredFields()[Ljava/lang/reflect/Field;': function (vm, self) { return JVM.javaArray(vm, 'Ljava/lang/reflect/Field;', declaredFields(self.$cls).map(function (f) { return fieldObj(vm, self.$cls, f); })); },
		'getFields()[Ljava/lang/reflect/Field;': function (vm, self) { return JVM.javaArray(vm, 'Ljava/lang/reflect/Field;', allPublicFields(self.$cls).map(function (p) { return fieldObj(vm, p.owner, p.f); })); },
		'getDeclaredField(Ljava/lang/String;)Ljava/lang/reflect/Field;': function (vm, self, a) {
			var f = self.$cls.fields[a[0]];
			if (!f) noSuch(vm, 'Field', self.$cls, a[0]);
			return fieldObj(vm, self.$cls, f);
		},
		'getField(Ljava/lang/String;)Ljava/lang/reflect/Field;': function (vm, self, a) {
			var r = self.$cls.findField(a[0]);
			if (!r) noSuch(vm, 'Field', self.$cls, a[0]);
			return fieldObj(vm, r.owner, r.f);
		},
		'getDeclaredMethods()[Ljava/lang/reflect/Method;': function (vm, self) { return JVM.javaArray(vm, 'Ljava/lang/reflect/Method;', declaredMethods(self.$cls).map(function (m) { return methodObj(vm, m); })); },
		'getMethods()[Ljava/lang/reflect/Method;': function (vm, self) { return JVM.javaArray(vm, 'Ljava/lang/reflect/Method;', allPublicMethods(self.$cls).map(function (m) { return methodObj(vm, m); })); },
		'getDeclaredMethod(Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;': function (vm, self, a) {
			var m = declaredMethods(self.$cls).filter(function (m) { return m.name === a[0] && paramsMatch(vm, m, a[1]); })[0];
			if (!m) noSuch(vm, 'Method', self.$cls, a[0]);
			return methodObj(vm, m);
		},
		'getMethod(Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;': function (vm, self, a) {
			var m = allPublicMethods(self.$cls).filter(function (m) { return m.name === a[0] && paramsMatch(vm, m, a[1]); })[0];
			if (!m) noSuch(vm, 'Method', self.$cls, a[0]);
			return methodObj(vm, m);
		},
		'getDeclaredConstructors()[Ljava/lang/reflect/Constructor;': function (vm, self) { return JVM.javaArray(vm, 'Ljava/lang/reflect/Constructor;', declaredMethods(self.$cls, true).map(function (m) { return methodObj(vm, m); })); },
		'getConstructors()[Ljava/lang/reflect/Constructor;': function (vm, self) { return JVM.javaArray(vm, 'Ljava/lang/reflect/Constructor;', declaredMethods(self.$cls, true).filter(function (m) { return m.access & JVM.ACC_PUBLIC; }).map(function (m) { return methodObj(vm, m); })); },
		'getDeclaredConstructor([Ljava/lang/Class;)Ljava/lang/reflect/Constructor;': function (vm, self, a) {
			var m = declaredMethods(self.$cls, true).filter(function (m) { return paramsMatch(vm, m, a[0]); })[0];
			if (!m) noSuch(vm, 'Method', self.$cls, '<init>');
			return methodObj(vm, m);
		},
		'getConstructor([Ljava/lang/Class;)Ljava/lang/reflect/Constructor;': function (vm, self, a) {
			var m = declaredMethods(self.$cls, true).filter(function (m) { return paramsMatch(vm, m, a[0]); })[0];
			if (!m) noSuch(vm, 'Method', self.$cls, '<init>');
			return methodObj(vm, m);
		},
		'getDeclaredClasses()[Ljava/lang/Class;': function (vm) { return vm.newArray('Ljava/lang/Class;', 0); },
		'getClasses()[Ljava/lang/Class;': function (vm) { return vm.newArray('Ljava/lang/Class;', 0); },
		'getEnclosingClass()Ljava/lang/Class;': function (vm, self) { var n = self.$cls.name, i = n.lastIndexOf('$'); return i > 0 ? vm.classObject(vm.loadClass(n.substring(0, i))) : null; },
		'getDeclaringClass()Ljava/lang/Class;': function (vm, self) { var n = self.$cls.name, i = n.lastIndexOf('$'); return i > 0 ? vm.classObject(vm.loadClass(n.substring(0, i))) : null; },
		'isAnnotation()Z': function (vm, self) { return self.$cls.access & 0x2000 ? 1 : 0; },
		'isMemberClass()Z': function (vm, self) { return self.$cls.name.indexOf('$') > 0 ? 1 : 0; },
		'isAnonymousClass()Z': function (vm, self) { return /\$\d+$/.test(self.$cls.name) ? 1 : 0; },
	}));
}

JVM.installReflect = installReflect;
JVM.reflect = { fieldObj: fieldObj, methodObj: methodObj, boxAs: boxAs, unboxAs: unboxAs, typeClass: typeClass };
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
	JVM.fileObj = fileObj;
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
	var sup = Object.create(null);
	var lines = text.split('\n');
	for (var i = 0; i < lines.length; i++) {
		var p = lines[i].split('\t');
		if (p[0] === 'C') { cls[p[1]] = p[2]; rev[p[2]] = p[1]; }
		else if (p[0] === 'F') { fld[p[1] + '.' + p[2]] = p[4]; srg[p[3]] = p[4]; }
		else if (p[0] === 'M') { mth[p[1] + '.' + p[2] + p[3]] = p[5]; srg[p[4]] = p[5]; }
		else if (p[0] === 'S') sup[p[1]] = [p[2]].concat(p[3] ? p[3].split(',') : []);
	}
	MODLOADER_CLASSES.forEach(function (n) { cls[n] = SRC + n; rev[SRC + n] = n; });
	var map = { cls: cls, rev: rev, fld: fld, mth: mth, srg: srg, sup: sup };
	vm.nameMap = map;
	vm.mcpParents = function (mcp) {
		var o = rev[mcp];
		var ps = o !== undefined ? sup[o] : null;
		return ps ? ps.map(function (x) { return cls[x] || x; }) : null;
	};
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
			if (!isMethod && !cls[c] && declaresField(vm, c, name)) return name;
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

function declaresField(vm, name, field) {
	var cache = vm.declFields || (vm.declFields = Object.create(null));
	var set = cache[name];
	if (!set) {
		set = Object.create(null);
		var src = vm.sources[name];
		if (src) {
			if (!src.parsed) src.parsed = JVM.parseClassFile(src.bytes);
			src.parsed.fields.forEach(function (f) { set[f.name] = true; });
		} else if (vm.classes[name] && vm.classes[name].cf && vm.classes[name].cf.origFields) {
			vm.classes[name].cf.origFields.forEach(function (f) { set[f] = true; });
		} else return false;
		cache[name] = set;
	}
	return !!set[field];
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
		if (!spec) return map.sup[name] || [];
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
var VANILLA_IDS = {};
(VANILLA_BLOCKS + ',' + VANILLA_ITEMS).split(',').forEach(function (kv) { VANILLA_IDS[+kv.split(' ')[1]] = true; });
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
function op(vm) { var g = vm.game; return g && (g.mode === 'run' || g.mode === 'gen') && g.op ? g.op.apply(null, Array.prototype.slice.call(arguments, 1)) : undefined; }
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
		'dropBlockAsItem(Lnet/minecraft/src/World;IIIII)V': function (vm, self, a) {
			vm.callVirtual(self, 'dropBlockAsItemWithChance', '(Lnet/minecraft/src/World;IIIIFI)V', [a[0], a[1], a[2], a[3], a[4], 1, a[5]]);
		},
		'dropBlockAsItemWithChance(Lnet/minecraft/src/World;IIIIFI)V': function (vm, self, a) {
			var w = a[0], rnd = w && w[':rand'];
			if (!rnd) return;
			var n = vm.callVirtual(self, 'quantityDroppedWithBonus', '(ILjava/util/Random;)I', [a[6], rnd]);
			for (var i = 0; i < n; i++) {
				if (vm.callVirtual(rnd, 'nextFloat', '()F', []) > a[5]) continue;
				var id = vm.callVirtual(self, 'idDropped', '(ILjava/util/Random;I)I', [a[4], rnd, a[6]]);
				if (id > 0) dropStack(vm, a[1] + 0.5, a[2] + 0.5, a[3] + 0.5, JVM.mc152.newStack(vm, id, 1, vm.callVirtual(self, 'damageDropped', '(I)I', [a[4]])));
			}
		},
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
		anyInit: function (vm, self, args, desc) {
			var sig = JVM.parseDesc(desc), id = 0, mat = null;
			for (var i = 0; i < sig.args.length; i++) {
				if (sig.args[i] === 'I' && !id) id = args[i];
				if (args[i] && args[i].cls && args[i].cls.name === SRC + 'Material') mat = args[i];
			}
			var mc = vm.loadClass(SRC + 'Material'); vm.initClass(mc);
			initBlock(vm, self, id, mat || mc.statics.rock);
		},
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
		if (!reg(vm).vanilla) {
			reg(vm).blocks[id] = self;
			self.$mod = vm.currentMod || '';
			if (VANILLA_IDS[id]) self.$override = true;
		}
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
		anyInit: function (vm, self, args, desc) {
			var sig = JVM.parseDesc(desc);
			for (var i = 0; i < sig.args.length; i++) if (sig.args[i] === 'I') { initItem(vm, self, 256 + args[i]); return; }
			initItem(vm, self, 0);
		},
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
		if (!reg(vm).vanilla && !self.$blockItem) { reg(vm).items[id] = self; self.$mod = vm.currentMod || ''; if (VANILLA_IDS[id]) self.$override = true; }
	}
	def('ItemBlock', { super: SRC + 'Item', methods: {
		'<init>(I)V': function (vm, self, a) { self.$blockItem = true; initItem(vm, self, a[0] + 256); self[':blockID'] = a[0] + 256; },
		'getBlockID()I': function (vm, self) { return self[':blockID']; },
		'getUnlocalizedName()Ljava/lang/String;': function (vm, self) { var b = blockById(vm, self[':blockID']); return b ? vm.callVirtual(b, 'getUnlocalizedName', '()Ljava/lang/String;', []) : 'tile.null'; },
		'getUnlocalizedName(Lnet/minecraft/src/ItemStack;)Ljava/lang/String;': function (vm, self) { var b = blockById(vm, self[':blockID']); return b ? vm.callVirtual(b, 'getUnlocalizedName', '()Ljava/lang/String;', []) : 'tile.null'; },
	} });
	function blockById(vm, id) { var c = vm.loadClass(SRC + 'Block'); vm.initClass(c); return c.statics.blocksList.a[id] || null; }
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

	var tr = function (vm, k) { var v = reg(vm).lang[k]; return v != null ? v : k; };
	def('StringTranslate', { methods: {
		'getCurrentLanguage()Ljava/lang/String;': function () { return 'en_US'; },
		'translateKey(Ljava/lang/String;)Ljava/lang/String;': function (vm, self, a) { return tr(vm, a[0]); },
		'translateNamedKey(Ljava/lang/String;)Ljava/lang/String;': function (vm, self, a) { return tr(vm, a[0] + '.name'); },
		'translateKeyFormat(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;': function (vm, self, a) { return vm.callStatic('java/lang/String', 'format', '(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;', [tr(vm, a[0]), a[1]]); },
		'isUnicode()Z': function () { return 0; },
		'getLanguageList()Ljava/util/TreeMap;': function (vm) { var m = vm.newObject(vm.loadClass('java/util/TreeMap')); vm.callVirtual(m, '<init>', '()V', []); vm.callVirtual(m, 'put', '(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;', ['en_US', 'English (US)']); return m; },
		'setLanguage(Ljava/lang/String;Z)V': function () {},
	}, staticMethods: {
		'getInstance()Lnet/minecraft/src/StringTranslate;': function (vm) { return vm.mcTranslate || (vm.mcTranslate = vm.newObject(vm.loadClass(SRC + 'StringTranslate'))); },
		'isBidirectional(Ljava/lang/String;)Z': function () { return 0; },
	} });
	def('StatCollector', { staticMethods: {
		'translateToLocal(Ljava/lang/String;)Ljava/lang/String;': function (vm, n, a) { return tr(vm, a[0]); },
		'translateToLocalFormatted(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;': function (vm, n, a) { return vm.callStatic('java/lang/String', 'format', '(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;', [tr(vm, a[0]), a[1]]); },
		'isTranslationKeyAvailable(Ljava/lang/String;)Z': function (vm, n, a) { return reg(vm).lang[a[0]] != null ? 1 : 0; },
	} });

	var intArr = function (vm, v) { var r = vm.newArray('I', v.length); v.forEach(function (x, i) { r.a[i] = x; }); return r; };
	def('Facing', { statics: { oppositeSide: null, offsetsXForSide: null, offsetsYForSide: null, offsetsZForSide: null, facings: null }, clinit: function (vm, c) {
		c.statics.oppositeSide = intArr(vm, [1, 0, 3, 2, 5, 4]);
		c.statics.offsetsXForSide = intArr(vm, [0, 0, 0, 0, -1, 1]);
		c.statics.offsetsYForSide = intArr(vm, [-1, 1, 0, 0, 0, 0]);
		c.statics.offsetsZForSide = intArr(vm, [0, 0, -1, 1, 0, 0]);
		c.statics.facings = JVM.javaArray(vm, 'Ljava/lang/String;', ['DOWN', 'UP', 'NORTH', 'SOUTH', 'WEST', 'EAST']);
	} });
	def('BlockPistonBase', { super: SRC + 'Block', methods: {
		'<init>(IZ)V': function (vm, self, a) {
			var mc = vm.loadClass(SRC + 'Material'); vm.initClass(mc);
			var bc = vm.loadClass(SRC + 'Block'); vm.initClass(bc);
			initBlock(vm, self, a[0], mc.statics.piston);
			self[':isSticky'] = a[1];
			self[':stepSound'] = bc.statics.soundStoneFootstep;
			self[':blockHardness'] = 0.5; self[':blockResistance'] = 2.5;
			var tc = vm.loadClass(SRC + 'CreativeTabs'); vm.initClass(tc); self.$tab = tc.statics.tabRedstone;
		},
		'isOpaqueCube()Z': function () { return 0; },
		'renderAsNormalBlock()Z': function () { return 0; },
		'getRenderType()I': function () { return 16; },
	}, staticMethods: {
		'getOrientation(I)I': function (vm, n, a) { return a[0] & 7; },
		'isExtended(I)Z': function (vm, n, a) { return (a[0] & 8) !== 0 ? 1 : 0; },
		'determineOrientation(Lnet/minecraft/src/World;IIILnet/minecraft/src/EntityLiving;)I': function (vm, n, a) {
			var e = a[4];
			if (Math.abs(e[':posX'] - a[1]) < 2 && Math.abs(e[':posZ'] - a[3]) < 2) {
				var d = e[':posY'] + 1.82 - (e[':yOffset'] || 0);
				if (d - a[2] > 2) return 1;
				if (a[2] - d > 0) return 0;
			}
			var l = Math.floor(Math.fround(e[':rotationYaw'] * 4 / 360) + 0.5) & 3;
			return l === 0 ? 2 : l === 1 ? 5 : l === 2 ? 3 : l === 3 ? 4 : 0;
		},
	} });

	installWorld(vm, def);
	installWorldGen(vm, def);
	if (JVM.installModels) JVM.installModels(vm);
	if (JVM.installServer) JVM.installServer(vm);
	if (JVM.installMobs) JVM.installMobs(vm);
	if (JVM.installForge) JVM.installForge(vm);
	if (JVM.installTiles) JVM.installTiles(vm);
	if (JVM.installSettings) JVM.installSettings(vm);
}

var SIN_TABLE = null;
function mhSin(f) {
	if (!SIN_TABLE) { SIN_TABLE = new Float32Array(65536); for (var i = 0; i < 65536; i++) SIN_TABLE[i] = Math.sin(i * Math.PI * 2 / 65536); }
	return SIN_TABLE[(Math.fround(Math.fround(f) * Math.fround(10430.378)) | 0) & 65535];
}
function mhCos(f) {
	if (!SIN_TABLE) mhSin(0);
	return SIN_TABLE[(Math.fround(Math.fround(Math.fround(f) * Math.fround(10430.378)) + 16384) | 0) & 65535];
}
var FPI = Math.fround(Math.PI);
function installWorldGen(vm, def) {
	var fl = function (d) { var i = d | 0; return d < i ? i - 1 : i; };
	def('MathHelper', { staticMethods: {
		'sin(F)F': function (vm, n, a) { return mhSin(a[0]); },
		'cos(F)F': function (vm, n, a) { return mhCos(a[0]); },
		'sqrt_float(F)F': function (vm, n, a) { return Math.fround(Math.sqrt(a[0])); },
		'sqrt_double(D)F': function (vm, n, a) { return Math.fround(Math.sqrt(a[0])); },
		'floor_float(F)I': function (vm, n, a) { return fl(a[0]); },
		'floor_double(D)I': function (vm, n, a) { return fl(a[0]); },
		'truncateDoubleToInt(D)I': function (vm, n, a) { return Math.trunc(a[0]) | 0; },
		'floor_double_long(D)J': function (vm, n, a) { return BigInt(Math.floor(a[0])); },
		'abs(F)F': function (vm, n, a) { return Math.abs(a[0]); },
		'abs_int(I)I': function (vm, n, a) { return a[0] < 0 ? -a[0] | 0 : a[0]; },
		'ceiling_float_int(F)I': function (vm, n, a) { var i = a[0] | 0; return a[0] > i ? i + 1 : i; },
		'ceiling_double_int(D)I': function (vm, n, a) { var i = a[0] | 0; return a[0] > i ? i + 1 : i; },
		'clamp_int(III)I': function (vm, n, a) { return a[0] < a[1] ? a[1] : a[0] > a[2] ? a[2] : a[0]; },
		'clamp_float(FFF)F': function (vm, n, a) { return a[0] < a[1] ? a[1] : a[0] > a[2] ? a[2] : a[0]; },
		'abs_max(DD)D': function (vm, n, a) { return Math.max(Math.abs(a[0]), Math.abs(a[1])); },
		'bucketInt(II)I': function (vm, n, a) { return a[0] < 0 ? -((-a[0] - 1) / a[1] | 0) - 1 : a[0] / a[1] | 0; },
		'getRandomIntegerInRange(Ljava/util/Random;II)I': function (vm, n, a) { return a[1] >= a[2] ? a[1] : vm.callVirtual(a[0], 'nextInt', '(I)I', [a[2] - a[1] + 1]) + a[1]; },
		'wrapAngleTo180_float(F)F': function (vm, n, a) { var f = Math.fround(a[0] % 360); if (f >= 180) f -= 360; if (f < -180) f += 360; return Math.fround(f); },
		'wrapAngleTo180_double(D)D': function (vm, n, a) { var f = a[0] % 360; if (f >= 180) f -= 360; if (f < -180) f += 360; return f; },
	} });
	def('WorldProvider', { access: JVM.ACC_PUBLIC | JVM.ACC_ABSTRACT, methods: {
		'isSurfaceWorld()Z': function (vm, self) { return self[':dimensionId'] === 0 ? 1 : 0; },
		'getDimensionName()Ljava/lang/String;': function (vm, self) { var d = self[':dimensionId']; return d === -1 ? 'Nether' : d === 1 ? 'The End' : 'Overworld'; },
		'getAverageGroundLevel()I': function () { return 64; },
		'getHeight()I': function () { return 128; },
		'getActualHeight()I': function () { return 128; },
	} });
	def('WorldGenerator', { access: JVM.ACC_PUBLIC | JVM.ACC_ABSTRACT,
		abstractMethods: { 'generate(Lnet/minecraft/src/World;Ljava/util/Random;III)Z': true },
		methods: {
			'<init>()V': function () {},
			'<init>(Z)V': function (vm, self, a) { self[':doBlockNotify'] = a[0]; },
			'setScale(DDD)V': function () {},
			'setBlock(Lnet/minecraft/src/World;IIII)V': function (vm, self, a) { vm.callVirtual(a[0], 'setBlock', '(IIIIII)Z', [a[1], a[2], a[3], a[4], 0, 3]); },
			'setBlockAndMetadata(Lnet/minecraft/src/World;IIIII)V': function (vm, self, a) { vm.callVirtual(a[0], 'setBlock', '(IIIIII)Z', [a[1], a[2], a[3], a[4], a[5], 3]); },
		} });
	var minable = function (vm, self, world, rand, x, y, z) {
		var n = self[':numberOfBlocks'], id = self[':minableBlockId'], meta = self[':minableBlockMeta'] | 0, target = self[':field_94523_c'];
		var f = Math.fround(vm.callVirtual(rand, 'nextFloat', '()F', []) * FPI);
		var s = Math.fround(Math.fround(mhSin(f) * n) / 8), c = Math.fround(Math.fround(mhCos(f) * n) / 8);
		var d0 = Math.fround(x + 8 + s), d1 = Math.fround(x + 8 - s), d2 = Math.fround(z + 8 + c), d3 = Math.fround(z + 8 - c);
		var d4 = y + vm.callVirtual(rand, 'nextInt', '(I)I', [3]) - 2, d5 = y + vm.callVirtual(rand, 'nextInt', '(I)I', [3]) - 2;
		for (var l = 0; l <= n; l++) {
			var d6 = d0 + (d1 - d0) * l / n, d7 = d4 + (d5 - d4) * l / n, d8 = d2 + (d3 - d2) * l / n;
			var d9 = vm.callVirtual(rand, 'nextDouble', '()D', []) * n / 16;
			var sw = Math.fround(mhSin(Math.fround(Math.fround(l * FPI) / n)) + 1);
			var d10 = sw * d9 + 1, d11 = sw * d9 + 1;
			var i1 = fl(d6 - d10 / 2), j1 = fl(d7 - d11 / 2), k1 = fl(d8 - d10 / 2);
			var l1 = fl(d6 + d10 / 2), i2 = fl(d7 + d11 / 2), j2 = fl(d8 + d10 / 2);
			for (var k2 = i1; k2 <= l1; k2++) {
				var d12 = (k2 + 0.5 - d6) / (d10 / 2);
				if (d12 * d12 >= 1) continue;
				for (var l2 = j1; l2 <= i2; l2++) {
					var d13 = (l2 + 0.5 - d7) / (d11 / 2);
					if (d12 * d12 + d13 * d13 >= 1) continue;
					for (var i3 = k1; i3 <= j2; i3++) {
						var d14 = (i3 + 0.5 - d8) / (d10 / 2);
						if (d12 * d12 + d13 * d13 + d14 * d14 < 1 && vm.callVirtual(world, 'getBlockId', '(III)I', [k2, l2, i3]) === target)
							vm.callVirtual(world, 'setBlock', '(IIIIII)Z', [k2, l2, i3, id, meta, 2]);
					}
				}
			}
		}
		return 1;
	};
	def('WorldGenMinable', { super: SRC + 'WorldGenerator', methods: {
		'<init>(II)V': function (vm, self, a) { self[':minableBlockId'] = a[0]; self[':numberOfBlocks'] = a[1]; self[':field_94523_c'] = 1; },
		'<init>(III)V': function (vm, self, a) { self[':minableBlockId'] = a[0]; self[':numberOfBlocks'] = a[1]; self[':field_94523_c'] = a[2]; },
		'<init>(IIII)V': function (vm, self, a) { self[':minableBlockId'] = a[0]; self[':minableBlockMeta'] = a[1]; self[':numberOfBlocks'] = a[2]; self[':field_94523_c'] = a[3]; },
		'generate(Lnet/minecraft/src/World;Ljava/util/Random;III)Z': function (vm, self, a) { return minable(vm, self, a[0], a[1], a[2], a[3], a[4]); },
	} });
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
	var w2 = vm.mcWorld, dim = vm.mcDim | 0;
	if (!w2[':provider'] || w2[':provider'][':dimensionId'] !== dim) {
		var pv = vm.newObject(vm.loadClass(SRC + 'WorldProvider'));
		pv[':dimensionId'] = dim; pv[':isHellWorld'] = dim === -1 ? 1 : 0; pv[':hasNoSky'] = dim === -1 ? 1 : 0;
		pv[':worldObj'] = w2;
		w2[':provider'] = pv;
	}
	if (JVM.mc152.onWorld) JVM.mc152.onWorld(vm, w2);
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
	if (JVM.mc152.onPlayer) JVM.mc152.onPlayer(vm, p);
	return p;
}
function heldStack(vm) {
	var h = op(vm, 'held');
	if (!h || !h.id) return null;
	return (function () { var s = vm.newObject(vm.loadClass(SRC + 'ItemStack')); s[':itemID'] = vm.game.itemToJava(h.id); s[':stackSize'] = h.count; s[':itemDamage'] = h.data || 0; return s; })();
}

function setBlock(vm, world, x, y, z, id, meta) {
	var old = op(vm, 'tile', x, y, z) || { id: 0, data: 0 };
	op(vm, 'settile', x, y, z, id, meta);
	var r = reg(vm);
	if (old.id !== id) {
		var ob = r.blocks[old.id];
		if (ob && old.id) vm.callVirtual(ob, 'breakBlock', '(Lnet/minecraft/src/World;IIIII)V', [world, x, y, z, old.id, old.data]);
		var nb = r.blocks[id];
		if (nb && id) vm.callVirtual(nb, 'onBlockAdded', '(Lnet/minecraft/src/World;III)V', [world, x, y, z]);
	}
	return 1;
}

var LIGHT0 = Object.create(null), NOMOVE = Object.create(null);
[0, 6, 20, 26, 27, 28, 30, 31, 32, 37, 38, 39, 40, 50, 51, 55, 59, 63, 64, 65, 66, 68, 69, 70, 71, 72, 75, 76, 77, 78, 83, 85, 90, 92, 93,
 94, 96, 101, 102, 104, 105, 106, 107, 111, 113, 115, 117, 118, 119, 120, 122, 127, 131, 132, 140, 141, 142, 143, 144, 145, 147, 148,
 149, 150, 151, 154, 157].forEach(function (i) { LIGHT0[i] = 1; });
[0, 6, 27, 28, 30, 31, 32, 37, 38, 39, 40, 50, 51, 55, 59, 66, 69, 75, 76, 77, 78, 83, 90, 93, 94, 104, 105, 106, 115, 119, 131, 132,
 141, 142, 143, 157].forEach(function (i) { NOMOVE[i] = 1; });

function installWorld(vm, def) {
	var g = function (vm) { return vm.game || { blockToGame: function (x) { return x; }, blockToJava: function (x) { return x; }, itemToGame: function (x) { return x; }, itemToJava: function (x) { return x; } }; };
	var tile = function (vm, x, y, z) { var t = op(vm, 'tile', x, y, z); return t ? t : { id: 0, data: 0 }; };
	def('IBlockAccess', { access: JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC });
	def('World', { interfaces: [SRC + 'IBlockAccess'], methods: {
		'getBlockId(III)I': function (vm, self, a) { return g(vm).blockToJava(tile(vm, a[0], a[1], a[2]).id); },
		'getBlockMetadata(III)I': function (vm, self, a) { return tile(vm, a[0], a[1], a[2]).data; },
		'isAirBlock(III)Z': function (vm, self, a) { return tile(vm, a[0], a[1], a[2]).id === 0 ? 1 : 0; },
		'setBlock(IIII)Z': function (vm, self, a) { return setBlock(vm, self, a[0], a[1], a[2], a[3], 0); },
		'setBlock(IIIIII)Z': function (vm, self, a) { return setBlock(vm, self, a[0], a[1], a[2], a[3], a[4]); },
		'setBlock(IIIII)Z': function (vm, self, a) { return setBlock(vm, self, a[0], a[1], a[2], a[3], a[4]); },
		'setBlockToAir(III)Z': function (vm, self, a) { return setBlock(vm, self, a[0], a[1], a[2], 0, 0); },
		'setBlockWithNotify(IIII)Z': function (vm, self, a) { return setBlock(vm, self, a[0], a[1], a[2], a[3], 0); },
		'setBlockMetadataWithNotify(IIIII)Z': function (vm, self, a) { op(vm, 'setdata', a[0], a[1], a[2], a[3]); return 1; },
		'setBlockMetadata(IIIII)Z': function (vm, self, a) { op(vm, 'setdata', a[0], a[1], a[2], a[3]); return 1; },
		'checkChunksExist(IIIIII)Z': function () { return 1; },
		'blockExists(III)Z': function () { return 1; },
		'doChunksNearChunkExist(IIII)Z': function () { return 1; },
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
		'getSeed()J': function (vm) { return BigInt(vm.mcSeed | 0); },
		'getWorldTime()J': function (vm) { return BigInt(op(vm, 'time') || 0); },
		'getTotalWorldTime()J': function (vm) { return BigInt(op(vm, 'time') || 0); },
		'setWorldTime(J)V': function (vm, self, a) { op(vm, 'settime', Number(a[0])); },
		'isDaytime()Z': function (vm) { var t = (op(vm, 'time') || 0) % 24000; return t < 12000 ? 1 : 0; },
		'getHeightValue(II)I': function (vm, self, a) { var y = 127; while (y > 0 && LIGHT0[tile(vm, a[0], y, a[1]).id]) y--; return y + 1; },
		'getTopSolidOrLiquidBlock(II)I': function (vm, self, a) { var y = 127, id; while (y > 0 && (NOMOVE[id = tile(vm, a[0], y, a[1]).id] || id === 18)) y--; return y + 1; },
		'getPrecipitationHeight(II)I': function (vm, self, a) { var y = 127, id; while (y > 0 && NOMOVE[id = tile(vm, a[0], y, a[1]).id] && id !== 8 && id !== 9 && id !== 10 && id !== 11) y--; return y + 1; },
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
	ent.anyInit = function (vm, self, args) { if (args[0] && args[0].cls && args[0].cls.name === SRC + 'World') self[':worldObj'] = args[0]; };
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
		var isBlock = vm.isInstance(o, bc);
		var holder = isBlock ? o.$itemBlock : o;
		var shown = null;
		if (holder) {
			var st = JVM.mc152.newStack(vm, isBlock ? o[':blockID'] : o[':itemID'], 1, 0);
			shown = safe(function () { return vm.callVirtual(holder, 'getItemDisplayName', '(Lnet/minecraft/src/ItemStack;)Ljava/lang/String;', [st]); }, null);
		} else if (isBlock) shown = safe(function () { return vm.callVirtual(o, 'getLocalizedName', '()Ljava/lang/String;', []); }, null);
		if (shown && typeof shown === 'string' && !/^(tile|item)\.[^ ]*$/.test(shown.trim())) return shown.trim();
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
		if (b.$mod !== modId || b.$override) return;
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
		if (b.$harvest && /^(pickaxe|axe|shovel|none)$/.test(b.$harvest.tool)) json.tool = b.$harvest.tool;
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
		if (it.$mod !== modId || it.$override) return;
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
		if (typeof o === 'string') { var ore = JVM.forgeOre && JVM.forgeOre(vm, o); return ore ? stackRef(ore) : null; }
		if (o instanceof JVM.JArray) return o.a.length ? stackRef(o.a[0]) : null;
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
			if (args[0] && args[0].$box !== undefined && args[0].cls.name === 'java/lang/Boolean') i = 1;
			if (args[i] instanceof JVM.JArray) { rows = Array.prototype.slice.call(args[i].a); i++; }
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
	if (JVM.collectMobs) {
		var cm = JVM.collectMobs(vm, modId, ref, safe);
		out.mobs = cm.mobs; out.mobFiles = cm.files;
		if (cm.skipped.length) vm.log('out', 'entities left out (not creatures, or nothing to draw them with): ' + cm.skipped.join(', '));
	}
	return out;
};

JVM.installMc152 = installMc152;
JVM.mc152 = { worldObj: worldObj, playerObj: playerObj, heldStack: heldStack, reg: reg, newStack: function (vm, id, n, d) { var s = vm.newObject(vm.loadClass(SRC + 'ItemStack')); s[':itemID'] = id; s[':stackSize'] = n; s[':itemDamage'] = d; return s; } };
})();

(function () {
'use strict';

var SRC = 'net/minecraft/src/';
function list(vm, arr) { return JVM.newList(vm, arr || []); }
function listAdd(vm, l, v) { vm.callVirtual(l, 'add', '(Ljava/lang/Object;)Z', [v]); }
function listArr(vm, l) { if (!l) return []; var a = vm.callVirtual(l, 'toArray', '()[Ljava/lang/Object;', []); return a ? Array.prototype.slice.call(a.a) : []; }

function initRenderer(vm, self, base, name, u, v) {
	self[':baseModel'] = base;
	self[':boxName'] = name;
	self[':textureWidth'] = base ? base[':textureWidth'] : 64;
	self[':textureHeight'] = base ? base[':textureHeight'] : 32;
	self[':textureOffsetX'] = u | 0; self[':textureOffsetY'] = v | 0;
	self[':showModel'] = 1; self[':isHidden'] = 0; self[':mirror'] = 0;
	self[':rotationPointX'] = 0; self[':rotationPointY'] = 0; self[':rotationPointZ'] = 0;
	self[':rotateAngleX'] = 0; self[':rotateAngleY'] = 0; self[':rotateAngleZ'] = 0;
	self[':offsetX'] = 0; self[':offsetY'] = 0; self[':offsetZ'] = 0;
	self[':cubeList'] = list(vm, []);
	self[':childModels'] = null;
	self.$boxes = [];
	if (base && base[':boxList']) listAdd(vm, base[':boxList'], self);
}
function addBox(vm, self, x, y, z, w, h, d, inflate, u, v, name) {
	var b = { x: x, y: y, z: z, w: w | 0, h: h | 0, d: d | 0, inflate: inflate || 0,
		u: u == null ? self[':textureOffsetX'] : u, v: v == null ? self[':textureOffsetY'] : v, mirror: !!self[':mirror'], name: name || null };
	self.$boxes.push(b);
	var box = vm.newObject(vm.loadClass(SRC + 'ModelBox'));
	box.$box = b;
	box[':posX1'] = x; box[':posY1'] = y; box[':posZ1'] = z;
	box[':posX2'] = x + w; box[':posY2'] = y + h; box[':posZ2'] = z + d;
	box[':field_78247_g'] = name;
	listAdd(vm, self[':cubeList'], box);
	return self;
}

function installModels(vm) {
	var def = function (n, s) { vm.defineNative(SRC + n, s); };
	var MB = 'Lnet/minecraft/src/ModelBase;', MR = 'Lnet/minecraft/src/ModelRenderer;';
	def('ModelBase', { methods: {
		'<init>()V': function (vm, self) { modelInit(vm, self); },
		'render(Lnet/minecraft/src/Entity;FFFFFF)V': function (vm, self) {
			var v = self.$vanilla && self.$vanilla.m.drawn;
			if (v) v.forEach(function (f) { var r = self[':' + f.replace(/\[\d+\]$/, '')]; if (r && r.a) r = r.a[+(/\[(\d+)\]$/.exec(f) || [0, 0])[1]]; if (r) r.$drawn = true; });
		},
		'setRotationAngles(FFFFFFLnet/minecraft/src/Entity;)V': function () {},
		'setLivingAnimations(Lnet/minecraft/src/EntityLiving;FFF)V': function () {},
		'getRandomModelBox(Ljava/util/Random;)Lnet/minecraft/src/ModelRenderer;': function (vm, self, a) { var l = listArr(vm, self[':boxList']); return l.length ? l[vm.callVirtual(a[0], 'nextInt', '(I)I', [l.length])] : null; },
		'setTextureOffset(Ljava/lang/String;II)V': function (vm, self, a) { (self.$texOffsets || (self.$texOffsets = {}))[a[0]] = [a[1], a[2]]; },
		'getTextureOffset(Ljava/lang/String;)Lnet/minecraft/src/TextureOffset;': function (vm, self, a) {
			var t = self.$texOffsets && self.$texOffsets[a[0]];
			if (!t) return null;
			var o = vm.newObject(vm.loadClass(SRC + 'TextureOffset')); o[':textureOffsetX'] = t[0]; o[':textureOffsetY'] = t[1];
			return o;
		},
	}, anyInit: function (vm, self) { modelInit(vm, self); } });
	function modelInit(vm, self) {
		if (self.$model) return;
		self.$model = true;
		self[':boxList'] = list(vm, []);
		self[':textureWidth'] = 64; self[':textureHeight'] = 32;
		self[':onGround'] = 0; self[':isRiding'] = 0; self[':isChild'] = 1;
		if (self.$vanilla) buildVanilla(vm, self, self.$vanilla.m, self.$vanilla.desc, self.$vanilla.args);
	}
	def('TextureOffset', { methods: { '<init>(II)V': function (vm, self, a) { self[':textureOffsetX'] = a[0]; self[':textureOffsetY'] = a[1]; } } });
	def('ModelRenderer', { methods: {
		'<init>(Lnet/minecraft/src/ModelBase;Ljava/lang/String;)V': function (vm, self, a) { initRenderer(vm, self, a[0], a[1], 0, 0); },
		'<init>(Lnet/minecraft/src/ModelBase;)V': function (vm, self, a) { initRenderer(vm, self, a[0], null, 0, 0); },
		'<init>(Lnet/minecraft/src/ModelBase;II)V': function (vm, self, a) { initRenderer(vm, self, a[0], null, a[1], a[2]); },
		'addChild(Lnet/minecraft/src/ModelRenderer;)V': function (vm, self, a) { if (!self[':childModels']) self[':childModels'] = list(vm, []); listAdd(vm, self[':childModels'], a[0]); },
		'setTextureOffset(II)Lnet/minecraft/src/ModelRenderer;': function (vm, self, a) { self[':textureOffsetX'] = a[0]; self[':textureOffsetY'] = a[1]; return self; },
		'addBox(Ljava/lang/String;FFFIII)Lnet/minecraft/src/ModelRenderer;': function (vm, self, a) {
			var name = self[':boxName'] + '.' + a[0];
			var t = self[':baseModel'] && self[':baseModel'].$texOffsets && self[':baseModel'].$texOffsets[name];
			if (t) { self[':textureOffsetX'] = t[0]; self[':textureOffsetY'] = t[1]; }
			return addBox(vm, self, a[1], a[2], a[3], a[4], a[5], a[6], 0, null, null, name);
		},
		'addBox(FFFIII)Lnet/minecraft/src/ModelRenderer;': function (vm, self, a) { return addBox(vm, self, a[0], a[1], a[2], a[3], a[4], a[5], 0); },
		'addBox(FFFIIIF)V': function (vm, self, a) { addBox(vm, self, a[0], a[1], a[2], a[3], a[4], a[5], a[6]); },
		'setRotationPoint(FFF)V': function (vm, self, a) { self[':rotationPointX'] = a[0]; self[':rotationPointY'] = a[1]; self[':rotationPointZ'] = a[2]; },
		'setTextureSize(II)Lnet/minecraft/src/ModelRenderer;': function (vm, self, a) { self[':textureWidth'] = a[0]; self[':textureHeight'] = a[1]; return self; },
		'render(F)V': function (vm, self) { self.$drawn = true; }, 'renderWithRotation(F)V': function (vm, self) { self.$drawn = true; }, 'postRender(F)V': function () {},
	} });
	def('ModelBox', { methods: {
		'<init>(Lnet/minecraft/src/ModelRenderer;IIFFFIIIF)V': function (vm, self, a) {
			self.$box = { x: a[3], y: a[4], z: a[5], w: a[6], h: a[7], d: a[8], inflate: a[9], u: a[1], v: a[2], mirror: !!(a[0] && a[0][':mirror']) };
			self[':posX1'] = a[3]; self[':posY1'] = a[4]; self[':posZ1'] = a[5];
			self[':posX2'] = a[3] + a[6]; self[':posY2'] = a[4] + a[7]; self[':posZ2'] = a[5] + a[8];
			if (a[0]) a[0].$boxes.push(self.$box);
		},
		'render(Lnet/minecraft/src/Tessellator;F)V': function () {},
	} });
	Object.keys(JVM.vanillaModels || {}).forEach(function (n) {
		var vmod = JVM.vanillaModels[n], m = {};
		Object.keys(vmod.ctors).forEach(function (d) {
			m['<init>' + d] = function (vm, self, a) {
				self.$model = false;
				self.$vanilla = { m: vmod, desc: d, args: a };
				modelInit(vm, self);
			};
		});
		def(n, { super: SRC + (vmod.super || 'ModelBase'), methods: m });
	});
}

function buildVanilla(vm, self, vmod, desc, args) {
	var c = vmod.ctors[desc];
	if (!c) return;
	var rec = JSON.parse(JSON.stringify(c.base));
	(c.d || []).forEach(function (dl) {
		var path = dl[0].split('.'), o = rec;
		for (var i = 0; i < path.length - 1; i++) o = o[path[i]];
		var v = args[dl[1]];
		o[path[path.length - 1]] += dl[2] * (typeof v === 'number' ? v : v ? 1 : 0);
	});
	vmod = rec;
	self[':textureWidth'] = vmod.tw; self[':textureHeight'] = vmod.th;
	Object.keys(vmod.extra || {}).forEach(function (k) { self[':' + k] = vmod.extra[k]; });
	var made = {};
	var make = function (name) {
		if (made[name]) return made[name];
		var p = vmod.parts[name];
		var r = vm.newObject(vm.loadClass(SRC + 'ModelRenderer'));
		initRenderer(vm, r, self, p.boxName || null, p.tex[0], p.tex[1]);
		r[':textureWidth'] = p.ts ? p.ts[0] : vmod.tw; r[':textureHeight'] = p.ts ? p.ts[1] : vmod.th;
		r[':rotationPointX'] = p.pivot[0]; r[':rotationPointY'] = p.pivot[1]; r[':rotationPointZ'] = p.pivot[2];
		if (p.rot) { r[':rotateAngleX'] = p.rot[0]; r[':rotateAngleY'] = p.rot[1]; r[':rotateAngleZ'] = p.rot[2]; }
		if (p.off) { r[':offsetX'] = p.off[0]; r[':offsetY'] = p.off[1]; r[':offsetZ'] = p.off[2]; }
		if (p.hidden) r[':showModel'] = 0;
		p.boxes.forEach(function (b) {
			r[':mirror'] = b[8] ? 1 : 0;
			addBox(vm, r, b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7][0], b[7][1]);
		});
		r[':mirror'] = p.mirror ? 1 : 0;
		made[name] = r;
		(p.children || []).forEach(function (c) {
			var ch = make(c);
			if (!r[':childModels']) r[':childModels'] = list(vm, []);
			listAdd(vm, r[':childModels'], ch);
		});
		return r;
	};
	var arrays = {};
	Object.keys(vmod.parts).forEach(function (name) {
		var r = make(name), p = vmod.parts[name];
		if (p.field) self[':' + p.field] = r;
		else if (p.arrayField) {
			var arr = arrays[p.arrayField] || (arrays[p.arrayField] = vm.newArray('Lnet/minecraft/src/ModelRenderer;', p.length));
			arr.a[p.index] = r;
		}
	});
	Object.keys(arrays).forEach(function (k) { self[':' + k] = arrays[k]; });
}

JVM.modelData = function (vm, model) {
	if (!model) return null;
	var seen = new Set(), childSet = new Set();
	var all = listArr(vm, model[':boxList']);
	all.forEach(function (r) { listArr(vm, r[':childModels']).forEach(function (c) { childSet.add(c); }); });
	var part = function (r) {
		seen.add(r);
		return {
			name: r[':boxName'] || null,
			pivot: [r[':rotationPointX'], r[':rotationPointY'], r[':rotationPointZ']],
			rot: [r[':rotateAngleX'], r[':rotateAngleY'], r[':rotateAngleZ']],
			hidden: !r[':showModel'] || !!r[':isHidden'],
			tex: [r[':textureWidth'], r[':textureHeight']],
			boxes: r.$boxes.map(function (b) { return { from: [b.x, b.y, b.z], size: [b.w, b.h, b.d], inflate: b.inflate, uv: [b.u, b.v], mirror: b.mirror }; }),
			children: listArr(vm, r[':childModels']).map(part),
		};
	};
	return { tw: model[':textureWidth'], th: model[':textureHeight'], parts: all.filter(function (r) { return !childSet.has(r); }).map(part) };
};

JVM.pose = function (vm, model, entity) {
	var e = entity || vm.newObject(vm.loadClass(SRC + 'EntityLiving'));
	JVM.run(vm, function () { vm.callVirtual(model, 'setLivingAnimations', '(Lnet/minecraft/src/EntityLiving;FFF)V', [e, 0, 0, 1]); });
	JVM.run(vm, function () { vm.callVirtual(model, 'setRotationAngles', '(FFFFFFLnet/minecraft/src/Entity;)V', [0, 0, 0, 0, 0, 0.0625, e]); });
};
JVM.drawnParts = function (vm, model, entity) {
	var all = listArr(vm, model[':boxList']);
	all.forEach(function (r) { r.$drawn = false; });
	JVM.run(vm, function () { vm.callVirtual(model, 'render', '(Lnet/minecraft/src/Entity;FFFFFF)V', [entity || vm.newObject(vm.loadClass(SRC + 'EntityLiving')), 0, 0, 0, 0, 0, 0.0625]); });
	var drawn = all.filter(function (r) { return r.$drawn; });
	return drawn.length ? drawn : null;
};
JVM.installModels = installModels;
})();

JVM.vanillaModels = {"ModelBat":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":64,"parts":{"batHead":{"field":"batHead","tex":[0,0],"pivot":[0,0,0],"boxes":[[-3,-3,-3,6,6,6,0,[0,0],0]],"children":["part0","part1"]},"batBody":{"field":"batBody","tex":[0,34],"pivot":[0,0,0],"boxes":[[-3,4,-3,6,12,6,0,[0,16],0],[-5,16,0,10,6,1,0,[0,34],0]],"children":["batRightWing","batLeftWing"]},"batRightWing":{"field":"batRightWing","tex":[42,0],"pivot":[0,0,0],"boxes":[[-12,1,1.5,10,16,1,0,[42,0],0]],"children":["batOuterRightWing"]},"batLeftWing":{"field":"batLeftWing","tex":[42,0],"pivot":[0,0,0],"mirror":1,"boxes":[[2,1,1.5,10,16,1,0,[42,0],1]],"children":["batOuterLeftWing"]},"batOuterRightWing":{"field":"batOuterRightWing","tex":[24,16],"pivot":[-12,1,1.5],"boxes":[[-8,1,0,8,12,1,0,[24,16],0]]},"batOuterLeftWing":{"field":"batOuterLeftWing","tex":[24,16],"pivot":[12,1,1.5],"mirror":1,"boxes":[[0,1,0,8,12,1,0,[24,16],1]]},"part0":{"tex":[24,0],"pivot":[0,0,0],"boxes":[[-4,-6,-2,3,4,1,0,[24,0],0]]},"part1":{"tex":[24,0],"pivot":[0,0,0],"mirror":1,"boxes":[[1,-6,-2,3,4,1,0,[24,0],1]]}}}}},"drawn":["batHead","batBody"]},"ModelBiped":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"bipedHead":{"field":"bipedHead","tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]},"bipedHeadwear":{"field":"bipedHeadwear","tex":[32,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"bipedBody":{"field":"bipedBody","tex":[16,16],"pivot":[0,0,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"bipedRightArm":{"field":"bipedRightArm","tex":[40,16],"pivot":[-5,2,0],"rot":[0,0,0.10000000149011612],"boxes":[[-3,-2,-2,4,12,4,0,[40,16],0]]},"bipedLeftArm":{"field":"bipedLeftArm","tex":[40,16],"pivot":[5,2,0],"rot":[0,0,-0.10000000149011612],"mirror":1,"boxes":[[-1,-2,-2,4,12,4,0,[40,16],1]]},"bipedRightLeg":{"field":"bipedRightLeg","tex":[0,16],"pivot":[-1.899999976158142,12,0.10000000149011612],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"bipedLeftLeg":{"field":"bipedLeftLeg","tex":[0,16],"pivot":[1.899999976158142,12,0.10000000149011612],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,16],1]]},"bipedEars":{"field":"bipedEars","tex":[24,0],"pivot":[0,0,0],"boxes":[[-3,-6,-1,6,6,1,0,[24,0],0]]},"bipedCloak":{"field":"bipedCloak","tex":[0,0],"pivot":[0,0,0],"boxes":[[-5,0,-1,10,16,1,0,[0,0],0]]}}}},"(F)V":{"base":{"tw":64,"th":32,"parts":{"bipedHead":{"field":"bipedHead","tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]},"bipedHeadwear":{"field":"bipedHeadwear","tex":[32,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"bipedBody":{"field":"bipedBody","tex":[16,16],"pivot":[0,0,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"bipedRightArm":{"field":"bipedRightArm","tex":[40,16],"pivot":[-5,2,0],"rot":[0,0,0.10000000149011612],"boxes":[[-3,-2,-2,4,12,4,0,[40,16],0]]},"bipedLeftArm":{"field":"bipedLeftArm","tex":[40,16],"pivot":[5,2,0],"rot":[0,0,-0.10000000149011612],"mirror":1,"boxes":[[-1,-2,-2,4,12,4,0,[40,16],1]]},"bipedRightLeg":{"field":"bipedRightLeg","tex":[0,16],"pivot":[-1.899999976158142,12,0.10000000149011612],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"bipedLeftLeg":{"field":"bipedLeftLeg","tex":[0,16],"pivot":[1.899999976158142,12,0.10000000149011612],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,16],1]]},"bipedEars":{"field":"bipedEars","tex":[24,0],"pivot":[0,0,0],"boxes":[[-3,-6,-1,6,6,1,0,[24,0],0]]},"bipedCloak":{"field":"bipedCloak","tex":[0,0],"pivot":[0,0,0],"boxes":[[-5,0,-1,10,16,1,0,[0,0],0]]}}},"d":[["parts.bipedHead.boxes.0.6",0,1],["parts.bipedHeadwear.boxes.0.6",0,1],["parts.bipedBody.boxes.0.6",0,1],["parts.bipedRightArm.boxes.0.6",0,1],["parts.bipedLeftArm.boxes.0.6",0,1],["parts.bipedRightLeg.boxes.0.6",0,1],["parts.bipedLeftLeg.boxes.0.6",0,1],["parts.bipedEars.boxes.0.6",0,1],["parts.bipedCloak.boxes.0.6",0,1]]},"(FFII)V":{"base":{"tw":0,"th":0,"parts":{"bipedHead":{"field":"bipedHead","tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]},"bipedHeadwear":{"field":"bipedHeadwear","tex":[32,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"bipedBody":{"field":"bipedBody","tex":[16,16],"pivot":[0,0,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"bipedRightArm":{"field":"bipedRightArm","tex":[40,16],"pivot":[-5,2,0],"rot":[0,0,0.10000000149011612],"boxes":[[-3,-2,-2,4,12,4,0,[40,16],0]]},"bipedLeftArm":{"field":"bipedLeftArm","tex":[40,16],"pivot":[5,2,0],"rot":[0,0,-0.10000000149011612],"mirror":1,"boxes":[[-1,-2,-2,4,12,4,0,[40,16],1]]},"bipedRightLeg":{"field":"bipedRightLeg","tex":[0,16],"pivot":[-1.899999976158142,12,0.10000000149011612],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"bipedLeftLeg":{"field":"bipedLeftLeg","tex":[0,16],"pivot":[1.899999976158142,12,0.10000000149011612],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,16],1]]},"bipedEars":{"field":"bipedEars","tex":[24,0],"pivot":[0,0,0],"boxes":[[-3,-6,-1,6,6,1,0,[24,0],0]]},"bipedCloak":{"field":"bipedCloak","tex":[0,0],"pivot":[0,0,0],"boxes":[[-5,0,-1,10,16,1,0,[0,0],0]]}}},"d":[["parts.bipedHead.boxes.0.6",0,1],["parts.bipedHeadwear.boxes.0.6",0,1],["parts.bipedBody.boxes.0.6",0,1],["parts.bipedRightArm.boxes.0.6",0,1],["parts.bipedLeftArm.boxes.0.6",0,1],["parts.bipedRightLeg.boxes.0.6",0,1],["parts.bipedLeftLeg.boxes.0.6",0,1],["parts.bipedEars.boxes.0.6",0,1],["parts.bipedCloak.boxes.0.6",0,1],["parts.bipedBody.pivot.1",1,1],["parts.bipedRightArm.pivot.1",1,1],["parts.bipedLeftArm.pivot.1",1,1],["tw",2,1],["parts.bipedHead.ts.0",2,1],["parts.bipedHeadwear.ts.0",2,1],["parts.bipedBody.ts.0",2,1],["parts.bipedRightArm.ts.0",2,1],["parts.bipedLeftArm.ts.0",2,1],["parts.bipedRightLeg.ts.0",2,1],["parts.bipedLeftLeg.ts.0",2,1],["parts.bipedEars.ts.0",2,1],["parts.bipedCloak.ts.0",2,1],["th",3,1],["parts.bipedHead.ts.1",3,1],["parts.bipedHeadwear.ts.1",3,1],["parts.bipedBody.ts.1",3,1],["parts.bipedRightArm.ts.1",3,1],["parts.bipedLeftArm.ts.1",3,1],["parts.bipedRightLeg.ts.1",3,1],["parts.bipedLeftLeg.ts.1",3,1],["parts.bipedEars.ts.1",3,1],["parts.bipedCloak.ts.1",3,1]]}},"drawn":["bipedHead","bipedHeadwear","bipedBody","bipedRightArm","bipedLeftArm","bipedRightLeg","bipedLeftLeg"]},"ModelBlaze":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"blazeSticks[0]":{"arrayField":"blazeSticks","index":0,"length":12,"tex":[0,16],"pivot":[9,-1,0],"boxes":[[0,0,0,2,8,2,0,[0,16],0]]},"blazeSticks[1]":{"arrayField":"blazeSticks","index":1,"length":12,"tex":[0,16],"pivot":[1.1021821408568715e-15,-1.1224087476730347,9],"boxes":[[0,0,0,2,8,2,0,[0,16],0]]},"blazeSticks[2]":{"arrayField":"blazeSticks","index":2,"length":12,"tex":[0,16],"pivot":[-9,-1.4596672058105469,1.1021821408568715e-15],"boxes":[[0,0,0,2,8,2,0,[0,16],0]]},"blazeSticks[3]":{"arrayField":"blazeSticks","index":3,"length":12,"tex":[0,16],"pivot":[0,-1.929208517074585,-9],"boxes":[[0,0,0,2,8,2,0,[0,16],0]]},"blazeSticks[4]":{"arrayField":"blazeSticks","index":4,"length":12,"tex":[0,16],"pivot":[4.949747562408447,1.5839191675186157,4.949747562408447],"boxes":[[0,0,0,2,8,2,0,[0,16],0]]},"blazeSticks[5]":{"arrayField":"blazeSticks","index":5,"length":12,"tex":[0,16],"pivot":[-4.949747562408447,1.1989107131958008,4.949747562408447],"boxes":[[0,0,0,2,8,2,0,[0,16],0]]},"blazeSticks[6]":{"arrayField":"blazeSticks","index":6,"length":12,"tex":[0,16],"pivot":[-4.949747562408447,1.0100092887878418,-4.949747562408447],"boxes":[[0,0,0,2,8,2,0,[0,16],0]]},"blazeSticks[7]":{"arrayField":"blazeSticks","index":7,"length":12,"tex":[0,16],"pivot":[4.949747562408447,1.0635323524475098,-4.949747562408447],"boxes":[[0,0,0,2,8,2,0,[0,16],0]]},"blazeSticks[8]":{"arrayField":"blazeSticks","index":8,"length":12,"tex":[0,16],"pivot":[4.455076217651367,11.960163116455078,2.269866943359375],"boxes":[[0,0,0,2,8,2,0,[0,16],0]]},"blazeSticks[9]":{"arrayField":"blazeSticks","index":9,"length":12,"tex":[0,16],"pivot":[-2.269866943359375,11.8930082321167,4.455076217651367],"boxes":[[0,0,0,2,8,2,0,[0,16],0]]},"blazeSticks[10]":{"arrayField":"blazeSticks","index":10,"length":12,"tex":[0,16],"pivot":[-4.455076217651367,11.346710205078125,-2.269866943359375],"boxes":[[0,0,0,2,8,2,0,[0,16],0]]},"blazeSticks[11]":{"arrayField":"blazeSticks","index":11,"length":12,"tex":[0,16],"pivot":[2.269866943359375,10.614307403564453,-4.455076217651367],"boxes":[[0,0,0,2,8,2,0,[0,16],0]]},"blazeHead":{"field":"blazeHead","tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-4,-4,8,8,8,0,[0,0],0]]}}}}},"drawn":["blazeSticks[0]","blazeSticks[1]","blazeSticks[2]","blazeSticks[3]","blazeSticks[4]","blazeSticks[5]","blazeSticks[6]","blazeSticks[7]","blazeSticks[8]","blazeSticks[9]","blazeSticks[10]","blazeSticks[11]","blazeHead"]},"ModelBoat":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"boatSides[0]":{"arrayField":"boatSides","index":0,"length":5,"tex":[0,8],"pivot":[0,4,0],"rot":[1.5707963705062866,0,0],"boxes":[[-12,-8,-3,24,16,4,0,[0,8],0]]},"boatSides[1]":{"arrayField":"boatSides","index":1,"length":5,"tex":[0,0],"pivot":[-11,4,0],"rot":[0,4.71238899230957,0],"boxes":[[-10,-7,-1,20,6,2,0,[0,0],0]]},"boatSides[2]":{"arrayField":"boatSides","index":2,"length":5,"tex":[0,0],"pivot":[11,4,0],"rot":[0,1.5707963705062866,0],"boxes":[[-10,-7,-1,20,6,2,0,[0,0],0]]},"boatSides[3]":{"arrayField":"boatSides","index":3,"length":5,"tex":[0,0],"pivot":[0,4,-9],"rot":[0,3.1415927410125732,0],"boxes":[[-10,-7,-1,20,6,2,0,[0,0],0]]},"boatSides[4]":{"arrayField":"boatSides","index":4,"length":5,"tex":[0,0],"pivot":[0,4,9],"boxes":[[-10,-7,-1,20,6,2,0,[0,0],0]]}}}}},"drawn":["boatSides[0]","boatSides[1]","boatSides[2]","boatSides[3]","boatSides[4]"]},"ModelBook":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"coverRight":{"field":"coverRight","tex":[0,0],"pivot":[0,0,-1],"rot":[0,3.1415927410125732,0],"boxes":[[-6,-5,0,6,10,0,0,[0,0],0]]},"coverLeft":{"field":"coverLeft","tex":[16,0],"pivot":[0,0,1],"boxes":[[0,-5,0,6,10,0,0,[16,0],0]]},"pagesRight":{"field":"pagesRight","tex":[0,10],"pivot":[0,0,0],"boxes":[[0,-4,-0.9900000095367432,5,8,1,0,[0,10],0]]},"pagesLeft":{"field":"pagesLeft","tex":[12,10],"pivot":[0,0,0],"boxes":[[0,-4,-0.009999999776482582,5,8,1,0,[12,10],0]]},"flippingPageRight":{"field":"flippingPageRight","tex":[24,10],"pivot":[0,0,0],"boxes":[[0,-4,0,5,8,0,0,[24,10],0]]},"flippingPageLeft":{"field":"flippingPageLeft","tex":[24,10],"pivot":[0,0,0],"boxes":[[0,-4,0,5,8,0,0,[24,10],0]]},"bookSpine":{"field":"bookSpine","tex":[12,0],"pivot":[0,0,0],"rot":[0,1.5707963705062866,0],"boxes":[[-1,-5,0,2,10,0,0,[12,0],0]]}}}}},"drawn":["coverRight","coverLeft","bookSpine","pagesRight","pagesLeft","flippingPageRight","flippingPageLeft"]},"ModelChest":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"chestLid":{"field":"chestLid","tex":[0,0],"ts":[64,64],"pivot":[1,7,15],"boxes":[[0,-5,-14,14,5,14,0,[0,0],0]]},"chestBelow":{"field":"chestBelow","tex":[0,19],"ts":[64,64],"pivot":[1,6,1],"boxes":[[0,0,0,14,10,14,0,[0,19],0]]},"chestKnob":{"field":"chestKnob","tex":[0,0],"ts":[64,64],"pivot":[8,7,15],"boxes":[[-1,-2,-15,2,4,1,0,[0,0],0]]}}}}}},"ModelChicken":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"head":{"field":"head","tex":[0,0],"pivot":[0,15,-4],"boxes":[[-2,-6,-2,4,6,3,0,[0,0],0]]},"body":{"field":"body","tex":[0,9],"pivot":[0,16,0],"rot":[1.5707963705062866,0,0],"boxes":[[-3,-4,-3,6,8,6,0,[0,9],0]]},"rightLeg":{"field":"rightLeg","tex":[26,0],"pivot":[-2,19,1],"boxes":[[-1,0,-3,3,5,3,0,[26,0],0]]},"leftLeg":{"field":"leftLeg","tex":[26,0],"pivot":[1,19,1],"boxes":[[-1,0,-3,3,5,3,0,[26,0],0]]},"rightWing":{"field":"rightWing","tex":[24,13],"pivot":[-4,13,0],"boxes":[[0,0,-3,1,4,6,0,[24,13],0]]},"leftWing":{"field":"leftWing","tex":[24,13],"pivot":[4,13,0],"boxes":[[-1,0,-3,1,4,6,0,[24,13],0]]},"bill":{"field":"bill","tex":[14,0],"pivot":[0,15,-4],"boxes":[[-2,-4,-4,4,2,2,0,[14,0],0]]},"chin":{"field":"chin","tex":[14,4],"pivot":[0,15,-4],"boxes":[[-1,-2,-3,2,2,2,0,[14,4],0]]}}}}},"drawn":["head","bill","chin","body","rightLeg","leftLeg","rightWing","leftWing"]},"ModelCow":{"super":"ModelQuadruped","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"head":{"field":"head","tex":[22,0],"pivot":[0,4,-8],"boxes":[[-4,-4,-6,8,8,6,0,[0,0],0],[-5,-5,-4,1,3,1,0,[22,0],0],[4,-5,-4,1,3,1,0,[22,0],0]]},"body":{"field":"body","tex":[52,0],"pivot":[0,5,2],"rot":[1.5707963705062866,0,0],"boxes":[[-6,-10,-7,12,18,10,0,[18,4],0],[-2,2,-8,4,6,1,0,[52,0],0]]},"leg1":{"field":"leg1","tex":[0,16],"pivot":[-4,12,7],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"leg2":{"field":"leg2","tex":[0,16],"pivot":[4,12,7],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"leg3":{"field":"leg3","tex":[0,16],"pivot":[-4,12,-6],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"leg4":{"field":"leg4","tex":[0,16],"pivot":[4,12,-6],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"part0":{"tex":[0,0],"pivot":[0,6,-6],"boxes":[[-4,-4,-8,8,8,8,0,[0,0],0]]},"part1":{"tex":[28,8],"pivot":[0,5,2],"boxes":[[-5,-10,-7,10,16,8,0,[28,8],0]]}},"extra":{"field_78145_g":8,"field_78151_h":6}}}},"drawn":["leg1","leg2","leg3","leg4","head","body"]},"ModelCreeper":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"head":{"field":"head","tex":[0,0],"pivot":[0,4,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]},"field_78133_b":{"field":"field_78133_b","tex":[32,0],"pivot":[0,4,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"body":{"field":"body","tex":[16,16],"pivot":[0,4,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"leg1":{"field":"leg1","tex":[0,16],"pivot":[-2,16,4],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]},"leg2":{"field":"leg2","tex":[0,16],"pivot":[2,16,4],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]},"leg3":{"field":"leg3","tex":[0,16],"pivot":[-2,16,-4],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]},"leg4":{"field":"leg4","tex":[0,16],"pivot":[2,16,-4],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]}}}},"(F)V":{"base":{"tw":64,"th":32,"parts":{"head":{"field":"head","tex":[0,0],"pivot":[0,4,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]},"field_78133_b":{"field":"field_78133_b","tex":[32,0],"pivot":[0,4,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"body":{"field":"body","tex":[16,16],"pivot":[0,4,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"leg1":{"field":"leg1","tex":[0,16],"pivot":[-2,16,4],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]},"leg2":{"field":"leg2","tex":[0,16],"pivot":[2,16,4],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]},"leg3":{"field":"leg3","tex":[0,16],"pivot":[-2,16,-4],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]},"leg4":{"field":"leg4","tex":[0,16],"pivot":[2,16,-4],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]}}},"d":[["parts.head.boxes.0.6",0,1],["parts.field_78133_b.boxes.0.6",0,1],["parts.body.boxes.0.6",0,1],["parts.leg1.boxes.0.6",0,1],["parts.leg2.boxes.0.6",0,1],["parts.leg3.boxes.0.6",0,1],["parts.leg4.boxes.0.6",0,1]]}},"drawn":["head","body","leg1","leg2","leg3","leg4"]},"ModelDragon":{"super":"ModelBase","ctors":{"(F)V":{"base":{"tw":256,"th":256,"parts":{"head":{"field":"head","boxName":"head","tex":[112,0],"pivot":[0,0,0],"boxes":[[-6,-1,-24,12,5,16,0,[176,44],0],[-8,-8,-10,16,16,16,0,[112,30],0],[-5,-12,-4,2,4,6,0,[0,0],1],[-5,-3,-22,2,2,4,0,[112,0],1],[3,-12,-4,2,4,6,0,[0,0],0],[3,-3,-22,2,2,4,0,[112,0],0]],"children":["jaw"]},"neck":{"field":"neck","boxName":"neck","tex":[48,0],"pivot":[0,0,0],"boxes":[[-5,-5,-5,10,10,10,0,[192,104],0],[-1,-9,-3,2,4,6,0,[48,0],0]]},"jaw":{"field":"jaw","boxName":"jaw","tex":[176,65],"pivot":[0,4,-8],"boxes":[[-6,0,-16,12,4,16,0,[176,65],0]]},"body":{"field":"body","boxName":"body","tex":[220,53],"pivot":[0,4,8],"boxes":[[-12,0,-16,24,24,64,0,[0,0],0],[-1,-6,-10,2,6,12,0,[220,53],0],[-1,-6,10,2,6,12,0,[220,53],0],[-1,-6,30,2,6,12,0,[220,53],0]]},"rearLeg":{"field":"rearLeg","boxName":"rearleg","tex":[0,0],"pivot":[-16,16,42],"boxes":[[-8,-4,-8,16,32,16,0,[0,0],0]],"children":["rearLegTip"]},"frontLeg":{"field":"frontLeg","boxName":"frontleg","tex":[112,104],"pivot":[-12,20,2],"boxes":[[-4,-4,-4,8,24,8,0,[112,104],0]],"children":["frontLegTip"]},"rearLegTip":{"field":"rearLegTip","boxName":"rearlegtip","tex":[196,0],"pivot":[0,32,-4],"boxes":[[-6,-2,0,12,32,12,0,[196,0],0]],"children":["rearFoot"]},"frontLegTip":{"field":"frontLegTip","boxName":"frontlegtip","tex":[226,138],"pivot":[0,20,-1],"boxes":[[-3,-1,-3,6,24,6,0,[226,138],0]],"children":["frontFoot"]},"rearFoot":{"field":"rearFoot","boxName":"rearfoot","tex":[112,0],"pivot":[0,31,4],"boxes":[[-9,0,-20,18,6,24,0,[112,0],0]]},"frontFoot":{"field":"frontFoot","boxName":"frontfoot","tex":[144,104],"pivot":[0,23,0],"boxes":[[-4,0,-12,8,4,16,0,[144,104],0]]},"wing":{"field":"wing","boxName":"wing","tex":[-56,88],"pivot":[-12,5,2],"boxes":[[-56,-4,-4,56,8,8,0,[112,88],0],[-56,0,2,56,0,56,0,[-56,88],0]],"children":["wingTip"]},"wingTip":{"field":"wingTip","boxName":"wingtip","tex":[-56,144],"pivot":[-56,0,0],"boxes":[[-56,-2,-2,56,4,4,0,[112,136],0],[-56,0,2,56,0,56,0,[-56,144],0]]}},"extra":{"partialTicks":1}}}}},"ModelEnderCrystal":{"super":"ModelBase","ctors":{"(FZ)V":{"base":{"tw":64,"th":32,"parts":{"cube":{"field":"cube","boxName":"cube","tex":[32,0],"pivot":[0,0,0],"boxes":[[-4,-4,-4,8,8,8,0,[32,0],0]]},"glass":{"field":"glass","boxName":"glass","tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-4,-4,8,8,8,0,[0,0],0]]}}}}},"drawn":["glass","cube"]},"ModelEnderman":{"super":"ModelBiped","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"bipedHead":{"field":"bipedHead","tex":[0,0],"pivot":[0,-13,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]},"bipedHeadwear":{"field":"bipedHeadwear","tex":[0,16],"pivot":[0,-13,0],"boxes":[[-4,-8,-4,8,8,8,-0.5,[0,16],0]]},"bipedBody":{"field":"bipedBody","tex":[32,16],"pivot":[0,-14,0],"boxes":[[-4,0,-2,8,12,4,0,[32,16],0]]},"bipedRightArm":{"field":"bipedRightArm","tex":[56,0],"pivot":[-5,-12,0],"rot":[0,0,0.10000000149011612],"boxes":[[-1,-2,-1,2,30,2,0,[56,0],0]]},"bipedLeftArm":{"field":"bipedLeftArm","tex":[56,0],"pivot":[5,-12,0],"rot":[0,0,-0.10000000149011612],"mirror":1,"boxes":[[-1,-2,-1,2,30,2,0,[56,0],1]]},"bipedRightLeg":{"field":"bipedRightLeg","tex":[56,0],"pivot":[-2,-5,0],"boxes":[[-1,0,-1,2,30,2,0,[56,0],0]]},"bipedLeftLeg":{"field":"bipedLeftLeg","tex":[56,0],"pivot":[2,-5,0],"mirror":1,"boxes":[[-1,0,-1,2,30,2,0,[56,0],1]]},"bipedEars":{"field":"bipedEars","tex":[24,0],"pivot":[0,0,0],"boxes":[[-3,-6,-1,6,6,1,0,[24,0],0]]},"bipedCloak":{"field":"bipedCloak","tex":[0,0],"pivot":[0,0,0],"boxes":[[-5,0,-1,10,16,1,0,[0,0],0]]},"part0":{"tex":[32,0],"pivot":[0,-14,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"part1":{"tex":[16,16],"pivot":[0,-14,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"part2":{"tex":[40,16],"pivot":[-5,-12,0],"boxes":[[-3,-2,-2,4,12,4,0,[40,16],0]]},"part3":{"tex":[40,16],"pivot":[5,-12,0],"mirror":1,"boxes":[[-1,-2,-2,4,12,4,0,[40,16],1]]},"part4":{"tex":[0,16],"pivot":[-1.899999976158142,-2,0],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"part5":{"tex":[0,16],"pivot":[1.899999976158142,-2,0],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,16],1]]}}}}},"drawn":["bipedHead","bipedHeadwear","bipedBody","bipedRightArm","bipedLeftArm","bipedRightLeg","bipedLeftLeg"]},"ModelGhast":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"body":{"field":"body","tex":[0,0],"pivot":[0,8,0],"boxes":[[-8,-8,-8,16,16,16,0,[0,0],0]]},"tentacles[0]":{"arrayField":"tentacles","index":0,"length":9,"tex":[0,0],"pivot":[-3.75,15,-5],"rot":[0.4000000059604645,0,0],"boxes":[[-1,0,-1,2,8,2,0,[0,0],0]]},"tentacles[1]":{"arrayField":"tentacles","index":1,"length":9,"tex":[0,0],"pivot":[1.25,15,-5],"rot":[0.5682902932167053,0,0],"boxes":[[-1,0,-1,2,13,2,0,[0,0],0]]},"tentacles[2]":{"arrayField":"tentacles","index":2,"length":9,"tex":[0,0],"pivot":[6.25,15,-5],"rot":[0.5818655490875244,0,0],"boxes":[[-1,0,-1,2,9,2,0,[0,0],0]]},"tentacles[3]":{"arrayField":"tentacles","index":3,"length":9,"tex":[0,0],"pivot":[-6.25,15,0],"rot":[0.4282265603542328,0,0],"boxes":[[-1,0,-1,2,11,2,0,[0,0],0]]},"tentacles[4]":{"arrayField":"tentacles","index":4,"length":9,"tex":[0,0],"pivot":[-1.25,15,0],"rot":[0.24864594638347626,0,0],"boxes":[[-1,0,-1,2,11,2,0,[0,0],0]]},"tentacles[5]":{"arrayField":"tentacles","index":5,"length":9,"tex":[0,0],"pivot":[3.75,15,0],"rot":[0.208210289478302,0,0],"boxes":[[-1,0,-1,2,10,2,0,[0,0],0]]},"tentacles[6]":{"arrayField":"tentacles","index":6,"length":9,"tex":[0,0],"pivot":[-3.75,15,5],"rot":[0.34411191940307617,0,0],"boxes":[[-1,0,-1,2,12,2,0,[0,0],0]]},"tentacles[7]":{"arrayField":"tentacles","index":7,"length":9,"tex":[0,0],"pivot":[1.25,15,5],"rot":[0.5313879251480103,0,0],"boxes":[[-1,0,-1,2,9,2,0,[0,0],0]]},"tentacles[8]":{"arrayField":"tentacles","index":8,"length":9,"tex":[0,0],"pivot":[6.25,15,5],"rot":[0.597871720790863,0,0],"boxes":[[-1,0,-1,2,12,2,0,[0,0],0]]}}}}},"drawn":["body","tentacles[0]","tentacles[1]","tentacles[2]","tentacles[3]","tentacles[4]","tentacles[5]","tentacles[6]","tentacles[7]","tentacles[8]"]},"ModelIronGolem":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"ironGolemHead":{"field":"ironGolemHead","tex":[24,0],"ts":[128,128],"pivot":[0,-7,-2],"boxes":[[-4,-12,-5.5,8,10,8,0,[0,0],0],[-1,-5,-7.5,2,4,2,0,[24,0],0]]},"ironGolemBody":{"field":"ironGolemBody","tex":[0,70],"ts":[128,128],"pivot":[0,-7,0],"boxes":[[-9,-2,-6,18,12,11,0,[0,40],0],[-4.5,10,-3,9,5,6,0.5,[0,70],0]]},"ironGolemRightArm":{"field":"ironGolemRightArm","tex":[60,21],"ts":[128,128],"pivot":[0,-7,0],"boxes":[[-13,-2.5,-3,4,30,6,0,[60,21],0]]},"ironGolemLeftArm":{"field":"ironGolemLeftArm","tex":[60,58],"ts":[128,128],"pivot":[0,-7,0],"boxes":[[9,-2.5,-3,4,30,6,0,[60,58],0]]},"ironGolemLeftLeg":{"field":"ironGolemLeftLeg","tex":[37,0],"ts":[128,128],"pivot":[-4,11,0],"boxes":[[-3.5,-3,-3,6,16,5,0,[37,0],0]]},"ironGolemRightLeg":{"field":"ironGolemRightLeg","tex":[60,0],"ts":[128,128],"pivot":[5,11,0],"mirror":1,"boxes":[[-3.5,-3,-3,6,16,5,0,[60,0],1]]}}}},"(F)V":{"base":{"tw":64,"th":32,"parts":{"ironGolemHead":{"field":"ironGolemHead","tex":[24,0],"ts":[128,128],"pivot":[0,-7,-2],"boxes":[[-4,-12,-5.5,8,10,8,0,[0,0],0],[-1,-5,-7.5,2,4,2,0,[24,0],0]]},"ironGolemBody":{"field":"ironGolemBody","tex":[0,70],"ts":[128,128],"pivot":[0,-7,0],"boxes":[[-9,-2,-6,18,12,11,0,[0,40],0],[-4.5,10,-3,9,5,6,0.5,[0,70],0]]},"ironGolemRightArm":{"field":"ironGolemRightArm","tex":[60,21],"ts":[128,128],"pivot":[0,-7,0],"boxes":[[-13,-2.5,-3,4,30,6,0,[60,21],0]]},"ironGolemLeftArm":{"field":"ironGolemLeftArm","tex":[60,58],"ts":[128,128],"pivot":[0,-7,0],"boxes":[[9,-2.5,-3,4,30,6,0,[60,58],0]]},"ironGolemLeftLeg":{"field":"ironGolemLeftLeg","tex":[37,0],"ts":[128,128],"pivot":[-4,11,0],"boxes":[[-3.5,-3,-3,6,16,5,0,[37,0],0]]},"ironGolemRightLeg":{"field":"ironGolemRightLeg","tex":[60,0],"ts":[128,128],"pivot":[5,11,0],"mirror":1,"boxes":[[-3.5,-3,-3,6,16,5,0,[60,0],1]]}}},"d":[["parts.ironGolemHead.boxes.0.6",0,1],["parts.ironGolemHead.boxes.1.6",0,1],["parts.ironGolemBody.boxes.0.6",0,1],["parts.ironGolemBody.boxes.1.6",0,1],["parts.ironGolemRightArm.boxes.0.6",0,1],["parts.ironGolemLeftArm.boxes.0.6",0,1],["parts.ironGolemLeftLeg.boxes.0.6",0,1],["parts.ironGolemRightLeg.boxes.0.6",0,1]]},"(FF)V":{"base":{"tw":64,"th":32,"parts":{"ironGolemHead":{"field":"ironGolemHead","tex":[24,0],"ts":[128,128],"pivot":[0,0,-2],"boxes":[[-4,-12,-5.5,8,10,8,0,[0,0],0],[-1,-5,-7.5,2,4,2,0,[24,0],0]]},"ironGolemBody":{"field":"ironGolemBody","tex":[0,70],"ts":[128,128],"pivot":[0,0,0],"boxes":[[-9,-2,-6,18,12,11,0,[0,40],0],[-4.5,10,-3,9,5,6,0.5,[0,70],0]]},"ironGolemRightArm":{"field":"ironGolemRightArm","tex":[60,21],"ts":[128,128],"pivot":[0,-7,0],"boxes":[[-13,-2.5,-3,4,30,6,0,[60,21],0]]},"ironGolemLeftArm":{"field":"ironGolemLeftArm","tex":[60,58],"ts":[128,128],"pivot":[0,-7,0],"boxes":[[9,-2.5,-3,4,30,6,0,[60,58],0]]},"ironGolemLeftLeg":{"field":"ironGolemLeftLeg","tex":[37,0],"ts":[128,128],"pivot":[-4,18,0],"boxes":[[-3.5,-3,-3,6,16,5,0,[37,0],0]]},"ironGolemRightLeg":{"field":"ironGolemRightLeg","tex":[60,0],"ts":[128,128],"pivot":[5,18,0],"mirror":1,"boxes":[[-3.5,-3,-3,6,16,5,0,[60,0],1]]}}},"d":[["parts.ironGolemHead.boxes.0.6",0,1],["parts.ironGolemHead.boxes.1.6",0,1],["parts.ironGolemBody.boxes.0.6",0,1],["parts.ironGolemBody.boxes.1.6",0,1],["parts.ironGolemRightArm.boxes.0.6",0,1],["parts.ironGolemLeftArm.boxes.0.6",0,1],["parts.ironGolemLeftLeg.boxes.0.6",0,1],["parts.ironGolemRightLeg.boxes.0.6",0,1],["parts.ironGolemHead.pivot.1",1,1],["parts.ironGolemBody.pivot.1",1,1],["parts.ironGolemLeftLeg.pivot.1",1,1],["parts.ironGolemRightLeg.pivot.1",1,1]]}},"drawn":["ironGolemHead","ironGolemBody","ironGolemRightArm","ironGolemLeftArm","ironGolemLeftLeg","ironGolemRightLeg"]},"ModelLargeChest":{"super":"ModelChest","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"chestLid":{"field":"chestLid","tex":[0,0],"ts":[128,64],"pivot":[1,7,15],"boxes":[[0,-5,-14,30,5,14,0,[0,0],0]]},"chestBelow":{"field":"chestBelow","tex":[0,19],"ts":[128,64],"pivot":[1,6,1],"boxes":[[0,0,0,30,10,14,0,[0,19],0]]},"chestKnob":{"field":"chestKnob","tex":[0,0],"ts":[128,64],"pivot":[16,7,15],"boxes":[[-1,-2,-15,2,4,1,0,[0,0],0]]},"part0":{"tex":[0,0],"ts":[64,64],"pivot":[1,7,15],"boxes":[[0,-5,-14,14,5,14,0,[0,0],0]]},"part1":{"tex":[0,0],"ts":[64,64],"pivot":[8,7,15],"boxes":[[-1,-2,-15,2,4,1,0,[0,0],0]]},"part2":{"tex":[0,19],"ts":[64,64],"pivot":[1,6,1],"boxes":[[0,0,0,14,10,14,0,[0,19],0]]}}}}}},"ModelMagmaCube":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"field_78109_a[0]":{"arrayField":"field_78109_a","index":0,"length":8,"tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,16,-4,8,1,8,0,[0,0],0]]},"field_78109_a[1]":{"arrayField":"field_78109_a","index":1,"length":8,"tex":[0,1],"pivot":[0,0,0],"boxes":[[-4,17,-4,8,1,8,0,[0,1],0]]},"field_78109_a[2]":{"arrayField":"field_78109_a","index":2,"length":8,"tex":[24,10],"pivot":[0,0,0],"boxes":[[-4,18,-4,8,1,8,0,[24,10],0]]},"field_78109_a[3]":{"arrayField":"field_78109_a","index":3,"length":8,"tex":[24,19],"pivot":[0,0,0],"boxes":[[-4,19,-4,8,1,8,0,[24,19],0]]},"field_78109_a[4]":{"arrayField":"field_78109_a","index":4,"length":8,"tex":[0,4],"pivot":[0,0,0],"boxes":[[-4,20,-4,8,1,8,0,[0,4],0]]},"field_78109_a[5]":{"arrayField":"field_78109_a","index":5,"length":8,"tex":[0,5],"pivot":[0,0,0],"boxes":[[-4,21,-4,8,1,8,0,[0,5],0]]},"field_78109_a[6]":{"arrayField":"field_78109_a","index":6,"length":8,"tex":[0,6],"pivot":[0,0,0],"boxes":[[-4,22,-4,8,1,8,0,[0,6],0]]},"field_78109_a[7]":{"arrayField":"field_78109_a","index":7,"length":8,"tex":[0,7],"pivot":[0,0,0],"boxes":[[-4,23,-4,8,1,8,0,[0,7],0]]},"field_78108_b":{"field":"field_78108_b","tex":[0,16],"pivot":[0,0,0],"boxes":[[-2,18,-2,4,4,4,0,[0,16],0]]}}}}},"drawn":["field_78109_a[0]","field_78109_a[1]","field_78109_a[2]","field_78109_a[3]","field_78109_a[4]","field_78109_a[5]","field_78109_a[6]","field_78109_a[7]","field_78108_b"]},"ModelMinecart":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"sideModels[0]":{"arrayField":"sideModels","index":0,"length":7,"tex":[0,10],"pivot":[0,4,0],"rot":[1.5707963705062866,0,0],"boxes":[[-10,-8,-1,20,16,2,0,[0,10],0]]},"sideModels[1]":{"arrayField":"sideModels","index":1,"length":7,"tex":[0,0],"pivot":[-9,4,0],"rot":[0,4.71238899230957,0],"boxes":[[-8,-9,-1,16,8,2,0,[0,0],0]]},"sideModels[2]":{"arrayField":"sideModels","index":2,"length":7,"tex":[0,0],"pivot":[9,4,0],"rot":[0,1.5707963705062866,0],"boxes":[[-8,-9,-1,16,8,2,0,[0,0],0]]},"sideModels[3]":{"arrayField":"sideModels","index":3,"length":7,"tex":[0,0],"pivot":[0,4,-7],"rot":[0,3.1415927410125732,0],"boxes":[[-8,-9,-1,16,8,2,0,[0,0],0]]},"sideModels[4]":{"arrayField":"sideModels","index":4,"length":7,"tex":[0,0],"pivot":[0,4,7],"boxes":[[-8,-9,-1,16,8,2,0,[0,0],0]]},"sideModels[5]":{"arrayField":"sideModels","index":5,"length":7,"tex":[44,10],"pivot":[0,4,0],"rot":[-1.5707963705062866,0,0],"boxes":[[-9,-7,-1,18,14,1,0,[44,10],0]]}}}}},"drawn":["sideModels[0]","sideModels[1]","sideModels[2]","sideModels[3]","sideModels[4]","sideModels[5]"]},"ModelOcelot":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"ocelotBackLeftLeg":{"field":"ocelotBackLeftLeg","tex":[8,13],"pivot":[1.100000023841858,18,5],"boxes":[[-1,0,1,2,6,2,0,[8,13],0]]},"ocelotBackRightLeg":{"field":"ocelotBackRightLeg","tex":[8,13],"pivot":[-1.100000023841858,18,5],"boxes":[[-1,0,1,2,6,2,0,[8,13],0]]},"ocelotFrontLeftLeg":{"field":"ocelotFrontLeftLeg","tex":[40,0],"pivot":[1.2000000476837158,13.800000190734863,-5],"boxes":[[-1,0,0,2,10,2,0,[40,0],0]]},"ocelotFrontRightLeg":{"field":"ocelotFrontRightLeg","tex":[40,0],"pivot":[-1.2000000476837158,13.800000190734863,-5],"boxes":[[-1,0,0,2,10,2,0,[40,0],0]]},"ocelotTail":{"field":"ocelotTail","tex":[0,15],"pivot":[0,15,8],"rot":[0.8999999761581421,0,0],"boxes":[[-0.5,0,0,1,8,1,0,[0,15],0]]},"ocelotTail2":{"field":"ocelotTail2","tex":[4,15],"pivot":[0,20,14],"rot":[1.72787606716156,0,0],"boxes":[[-0.5,0,0,1,8,1,0,[4,15],0]]},"ocelotHead":{"field":"ocelotHead","boxName":"head","tex":[6,10],"pivot":[0,15,-9],"boxes":[[-2.5,-2,-3,5,4,5,0,[0,0],0],[-1.5,0,-4,3,2,2,0,[0,24],0],[-2,-3,0,1,1,2,0,[0,10],0],[1,-3,0,1,1,2,0,[6,10],0]]},"ocelotBody":{"field":"ocelotBody","tex":[20,0],"pivot":[0,12,-10],"rot":[1.5707963705062866,0,0],"boxes":[[-2,3,-8,4,16,6,0,[20,0],0]]}},"extra":{"field_78163_i":1}}}},"drawn":["ocelotHead","ocelotBody","ocelotTail","ocelotTail2","ocelotBackLeftLeg","ocelotBackRightLeg","ocelotFrontLeftLeg","ocelotFrontRightLeg"]},"ModelPig":{"super":"ModelQuadruped","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"head":{"field":"head","tex":[16,16],"pivot":[0,12,-6],"boxes":[[-4,-4,-8,8,8,8,0,[0,0],0],[-2,0,-9,4,3,1,0,[16,16],0]]},"body":{"field":"body","tex":[28,8],"pivot":[0,11,2],"rot":[1.5707963705062866,0,0],"boxes":[[-5,-10,-7,10,16,8,0,[28,8],0]]},"leg1":{"field":"leg1","tex":[0,16],"pivot":[-3,18,7],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]},"leg2":{"field":"leg2","tex":[0,16],"pivot":[3,18,7],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]},"leg3":{"field":"leg3","tex":[0,16],"pivot":[-3,18,-5],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]},"leg4":{"field":"leg4","tex":[0,16],"pivot":[3,18,-5],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]}},"extra":{"field_78145_g":4,"field_78151_h":4}}},"(F)V":{"base":{"tw":64,"th":32,"parts":{"head":{"field":"head","tex":[16,16],"pivot":[0,12,-6],"boxes":[[-4,-4,-8,8,8,8,0,[0,0],0],[-2,0,-9,4,3,1,0,[16,16],0]]},"body":{"field":"body","tex":[28,8],"pivot":[0,11,2],"rot":[1.5707963705062866,0,0],"boxes":[[-5,-10,-7,10,16,8,0,[28,8],0]]},"leg1":{"field":"leg1","tex":[0,16],"pivot":[-3,18,7],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]},"leg2":{"field":"leg2","tex":[0,16],"pivot":[3,18,7],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]},"leg3":{"field":"leg3","tex":[0,16],"pivot":[-3,18,-5],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]},"leg4":{"field":"leg4","tex":[0,16],"pivot":[3,18,-5],"boxes":[[-2,0,-2,4,6,4,0,[0,16],0]]}},"extra":{"field_78145_g":4,"field_78151_h":4}},"d":[["parts.head.boxes.0.6",0,1],["parts.head.boxes.1.6",0,1],["parts.body.boxes.0.6",0,1],["parts.leg1.boxes.0.6",0,1],["parts.leg2.boxes.0.6",0,1],["parts.leg3.boxes.0.6",0,1],["parts.leg4.boxes.0.6",0,1]]}},"drawn":["head","body","leg1","leg2","leg3","leg4"]},"ModelQuadruped":{"super":"ModelBase","ctors":{"(IF)V":{"base":{"tw":64,"th":32,"parts":{"head":{"field":"head","tex":[0,0],"pivot":[0,18,-6],"boxes":[[-4,-4,-8,8,8,8,0,[0,0],0]]},"body":{"field":"body","tex":[28,8],"pivot":[0,17,2],"rot":[1.5707963705062866,0,0],"boxes":[[-5,-10,-7,10,16,8,0,[28,8],0]]},"leg1":{"field":"leg1","tex":[0,16],"pivot":[-3,24,7],"boxes":[[-2,0,-2,4,0,4,0,[0,16],0]]},"leg2":{"field":"leg2","tex":[0,16],"pivot":[3,24,7],"boxes":[[-2,0,-2,4,0,4,0,[0,16],0]]},"leg3":{"field":"leg3","tex":[0,16],"pivot":[-3,24,-5],"boxes":[[-2,0,-2,4,0,4,0,[0,16],0]]},"leg4":{"field":"leg4","tex":[0,16],"pivot":[3,24,-5],"boxes":[[-2,0,-2,4,0,4,0,[0,16],0]]}},"extra":{"field_78145_g":8,"field_78151_h":4}},"d":[["parts.head.pivot.1",0,-1],["parts.body.pivot.1",0,-1],["parts.leg1.pivot.1",0,-1],["parts.leg1.boxes.0.4",0,1],["parts.leg2.pivot.1",0,-1],["parts.leg2.boxes.0.4",0,1],["parts.leg3.pivot.1",0,-1],["parts.leg3.boxes.0.4",0,1],["parts.leg4.pivot.1",0,-1],["parts.leg4.boxes.0.4",0,1],["parts.head.boxes.0.6",1,1],["parts.body.boxes.0.6",1,1],["parts.leg1.boxes.0.6",1,1],["parts.leg2.boxes.0.6",1,1],["parts.leg3.boxes.0.6",1,1],["parts.leg4.boxes.0.6",1,1]]}},"drawn":["head","body","leg1","leg2","leg3","leg4"]},"ModelSheep1":{"super":"ModelQuadruped","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"head":{"field":"head","tex":[0,0],"pivot":[0,6,-8],"boxes":[[-3,-4,-4,6,6,6,0.6000000238418579,[0,0],0]]},"body":{"field":"body","tex":[28,8],"pivot":[0,5,2],"rot":[1.5707963705062866,0,0],"boxes":[[-4,-10,-7,8,16,6,1.75,[28,8],0]]},"leg1":{"field":"leg1","tex":[0,16],"pivot":[-3,12,7],"boxes":[[-2,0,-2,4,6,4,0.5,[0,16],0]]},"leg2":{"field":"leg2","tex":[0,16],"pivot":[3,12,7],"boxes":[[-2,0,-2,4,6,4,0.5,[0,16],0]]},"leg3":{"field":"leg3","tex":[0,16],"pivot":[-3,12,-5],"boxes":[[-2,0,-2,4,6,4,0.5,[0,16],0]]},"leg4":{"field":"leg4","tex":[0,16],"pivot":[3,12,-5],"boxes":[[-2,0,-2,4,6,4,0.5,[0,16],0]]},"part0":{"tex":[0,0],"pivot":[0,6,-6],"boxes":[[-4,-4,-8,8,8,8,0,[0,0],0]]},"part1":{"tex":[28,8],"pivot":[0,5,2],"boxes":[[-5,-10,-7,10,16,8,0,[28,8],0]]},"part2":{"tex":[0,16],"pivot":[-3,12,7],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"part3":{"tex":[0,16],"pivot":[3,12,7],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"part4":{"tex":[0,16],"pivot":[-3,12,-5],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"part5":{"tex":[0,16],"pivot":[3,12,-5],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]}},"extra":{"field_78145_g":8,"field_78151_h":4}}}},"drawn":["head","body","leg1","leg2","leg3","leg4"]},"ModelSheep2":{"super":"ModelQuadruped","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"head":{"field":"head","tex":[0,0],"pivot":[0,6,-8],"boxes":[[-3,-4,-6,6,6,8,0,[0,0],0]]},"body":{"field":"body","tex":[28,8],"pivot":[0,5,2],"rot":[1.5707963705062866,0,0],"boxes":[[-4,-10,-7,8,16,6,0,[28,8],0]]},"leg1":{"field":"leg1","tex":[0,16],"pivot":[-3,12,7],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"leg2":{"field":"leg2","tex":[0,16],"pivot":[3,12,7],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"leg3":{"field":"leg3","tex":[0,16],"pivot":[-3,12,-5],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"leg4":{"field":"leg4","tex":[0,16],"pivot":[3,12,-5],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"part0":{"tex":[0,0],"pivot":[0,6,-6],"boxes":[[-4,-4,-8,8,8,8,0,[0,0],0]]},"part1":{"tex":[28,8],"pivot":[0,5,2],"boxes":[[-5,-10,-7,10,16,8,0,[28,8],0]]}},"extra":{"field_78145_g":8,"field_78151_h":4}}}},"drawn":["leg1","leg2","leg3","leg4","head","body"]},"ModelSign":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"signBoard":{"field":"signBoard","tex":[0,0],"pivot":[0,0,0],"boxes":[[-12,-14,-1,24,12,2,0,[0,0],0]]},"signStick":{"field":"signStick","tex":[0,14],"pivot":[0,0,0],"boxes":[[-1,-2,-1,2,14,2,0,[0,14],0]]}}}}}},"ModelSilverfish":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"silverfishBodyParts[0]":{"arrayField":"silverfishBodyParts","index":0,"length":7,"tex":[0,0],"pivot":[0,22,-3.5],"rot":[0,0.471238911151886,0],"boxes":[[-1.5,0,-1,3,2,2,0,[0,0],0]]},"silverfishBodyParts[1]":{"arrayField":"silverfishBodyParts","index":1,"length":7,"tex":[0,4],"pivot":[0.28523990511894226,21,-1.5],"rot":[0,0.27992069721221924,0],"boxes":[[-2,0,-1,4,3,2,0,[0,4],0]]},"silverfishBodyParts[2]":{"arrayField":"silverfishBodyParts","index":2,"length":7,"tex":[0,9],"pivot":[0,20,1],"rot":[0,0.09233397245407104,0],"boxes":[[-3,0,-1.5,6,4,3,0,[0,9],0]]},"silverfishBodyParts[3]":{"arrayField":"silverfishBodyParts","index":3,"length":7,"tex":[0,16],"pivot":[0.6205772757530212,21,4],"rot":[0,0.04916318878531456,0],"boxes":[[-1.5,0,-1.5,3,3,3,0,[0,16],0]]},"silverfishBodyParts[4]":{"arrayField":"silverfishBodyParts","index":4,"length":7,"tex":[0,22],"pivot":[1.1951626539230347,22,7],"rot":[0,-0.14558644592761993,0],"boxes":[[-1,0,-1.5,2,2,3,0,[0,22],0]]},"silverfishBodyParts[5]":{"arrayField":"silverfishBodyParts","index":5,"length":7,"tex":[11,0],"pivot":[1.3328649997711182,23,9.5],"rot":[0,-0.44428831338882446,0],"boxes":[[-1,0,-1,2,1,2,0,[11,0],0]]},"silverfishBodyParts[6]":{"arrayField":"silverfishBodyParts","index":6,"length":7,"tex":[13,4],"pivot":[0.7766903042793274,23,11.5],"rot":[0,-0.7469534277915955,0],"boxes":[[-0.5,0,-1,1,1,2,0,[13,4],0]]},"silverfishWings[0]":{"arrayField":"silverfishWings","index":0,"length":3,"tex":[20,0],"pivot":[0,16,1],"rot":[0,0.09233397245407104,0],"boxes":[[-5,0,-1.5,10,8,3,0,[20,0],0]]},"silverfishWings[1]":{"arrayField":"silverfishWings","index":1,"length":3,"tex":[20,11],"pivot":[1.1951626539230347,20,7],"rot":[0,-0.14558644592761993,0],"boxes":[[-3,0,-1.5,6,4,3,0,[20,11],0]]},"silverfishWings[2]":{"arrayField":"silverfishWings","index":2,"length":3,"tex":[20,18],"pivot":[0.28523990511894226,19,-1.5],"rot":[0,0.27992069721221924,0],"boxes":[[-3,0,-1.5,6,5,2,0,[20,18],0]]}}}}},"drawn":["silverfishBodyParts[0]","silverfishBodyParts[1]","silverfishBodyParts[2]","silverfishBodyParts[3]","silverfishBodyParts[4]","silverfishBodyParts[5]","silverfishBodyParts[6]","silverfishWings[0]","silverfishWings[1]","silverfishWings[2]"]},"ModelSkeleton":{"super":"ModelZombie","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"bipedHead":{"field":"bipedHead","tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]},"bipedHeadwear":{"field":"bipedHeadwear","tex":[32,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"bipedBody":{"field":"bipedBody","tex":[16,16],"pivot":[0,0,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"bipedRightArm":{"field":"bipedRightArm","tex":[40,16],"pivot":[-5,2,0],"rot":[-1.5707963705062866,-0.10000000149011612,0.10000000149011612],"boxes":[[-1,-2,-1,2,12,2,0,[40,16],0]]},"bipedLeftArm":{"field":"bipedLeftArm","tex":[40,16],"pivot":[5,2,0],"rot":[-1.5707963705062866,0.10000000149011612,-0.10000000149011612],"mirror":1,"boxes":[[-1,-2,-1,2,12,2,0,[40,16],1]]},"bipedRightLeg":{"field":"bipedRightLeg","tex":[0,16],"pivot":[-2,12,0.10000000149011612],"boxes":[[-1,0,-1,2,12,2,0,[0,16],0]]},"bipedLeftLeg":{"field":"bipedLeftLeg","tex":[0,16],"pivot":[2,12,0.10000000149011612],"mirror":1,"boxes":[[-1,0,-1,2,12,2,0,[0,16],1]]},"bipedEars":{"field":"bipedEars","tex":[24,0],"pivot":[0,0,0],"boxes":[[-3,-6,-1,6,6,1,0,[24,0],0]]},"bipedCloak":{"field":"bipedCloak","tex":[0,0],"pivot":[0,0,0],"boxes":[[-5,0,-1,10,16,1,0,[0,0],0]]},"part0":{"tex":[40,16],"pivot":[-5,2,0],"boxes":[[-3,-2,-2,4,12,4,0,[40,16],0]]},"part1":{"tex":[40,16],"pivot":[5,2,0],"mirror":1,"boxes":[[-1,-2,-2,4,12,4,0,[40,16],1]]},"part2":{"tex":[0,16],"pivot":[-1.899999976158142,12,0],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"part3":{"tex":[0,16],"pivot":[1.899999976158142,12,0],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,16],1]]}}}},"(F)V":{"base":{"tw":64,"th":32,"parts":{"bipedHead":{"field":"bipedHead","tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]},"bipedHeadwear":{"field":"bipedHeadwear","tex":[32,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"bipedBody":{"field":"bipedBody","tex":[16,16],"pivot":[0,0,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"bipedRightArm":{"field":"bipedRightArm","tex":[40,16],"pivot":[-5,2,0],"rot":[-1.5707963705062866,-0.10000000149011612,0.10000000149011612],"boxes":[[-1,-2,-1,2,12,2,0,[40,16],0]]},"bipedLeftArm":{"field":"bipedLeftArm","tex":[40,16],"pivot":[5,2,0],"rot":[-1.5707963705062866,0.10000000149011612,-0.10000000149011612],"mirror":1,"boxes":[[-1,-2,-1,2,12,2,0,[40,16],1]]},"bipedRightLeg":{"field":"bipedRightLeg","tex":[0,16],"pivot":[-2,12,0.10000000149011612],"boxes":[[-1,0,-1,2,12,2,0,[0,16],0]]},"bipedLeftLeg":{"field":"bipedLeftLeg","tex":[0,16],"pivot":[2,12,0.10000000149011612],"mirror":1,"boxes":[[-1,0,-1,2,12,2,0,[0,16],1]]},"bipedEars":{"field":"bipedEars","tex":[24,0],"pivot":[0,0,0],"boxes":[[-3,-6,-1,6,6,1,0,[24,0],0]]},"bipedCloak":{"field":"bipedCloak","tex":[0,0],"pivot":[0,0,0],"boxes":[[-5,0,-1,10,16,1,0,[0,0],0]]},"part0":{"tex":[40,16],"pivot":[-5,2,0],"boxes":[[-3,-2,-2,4,12,4,0,[40,16],0]]},"part1":{"tex":[40,16],"pivot":[5,2,0],"mirror":1,"boxes":[[-1,-2,-2,4,12,4,0,[40,16],1]]},"part2":{"tex":[0,16],"pivot":[-1.899999976158142,12,0],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"part3":{"tex":[0,16],"pivot":[1.899999976158142,12,0],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,16],1]]}}},"d":[["parts.bipedHead.boxes.0.6",0,1],["parts.bipedHeadwear.boxes.0.6",0,1],["parts.bipedBody.boxes.0.6",0,1],["parts.bipedRightArm.boxes.0.6",0,1],["parts.bipedLeftArm.boxes.0.6",0,1],["parts.bipedRightLeg.boxes.0.6",0,1],["parts.bipedLeftLeg.boxes.0.6",0,1],["parts.bipedEars.boxes.0.6",0,1],["parts.bipedCloak.boxes.0.6",0,1],["parts.part0.boxes.0.6",0,1],["parts.part1.boxes.0.6",0,1],["parts.part2.boxes.0.6",0,1],["parts.part3.boxes.0.6",0,1]]}},"drawn":["bipedHead","bipedHeadwear","bipedBody","bipedRightArm","bipedLeftArm","bipedRightLeg","bipedLeftLeg"]},"ModelSkeletonHead":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":64,"parts":{"skeletonHead":{"field":"skeletonHead","tex":[0,35],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,35],0]]}}}},"(IIII)V":{"base":{"tw":0,"th":0,"parts":{"skeletonHead":{"field":"skeletonHead","tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]}}},"d":[["parts.skeletonHead.tex.0",0,1],["parts.skeletonHead.boxes.0.7.0",0,1],["parts.skeletonHead.tex.1",1,1],["parts.skeletonHead.boxes.0.7.1",1,1],["tw",2,1],["parts.skeletonHead.ts.0",2,1],["th",3,1],["parts.skeletonHead.ts.1",3,1]]}},"drawn":["skeletonHead"]},"ModelSlime":{"super":"ModelBase","ctors":{"(I)V":{"base":{"tw":64,"th":32,"parts":{"slimeBodies":{"field":"slimeBodies","tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,16,-4,8,8,8,0,[0,0],0]]}}}}},"drawn":["slimeBodies"]},"ModelSnowMan":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"body":{"field":"body","tex":[0,16],"ts":[64,64],"pivot":[0,13,0],"boxes":[[-5,-10,-5,10,10,10,-0.5,[0,16],0]]},"bottomBody":{"field":"bottomBody","tex":[0,36],"ts":[64,64],"pivot":[0,24,0],"boxes":[[-6,-12,-6,12,12,12,-0.5,[0,36],0]]},"head":{"field":"head","tex":[0,0],"ts":[64,64],"pivot":[0,4,0],"boxes":[[-4,-8,-4,8,8,8,-0.5,[0,0],0]]},"rightHand":{"field":"rightHand","tex":[32,0],"ts":[64,64],"pivot":[5,6,0],"rot":[0,0,1],"boxes":[[-1,0,-1,12,2,2,-0.5,[32,0],0]]},"leftHand":{"field":"leftHand","tex":[32,0],"ts":[64,64],"pivot":[-5,6,0],"rot":[0,3.1415927410125732,-1],"boxes":[[-1,0,-1,12,2,2,-0.5,[32,0],0]]}}}}},"drawn":["head","rightHand","leftHand","body","bottomBody"]},"ModelSpider":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"spiderHead":{"field":"spiderHead","tex":[32,4],"pivot":[0,15,-3],"boxes":[[-4,-4,-8,8,8,8,0,[32,4],0]]},"spiderNeck":{"field":"spiderNeck","tex":[0,0],"pivot":[0,15,0],"boxes":[[-3,-3,-3,6,6,6,0,[0,0],0]]},"spiderBody":{"field":"spiderBody","tex":[0,12],"pivot":[0,15,9],"boxes":[[-5,-4,-6,10,8,12,0,[0,12],0]]},"spiderLeg1":{"field":"spiderLeg1","tex":[18,0],"pivot":[-4,15,2],"rot":[0,0.7853981852531433,-0.7853981852531433],"boxes":[[-15,-1,-1,16,2,2,0,[18,0],0]]},"spiderLeg2":{"field":"spiderLeg2","tex":[18,0],"pivot":[4,15,2],"rot":[0,-0.7853981852531433,0.7853981852531433],"boxes":[[-1,-1,-1,16,2,2,0,[18,0],0]]},"spiderLeg3":{"field":"spiderLeg3","tex":[18,0],"pivot":[-4,15,1],"rot":[0,0.39269909262657166,-0.5811946392059326],"boxes":[[-15,-1,-1,16,2,2,0,[18,0],0]]},"spiderLeg4":{"field":"spiderLeg4","tex":[18,0],"pivot":[4,15,1],"rot":[0,-0.39269909262657166,0.5811946392059326],"boxes":[[-1,-1,-1,16,2,2,0,[18,0],0]]},"spiderLeg5":{"field":"spiderLeg5","tex":[18,0],"pivot":[-4,15,0],"rot":[0,-0.39269909262657166,-0.5811946392059326],"boxes":[[-15,-1,-1,16,2,2,0,[18,0],0]]},"spiderLeg6":{"field":"spiderLeg6","tex":[18,0],"pivot":[4,15,0],"rot":[0,0.39269909262657166,0.5811946392059326],"boxes":[[-1,-1,-1,16,2,2,0,[18,0],0]]},"spiderLeg7":{"field":"spiderLeg7","tex":[18,0],"pivot":[-4,15,-1],"rot":[0,-0.7853981852531433,-0.7853981852531433],"boxes":[[-15,-1,-1,16,2,2,0,[18,0],0]]},"spiderLeg8":{"field":"spiderLeg8","tex":[18,0],"pivot":[4,15,-1],"rot":[0,0.7853981852531433,0.7853981852531433],"boxes":[[-1,-1,-1,16,2,2,0,[18,0],0]]}}}}},"drawn":["spiderHead","spiderNeck","spiderBody","spiderLeg1","spiderLeg2","spiderLeg3","spiderLeg4","spiderLeg5","spiderLeg6","spiderLeg7","spiderLeg8"]},"ModelSquid":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"squidBody":{"field":"squidBody","tex":[0,0],"pivot":[0,8,0],"boxes":[[-6,-8,-6,12,16,12,0,[0,0],0]]},"squidTentacles[0]":{"arrayField":"squidTentacles","index":0,"length":8,"tex":[48,0],"pivot":[5,15,0],"rot":[0,1.5707963705062866,0],"boxes":[[-1,0,-1,2,18,2,0,[48,0],0]]},"squidTentacles[1]":{"arrayField":"squidTentacles","index":1,"length":8,"tex":[48,0],"pivot":[3.535533905029297,15,3.535533905029297],"rot":[0,0.7853981852531433,0],"boxes":[[-1,0,-1,2,18,2,0,[48,0],0]]},"squidTentacles[2]":{"arrayField":"squidTentacles","index":2,"length":8,"tex":[48,0],"pivot":[3.0616169991140216e-16,15,5],"boxes":[[-1,0,-1,2,18,2,0,[48,0],0]]},"squidTentacles[3]":{"arrayField":"squidTentacles","index":3,"length":8,"tex":[48,0],"pivot":[-3.535533905029297,15,3.535533905029297],"rot":[0,-0.7853981852531433,0],"boxes":[[-1,0,-1,2,18,2,0,[48,0],0]]},"squidTentacles[4]":{"arrayField":"squidTentacles","index":4,"length":8,"tex":[48,0],"pivot":[-5,15,6.123233998228043e-16],"rot":[0,-1.5707963705062866,0],"boxes":[[-1,0,-1,2,18,2,0,[48,0],0]]},"squidTentacles[5]":{"arrayField":"squidTentacles","index":5,"length":8,"tex":[48,0],"pivot":[-3.535533905029297,15,-3.535533905029297],"rot":[0,-2.356194496154785,0],"boxes":[[-1,0,-1,2,18,2,0,[48,0],0]]},"squidTentacles[6]":{"arrayField":"squidTentacles","index":6,"length":8,"tex":[48,0],"pivot":[-9.184850467946473e-16,15,-5],"rot":[0,-3.1415927410125732,0],"boxes":[[-1,0,-1,2,18,2,0,[48,0],0]]},"squidTentacles[7]":{"arrayField":"squidTentacles","index":7,"length":8,"tex":[48,0],"pivot":[3.535533905029297,15,-3.535533905029297],"rot":[0,-3.9269907474517822,0],"boxes":[[-1,0,-1,2,18,2,0,[48,0],0]]}}}}},"drawn":["squidBody","squidTentacles[0]","squidTentacles[1]","squidTentacles[2]","squidTentacles[3]","squidTentacles[4]","squidTentacles[5]","squidTentacles[6]","squidTentacles[7]"]},"ModelVillager":{"super":"ModelBase","ctors":{"(F)V":{"base":{"tw":64,"th":32,"parts":{"villagerHead":{"field":"villagerHead","tex":[0,0],"ts":[64,64],"pivot":[0,0,0],"boxes":[[-4,-10,-4,8,10,8,0,[0,0],0]],"children":["field_82898_f"]},"villagerBody":{"field":"villagerBody","tex":[0,38],"ts":[64,64],"pivot":[0,0,0],"boxes":[[-4,0,-3,8,12,6,0,[16,20],0],[-4,0,-3,8,18,6,0.5,[0,38],0]]},"villagerArms":{"field":"villagerArms","tex":[40,38],"ts":[64,64],"pivot":[0,3,-1],"rot":[-0.75,0,0],"boxes":[[-8,-2,-2,4,8,4,0,[44,22],0],[4,-2,-2,4,8,4,0,[44,22],0],[-4,2,-2,8,4,4,0,[40,38],0]]},"rightVillagerLeg":{"field":"rightVillagerLeg","tex":[0,22],"ts":[64,64],"pivot":[-2,12,0],"boxes":[[-2,0,-2,4,12,4,0,[0,22],0]]},"leftVillagerLeg":{"field":"leftVillagerLeg","tex":[0,22],"ts":[64,64],"pivot":[2,12,0],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,22],1]]},"field_82898_f":{"field":"field_82898_f","tex":[24,0],"ts":[64,64],"pivot":[0,-2,0],"boxes":[[-1,-1,-6,2,4,2,0,[24,0],0]]}}},"d":[["parts.villagerHead.boxes.0.6",0,1],["parts.villagerBody.boxes.0.6",0,1],["parts.villagerBody.boxes.1.6",0,1],["parts.villagerArms.boxes.0.6",0,1],["parts.villagerArms.boxes.1.6",0,1],["parts.villagerArms.boxes.2.6",0,1],["parts.rightVillagerLeg.boxes.0.6",0,1],["parts.leftVillagerLeg.boxes.0.6",0,1],["parts.field_82898_f.boxes.0.6",0,1]]},"(FFII)V":{"base":{"tw":64,"th":32,"parts":{"villagerHead":{"field":"villagerHead","tex":[0,0],"ts":[0,0],"pivot":[0,0,0],"boxes":[[-4,-10,-4,8,10,8,0,[0,0],0]],"children":["field_82898_f"]},"villagerBody":{"field":"villagerBody","tex":[0,38],"ts":[0,0],"pivot":[0,0,0],"boxes":[[-4,0,-3,8,12,6,0,[16,20],0],[-4,0,-3,8,18,6,0.5,[0,38],0]]},"villagerArms":{"field":"villagerArms","tex":[40,38],"ts":[0,0],"pivot":[0,3,-1],"rot":[-0.75,0,0],"boxes":[[-8,-2,-2,4,8,4,0,[44,22],0],[4,-2,-2,4,8,4,0,[44,22],0],[-4,2,-2,8,4,4,0,[40,38],0]]},"rightVillagerLeg":{"field":"rightVillagerLeg","tex":[0,22],"ts":[0,0],"pivot":[-2,12,0],"boxes":[[-2,0,-2,4,12,4,0,[0,22],0]]},"leftVillagerLeg":{"field":"leftVillagerLeg","tex":[0,22],"ts":[0,0],"pivot":[2,12,0],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,22],1]]},"field_82898_f":{"field":"field_82898_f","tex":[24,0],"ts":[0,0],"pivot":[0,-2,0],"boxes":[[-1,-1,-6,2,4,2,0,[24,0],0]]}}},"d":[["parts.villagerHead.boxes.0.6",0,1],["parts.villagerBody.boxes.0.6",0,1],["parts.villagerBody.boxes.1.6",0,1],["parts.villagerArms.boxes.0.6",0,1],["parts.villagerArms.boxes.1.6",0,1],["parts.villagerArms.boxes.2.6",0,1],["parts.rightVillagerLeg.boxes.0.6",0,1],["parts.leftVillagerLeg.boxes.0.6",0,1],["parts.field_82898_f.boxes.0.6",0,1],["parts.villagerHead.pivot.1",1,1],["parts.villagerBody.pivot.1",1,1],["parts.rightVillagerLeg.pivot.1",1,1],["parts.leftVillagerLeg.pivot.1",1,1],["parts.field_82898_f.pivot.1",1,1],["parts.villagerHead.ts.0",2,1],["parts.villagerBody.ts.0",2,1],["parts.villagerArms.ts.0",2,1],["parts.rightVillagerLeg.ts.0",2,1],["parts.leftVillagerLeg.ts.0",2,1],["parts.field_82898_f.ts.0",2,1],["parts.villagerHead.ts.1",3,1],["parts.villagerBody.ts.1",3,1],["parts.villagerArms.ts.1",3,1],["parts.rightVillagerLeg.ts.1",3,1],["parts.leftVillagerLeg.ts.1",3,1],["parts.field_82898_f.ts.1",3,1]]}},"drawn":["villagerHead","villagerBody","villagerArms","rightVillagerLeg","leftVillagerLeg"]},"ModelWitch":{"super":"ModelVillager","ctors":{"(F)V":{"base":{"tw":64,"th":32,"parts":{"field_82901_h":{"field":"field_82901_h","tex":[0,0],"ts":[64,128],"pivot":[0,-2,0],"boxes":[[0,3,-6.75,1,1,1,-0.25,[0,0],0]]},"witchHat":{"field":"witchHat","tex":[0,64],"ts":[64,128],"pivot":[-5,-10.03125,-5],"boxes":[[0,0,0,10,2,10,0,[0,64],0]],"children":["part0"]},"villagerHead":{"field":"villagerHead","tex":[0,0],"ts":[64,128],"pivot":[0,0,0],"boxes":[[-4,-10,-4,8,10,8,0,[0,0],0]],"children":["field_82898_f","witchHat"]},"villagerBody":{"field":"villagerBody","tex":[0,38],"ts":[64,128],"pivot":[0,0,0],"boxes":[[-4,0,-3,8,12,6,0,[16,20],0],[-4,0,-3,8,18,6,0.5,[0,38],0]]},"villagerArms":{"field":"villagerArms","tex":[40,38],"ts":[64,128],"pivot":[0,3,-1],"rot":[-0.75,0,0],"boxes":[[-8,-2,-2,4,8,4,0,[44,22],0],[4,-2,-2,4,8,4,0,[44,22],0],[-4,2,-2,8,4,4,0,[40,38],0]]},"rightVillagerLeg":{"field":"rightVillagerLeg","tex":[0,22],"ts":[64,128],"pivot":[-2,12,0],"boxes":[[-2,0,-2,4,12,4,0,[0,22],0]]},"leftVillagerLeg":{"field":"leftVillagerLeg","tex":[0,22],"ts":[64,128],"pivot":[2,12,0],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,22],1]]},"field_82898_f":{"field":"field_82898_f","tex":[24,0],"ts":[64,128],"pivot":[0,-2,0],"rot":[0,0,0.04363323375582695],"boxes":[[-1,-1,-6,2,4,2,0,[24,0],0]],"children":["field_82901_h"]},"part0":{"tex":[0,76],"ts":[64,128],"pivot":[1.75,-4,2],"rot":[-0.05235987901687622,0,0.02617993950843811],"boxes":[[0,0,0,7,4,7,0,[0,76],0]],"children":["part1"]},"part1":{"tex":[0,87],"ts":[64,128],"pivot":[1.75,-4,2],"rot":[-0.10471975803375244,0,0.05235987901687622],"boxes":[[0,0,0,4,4,4,0,[0,87],0]],"children":["part2"]},"part2":{"tex":[0,95],"ts":[64,128],"pivot":[1.75,-2,2],"rot":[-0.20943951606750488,0,0.10471975803375244],"boxes":[[0,0,0,1,2,1,0.25,[0,95],0]]}}},"d":[["parts.villagerHead.boxes.0.6",0,1],["parts.villagerBody.boxes.0.6",0,1],["parts.villagerBody.boxes.1.6",0,1],["parts.villagerArms.boxes.0.6",0,1],["parts.villagerArms.boxes.1.6",0,1],["parts.villagerArms.boxes.2.6",0,1],["parts.rightVillagerLeg.boxes.0.6",0,1],["parts.leftVillagerLeg.boxes.0.6",0,1],["parts.field_82898_f.boxes.0.6",0,1]]}},"drawn":["villagerHead","villagerBody","villagerArms","rightVillagerLeg","leftVillagerLeg"]},"ModelWither":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":64,"parts":{"field_82905_a[0]":{"arrayField":"field_82905_a","index":0,"length":3,"tex":[0,16],"pivot":[0,0,0],"boxes":[[-10,3.9000000953674316,-0.5,20,3,3,0,[0,16],0]]},"field_82905_a[1]":{"arrayField":"field_82905_a","index":1,"length":3,"tex":[24,22],"pivot":[-2,6.900000095367432,-0.5],"rot":[0.36128315329551697,0,0],"boxes":[[0,0,0,3,10,3,0,[0,22],0],[-4,1.5,0.5,11,2,2,0,[24,22],0],[-4,4,0.5,11,2,2,0,[24,22],0],[-4,6.5,0.5,11,2,2,0,[24,22],0]]},"field_82905_a[2]":{"arrayField":"field_82905_a","index":2,"length":3,"tex":[12,22],"pivot":[-2,16.254549026489258,3.034461498260498],"rot":[1.146681308746338,0,0],"boxes":[[0,0,0,3,6,3,0,[12,22],0]]},"field_82904_b[0]":{"arrayField":"field_82904_b","index":0,"length":3,"tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-4,-4,8,8,8,0,[0,0],0]]},"field_82904_b[1]":{"arrayField":"field_82904_b","index":1,"length":3,"tex":[32,0],"pivot":[-8,4,0],"boxes":[[-4,-4,-4,6,6,6,0,[32,0],0]]},"field_82904_b[2]":{"arrayField":"field_82904_b","index":2,"length":3,"tex":[32,0],"pivot":[10,4,0],"boxes":[[-4,-4,-4,6,6,6,0,[32,0],0]]}}}}},"drawn":["field_82905_a[0]","field_82905_a[1]","field_82905_a[2]","field_82904_b[0]","field_82904_b[1]","field_82904_b[2]"]},"ModelWolf":{"super":"ModelBase","ctors":{"()V":{"base":{"tw":64,"th":32,"parts":{"wolfHeadMain":{"field":"wolfHeadMain","tex":[0,10],"pivot":[-1,13.5,-7],"boxes":[[-3,-3,-2,6,6,4,0,[0,0],0],[-3,-5,0,2,2,1,0,[16,14],0],[1,-5,0,2,2,1,0,[16,14],0],[-1.5,0,-5,3,3,4,0,[0,10],0]]},"wolfBody":{"field":"wolfBody","tex":[18,14],"pivot":[0,14,2],"rot":[1.5707963705062866,0,0],"boxes":[[-4,-2,-3,6,9,6,0,[18,14],0]]},"wolfLeg1":{"field":"wolfLeg1","tex":[0,18],"pivot":[-2.5,16,7],"boxes":[[-1,0,-1,2,8,2,0,[0,18],0]]},"wolfLeg2":{"field":"wolfLeg2","tex":[0,18],"pivot":[0.5,16,7],"boxes":[[-1,0,-1,2,8,2,0,[0,18],0]]},"wolfLeg3":{"field":"wolfLeg3","tex":[0,18],"pivot":[-2.5,16,-4],"boxes":[[-1,0,-1,2,8,2,0,[0,18],0]]},"wolfLeg4":{"field":"wolfLeg4","tex":[0,18],"pivot":[0.5,16,-4],"boxes":[[-1,0,-1,2,8,2,0,[0,18],0]]},"wolfTail":{"field":"wolfTail","tex":[9,18],"pivot":[-1,12,8],"boxes":[[-1,0,-1,2,8,2,0,[9,18],0]]},"wolfMane":{"field":"wolfMane","tex":[21,0],"pivot":[-1,14,-3],"rot":[1.5707963705062866,0,0],"boxes":[[-4,-3,-3,8,6,7,0,[21,0],0]]}}}}},"drawn":["wolfHeadMain","wolfBody","wolfMane","wolfLeg1","wolfLeg2","wolfLeg3","wolfLeg4","wolfTail"]},"ModelZombie":{"super":"ModelBiped","ctors":{"()V":{"base":{"tw":64,"th":64,"parts":{"bipedHead":{"field":"bipedHead","tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]},"bipedHeadwear":{"field":"bipedHeadwear","tex":[32,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"bipedBody":{"field":"bipedBody","tex":[16,16],"pivot":[0,0,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"bipedRightArm":{"field":"bipedRightArm","tex":[40,16],"pivot":[-5,2,0],"rot":[-1.5707963705062866,-0.10000000149011612,0.10000000149011612],"boxes":[[-3,-2,-2,4,12,4,0,[40,16],0]]},"bipedLeftArm":{"field":"bipedLeftArm","tex":[40,16],"pivot":[5,2,0],"rot":[-1.5707963705062866,0.10000000149011612,-0.10000000149011612],"mirror":1,"boxes":[[-1,-2,-2,4,12,4,0,[40,16],1]]},"bipedRightLeg":{"field":"bipedRightLeg","tex":[0,16],"pivot":[-1.899999976158142,12,0.10000000149011612],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"bipedLeftLeg":{"field":"bipedLeftLeg","tex":[0,16],"pivot":[1.899999976158142,12,0.10000000149011612],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,16],1]]},"bipedEars":{"field":"bipedEars","tex":[24,0],"pivot":[0,0,0],"boxes":[[-3,-6,-1,6,6,1,0,[24,0],0]]},"bipedCloak":{"field":"bipedCloak","tex":[0,0],"pivot":[0,0,0],"boxes":[[-5,0,-1,10,16,1,0,[0,0],0]]}}}},"(FFII)V":{"base":{"tw":0,"th":0,"parts":{"bipedHead":{"field":"bipedHead","tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]},"bipedHeadwear":{"field":"bipedHeadwear","tex":[32,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"bipedBody":{"field":"bipedBody","tex":[16,16],"pivot":[0,0,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"bipedRightArm":{"field":"bipedRightArm","tex":[40,16],"pivot":[-5,2,0],"rot":[-1.5707963705062866,-0.10000000149011612,0.10000000149011612],"boxes":[[-3,-2,-2,4,12,4,0,[40,16],0]]},"bipedLeftArm":{"field":"bipedLeftArm","tex":[40,16],"pivot":[5,2,0],"rot":[-1.5707963705062866,0.10000000149011612,-0.10000000149011612],"mirror":1,"boxes":[[-1,-2,-2,4,12,4,0,[40,16],1]]},"bipedRightLeg":{"field":"bipedRightLeg","tex":[0,16],"pivot":[-1.899999976158142,12,0.10000000149011612],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"bipedLeftLeg":{"field":"bipedLeftLeg","tex":[0,16],"pivot":[1.899999976158142,12,0.10000000149011612],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,16],1]]},"bipedEars":{"field":"bipedEars","tex":[24,0],"pivot":[0,0,0],"boxes":[[-3,-6,-1,6,6,1,0,[24,0],0]]},"bipedCloak":{"field":"bipedCloak","tex":[0,0],"pivot":[0,0,0],"boxes":[[-5,0,-1,10,16,1,0,[0,0],0]]}}},"d":[["parts.bipedHead.boxes.0.6",0,1],["parts.bipedHeadwear.boxes.0.6",0,1],["parts.bipedBody.boxes.0.6",0,1],["parts.bipedRightArm.boxes.0.6",0,1],["parts.bipedLeftArm.boxes.0.6",0,1],["parts.bipedRightLeg.boxes.0.6",0,1],["parts.bipedLeftLeg.boxes.0.6",0,1],["parts.bipedEars.boxes.0.6",0,1],["parts.bipedCloak.boxes.0.6",0,1],["parts.bipedBody.pivot.1",1,1],["parts.bipedRightArm.pivot.1",1,1],["parts.bipedLeftArm.pivot.1",1,1],["tw",2,1],["parts.bipedHead.ts.0",2,1],["parts.bipedHeadwear.ts.0",2,1],["parts.bipedBody.ts.0",2,1],["parts.bipedRightArm.ts.0",2,1],["parts.bipedLeftArm.ts.0",2,1],["parts.bipedRightLeg.ts.0",2,1],["parts.bipedLeftLeg.ts.0",2,1],["parts.bipedEars.ts.0",2,1],["parts.bipedCloak.ts.0",2,1],["th",3,1],["parts.bipedHead.ts.1",3,1],["parts.bipedHeadwear.ts.1",3,1],["parts.bipedBody.ts.1",3,1],["parts.bipedRightArm.ts.1",3,1],["parts.bipedLeftArm.ts.1",3,1],["parts.bipedRightLeg.ts.1",3,1],["parts.bipedLeftLeg.ts.1",3,1],["parts.bipedEars.ts.1",3,1],["parts.bipedCloak.ts.1",3,1]]},"(FZ)V":{"base":{"tw":64,"th":64,"parts":{"bipedHead":{"field":"bipedHead","tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]},"bipedHeadwear":{"field":"bipedHeadwear","tex":[32,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"bipedBody":{"field":"bipedBody","tex":[16,16],"pivot":[0,0,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"bipedRightArm":{"field":"bipedRightArm","tex":[40,16],"pivot":[-5,2,0],"rot":[-1.5707963705062866,-0.10000000149011612,0.10000000149011612],"boxes":[[-3,-2,-2,4,12,4,0,[40,16],0]]},"bipedLeftArm":{"field":"bipedLeftArm","tex":[40,16],"pivot":[5,2,0],"rot":[-1.5707963705062866,0.10000000149011612,-0.10000000149011612],"mirror":1,"boxes":[[-1,-2,-2,4,12,4,0,[40,16],1]]},"bipedRightLeg":{"field":"bipedRightLeg","tex":[0,16],"pivot":[-1.899999976158142,12,0.10000000149011612],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"bipedLeftLeg":{"field":"bipedLeftLeg","tex":[0,16],"pivot":[1.899999976158142,12,0.10000000149011612],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,16],1]]},"bipedEars":{"field":"bipedEars","tex":[24,0],"pivot":[0,0,0],"boxes":[[-3,-6,-1,6,6,1,0,[24,0],0]]},"bipedCloak":{"field":"bipedCloak","tex":[0,0],"pivot":[0,0,0],"boxes":[[-5,0,-1,10,16,1,0,[0,0],0]]}}},"d":[["parts.bipedHead.boxes.0.6",0,1],["parts.bipedHeadwear.boxes.0.6",0,1],["parts.bipedBody.boxes.0.6",0,1],["parts.bipedRightArm.boxes.0.6",0,1],["parts.bipedLeftArm.boxes.0.6",0,1],["parts.bipedRightLeg.boxes.0.6",0,1],["parts.bipedLeftLeg.boxes.0.6",0,1],["parts.bipedEars.boxes.0.6",0,1],["parts.bipedCloak.boxes.0.6",0,1],["th",1,-32],["parts.bipedHead.ts.1",1,-32],["parts.bipedHeadwear.ts.1",1,-32],["parts.bipedBody.ts.1",1,-32],["parts.bipedRightArm.ts.1",1,-32],["parts.bipedLeftArm.ts.1",1,-32],["parts.bipedRightLeg.ts.1",1,-32],["parts.bipedLeftLeg.ts.1",1,-32],["parts.bipedEars.ts.1",1,-32],["parts.bipedCloak.ts.1",1,-32]]}},"drawn":["bipedHead","bipedHeadwear","bipedBody","bipedRightArm","bipedLeftArm","bipedRightLeg","bipedLeftLeg"]},"ModelZombieVillager":{"super":"ModelBiped","ctors":{"()V":{"base":{"tw":64,"th":64,"parts":{"bipedHead":{"field":"bipedHead","tex":[24,32],"pivot":[0,0,0],"boxes":[[-4,-10,-4,8,10,8,0,[0,32],0],[-1,-3,-6,2,4,2,0,[24,32],0]]},"bipedHeadwear":{"field":"bipedHeadwear","tex":[32,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"bipedBody":{"field":"bipedBody","tex":[16,16],"pivot":[0,0,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"bipedRightArm":{"field":"bipedRightArm","tex":[40,16],"pivot":[-5,2,0],"rot":[-1.5707963705062866,-0.10000000149011612,0.10000000149011612],"boxes":[[-3,-2,-2,4,12,4,0,[40,16],0]]},"bipedLeftArm":{"field":"bipedLeftArm","tex":[40,16],"pivot":[5,2,0],"rot":[-1.5707963705062866,0.10000000149011612,-0.10000000149011612],"mirror":1,"boxes":[[-1,-2,-2,4,12,4,0,[40,16],1]]},"bipedRightLeg":{"field":"bipedRightLeg","tex":[0,16],"pivot":[-1.899999976158142,12,0.10000000149011612],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"bipedLeftLeg":{"field":"bipedLeftLeg","tex":[0,16],"pivot":[1.899999976158142,12,0.10000000149011612],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,16],1]]},"bipedEars":{"field":"bipedEars","tex":[24,0],"pivot":[0,0,0],"boxes":[[-3,-6,-1,6,6,1,0,[24,0],0]]},"bipedCloak":{"field":"bipedCloak","tex":[0,0],"pivot":[0,0,0],"boxes":[[-5,0,-1,10,16,1,0,[0,0],0]]},"part0":{"tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]}}}},"(FFZ)V":{"base":{"tw":64,"th":64,"parts":{"bipedHead":{"field":"bipedHead","tex":[24,32],"pivot":[0,0,0],"boxes":[[-4,-10,-4,8,10,8,0,[0,32],0],[-1,-3,-6,2,4,2,0,[24,32],0]]},"bipedHeadwear":{"field":"bipedHeadwear","tex":[32,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0.5,[32,0],0]]},"bipedBody":{"field":"bipedBody","tex":[16,16],"pivot":[0,0,0],"boxes":[[-4,0,-2,8,12,4,0,[16,16],0]]},"bipedRightArm":{"field":"bipedRightArm","tex":[40,16],"pivot":[-5,2,0],"rot":[-1.5707963705062866,-0.10000000149011612,0.10000000149011612],"boxes":[[-3,-2,-2,4,12,4,0,[40,16],0]]},"bipedLeftArm":{"field":"bipedLeftArm","tex":[40,16],"pivot":[5,2,0],"rot":[-1.5707963705062866,0.10000000149011612,-0.10000000149011612],"mirror":1,"boxes":[[-1,-2,-2,4,12,4,0,[40,16],1]]},"bipedRightLeg":{"field":"bipedRightLeg","tex":[0,16],"pivot":[-1.899999976158142,12,0.10000000149011612],"boxes":[[-2,0,-2,4,12,4,0,[0,16],0]]},"bipedLeftLeg":{"field":"bipedLeftLeg","tex":[0,16],"pivot":[1.899999976158142,12,0.10000000149011612],"mirror":1,"boxes":[[-2,0,-2,4,12,4,0,[0,16],1]]},"bipedEars":{"field":"bipedEars","tex":[24,0],"pivot":[0,0,0],"boxes":[[-3,-6,-1,6,6,1,0,[24,0],0]]},"bipedCloak":{"field":"bipedCloak","tex":[0,0],"pivot":[0,0,0],"boxes":[[-5,0,-1,10,16,1,0,[0,0],0]]},"part0":{"tex":[0,0],"pivot":[0,0,0],"boxes":[[-4,-8,-4,8,8,8,0,[0,0],0]]}}}}},"drawn":["bipedHeadwear","bipedBody","bipedRightArm","bipedLeftArm","bipedRightLeg","bipedLeftLeg","bipedHead"]}};

(function () {
'use strict';

var SRC = 'net/minecraft/src/', FML = 'cpw/mods/fml/', FORGE = 'net/minecraftforge/';
var L = function (n) { return 'L' + n + ';'; };
var JObject = JVM.JObject;

function reg(vm) { return JVM.mc152.reg(vm); }
function forge(vm) {
	var r = reg(vm);
	return r.forge || (r.forge = {
		mods: [],
		worldGens: [],
		tickHandlers: [],
		fuel: [], crafting: [], pickup: [], playerTrackers: [], connection: [], guiHandlers: {},
		entities: [],
		spawns: [],
		tileEntities: {},
		renderers: [], commands: [], ores: {}, oreNames: [], harvest: [],
		buses: {},
		markers: {},
	});
}
function op(vm) { var g = vm.game; return g && (g.mode === 'run' || g.mode === 'gen') && g.op ? g.op.apply(null, Array.prototype.slice.call(arguments, 1)) : undefined; }
function str(vm, v) { return vm.toJavaString(v); }
function format(vm, fmt, arr) {
	try { return vm.callStatic('java/lang/String', 'format', '(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;', [String(fmt), arr || vm.newArray('Ljava/lang/Object;', 0)]); }
	catch (e) { return String(fmt); }
}
function enumOf(vm, cname, name) { var c = vm.loadClass(cname); vm.initClass(c); return c.statics[name]; }
function enumSetOf(vm, values) {
	var s = vm.callStatic('java/util/EnumSet', 'noneOf', '(Ljava/lang/Class;)Ljava/util/EnumSet;', [null]);
	values.forEach(function (v) { vm.callVirtual(s, 'add', '(Ljava/lang/Object;)Z', [v]); });
	return s;
}
function listOf(vm, coll) {
	if (!coll) return [];
	var arr = vm.callVirtual(coll, 'toArray', '()[Ljava/lang/Object;', []);
	return arr ? Array.prototype.slice.call(arr.a) : [];
}
var enumSpec = function (names, init, extra) {
	var spec = {
		super: 'java/lang/Enum',
		statics: (function () { var s = { $VALUES: null }; names.forEach(function (n) { s[n] = null; }); return s; })(),
		clinit: function (vm, c) {
			c.$values = names.map(function (n, i) { var o = vm.newObject(c); o.$name = n; o.$ordinal = i; if (init) init(vm, o, n, i); c.statics[n] = o; return o; });
		},
	};
	var cn = null;
	spec.staticMethods = {};
	spec.methods = {};
	spec.$names = names;
	Object.assign(spec, extra || {});
	return spec;
};
function enumStatics(vm, cname) {
	var spec = vm.natives[cname];
	spec.staticMethods = Object.assign({}, spec.staticMethods);
	spec.staticMethods['values()[L' + cname + ';'] = function (vm) { var c = vm.loadClass(cname); vm.initClass(c); return JVM.javaArray(vm, L(cname), c.$values.slice()); };
	spec.staticMethods['valueOf(Ljava/lang/String;)L' + cname + ';'] = function (vm, n, a) {
		var c = vm.loadClass(cname); vm.initClass(c);
		var v = c.$values.filter(function (x) { return x.$name === a[0]; })[0];
		if (!v) vm.throwNew('java/lang/IllegalArgumentException', 'No enum constant ' + cname.replace(/[/]/g, '.') + '.' + a[0]);
		return v;
	};
}
function classAnn(vm, c, type) {
	for (var k = c; k; k = k.superClass) {
		var a = JVM.annotation(vm, JVM.classAnnotations(k), type);
		if (a) return a;
		if (k.spec && k.spec.annotations && k.spec.annotations.indexOf(type) >= 0) return { type: L(type), values: {} };
	}
	return null;
}
function sval(a, name, dflt) { var e = a && a.values[name]; return e && e.v !== undefined ? e.v : dflt; }

function findFieldByNames(vm, cls, names) {
	var map = vm.nameMap;
	for (var i = 0; i < names.length; i++) {
		var n = names[i];
		if (n == null) continue;
		var r = cls.findField(n);
		if (r) return r;
		if (map) {
			var m = map.srg[n];
			if (m && (r = cls.findField(m))) return r;
			for (var k = cls; k; k = k.superClass) {
				var ob = map.rev[k.name];
				var mm = ob !== undefined && map.fld[ob + '.' + n];
				if (mm && (r = cls.findField(mm))) return r;
			}
		}
	}
	return null;
}
function fieldIndex(cls, idx) {
	var names = cls.cf ? cls.cf.fields.map(function (f) { return f.name; }) : Object.keys(cls.fields);
	var n = names[idx];
	return n != null ? { owner: cls, f: cls.fields[n] } : null;
}
function getField(vm, r, obj) { if (r.f.static) { vm.initClass(r.owner); return r.owner.statics[r.f.name]; } return obj ? obj[':' + r.f.name] : null; }
function setField(vm, r, obj, v) { if (r.f.static) { vm.initClass(r.owner); r.owner.statics[r.f.name] = v; } else if (obj) obj[':' + r.f.name] = v; }
JVM.findFieldByNames = findFieldByNames;

var CFG_ALLOWED = /^[A-Za-z0-9._-]*$/;
function cfgState(self) { return self.$cfg || (self.$cfg = { cats: {}, order: [], caseSensitive: false, path: null, children: {} }); }
function newCat(cfg, name, parent) {
	var q = parent ? parent.q + '.' + name : name;
	var c = { name: name, parent: parent, q: q, comment: null, props: {}, children: [] };
	if (parent) parent.children.push(c);
	cfg.cats[q] = c;
	return c;
}
function getCategory(cfg, category) {
	var ret = cfg.cats[category];
	if (ret) return ret;
	if (category.indexOf('.') >= 0) {
		var h = category.split('.'), parent = cfg.cats[h[0]] || newCat(cfg, h[0], null);
		for (var i = 1; i < h.length; i++) {
			var q = parent.q + '.' + h[i];
			ret = cfg.cats[q] || newCat(cfg, h[i], parent);
			parent = ret;
		}
		return ret;
	}
	return newCat(cfg, category, null);
}
function newProp(vm, name, value, values, type, read) {
	var p = vm.newObject(vm.loadClass(FORGE + 'common/Property'));
	p[':name'] = name;
	p.$type = type;
	p.$list = values != null;
	p[':value'] = values != null ? '' : value;
	p[':valueList'] = values != null ? JVM.javaArray(vm, 'Ljava/lang/String;', values) : null;
	p.$wasRead = !!read;
	p.$changed = false;
	return p;
}
function propString(p) { return p[':value'] == null ? '' : String(p[':value']); }
function propList(p) { return p[':valueList'] ? Array.prototype.slice.call(p[':valueList'].a).map(String) : []; }
function javaInt(s) { if (!/^[+-]?\d+$/.test(s)) return null; var n = +s; return n >= -2147483648 && n <= 2147483647 ? n : null; }
function javaDouble(s) { s = String(s).trim(); return /^[+-]?(NaN|Infinity|(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?)[dDfF]?$/.test(s) ? parseFloat(s.replace(/[dDfF]$/, '')) : null; }
function javaBool(s) { return /^(true|false)$/i.test(s); }
function propSet(p, value) { p[':value'] = value; p.$changed = true; }
function cfgGet(vm, self, category, key, dflt, comment, type, isList) {
	var cfg = cfgState(self);
	if (!cfg.caseSensitive) category = category.toLowerCase();
	var cat = getCategory(cfg, category);
	var prop = cat.props[key];
	if (prop) {
		if (prop.$type == null) {
			var np = prop.$list ? newProp(vm, key, null, propList(prop), type) : newProp(vm, key, propString(prop), null, type);
			cat.props[key] = prop = np;
		}
		prop[':comment'] = comment;
		if (prop.$default === undefined) prop.$default = isList ? dflt : dflt;
		prop.$cat = category;
		return prop;
	}
	if (dflt == null) return null;
	prop = isList ? newProp(vm, key, null, dflt, type) : newProp(vm, key, dflt, null, type);
	if (!isList) propSet(prop, dflt);
	cat.props[key] = prop;
	prop[':comment'] = comment;
	prop.$default = dflt;
	prop.$cat = category;
	return prop;
}
function cfgLoad(vm, self) {
	var cfg = cfgState(self), fs = vm.fs, path = cfg.path;
	if (!fs || !path) return;
	var dir = path.lastIndexOf('/') > 0 ? path.substring(0, path.lastIndexOf('/')) : '';
	if (dir) fs.mkdirs(dir);
	var bytes = fs.read(path);
	if (!bytes) { fs.write(path, new Uint8Array(0)); return; }
	var text = new TextDecoder('utf-8').decode(bytes).replace(/^﻿/, '');
	var lines = text.split(/\r\n|\n|\r/);
	var cur = null, type = null, tmp = null, name = null;
	for (var ln = 0; ln < lines.length; ln++) {
		var line = lines[ln];
		if (/^START: "([^"]+)"$/.test(line) || /^END: "([^"]+)"$/.test(line)) continue;
		var ns = -1, ne = -1, skip = false, quoted = false;
		for (var i = 0; i < line.length && !skip; ++i) {
			var ch = line.charAt(i);
			if (/[\p{L}\p{N}]/u.test(ch) || '._-'.indexOf(ch) >= 0 || (quoted && ch !== '"')) { if (ns === -1) ns = i; ne = i; }
			else if (/\s/.test(ch)) {   }
			else switch (ch) {
				case '#': skip = true; continue;
				case '"': if (quoted) quoted = false; if (!quoted && ns === -1) quoted = true; break;
				case '{': {
					name = line.substring(ns, ne + 1);
					var q = cur ? cur.q + '.' + name : name;
					cur = cfg.cats[q] || newCat(cfg, name, cur);
					name = null;
					break;
				}
				case '}': if (!cur) throw new Error('config file corrupt (too many closing braces) at line ' + (ln + 1)); cur = cur.parent; break;
				case '=':
					name = line.substring(ns, ne + 1);
					if (!cur) throw new Error("'" + name + "' has no scope at line " + (ln + 1));
					cur.props[name] = newProp(vm, name, line.substring(i + 1), null, type, true);
					i = line.length;
					break;
				case ':': type = 'SIBD'.indexOf(line.substring(ns, ne + 1).charAt(0)) >= 0 ? line.substring(ns, ne + 1).charAt(0) : null; ns = ne = -1; break;
				case '<':
					if (tmp) throw new Error('malformed list at line ' + (ln + 1));
					name = line.substring(ns, ne + 1);
					tmp = []; skip = true;
					break;
				case '>':
					if (!tmp) throw new Error('malformed list at line ' + (ln + 1));
					cur.props[name] = newProp(vm, name, null, tmp, type, true);
					name = null; tmp = null; type = null;
					break;
				default: throw new Error("unknown character '" + ch + "' at line " + (ln + 1));
			}
		}
		if (quoted) throw new Error('unmatched quote at line ' + (ln + 1));
		else if (tmp && !skip) tmp.push(line.trim());
	}
	Object.keys(cfg.cats).forEach(function (k) { Object.keys(cfg.cats[k].props).forEach(function (p) { cfg.cats[k].props[p].$changed = false; }); });
}
function cfgSave(vm, self) {
	var cfg = cfgState(self), fs = vm.fs;
	if (!fs || !cfg.path) return;
	var NL = '\n', out = [];
	var w = function () { out.push(Array.prototype.join.call(arguments, '') + NL); };
	var pad = function (n) { return new Array(n + 1).join('    '); };
	var quote = function (n) { return CFG_ALLOWED.test(n) ? n : '"' + n + '"'; };
	var sortKeys = function (o) { return Object.keys(o).sort(); };
	var writeCat = function (c, indent) {
		var p0 = pad(indent), p1 = pad(indent + 1), p2 = pad(indent + 2);
		w(p0, '####################');
		w(p0, '# ', c.name);
		if (c.comment != null) { w(p0, '#==================='); String(c.comment).split(/\r?\n/).forEach(function (l) { w(p0, '# ', l); }); }
		w(p0, '####################', NL);
		w(p0, quote(c.name), ' {');
		sortKeys(c.props).forEach(function (k, x) {
			var prop = c.props[k];
			if (prop[':comment'] != null) {
				if (x !== 0) out.push(NL);
				String(prop[':comment']).split(/\r?\n/).forEach(function (l) { w(p1, '# ', l); });
			}
			var pn = quote(prop[':name']);
			if (prop.$list) { w(p1, prop.$type || 'S', ':', pn, ' <'); propList(prop).forEach(function (l) { w(p2, l); }); w(p1, ' >'); }
			else if (prop.$type == null) w(p1, pn, '=', propString(prop));
			else w(p1, prop.$type, ':', pn, '=', propString(prop));
		});
		c.children.slice().sort(function (a, b) { return a.q < b.q ? -1 : a.q > b.q ? 1 : 0; }).forEach(function (ch) { writeCat(ch, indent + 1); });
		w(p0, '}', NL);
	};
	out.push('# Configuration file' + NL + NL);
	sortKeys(cfg.cats).forEach(function (k) { var c = cfg.cats[k]; if (!c.parent) { writeCat(c, 0); out.push(NL); } });
	var dir = cfg.path.lastIndexOf('/') > 0 ? cfg.path.substring(0, cfg.path.lastIndexOf('/')) : '';
	if (dir) fs.mkdirs(dir);
	fs.write(cfg.path, new TextEncoder().encode(out.join('')));
}
function cfgTrack(vm, self) { var f = forge(vm); (f.configs || (f.configs = [])).push({ mod: vm.currentMod, cfg: self }); }
JVM.forgeConfigs = function (vm, modId) {
	var f = vm.mcReg && vm.mcReg.forge;
	return (f && f.configs || []).filter(function (c) { return c.mod === modId; }).map(function (c) {
		var st = cfgState(c.cfg);
		return { path: st.path, cats: Object.keys(st.cats).sort().map(function (q) {
			var cat = st.cats[q];
			return { name: q, comment: cat.comment, props: Object.keys(cat.props).sort().map(function (k) {
				var p = cat.props[k];
				return { key: k, type: p.$type, list: p.$list, value: p.$list ? propList(p) : propString(p), def: p.$default, comment: p[':comment'], id: !!p.$isId };
			}) };
		}) };
	});
};
function cfgBlockId(vm, self, category, key, dflt, comment, lower, upper) {
	var f = forge(vm), prop = cfgGet(vm, self, category, key, '-1', comment, 'I');
	prop.$isId = true;
	if (javaInt(propString(prop)) === null) propSet(prop, '-1');
	var v = javaInt(propString(prop));
	if (v !== -1) { f.markers[v] = true; return prop; }
	var bc = vm.loadClass(SRC + 'Block'); vm.initClass(bc);
	var list = bc.statics.blocksList.a;
	if (dflt < lower) { vm.warnOnce('cfg-low:' + vm.currentMod, 'block id defaults below ' + lower + ' were moved to free ids (as Forge does)'); dflt = upper - 1; }
	if (!list[dflt] && !f.markers[dflt]) { propSet(prop, String(dflt)); f.markers[dflt] = true; return prop; }
	for (var j = upper - 1; j > 0; j--) if (!list[j] && !f.markers[j]) { propSet(prop, String(j)); f.markers[j] = true; return prop; }
	vm.throwNew('java/lang/RuntimeException', 'No more block ids available for ' + key);
}
function cfgItemId(vm, self, category, key, dflt, comment) {
	var f = forge(vm), prop = cfgGet(vm, self, category, key, '-1', comment, 'I');
	prop.$isId = true;
	if (javaInt(propString(prop)) === null) propSet(prop, '-1');
	var v = javaInt(propString(prop)), shift = dflt + 256;
	if (v !== -1) { f.markers[v + 256] = true; return prop; }
	var ic = vm.loadClass(SRC + 'Item'); vm.initClass(ic);
	var list = ic.statics.itemsList.a;
	if (!list[shift] && !f.markers[shift] && shift >= 4096) { propSet(prop, String(dflt)); f.markers[shift] = true; return prop; }
	for (var x = list.length - 1; x >= 256; x--) if (!list[x] && !f.markers[x]) { propSet(prop, String(x - 256)); f.markers[x] = true; return prop; }
	vm.throwNew('java/lang/RuntimeException', 'No more item ids available for ' + key);
}
function dstr(vm, d) { return vm.callStatic('java/lang/Double', 'toString', '(D)Ljava/lang/String;', [d]); }

function installConfig(vm, def) {
	var C = FORGE + 'common/Configuration', P = FORGE + 'common/Property';
	var m = {
		'<init>()V': function () {},
		'<init>(Ljava/io/File;)V': function (vm, self, a) { cfgState(self).path = a[0] ? a[0].$path : null; cfgTrack(vm, self); JVM.run(vm, function () { cfgLoad(vm, self); }); },
		'<init>(Ljava/io/File;Z)V': function (vm, self, a) { var c = cfgState(self); c.path = a[0] ? a[0].$path : null; c.caseSensitive = !!a[1]; cfgTrack(vm, self); JVM.run(vm, function () { cfgLoad(vm, self); }); },
		'load()V': function (vm, self) { try { cfgLoad(vm, self); } catch (e) { if (e instanceof JVM.JavaThrow) throw e; vm.throwNew('java/lang/RuntimeException', e.message); } },
		'save()V': function (vm, self) { cfgSave(vm, self); },
		'hasChanged()Z': function (vm, self) { var c = cfgState(self); return Object.keys(c.cats).some(function (k) { return Object.keys(c.cats[k].props).some(function (p) { return c.cats[k].props[p].$changed; }); }) ? 1 : 0; },
		'hasCategory(Ljava/lang/String;)Z': function (vm, self, a) { return cfgState(self).cats[a[0]] ? 1 : 0; },
		'hasKey(Ljava/lang/String;Ljava/lang/String;)Z': function (vm, self, a) { var c = cfgState(self).cats[a[0]]; return c && c.props[a[1]] ? 1 : 0; },
		'addCustomCategoryComment(Ljava/lang/String;Ljava/lang/String;)V': function (vm, self, a) { var c = cfgState(self); getCategory(c, c.caseSensitive ? a[0] : a[0].toLowerCase()).comment = a[1]; },
		'getCategory(Ljava/lang/String;)Lnet/minecraftforge/common/ConfigCategory;': function (vm, self, a) {
			var cat = getCategory(cfgState(self), a[0]);
			var o = cat.obj || (cat.obj = vm.newObject(vm.loadClass(FORGE + 'common/ConfigCategory')));
			o.$cat = cat;
			return o;
		},
		'getCategoryNames()Ljava/util/Set;': function (vm, self) {
			var s = vm.newObject(vm.loadClass('java/util/TreeSet')); vm.callVirtual(s, '<init>', '()V', []);
			Object.keys(cfgState(self).cats).forEach(function (k) { vm.callVirtual(s, 'add', '(Ljava/lang/Object;)Z', [k]); });
			return s;
		},
	};
	var blk = function (cat, key, d, cmt, lo, hi) { return function (vm, self, a) { return cfgBlockId(vm, self, cat(a), key(a), d(a), cmt(a), lo, hi); }; };
	var A = function (i) { return function (a) { return a[i]; }; }, K = function (v) { return function () { return v; }; };
	m['getBlock(Ljava/lang/String;I)Lnet/minecraftforge/common/Property;'] = blk(K('block'), A(0), A(1), K(null), 256, 4096);
	m['getBlock(Ljava/lang/String;ILjava/lang/String;)Lnet/minecraftforge/common/Property;'] = blk(K('block'), A(0), A(1), A(2), 256, 4096);
	m['getBlock(Ljava/lang/String;Ljava/lang/String;I)Lnet/minecraftforge/common/Property;'] = blk(A(0), A(1), A(2), K(null), 256, 4096);
	m['getBlock(Ljava/lang/String;Ljava/lang/String;ILjava/lang/String;)Lnet/minecraftforge/common/Property;'] = blk(A(0), A(1), A(2), A(3), 256, 4096);
	m['getTerrainBlock(Ljava/lang/String;Ljava/lang/String;ILjava/lang/String;)Lnet/minecraftforge/common/Property;'] = blk(A(0), A(1), A(2), A(3), 0, 256);
	var itm = function (cat, key, d, cmt) { return function (vm, self, a) { return cfgItemId(vm, self, cat(a), key(a), d(a), cmt(a)); }; };
	m['getItem(Ljava/lang/String;I)Lnet/minecraftforge/common/Property;'] = itm(K('item'), A(0), A(1), K(null));
	m['getItem(Ljava/lang/String;ILjava/lang/String;)Lnet/minecraftforge/common/Property;'] = itm(K('item'), A(0), A(1), A(2));
	m['getItem(Ljava/lang/String;Ljava/lang/String;I)Lnet/minecraftforge/common/Property;'] = itm(A(0), A(1), A(2), K(null));
	m['getItem(Ljava/lang/String;Ljava/lang/String;ILjava/lang/String;)Lnet/minecraftforge/common/Property;'] = itm(A(0), A(1), A(2), A(3));
	var PR = 'Lnet/minecraftforge/common/Property;';
	var typed = function (t, conv, check) {
		return function (vm, self, a) {
			var prop = cfgGet(vm, self, a[0], a[1], conv(vm, a[2]), a[3] === undefined ? null : a[3], t);
			if (!check(propString(prop))) propSet(prop, conv(vm, a[2]));
			return prop;
		};
	};
	var I = typed('I', function (vm, v) { return String(v); }, function (s) { return javaInt(s) !== null; });
	var B = typed('B', function (vm, v) { return v ? 'true' : 'false'; }, javaBool);
	var D = typed('D', function (vm, v) { return dstr(vm, v); }, function (s) { return javaDouble(s) !== null; });
	var S = function (vm, self, a) { return cfgGet(vm, self, a[0], a[1], a[2], a[3] === undefined ? null : a[3], 'S'); };
	var list = function (t, conv, check) {
		return function (vm, self, a) {
			var vals = a[2] ? Array.prototype.slice.call(a[2].a).map(function (v) { return conv(vm, v); }) : null;
			var prop = cfgGet(vm, self, a[0], a[1], vals, a[3] === undefined ? null : a[3], t, true);
			if (check && !propList(prop).every(check)) prop[':valueList'] = JVM.javaArray(vm, 'Ljava/lang/String;', vals || []), prop.$changed = true;
			return prop;
		};
	};
	[['I', I], ['Z', B], ['D', D], ['Ljava/lang/String;', S]].forEach(function (p) {
		m['get(Ljava/lang/String;Ljava/lang/String;' + p[0] + ')' + PR] = p[1];
		m['get(Ljava/lang/String;Ljava/lang/String;' + p[0] + 'Ljava/lang/String;)' + PR] = p[1];
	});
	[['[I', list('I', function (vm, v) { return String(v); }, function (s) { return javaInt(s) !== null; })],
	 ['[Z', list('B', function (vm, v) { return v ? 'true' : 'false'; }, javaBool)],
	 ['[D', list('D', dstr, function (s) { return javaDouble(s) !== null; })],
	 ['[Ljava/lang/String;', list('S', function (vm, v) { return String(v); }, null)]].forEach(function (p) {
		m['get(Ljava/lang/String;Ljava/lang/String;' + p[0] + ')' + PR] = p[1];
		m['get(Ljava/lang/String;Ljava/lang/String;' + p[0] + 'Ljava/lang/String;)' + PR] = p[1];
	});
	def(C, { methods: m, statics: { CATEGORY_GENERAL: 'general', CATEGORY_BLOCK: 'block', CATEGORY_ITEM: 'item', ALLOWED_CHARS: '._-', DEFAULT_ENCODING: 'UTF-8', CATEGORY_SPLITTER: '.', NEW_LINE: '\n' } });
	def(FORGE + 'common/ConfigCategory', { methods: {
		'getName()Ljava/lang/String;': function (vm, self) { return self.$cat.name; },
		'getQualifiedName()Ljava/lang/String;': function (vm, self) { return self.$cat.q; },
		'setComment(Ljava/lang/String;)V': function (vm, self, a) { self.$cat.comment = a[0]; },
		'containsKey(Ljava/lang/String;)Z': function (vm, self, a) { return self.$cat.props[a[0]] ? 1 : 0; },
		'get(Ljava/lang/String;)Lnet/minecraftforge/common/Property;': function (vm, self, a) { return self.$cat.props[a[0]] || null; },
		'get(Ljava/lang/Object;)Ljava/lang/Object;': function (vm, self, a) { return self.$cat.props[a[0]] || null; },
		'put(Ljava/lang/String;Lnet/minecraftforge/common/Property;)Lnet/minecraftforge/common/Property;': function (vm, self, a) { var o = self.$cat.props[a[0]] || null; self.$cat.props[a[0]] = a[1]; return o; },
		'remove(Ljava/lang/Object;)Lnet/minecraftforge/common/Property;': function (vm, self, a) { var o = self.$cat.props[a[0]] || null; delete self.$cat.props[a[0]]; return o; },
		'size()I': function (vm, self) { return Object.keys(self.$cat.props).length; },
		'isEmpty()Z': function (vm, self) { return Object.keys(self.$cat.props).length ? 0 : 1; },
		'keySet()Ljava/util/Set;': function (vm, self) { var s = vm.newObject(vm.loadClass('java/util/TreeSet')); vm.callVirtual(s, '<init>', '()V', []); Object.keys(self.$cat.props).forEach(function (k) { vm.callVirtual(s, 'add', '(Ljava/lang/Object;)Z', [k]); }); return s; },
		'values()Ljava/util/Collection;': function (vm, self) { return JVM.newList(vm, Object.keys(self.$cat.props).sort().map(function (k) { return self.$cat.props[k]; })); },
		'isChild()Z': function (vm, self) { return self.$cat.parent ? 1 : 0; },
	} });
	def(P + '$Type', Object.assign(enumSpec(['STRING', 'INTEGER', 'BOOLEAN', 'DOUBLE'], function (vm, o, n) { o.$id = n.charAt(0); }), {}));
	vm.natives[P + '$Type'].methods = {
		'getID()C': function (vm, self) { return self.$id.charCodeAt(0); },
	};
	vm.natives[P + '$Type'].staticMethods = { 'tryParse(C)Lnet/minecraftforge/common/Property$Type;': function (vm, n, a) {
		var c = vm.loadClass(P + '$Type'); vm.initClass(c);
		return c.$values.filter(function (v) { return v.$id.charCodeAt(0) === a[0]; })[0] || null;
	} };
	enumStatics(vm, P + '$Type');
	var typeObj = function (vm, t) { if (!t) return null; var c = vm.loadClass(P + '$Type'); vm.initClass(c); return c.$values.filter(function (v) { return v.$id === t; })[0]; };
	var typeChar = function (o) { return o ? o.$id : null; };
	def(P, { fields: { name: 'Ljava/lang/String;', value: 'Ljava/lang/String;', comment: 'Ljava/lang/String;', valueList: '[Ljava/lang/String;' }, methods: {
		'<init>()V': function (vm, self) { self.$type = null; self.$list = false; },
		'<init>(Ljava/lang/String;Ljava/lang/String;Lnet/minecraftforge/common/Property$Type;)V': function (vm, self, a) { self[':name'] = a[0]; self[':value'] = a[1]; self.$type = typeChar(a[2]); self.$list = false; },
		'<init>(Ljava/lang/String;[Ljava/lang/String;Lnet/minecraftforge/common/Property$Type;)V': function (vm, self, a) { self[':name'] = a[0]; self[':value'] = ''; self[':valueList'] = a[1]; self.$type = typeChar(a[2]); self.$list = true; },
		'getName()Ljava/lang/String;': function (vm, self) { return self[':name']; },
		'setName(Ljava/lang/String;)V': function (vm, self, a) { self[':name'] = a[0]; },
		'getString()Ljava/lang/String;': function (vm, self) { return propString(self); },
		'getInt()I': function (vm, self) { var v = javaInt(propString(self)); return v === null ? -1 : v; },
		'getInt(I)I': function (vm, self, a) { var v = javaInt(propString(self)); return v === null ? a[0] : v; },
		'isIntValue()Z': function (vm, self) { return javaInt(propString(self)) !== null ? 1 : 0; },
		'getBoolean(Z)Z': function (vm, self, a) { var s = propString(self); return javaBool(s) ? (s.toLowerCase() === 'true' ? 1 : 0) : a[0]; },
		'isBooleanValue()Z': function (vm, self) { return javaBool(propString(self)) ? 1 : 0; },
		'getDouble(D)D': function (vm, self, a) { var v = javaDouble(propString(self)); return v === null ? a[0] : v; },
		'isDoubleValue()Z': function (vm, self) { return javaDouble(propString(self)) !== null ? 1 : 0; },
		'getStringList()[Ljava/lang/String;': function (vm, self) { return JVM.javaArray(vm, 'Ljava/lang/String;', propList(self)); },
		'getIntList()[I': function (vm, self) { var v = propList(self).map(javaInt).filter(function (x) { return x !== null; }), r = vm.newArray('I', v.length); v.forEach(function (x, i) { r.a[i] = x; }); return r; },
		'isIntList()Z': function (vm, self) { return propList(self).every(function (s) { return javaInt(s) !== null; }) ? 1 : 0; },
		'getBooleanList()[Z': function (vm, self) { var v = propList(self).filter(javaBool), r = vm.newArray('Z', v.length); v.forEach(function (x, i) { r.a[i] = x.toLowerCase() === 'true' ? 1 : 0; }); return r; },
		'isBooleanList()Z': function (vm, self) { return propList(self).every(javaBool) ? 1 : 0; },
		'getDoubleList()[D': function (vm, self) { var v = propList(self).map(javaDouble).filter(function (x) { return x !== null; }), r = vm.newArray('D', v.length); v.forEach(function (x, i) { r.a[i] = x; }); return r; },
		'isDoubleList()Z': function (vm, self) { return propList(self).every(function (s) { return javaDouble(s) !== null; }) ? 1 : 0; },
		'isList()Z': function (vm, self) { return self.$list ? 1 : 0; },
		'wasRead()Z': function (vm, self) { return self.$wasRead ? 1 : 0; },
		'getType()Lnet/minecraftforge/common/Property$Type;': function (vm, self) { return typeObj(vm, self.$type); },
		'hasChanged()Z': function (vm, self) { return self.$changed ? 1 : 0; },
		'set(Ljava/lang/String;)V': function (vm, self, a) { propSet(self, a[0]); },
		'set([Ljava/lang/String;)V': function (vm, self, a) { self[':valueList'] = a[0]; self.$changed = true; },
		'set(I)V': function (vm, self, a) { propSet(self, String(a[0])); },
		'set(Z)V': function (vm, self, a) { propSet(self, a[0] ? 'true' : 'false'); },
		'set(D)V': function (vm, self, a) { propSet(self, dstr(vm, a[0])); },
		'toString()Ljava/lang/String;': function (vm, self) { return propString(self); },
	} });
}

var PRIORITIES = ['HIGHEST', 'HIGH', 'NORMAL', 'LOW', 'LOWEST'];
function busObj(vm, name) {
	var f = forge(vm);
	if (f.buses[name]) return f.buses[name];
	var b = vm.newObject(vm.loadClass(FORGE + 'event/EventBus'));
	b.$listeners = [];
	b.$name = name;
	return (f.buses[name] = b);
}
function eventCancelable(vm, e) { return !!classAnn(vm, e.cls, FORGE + 'event/Cancelable'); }
function eventHasResult(vm, e) { return !!classAnn(vm, e.cls, FORGE + 'event/Event$HasResult'); }
function busRegister(vm, bus, target) {
	if (!target) return;
	var seen = {};
	for (var c = vm.classOf(target); c; c = c.superClass) {
		Object.keys(c.methods).forEach(function (k) {
			var m = c.methods[k];
			if (seen[k] || m.isStatic || m.sig.args.length !== 1) return;
			var a = JVM.annotation(vm, m.annotations, FORGE + 'event/ForgeSubscribe');
			if (!a) return;
			seen[k] = true;
			var pr = a.values.priority ? a.values.priority.name : 'NORMAL';
			var rc = a.values.receiveCanceled ? !!a.values.receiveCanceled.v : false;
			bus.$listeners.push({ target: target, m: m, type: JVM.reflect.typeClass(vm, m.sig.args[0]), pri: Math.max(0, PRIORITIES.indexOf(pr)), rc: rc, seq: bus.$listeners.length });
		});
	}
}
function busPost(vm, bus, ev) {
	if (!ev) return 0;
	var ec = vm.classOf(ev);
	var ls = bus.$listeners.filter(function (l) { return ec.isSubclassOf(l.type) && !l.type.absent; });
	ls.sort(function (a, b) { return a.pri - b.pri || a.seq - b.seq; });
	ls.forEach(function (l) {
		if (ev.$canceled && !l.rc) return;
		if (l.m.cls.source) vm.currentMod = l.m.cls.source;
		var t = l.m.cls.findMethod && vm.classOf(l.target).findMethod(l.m.key) || l.m;
		vm.invoke(t, l.target, [ev]);
	});
	return ev.$canceled ? 1 : 0;
}
JVM.forgePost = function (vm, cname, fill, busName) {
	var f = vm.mcReg && vm.mcReg.forge;
	if (!f || !f.buses[busName || 'EVENT_BUS'] || !f.buses[busName || 'EVENT_BUS'].$listeners.length) return null;
	var bus = f.buses[busName || 'EVENT_BUS'], ev = null;
	JVM.run(vm, function () {
		ev = vm.newObject(vm.loadClass(cname));
		ev.$result = enumOf(vm, FORGE + 'event/Event$Result', 'DEFAULT');
		if (fill) fill(ev);
		busPost(vm, bus, ev);
	});
	return ev;
};

function installEvents(vm, def) {
	def(FORGE + 'event/EventBus', { methods: {
		'<init>()V': function (vm, self) { self.$listeners = []; },
		'register(Ljava/lang/Object;)V': function (vm, self, a) { busRegister(vm, self, a[0]); },
		'unregister(Ljava/lang/Object;)V': function (vm, self, a) { self.$listeners = self.$listeners.filter(function (l) { return l.target !== a[0]; }); },
		'post(Lnet/minecraftforge/event/Event;)Z': function (vm, self, a) { return busPost(vm, self, a[0]); },
	} });
	def(FORGE + 'event/Event$Result', enumSpec(['DENY', 'DEFAULT', 'ALLOW']));
	enumStatics(vm, FORGE + 'event/Event$Result');
	def(FORGE + 'event/EventPriority', enumSpec(PRIORITIES));
	enumStatics(vm, FORGE + 'event/EventPriority');
	def(FORGE + 'event/Event', { methods: {
		'<init>()V': function (vm, self) { self.$result = enumOf(vm, FORGE + 'event/Event$Result', 'DEFAULT'); },
		'isCancelable()Z': function (vm, self) { return eventCancelable(vm, self) ? 1 : 0; },
		'isCanceled()Z': function (vm, self) { return self.$canceled ? 1 : 0; },
		'setCanceled(Z)V': function (vm, self, a) {
			if (!eventCancelable(vm, self)) vm.throwNew('java/lang/IllegalArgumentException', 'Attempted to cancel a uncancelable event');
			self.$canceled = !!a[0];
		},
		'hasResult()Z': function (vm, self) { return eventHasResult(vm, self) ? 1 : 0; },
		'getResult()Lnet/minecraftforge/event/Event$Result;': function (vm, self) { return self.$result || enumOf(vm, FORGE + 'event/Event$Result', 'DEFAULT'); },
		'setResult(Lnet/minecraftforge/event/Event$Result;)V': function (vm, self, a) { self.$result = a[0]; },
		'getListenerList()Lnet/minecraftforge/event/ListenerList;': function () { return null; },
		'setup()V': function () {},
	} });
	var ev = function (name, sup, fields, ctor, cancelable, extra) {
		var methods = {};
		if (ctor) methods[ctor.desc] = function (vm, self, a) {
			self.$result = enumOf(vm, FORGE + 'event/Event$Result', 'DEFAULT');
			ctor.set(self, a, vm);
		};
		def(FORGE + name, Object.assign({ super: FORGE + sup, fields: fields || {}, methods: Object.assign(methods, extra || {}), annotations: cancelable ? [FORGE + 'event/Cancelable'] : [] }));
	};
	var W = SRC + 'World', EP = SRC + 'EntityPlayer', E = SRC + 'Entity', EL = SRC + 'EntityLiving', IS = SRC + 'ItemStack';
	ev('event/world/WorldEvent', 'event/Event', { world: L(W) }, { desc: '<init>(Lnet/minecraft/src/World;)V', set: function (s, a) { s[':world'] = a[0]; } });
	['Load', 'Unload', 'Save'].forEach(function (k) { ev('event/world/WorldEvent$' + k, 'event/world/WorldEvent', {}, { desc: '<init>(Lnet/minecraft/src/World;)V', set: function (s, a) { s[':world'] = a[0]; } }); });
	ev('event/entity/EntityEvent', 'event/Event', { entity: L(E) }, { desc: '<init>(Lnet/minecraft/src/Entity;)V', set: function (s, a) { s[':entity'] = a[0]; } });
	ev('event/entity/living/LivingEvent', 'event/entity/EntityEvent', { entityLiving: L(EL) }, { desc: '<init>(Lnet/minecraft/src/EntityLiving;)V', set: function (s, a) { s[':entity'] = a[0]; s[':entityLiving'] = a[0]; } });
	ev('event/entity/player/PlayerEvent', 'event/entity/living/LivingEvent', { entityPlayer: L(EP) }, { desc: '<init>(Lnet/minecraft/src/EntityPlayer;)V', set: function (s, a) { s[':entity'] = s[':entityLiving'] = s[':entityPlayer'] = a[0]; } });
	var pl = function (s, a) { s[':entity'] = s[':entityLiving'] = s[':entityPlayer'] = a[0]; };
	ev('event/entity/player/PlayerEvent$BreakSpeed', 'event/entity/player/PlayerEvent', { block: L(SRC + 'Block'), metadata: 'I', originalSpeed: 'F', newSpeed: 'F' },
		{ desc: '<init>(Lnet/minecraft/src/EntityPlayer;Lnet/minecraft/src/Block;IF)V', set: function (s, a) { pl(s, a); s[':block'] = a[1]; s[':metadata'] = a[2]; s[':originalSpeed'] = a[3]; s[':newSpeed'] = a[3]; } }, true);
	ev('event/entity/player/PlayerEvent$HarvestCheck', 'event/entity/player/PlayerEvent', { block: L(SRC + 'Block'), success: 'Z' },
		{ desc: '<init>(Lnet/minecraft/src/EntityPlayer;Lnet/minecraft/src/Block;Z)V', set: function (s, a) { pl(s, a); s[':block'] = a[1]; s[':success'] = a[2]; } });
	ev('event/entity/player/UseHoeEvent', 'event/entity/player/PlayerEvent', { current: L(IS), world: L(W), x: 'I', y: 'I', z: 'I' },
		{ desc: '<init>(Lnet/minecraft/src/EntityPlayer;Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/World;III)V', set: function (s, a) { pl(s, a); s[':current'] = a[1]; s[':world'] = a[2]; s[':x'] = a[3]; s[':y'] = a[4]; s[':z'] = a[5]; } }, true);
	ev('event/entity/player/BonemealEvent', 'event/entity/player/PlayerEvent', { world: L(W), ID: 'I', X: 'I', Y: 'I', Z: 'I' },
		{ desc: '<init>(Lnet/minecraft/src/EntityPlayer;Lnet/minecraft/src/World;IIII)V', set: function (s, a) { pl(s, a); s[':world'] = a[1]; s[':ID'] = a[2]; s[':X'] = a[3]; s[':Y'] = a[4]; s[':Z'] = a[5]; } }, true);
	def(FORGE + 'event/entity/player/PlayerInteractEvent$Action', enumSpec(['RIGHT_CLICK_AIR', 'RIGHT_CLICK_BLOCK', 'LEFT_CLICK_BLOCK']));
	enumStatics(vm, FORGE + 'event/entity/player/PlayerInteractEvent$Action');
	ev('event/entity/player/PlayerInteractEvent', 'event/entity/player/PlayerEvent', { action: L(FORGE + 'event/entity/player/PlayerInteractEvent$Action'), x: 'I', y: 'I', z: 'I', face: 'I', useBlock: L(FORGE + 'event/Event$Result'), useItem: L(FORGE + 'event/Event$Result') },
		{ desc: '<init>(Lnet/minecraft/src/EntityPlayer;Lnet/minecraftforge/event/entity/player/PlayerInteractEvent$Action;IIII)V', set: function (s, a, vm) {
			pl(s, a); s[':action'] = a[1]; s[':x'] = a[2]; s[':y'] = a[3]; s[':z'] = a[4]; s[':face'] = a[5];
			s[':useBlock'] = s[':useItem'] = enumOf(vm, FORGE + 'event/Event$Result', 'DEFAULT');
		} }, true);
	ev('event/entity/item/ItemEvent', 'event/entity/EntityEvent', { entityItem: L(SRC + 'EntityItem') }, null);
	ev('event/entity/player/EntityItemPickupEvent', 'event/entity/player/PlayerEvent', { item: L(SRC + 'EntityItem') }, null, true);
	ev('event/entity/EntityJoinWorldEvent', 'event/entity/EntityEvent', { world: L(W) }, { desc: '<init>(Lnet/minecraft/src/Entity;Lnet/minecraft/src/World;)V', set: function (s, a) { s[':entity'] = a[0]; s[':world'] = a[1]; } }, true);
	ev('event/terraingen/PopulateChunkEvent', 'event/Event', { chunkProvider: L(SRC + 'IChunkProvider'), world: L(W), rand: 'Ljava/util/Random;', chunkX: 'I', chunkZ: 'I', hasVillageGenerated: 'Z' }, null);
	['Pre', 'Post'].forEach(function (k) { ev('event/terraingen/PopulateChunkEvent$' + k, 'event/terraingen/PopulateChunkEvent', {}, null); });
	ev('client/event/TextureStitchEvent', 'event/Event', { map: L(SRC + 'TextureMap') }, null);
	['Pre', 'Post'].forEach(function (k) { ev('client/event/TextureStitchEvent$' + k, 'client/event/TextureStitchEvent', {}, null); });
	ev('client/event/sound/SoundLoadEvent', 'event/Event', { manager: L(SRC + 'SoundManager') }, null);
}

function containerObj(vm, mod) {
	if (mod.container) return mod.container;
	var c = vm.newObject(vm.loadClass(FML + 'common/FMLModContainer'));
	c.$mod = mod;
	var md = vm.newObject(vm.loadClass(FML + 'common/ModMetadata'));
	md[':modId'] = mod.id; md[':name'] = mod.name; md[':version'] = mod.version;
	md[':description'] = mod.info && mod.info.description || ''; md[':url'] = mod.info && mod.info.url || '';
	md[':credits'] = mod.info && mod.info.credits || '';
	md[':authorList'] = JVM.newList(vm, (mod.info && mod.info.authors || mod.info && mod.info.authorList || []).map(String));
	md[':autogenerated'] = mod.info ? 0 : 1;
	c.$md = md;
	return (mod.container = c);
}
function modById(vm, id) { return forge(vm).mods.filter(function (m) { return m.id === id; })[0] || null; }
function activeMod(vm) { var f = forge(vm); return f.active || f.mods[f.mods.length - 1] || null; }
function sideObj(vm, n) { return enumOf(vm, FML + 'relauncher/Side', n); }
function effectiveSide(vm) { var g = vm.game; return sideObj(vm, g && (g.mode === 'run' || g.mode === 'gen') ? 'SERVER' : 'CLIENT'); }

function installFml(vm, def) {
	var C = FML + 'common/';
	var ANN = JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC | 0x2000;
	['Mod', 'Mod$Init', 'Mod$PreInit', 'Mod$PostInit', 'Mod$Instance', 'Mod$Metadata', 'Mod$EventHandler', 'Mod$ServerStarting',
	 'Mod$ServerStarted', 'Mod$ServerStopping', 'Mod$ServerStopped', 'Mod$ServerAboutToStart', 'Mod$IMCCallback', 'Mod$FingerprintWarning',
	 'Mod$Block', 'Mod$Item', 'SidedProxy', 'network/NetworkMod', 'network/NetworkMod$SidedPacketHandler', 'network/NetworkMod$VersionCheckHandler',
	 'network/NetworkMod$NULL'].forEach(function (n) { def(C + n, { access: ANN, interfaces: ['java/lang/annotation/Annotation'] }); });
	[FML + 'relauncher/SideOnly', FORGE + 'event/ForgeSubscribe', FORGE + 'event/Cancelable', FORGE + 'event/Event$HasResult'].forEach(function (n) { def(n, { access: ANN, interfaces: ['java/lang/annotation/Annotation'] }); });
	var IFACE = JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC;
	['ITickHandler', 'IScheduledTickHandler', 'IWorldGenerator', 'IFuelHandler', 'ICraftingHandler', 'IPickupNotifier', 'IPlayerTracker',
	 'IDispenserHandler', 'ICrashCallable', 'network/IConnectionHandler', 'network/IPacketHandler', 'network/IGuiHandler', 'network/IChatListener',
	 'network/Player', 'registry/IEntityAdditionalSpawnData', 'registry/IThrowableEntity'].forEach(function (n) { def(C + n, { access: IFACE, interfaces: n === 'IScheduledTickHandler' ? [C + 'ITickHandler'] : [] }); });
	def(FML + 'relauncher/Side', enumSpec(['CLIENT', 'SERVER', 'BUKKIT'], null, {}));
	vm.natives[FML + 'relauncher/Side'].methods = {
		'isClient()Z': function (vm, self) { return self.$name === 'CLIENT' ? 1 : 0; },
		'isServer()Z': function (vm, self) { return self.$name !== 'CLIENT' ? 1 : 0; },
	};
	enumStatics(vm, FML + 'relauncher/Side');
	def(C + 'TickType', enumSpec(['WORLD', 'RENDER', 'GUI', 'CLIENTGUI', 'WORLDLOAD', 'CLIENT', 'PLAYER', 'SERVER']));
	vm.natives[C + 'TickType'].methods = { 'partnerTicks()Ljava/util/EnumSet;': function (vm, self) {
		var P = { CLIENT: 'RENDER', RENDER: 'CLIENT', GUI: 'CLIENTGUI', CLIENTGUI: 'GUI' }[self.$name];
		return enumSetOf(vm, P ? [enumOf(vm, C + 'TickType', P)] : []);
	} };
	enumStatics(vm, C + 'TickType');
	def(C + 'LoaderState', enumSpec(['NOINIT', 'LOADING', 'CONSTRUCTING', 'PREINITIALIZATION', 'INITIALIZATION', 'POSTINITIALIZATION', 'AVAILABLE', 'SERVER_ABOUT_TO_START', 'SERVER_STARTING', 'SERVER_STARTED', 'SERVER_STOPPING', 'SERVER_STOPPED', 'ERRORED']));
	enumStatics(vm, C + 'LoaderState');

	var logAt = function (vm, level, text) { var lv = level && level.$name || String(level || ''); vm.log(/SEVERE|WARNING/.test(lv) ? 'warn' : 'out', text); };
	var lvlStatic = function (lv) { return function (vm, n, a) { logAt(vm, { $name: lv }, format(vm, a[0], a[1])); }; };
	def(C + 'FMLLog', { staticMethods: {
		'log(Ljava/lang/String;Ljava/util/logging/Level;Ljava/lang/String;[Ljava/lang/Object;)V': function (vm, n, a) { logAt(vm, a[1], '[' + a[0] + '] ' + format(vm, a[2], a[3])); },
		'log(Ljava/util/logging/Level;Ljava/lang/String;[Ljava/lang/Object;)V': function (vm, n, a) { logAt(vm, a[0], format(vm, a[1], a[2])); },
		'log(Ljava/lang/String;Ljava/util/logging/Level;Ljava/lang/Throwable;Ljava/lang/String;[Ljava/lang/Object;)V': function (vm, n, a) { logAt(vm, a[1], '[' + a[0] + '] ' + format(vm, a[3], a[4]) + ' (' + JVM.describeThrowable(a[2]) + ')'); },
		'log(Ljava/util/logging/Level;Ljava/lang/Throwable;Ljava/lang/String;[Ljava/lang/Object;)V': function (vm, n, a) { logAt(vm, a[0], format(vm, a[2], a[3]) + ' (' + JVM.describeThrowable(a[1]) + ')'); },
		'severe(Ljava/lang/String;[Ljava/lang/Object;)V': lvlStatic('SEVERE'),
		'warning(Ljava/lang/String;[Ljava/lang/Object;)V': lvlStatic('WARNING'),
		'info(Ljava/lang/String;[Ljava/lang/Object;)V': lvlStatic('INFO'),
		'fine(Ljava/lang/String;[Ljava/lang/Object;)V': lvlStatic('FINE'),
		'finer(Ljava/lang/String;[Ljava/lang/Object;)V': lvlStatic('FINER'),
		'finest(Ljava/lang/String;[Ljava/lang/Object;)V': lvlStatic('FINEST'),
		'getLogger()Ljava/util/logging/Logger;': function (vm) { return vm.callStatic('java/util/logging/Logger', 'getLogger', '(Ljava/lang/String;)Ljava/util/logging/Logger;', ['FML']); },
		'makeLog(Ljava/lang/String;)V': function () {},
	} });

	def(C + 'ModContainer', { access: JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC });
	def(C + 'ModMetadata', { fields: { modId: 'Ljava/lang/String;', name: 'Ljava/lang/String;', version: 'Ljava/lang/String;', description: 'Ljava/lang/String;', url: 'Ljava/lang/String;', credits: 'Ljava/lang/String;', authorList: 'Ljava/util/List;', autogenerated: 'Z', logoFile: 'Ljava/lang/String;', updateUrl: 'Ljava/lang/String;', parent: 'Ljava/lang/String;' }, methods: {
		'<init>()V': function () {},
		'getAuthorList()Ljava/lang/String;': function (vm, self) { return listOf(vm, self[':authorList']).join(', '); },
		'getChildModList()Ljava/lang/String;': function () { return ''; },
		'printableSortingRules()Ljava/lang/String;': function () { return ''; },
	} });
	var mc = function (f) { return function (vm, self) { return f(self.$mod, vm, self); }; };
	def(C + 'FMLModContainer', { interfaces: [C + 'ModContainer'], methods: {
		'getModId()Ljava/lang/String;': mc(function (m) { return m.id; }),
		'getName()Ljava/lang/String;': mc(function (m) { return m.name; }),
		'getVersion()Ljava/lang/String;': mc(function (m) { return m.version; }),
		'getDisplayVersion()Ljava/lang/String;': mc(function (m) { return m.version; }),
		'getMod()Ljava/lang/Object;': mc(function (m) { return m.instance; }),
		'getMetadata()Lcpw/mods/fml/common/ModMetadata;': mc(function (m, vm, self) { return self.$md; }),
		'getSource()Ljava/io/File;': mc(function (m, vm) { return JVM.fileObj(vm, 'mods/' + m.id + '.jar'); }),
		'getSortingRules()Ljava/lang/String;': function () { return ''; },
		'matches(Ljava/lang/Object;)Z': mc(function (m, vm, self) { return 0; }),
		'toString()Ljava/lang/String;': mc(function (m) { return m.id; }),
		'isImmutable()Z': function () { return 0; },
		'isNetworkMod()Z': function () { return 1; },
		'getRequirements()Ljava/util/Set;': function (vm) { return vm.callStatic('java/util/Collections', 'emptySet', '()Ljava/util/Set;', []); },
		'getDependencies()Ljava/util/List;': function (vm) { return JVM.newList(vm, []); },
		'getDependants()Ljava/util/List;': function (vm) { return JVM.newList(vm, []); },
	} });
	def(C + 'DummyModContainer', { super: C + 'FMLModContainer', methods: {} });
	def(C + 'MinecraftDummyContainer', { super: C + 'FMLModContainer', methods: {
		'getVersion()Ljava/lang/String;': function () { return '1.5.2'; },
		'getModId()Ljava/lang/String;': function () { return 'Minecraft'; },
		'getName()Ljava/lang/String;': function () { return 'Minecraft'; },
	} });
	var loaderObj = function (vm) { var f = forge(vm); return f.loader || (f.loader = vm.newObject(vm.loadClass(C + 'Loader'))); };
	var mcContainer = function (vm) { var f = forge(vm); if (!f.mcCont) { f.mcCont = vm.newObject(vm.loadClass(C + 'MinecraftDummyContainer')); f.mcCont.$mod = { id: 'Minecraft', name: 'Minecraft', version: '1.5.2' }; } return f.mcCont; };
	var isLoaded = function (vm, id) {
		if (id === 'Forge' || id === 'FML' || id === 'mcp' || id === 'Minecraft') return 1;
		if (modById(vm, id)) return 1;
		return reg(vm).mods.some(function (m) { return m.cls.name === id || m.cls.name.replace(/^mod_/, '') === id; }) ? 1 : 0;
	};
	def(C + 'Loader', { methods: {
		'getModList()Ljava/util/List;': function (vm) { return JVM.newList(vm, forge(vm).mods.map(function (m) { return containerObj(vm, m); })); },
		'getActiveModList()Ljava/util/List;': function (vm) { return JVM.newList(vm, forge(vm).mods.map(function (m) { return containerObj(vm, m); })); },
		'getIndexedModList()Ljava/util/Map;': function (vm) {
			var map = vm.newObject(vm.loadClass('java/util/HashMap')); vm.callVirtual(map, '<init>', '()V', []);
			forge(vm).mods.forEach(function (m) { vm.callVirtual(map, 'put', '(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;', [m.id, containerObj(vm, m)]); });
			return map;
		},
		'getConfigDir()Ljava/io/File;': function (vm) { return JVM.fileObj(vm, 'config'); },
		'getMinecraftModContainer()Lcpw/mods/fml/common/ModContainer;': function (vm) { return mcContainer(vm); },
		'getMinecraftModContainer()Lcpw/mods/fml/common/MinecraftDummyContainer;': function (vm) { return mcContainer(vm); },
		'activeModContainer()Lcpw/mods/fml/common/ModContainer;': function (vm) { var m = activeMod(vm); return m ? containerObj(vm, m) : null; },
		'getMCVersionString()Ljava/lang/String;': function () { return 'Minecraft 1.5.2'; },
		'getFMLVersionString()Ljava/lang/String;': function () { return '5.2.23.737'; },
		'isInState(Lcpw/mods/fml/common/LoaderState;)Z': function (vm, self, a) { return a[0] && a[0].$name === (forge(vm).state || 'AVAILABLE') ? 1 : 0; },
		'hasReachedState(Lcpw/mods/fml/common/LoaderState;)Z': function () { return 1; },
		'getModClassLoader()Ljava/lang/ClassLoader;': function (vm) { return JVM.classLoaderObj(vm); },
	}, staticMethods: {
		'instance()Lcpw/mods/fml/common/Loader;': function (vm) { return loaderObj(vm); },
		'isModLoaded(Ljava/lang/String;)Z': function (vm, n, a) { return isLoaded(vm, a[0]); },
	} });
	def(C + 'FMLCommonHandler', { methods: {
		'getEffectiveSide()Lcpw/mods/fml/relauncher/Side;': function (vm) { return effectiveSide(vm); },
		'getSide()Lcpw/mods/fml/relauncher/Side;': function (vm) { return sideObj(vm, 'CLIENT'); },
		'getMinecraftServerInstance()Lnet/minecraft/server/MinecraftServer;': function (vm) { var f = forge(vm); return f.server || (f.server = vm.newObject(vm.loadClass('net/minecraft/server/MinecraftServer'))); },
		'getModName()Ljava/lang/String;': function () { return 'fml,forge'; },
		'getBrandings()Ljava/util/List;': function (vm) { return JVM.newList(vm, ['Minecraft 1.5.2', 'FML']); },
		'registerCrashCallable(Lcpw/mods/fml/common/ICrashCallable;)V': function () {},
		'raiseException(Ljava/lang/Throwable;Ljava/lang/String;Z)V': function (vm, self, a) { vm.log('warn', a[1] + ': ' + JVM.describeThrowable(a[0])); },
		'getFMLLogger()Ljava/util/logging/Logger;': function (vm) { return vm.callStatic('java/util/logging/Logger', 'getLogger', '(Ljava/lang/String;)Ljava/util/logging/Logger;', ['FML']); },
		'getMinecraftLogger()Ljava/util/logging/Logger;': function (vm) { return vm.callStatic('java/util/logging/Logger', 'getLogger', '(Ljava/lang/String;)Ljava/util/logging/Logger;', ['Minecraft']); },
	}, staticMethods: {
		'instance()Lcpw/mods/fml/common/FMLCommonHandler;': function (vm) { var f = forge(vm); return f.handler || (f.handler = vm.newObject(vm.loadClass(C + 'FMLCommonHandler'))); },
	} });
	def(FML + 'client/FMLClientHandler', { methods: {
		'getClient()Lnet/minecraft/client/Minecraft;': function (vm) { return vm.callStatic(SRC + 'ModLoader', 'getMinecraftInstance', '()Lnet/minecraft/client/Minecraft;', []); },
		'displayGuiScreen(Lnet/minecraft/src/EntityPlayer;Lnet/minecraft/src/GuiScreen;)V': function (vm) { vm.warnOnce('fml:gui', 'mod screens are not available yet (left unplugged)'); },
		'getSide()Lcpw/mods/fml/relauncher/Side;': function (vm) { return sideObj(vm, 'CLIENT'); },
	}, staticMethods: {
		'instance()Lcpw/mods/fml/client/FMLClientHandler;': function (vm) { var f = forge(vm); return f.client || (f.client = vm.newObject(vm.loadClass(FML + 'client/FMLClientHandler'))); },
	} });

	var E = C + 'event/';
	def(E + 'FMLEvent', { methods: { 'getEventType()Ljava/lang/String;': function (vm, self) { return self.cls.name.substring(self.cls.name.lastIndexOf('/') + 1); } } });
	def(E + 'FMLStateEvent', { super: E + 'FMLEvent', methods: { 'getSide()Lcpw/mods/fml/relauncher/Side;': function (vm) { return sideObj(vm, 'CLIENT'); } } });
	var modOf = function (self) { return self.$mod; };
	def(E + 'FMLPreInitializationEvent', { super: E + 'FMLStateEvent', methods: {
		'getSuggestedConfigurationFile()Ljava/io/File;': function (vm, self) { return JVM.fileObj(vm, 'config/' + modOf(self).id + '.cfg'); },
		'getModConfigurationDirectory()Ljava/io/File;': function (vm) { return JVM.fileObj(vm, 'config'); },
		'getSourceFile()Ljava/io/File;': function (vm, self) { return JVM.fileObj(vm, 'mods/' + modOf(self).id + '.jar'); },
		'getModMetadata()Lcpw/mods/fml/common/ModMetadata;': function (vm, self) { return containerObj(vm, modOf(self)).$md; },
		'getModLog()Ljava/util/logging/Logger;': function (vm, self) { return vm.callStatic('java/util/logging/Logger', 'getLogger', '(Ljava/lang/String;)Ljava/util/logging/Logger;', [modOf(self).id]); },
		'getVersionProperties()Ljava/util/Properties;': function () { return null; },
		'getAsmData()Lcpw/mods/fml/common/discovery/ASMDataTable;': function () { return null; },
	} });
	def(E + 'FMLInitializationEvent', { super: E + 'FMLStateEvent', methods: {} });
	def(E + 'FMLPostInitializationEvent', { super: E + 'FMLStateEvent', methods: {
		'buildSoftDependProxy(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/Object;': function () { return null; },
	} });
	def(E + 'FMLServerStartingEvent', { super: E + 'FMLStateEvent', methods: {
		'getServer()Lnet/minecraft/server/MinecraftServer;': function (vm) { return vm.callVirtual(vm.callStatic(C + 'FMLCommonHandler', 'instance', '()Lcpw/mods/fml/common/FMLCommonHandler;', []), 'getMinecraftServerInstance', '()Lnet/minecraft/server/MinecraftServer;', []); },
		'registerServerCommand(Lnet/minecraft/src/ICommand;)V': function (vm, self, a) { forge(vm).commands.push(a[0]); },
	} });
	['FMLServerAboutToStartEvent', 'FMLServerStartedEvent', 'FMLServerStoppingEvent', 'FMLServerStoppedEvent', 'FMLLoadCompleteEvent'].forEach(function (n) { def(E + n, { super: E + 'FMLStateEvent', methods: {} }); });
	def(E + 'FMLInterModComms$IMCEvent', { super: E + 'FMLEvent', methods: { 'getMessages()Lcom/google/common/collect/ImmutableList;': function (vm) { return JVM.newList(vm, []); } } });
	def(E + 'FMLInterModComms', { staticMethods: {
		'sendMessage(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)Z': function () { return 1; },
		'sendMessage(Ljava/lang/String;Ljava/lang/String;Lnet/minecraft/src/NBTTagCompound;)Z': function () { return 1; },
		'sendMessage(Ljava/lang/String;Ljava/lang/String;Lnet/minecraft/src/ItemStack;)Z': function () { return 1; },
		'sendRuntimeMessage(Ljava/lang/Object;Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V': function () {},
		'fetchRuntimeMessages(Ljava/lang/Object;)Lcom/google/common/collect/ImmutableList;': function (vm) { return JVM.newList(vm, []); },
	} });

	var R = C + 'registry/';
	var blockOf = function (vm, o) { return o; };
	var regBlock = function (vm, block, itemCls) {
		if (!block) return;
		block.$registered = true;
		if (!itemCls) itemCls = vm.loadClass(SRC + 'ItemBlock');
		var id = block[':blockID'] - 256, o = vm.newObject(itemCls);
		var m1 = itemCls.findDeclared('<init>(I)V'), m2 = itemCls.findDeclared('<init>(ILnet/minecraft/src/Block;)V');
		if (m1 && !(m2 && m1.cls.native && !m2.cls.native)) vm.invoke(m1, o, [id]);
		else if (m2) vm.invoke(m2, o, [id, block]);
		else { vm.log('warn', 'no item constructor for ' + itemCls.name.replace(/[/]/g, '.')); return; }
		o.$blockItem = true;
		block.$itemBlock = o;
	};
	var CLS = function (a, i) { return a[i] ? a[i].$cls : null; };
	var ml = function (name, desc) { return function (vm, n, a) { return vm.callStatic(SRC + 'ModLoader', name, desc, a); }; };
	def(R + 'GameRegistry', { staticMethods: {
		'registerBlock(Lnet/minecraft/src/Block;)V': function (vm, n, a) { regBlock(vm, a[0], null); },
		'registerBlock(Lnet/minecraft/src/Block;Ljava/lang/String;)V': function (vm, n, a) { regBlock(vm, a[0], null); if (a[0]) a[0].$regName = a[1]; },
		'registerBlock(Lnet/minecraft/src/Block;Ljava/lang/Class;)V': function (vm, n, a) { regBlock(vm, a[0], CLS(a, 1)); },
		'registerBlock(Lnet/minecraft/src/Block;Ljava/lang/Class;Ljava/lang/String;)V': function (vm, n, a) { regBlock(vm, a[0], CLS(a, 1)); if (a[0]) a[0].$regName = a[2]; },
		'registerBlock(Lnet/minecraft/src/Block;Ljava/lang/Class;Ljava/lang/String;Ljava/lang/String;)V': function (vm, n, a) { regBlock(vm, a[0], CLS(a, 1)); if (a[0]) a[0].$regName = a[2]; },
		'registerItem(Lnet/minecraft/src/Item;Ljava/lang/String;)V': function (vm, n, a) { if (a[0]) a[0].$regName = a[1]; },
		'registerItem(Lnet/minecraft/src/Item;Ljava/lang/String;Ljava/lang/String;)V': function (vm, n, a) { if (a[0]) a[0].$regName = a[1]; },
		'addRecipe(Lnet/minecraft/src/ItemStack;[Ljava/lang/Object;)V': ml('addRecipe', '(Lnet/minecraft/src/ItemStack;[Ljava/lang/Object;)V'),
		'addShapedRecipe(Lnet/minecraft/src/ItemStack;[Ljava/lang/Object;)Lnet/minecraft/src/IRecipe;': function (vm, n, a) { vm.callStatic(SRC + 'ModLoader', 'addRecipe', '(Lnet/minecraft/src/ItemStack;[Ljava/lang/Object;)V', a); return null; },
		'addShapelessRecipe(Lnet/minecraft/src/ItemStack;[Ljava/lang/Object;)V': ml('addShapelessRecipe', '(Lnet/minecraft/src/ItemStack;[Ljava/lang/Object;)V'),
		'addRecipe(Lnet/minecraft/src/IRecipe;)V': function (vm, n, a) { addIRecipe(vm, a[0]); },
		'addSmelting(ILnet/minecraft/src/ItemStack;F)V': ml('addSmelting', '(ILnet/minecraft/src/ItemStack;F)V'),
		'registerWorldGenerator(Lcpw/mods/fml/common/IWorldGenerator;)V': function (vm, n, a) { var g = forge(vm).worldGens; if (a[0] && g.indexOf(a[0]) < 0) { g.push(a[0]); a[0].$mod = vm.currentMod; } },
		'registerFuelHandler(Lcpw/mods/fml/common/IFuelHandler;)V': function (vm, n, a) { forge(vm).fuel.push(a[0]); },
		'registerCraftingHandler(Lcpw/mods/fml/common/ICraftingHandler;)V': function (vm, n, a) { forge(vm).crafting.push(a[0]); },
		'registerPickupHandler(Lcpw/mods/fml/common/IPickupNotifier;)V': function (vm, n, a) { forge(vm).pickup.push(a[0]); },
		'registerPlayerTracker(Lcpw/mods/fml/common/IPlayerTracker;)V': function (vm, n, a) { forge(vm).playerTrackers.push(a[0]); },
		'registerTileEntity(Ljava/lang/Class;Ljava/lang/String;)V': function (vm, n, a) { forge(vm).tileEntities[a[1]] = CLS(a, 0); },
		'registerTileEntityWithAlternatives(Ljava/lang/Class;Ljava/lang/String;[Ljava/lang/String;)V': function (vm, n, a) { forge(vm).tileEntities[a[1]] = CLS(a, 0); },
		'registerDispenserHandler(Lcpw/mods/fml/common/IDispenserHandler;)V': function (vm) { vm.warnOnce('fml:dispenser', 'dispenser behaviour is not available here (left unplugged)'); },
		'getFuelValue(Lnet/minecraft/src/ItemStack;)I': function (vm, n, a) { return forge(vm).fuel.reduce(function (mx, h) { return Math.max(mx, vm.callVirtual(h, 'getBurnTime', '(Lnet/minecraft/src/ItemStack;)I', [a[0]])); }, 0); },
		'findBlock(Ljava/lang/String;Ljava/lang/String;)Lnet/minecraft/src/Block;': function (vm, n, a) { var r = reg(vm); var k = Object.keys(r.blocks).filter(function (i) { return r.blocks[i].$regName === a[1]; })[0]; return k ? r.blocks[k] : null; },
		'findItem(Ljava/lang/String;Ljava/lang/String;)Lnet/minecraft/src/Item;': function (vm, n, a) { var r = reg(vm); var k = Object.keys(r.items).filter(function (i) { return r.items[i].$regName === a[1]; })[0]; return k ? r.items[k] : null; },
		'generateWorld(IILnet/minecraft/src/World;Lnet/minecraft/src/IChunkProvider;Lnet/minecraft/src/IChunkProvider;)V': function (vm, n, a) { generateWorld(vm, a[0], a[1], a[2]); },
	} });
	var langAdd = function (vm, key, lang, value) { if (!lang || /^en_/i.test(lang)) reg(vm).lang[key] = value; };
	var nameKey = function (vm, o) {
		if (!o) return null;
		if (vm.isInstance(o, vm.loadClass(SRC + 'ItemStack'))) return vm.callVirtual(o, 'getItemName', '()Ljava/lang/String;', []);
		if (vm.isInstance(o, vm.loadClass(SRC + 'Item'))) return vm.callVirtual(o, 'getUnlocalizedName', '()Ljava/lang/String;', []);
		if (vm.isInstance(o, vm.loadClass(SRC + 'Block'))) return vm.callVirtual(o, 'getUnlocalizedName', '()Ljava/lang/String;', []);
		vm.throwNew('java/lang/IllegalArgumentException', 'Illegal object for naming ' + vm.toJavaString(o));
	};
	var langInst = function (vm) { var f = forge(vm); return f.lang || (f.lang = vm.newObject(vm.loadClass(R + 'LanguageRegistry'))); };
	var loadLangFile = function (vm, path, lang, isXml) {
		var p = String(path || '').replace(/^\/+/, ''), b = vm.resources[p];
		if (!b) { vm.log('warn', 'the language resource ' + path + ' cannot be located'); return; }
		var text = new TextDecoder('utf-8').decode(b);
		if (isXml) {
			var re = /<entry\s+key\s*=\s*"([^"]*)"\s*>([\s\S]*?)<\/entry>/g, m;
			while ((m = re.exec(text))) langAdd(vm, m[1], lang, m[2].replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"').replace(/&apos;/g, "'").replace(/&amp;/g, '&'));
		} else text.split(/\r?\n/).forEach(function (l) {
			if (/^\s*[#!]/.test(l)) return;
			var i = l.search(/[=:]/);
			if (i > 0) langAdd(vm, l.substring(0, i).trim(), lang, l.substring(i + 1).trim());
		});
	};
	def(R + 'LanguageRegistry', { methods: {
		'getStringLocalization(Ljava/lang/String;)Ljava/lang/String;': function (vm, self, a) { return reg(vm).lang[a[0]] || ''; },
		'getStringLocalization(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;': function (vm, self, a) { return reg(vm).lang[a[0]] || ''; },
		'addStringLocalization(Ljava/lang/String;Ljava/lang/String;)V': function (vm, self, a) { langAdd(vm, a[0], 'en_US', a[1]); },
		'addStringLocalization(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;)V': function (vm, self, a) { langAdd(vm, a[0], a[1], a[2]); },
		'addStringLocalization(Ljava/util/Properties;)V': function (vm, self, a) { listOf(vm, vm.callVirtual(a[0], 'keySet', '()Ljava/util/Set;', [])).forEach(function (k) { langAdd(vm, k, 'en_US', vm.callVirtual(a[0], 'getProperty', '(Ljava/lang/String;)Ljava/lang/String;', [k])); }); },
		'addStringLocalization(Ljava/util/Properties;Ljava/lang/String;)V': function (vm, self, a) { listOf(vm, vm.callVirtual(a[0], 'keySet', '()Ljava/util/Set;', [])).forEach(function (k) { langAdd(vm, k, a[1], vm.callVirtual(a[0], 'getProperty', '(Ljava/lang/String;)Ljava/lang/String;', [k])); }); },
		'addNameForObject(Ljava/lang/Object;Ljava/lang/String;Ljava/lang/String;)V': function (vm, self, a) { langAdd(vm, nameKey(vm, a[0]) + '.name', a[1], a[2]); },
		'loadLocalization(Ljava/lang/String;Ljava/lang/String;Z)V': function (vm, self, a) { loadLangFile(vm, a[0], a[1], a[2]); },
		'loadLocalization(Ljava/net/URL;Ljava/lang/String;Z)V': function (vm, self, a) { loadLangFile(vm, a[0] && a[0].$path, a[1], a[2]); },
	}, staticMethods: {
		'instance()Lcpw/mods/fml/common/registry/LanguageRegistry;': function (vm) { return langInst(vm); },
		'addName(Ljava/lang/Object;Ljava/lang/String;)V': function (vm, n, a) { langAdd(vm, nameKey(vm, a[0]) + '.name', 'en_US', a[1]); },
		'reloadLanguageTable()V': function () {},
	} });
	var tick = function (scheduled) { return function (vm, n, a) { if (a[0]) forge(vm).tickHandlers.push({ h: a[0], side: a[1] ? a[1].$name : 'CLIENT', scheduled: scheduled, wait: 0, mod: vm.currentMod }); }; };
	def(R + 'TickRegistry', { staticMethods: {
		'registerTickHandler(Lcpw/mods/fml/common/ITickHandler;Lcpw/mods/fml/relauncher/Side;)V': tick(false),
		'registerScheduledTickHandler(Lcpw/mods/fml/common/IScheduledTickHandler;Lcpw/mods/fml/relauncher/Side;)V': tick(true),
	} });
	var ent = function (kind) { return function (vm, n, a) { forge(vm).entities.push({ kind: kind, args: Array.prototype.slice.call(a), mod: vm.currentMod }); }; };
	var spawn = function (vm, n, a) { forge(vm).spawns.push({ args: Array.prototype.slice.call(a), mod: vm.currentMod }); };
	var entInst = function (vm) { var f = forge(vm); return f.entReg || (f.entReg = vm.newObject(vm.loadClass(R + 'EntityRegistry'))); };
	def(R + 'EntityRegistry', { methods: {}, staticMethods: {
		'instance()Lcpw/mods/fml/common/registry/EntityRegistry;': function (vm) { return entInst(vm); },
		'registerModEntity(Ljava/lang/Class;Ljava/lang/String;ILjava/lang/Object;IIZ)V': ent('mod'),
		'registerGlobalEntityID(Ljava/lang/Class;Ljava/lang/String;I)V': ent('global'),
		'registerGlobalEntityID(Ljava/lang/Class;Ljava/lang/String;III)V': ent('global'),
		'findGlobalUniqueEntityId()I': function (vm) { var f = forge(vm); f.nextEntity = (f.nextEntity || 255); while (f.nextEntity > 0 && [50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 120, 200].indexOf(f.nextEntity) >= 0) f.nextEntity--; return f.nextEntity--; },
		'addSpawn(Ljava/lang/Class;IIILnet/minecraft/src/EnumCreatureType;[Lnet/minecraft/src/BiomeGenBase;)V': spawn,
		'addSpawn(Ljava/lang/String;IIILnet/minecraft/src/EnumCreatureType;[Lnet/minecraft/src/BiomeGenBase;)V': spawn,
		'removeSpawn(Ljava/lang/Class;Lnet/minecraft/src/EnumCreatureType;[Lnet/minecraft/src/BiomeGenBase;)V': function () {},
		'removeSpawn(Ljava/lang/String;Lnet/minecraft/src/EnumCreatureType;[Lnet/minecraft/src/BiomeGenBase;)V': function () {},
	} });
	def(R + 'VillagerRegistry', { methods: {
		'registerVillagerId(I)V': function () {}, 'registerVillagerSkin(ILnet/minecraft/src/ResourceLocation;)V': function () {},
		'registerVillageTradeHandler(ILcpw/mods/fml/common/registry/VillagerRegistry$IVillageTradeHandler;)V': function () {},
		'registerVillageCreationHandler(Lcpw/mods/fml/common/registry/VillagerRegistry$IVillageCreationHandler;)V': function () {},
	}, staticMethods: { 'instance()Lcpw/mods/fml/common/registry/VillagerRegistry;': function (vm) { var f = forge(vm); return f.villagers || (f.villagers = vm.newObject(vm.loadClass(R + 'VillagerRegistry'))); } } });

	var N = C + 'network/';
	def(N + 'NetworkRegistry', { methods: {
		'registerConnectionHandler(Lcpw/mods/fml/common/network/IConnectionHandler;)V': function (vm, self, a) { forge(vm).connection.push(a[0]); },
		'registerGuiHandler(Ljava/lang/Object;Lcpw/mods/fml/common/network/IGuiHandler;)V': function (vm, self, a) { var m = a[0] && forge(vm).mods.filter(function (x) { return x.instance === a[0]; })[0]; forge(vm).guiHandlers[m ? m.id : vm.currentMod] = a[1]; },
		'registerChannel(Lcpw/mods/fml/common/network/IPacketHandler;Ljava/lang/String;)V': function () {},
		'registerChannel(Lcpw/mods/fml/common/network/IPacketHandler;Ljava/lang/String;Lcpw/mods/fml/relauncher/Side;)V': function () {},
		'registerChatListener(Lcpw/mods/fml/common/network/IChatListener;)V': function () {},
	}, staticMethods: { 'instance()Lcpw/mods/fml/common/network/NetworkRegistry;': function (vm) { var f = forge(vm); return f.net || (f.net = vm.newObject(vm.loadClass(N + 'NetworkRegistry'))); } } });
	def(N + 'PacketDispatcher', { staticMethods: (function () {
		var s = {}, nop = function () {};
		['sendPacketToServer(Lnet/minecraft/src/Packet;)V', 'sendPacketToPlayer(Lnet/minecraft/src/Packet;Lcpw/mods/fml/common/network/Player;)V',
		 'sendPacketToAllAround(DDDDILnet/minecraft/src/Packet;)V', 'sendPacketToAllInDimension(Lnet/minecraft/src/Packet;I)V',
		 'sendPacketToAllPlayers(Lnet/minecraft/src/Packet;)V'].forEach(function (k) { s[k] = nop; });
		s['getPacket(Ljava/lang/String;[B)Lnet/minecraft/src/Packet250CustomPayload;'] = function (vm) { return vm.newObject(vm.loadClass(SRC + 'Packet250CustomPayload')); };
		return s;
	})() });

	def(FML + 'client/registry/RenderingRegistry', { methods: {}, staticMethods: {
		'instance()Lcpw/mods/fml/client/registry/RenderingRegistry;': function (vm) { var f = forge(vm); return f.rr || (f.rr = vm.newObject(vm.loadClass(FML + 'client/registry/RenderingRegistry'))); },
		'getNextAvailableRenderId()I': function (vm) { var f = forge(vm); return (f.renderId = (f.renderId || 40) + 1); },
		'addNewArmourRendererPrefix(Ljava/lang/String;)I': function (vm, n, a) { var f = forge(vm); (f.armorPrefixes || (f.armorPrefixes = [])).push(a[0]); return 4 + f.armorPrefixes.length; },
		'registerEntityRenderingHandler(Ljava/lang/Class;Lnet/minecraft/src/Render;)V': function (vm, n, a) { forge(vm).renderers.push({ cls: CLS(a, 0), render: a[1] }); },
		'registerBlockHandler(Lcpw/mods/fml/client/registry/ISimpleBlockRenderingHandler;)V': function () {},
		'registerBlockHandler(ILcpw/mods/fml/client/registry/ISimpleBlockRenderingHandler;)V': function () {},
	} });
	def(FML + 'client/registry/ClientRegistry', { staticMethods: {
		'registerTileEntity(Ljava/lang/Class;Ljava/lang/String;Lnet/minecraft/src/TileEntitySpecialRenderer;)V': function (vm, n, a) { forge(vm).tileEntities[a[1]] = CLS(a, 0); },
		'bindTileEntitySpecialRenderer(Ljava/lang/Class;Lnet/minecraft/src/TileEntitySpecialRenderer;)V': function () {},
		'registerKeyBinding(Lnet/minecraft/src/KeyBinding;)V': function () {},
	} });
	def(FML + 'client/registry/KeyBindingRegistry', { staticMethods: {
		'registerKeyBinding(Lcpw/mods/fml/client/registry/KeyBindingRegistry$KeyHandler;)V': function (vm, n, a) { (forge(vm).keyHandlers || (forge(vm).keyHandlers = [])).push(a[0]); },
	} });
	def(FML + 'client/registry/KeyBindingRegistry$KeyHandler', { methods: {
		'<init>([Lnet/minecraft/src/KeyBinding;[Z)V': function (vm, self, a) { self[':keyBindings'] = a[0]; },
		'<init>([Lnet/minecraft/src/KeyBinding;)V': function (vm, self, a) { self[':keyBindings'] = a[0]; },
		'getKeyBindings()[Lnet/minecraft/src/KeyBinding;': function (vm, self) { return self[':keyBindings']; },
	} });

	var names = function (arr) { return arr ? Array.prototype.slice.call(arr.a) : []; };
	var rget = function (vm, cls, obj, ns) { var r = findFieldByNames(vm, cls.$cls, ns); if (!r) vm.throwNew(FML + 'common/ObfuscationReflectionHelper$UnableToAccessFieldException', ns.join(',')); return getField(vm, r, obj); };
	var rset = function (vm, cls, obj, v, ns) { var r = findFieldByNames(vm, cls.$cls, ns); if (!r) vm.throwNew(FML + 'common/ObfuscationReflectionHelper$UnableToAccessFieldException', ns.join(',')); setField(vm, r, obj, v); };
	def(FML + 'common/ObfuscationReflectionHelper$UnableToAccessFieldException', { super: 'java/lang/RuntimeException' });
	[FML + 'common/ObfuscationReflectionHelper', FML + 'relauncher/ReflectionHelper'].forEach(function (cn) {
		def(cn, { staticMethods: {
			'getPrivateValue(Ljava/lang/Class;Ljava/lang/Object;I)Ljava/lang/Object;': function (vm, n, a) { var r = fieldIndex(a[0].$cls, a[2]); return r ? JVM.reflect.boxAs(vm, getField(vm, r, a[1]), r.f.desc) : null; },
			'getPrivateValue(Ljava/lang/Class;Ljava/lang/Object;[Ljava/lang/String;)Ljava/lang/Object;': function (vm, n, a) { var r = findFieldByNames(vm, a[0].$cls, names(a[2])); return r ? JVM.reflect.boxAs(vm, getField(vm, r, a[1]), r.f.desc) : rget(vm, a[0], a[1], names(a[2])); },
			'setPrivateValue(Ljava/lang/Class;Ljava/lang/Object;Ljava/lang/Object;I)V': function (vm, n, a) { var r = fieldIndex(a[0].$cls, a[3]); if (r) setField(vm, r, a[1], JVM.reflect.unboxAs(a[2], r.f.desc)); },
			'setPrivateValue(Ljava/lang/Class;Ljava/lang/Object;Ljava/lang/Object;[Ljava/lang/String;)V': function (vm, n, a) { var r = findFieldByNames(vm, a[0].$cls, names(a[3])); if (r) setField(vm, r, a[1], JVM.reflect.unboxAs(a[2], r.f.desc)); else rset(vm, a[0], a[1], a[2], names(a[3])); },
			'findField(Ljava/lang/Class;[Ljava/lang/String;)Ljava/lang/reflect/Field;': function (vm, n, a) { var r = findFieldByNames(vm, a[0].$cls, names(a[1])); return r ? JVM.reflect.fieldObj(vm, r.owner, r.f) : null; },
			'getClass(Ljava/lang/ClassLoader;[Ljava/lang/String;)Ljava/lang/Class;': function (vm, n, a) { var ns = names(a[1]); for (var i = 0; i < ns.length; i++) { var c = vm.loadClass(ns[i].replace(/[.]/g, '/')); if (!c.absent) return vm.classObject(c); } return null; },
		} });
	});
}

var PHASE_ANN = {
	preInit: ['Mod$PreInit', 'FMLPreInitializationEvent'], init: ['Mod$Init', 'FMLInitializationEvent'], postInit: ['Mod$PostInit', 'FMLPostInitializationEvent'],
	serverAboutToStart: ['Mod$ServerAboutToStart', 'FMLServerAboutToStartEvent'], serverStarting: ['Mod$ServerStarting', 'FMLServerStartingEvent'],
	serverStarted: ['Mod$ServerStarted', 'FMLServerStartedEvent'], serverStopping: ['Mod$ServerStopping', 'FMLServerStoppingEvent'],
	serverStopped: ['Mod$ServerStopped', 'FMLServerStoppedEvent'],
};
function gatherHandlers(vm, cls) {
	var out = {};
	for (var c = cls; c && !c.native; c = c.superClass) {
		Object.keys(c.methods).forEach(function (k) {
			var m = c.methods[k];
			if (!m.annotations || m.sig.args.length !== 1) return;
			Object.keys(PHASE_ANN).forEach(function (ph) {
				var p = PHASE_ANN[ph], evType = 'Lcpw/mods/fml/common/event/' + p[1] + ';';
				var hit = JVM.annotation(vm, m.annotations, 'cpw/mods/fml/common/' + p[0]) ||
					(JVM.annotation(vm, m.annotations, 'cpw/mods/fml/common/Mod$EventHandler') && m.sig.args[0] === evType);
				if (hit && !(out[ph] || []).some(function (x) { return x.key === m.key; })) (out[ph] = out[ph] || []).push(m);
			});
		});
	}
	return out;
}
var MOD_SIG = 'Lcpw/mods/fml/common/Mod;';
function bytesHave(b, s) {
	var n = s.length, first = s.charCodeAt(0);
	outer: for (var i = 0, end = b.length - n; i <= end; i++) {
		if (b[i] !== first) continue;
		for (var k = 1; k < n; k++) if (b[i + k] !== s.charCodeAt(k)) continue outer;
		return true;
	}
	return false;
}
JVM.findForgeMods = function (vm, classes) {
	return classes.filter(function (cn) {
		var src = vm.sources[cn];
		if (src) return bytesHave(src.bytes, MOD_SIG);
		var c = vm.classes[cn];
		return !!(c && c.cf && JVM.annotation(vm, c.cf.annotations, 'cpw/mods/fml/common/Mod'));
	}).filter(function (cn) {
		var c = vm.loadClass(cn);
		return !!(c.cf && JVM.annotation(vm, c.cf.annotations, 'cpw/mods/fml/common/Mod'));
	});
};
JVM.forgeLoad = function (vm, modClasses, allClasses, info) {
	var f = forge(vm), mods = [];
	modClasses.forEach(function (cn) {
		var cls = vm.loadClass(cn), a = JVM.annotation(vm, cls.cf.annotations, 'cpw/mods/fml/common/Mod');
		var id = sval(a, 'modid', cn.substring(cn.lastIndexOf('/') + 1));
		var meta = (info || []).filter(function (x) { return x && x.modid === id; })[0] || null;
		var mod = { id: id, name: sval(a, 'name', '') || (meta && meta.name) || id, version: sval(a, 'version', '') || (meta && meta.version) || '1.0',
			info: meta, cls: cls, owner: vm.currentMod, handlers: gatherHandlers(vm, cls), instance: null };
		f.mods.push(mod);
		mods.push(mod);
	});
	var step = function (mod, what, fn) {
		f.active = mod;
		var r = JVM.run(vm, fn);
		f.active = null;
		if (!r.ok) vm.log('error', mod.id + ': ' + what + ' failed');
		return r;
	};
	f.state = 'CONSTRUCTING';
	mods.forEach(function (mod) {
		step(mod, 'construction', function () {
			vm.initClass(mod.cls);
			mod.instance = vm.newObject(mod.cls);
			var ctor = mod.cls.findDeclared('<init>()V');
			if (ctor) vm.invoke(ctor, mod.instance, []);
		});
		allClasses.forEach(function (cn) {
			var src = vm.sources[cn];
			if (src && !bytesHave(src.bytes, 'SidedProxy;')) return;
			var c = vm.loadClass(cn);
			if (!c.cf) return;
			Object.keys(c.fields).forEach(function (fn) {
				var fd = c.fields[fn], sp = JVM.annotation(vm, fd.annotations, 'cpw/mods/fml/common/SidedProxy');
				if (!sp || c.statics[fn] != null) return;
				var target = sval(sp, 'clientSide', '') || sval(sp, 'serverSide', '');
				if (!target) return;
				step(mod, '@SidedProxy ' + target, function () {
					var pc = vm.loadClass(target.replace(/[.]/g, '/'));
					var o = vm.newObject(pc), k = pc.findDeclared('<init>()V');
					if (k) vm.invoke(k, o, []);
					vm.initClass(c);
					if (fd.static) c.statics[fn] = o;
				});
			});
		});
		Object.keys(mod.cls.fields).forEach(function (fn) {
			var fd = mod.cls.fields[fn];
			var ia = JVM.annotation(vm, fd.annotations, 'cpw/mods/fml/common/Mod$Instance');
			if (ia) {
				var want = sval(ia, 'value', '');
				var target = want && want !== mod.id ? modById(vm, want) : mod;
				var v = target ? target.instance : null;
				if (fd.static) mod.cls.statics[fn] = v; else if (mod.instance) mod.instance[':' + fn] = v;
			}
			if (JVM.annotation(vm, fd.annotations, 'cpw/mods/fml/common/Mod$Metadata')) {
				var md = containerObj(vm, mod).$md;
				if (fd.static) mod.cls.statics[fn] = md; else if (mod.instance) mod.instance[':' + fn] = md;
			}
		});
	});
	[['preInit', 'PREINITIALIZATION'], ['init', 'INITIALIZATION'], ['postInit', 'POSTINITIALIZATION']].forEach(function (ph) {
		f.state = ph[1];
		mods.forEach(function (mod) { JVM.forgePhase(vm, mod, ph[0]); });
	});
	f.state = 'AVAILABLE';
	return mods;
};
JVM.forgePhase = function (vm, mod, phase) {
	var hs = mod.handlers[phase];
	if (!hs || !mod.instance) return;
	var f = forge(vm);
	vm.currentMod = mod.owner || vm.currentMod;
	var ev = vm.newObject(vm.loadClass('cpw/mods/fml/common/event/' + PHASE_ANN[phase][1]));
	ev.$mod = mod;
	hs.forEach(function (m) {
		f.active = mod;
		var r = JVM.run(vm, function () { vm.invoke(m, mod.instance, [ev]); });
		f.active = null;
		if (!r.ok) vm.log('error', mod.id + ': ' + phase + ' failed');
	});
};
JVM.forgeWorldStart = function (vm) {
	var f = vm.mcReg && vm.mcReg.forge;
	if (!f) return;
	['serverAboutToStart', 'serverStarting', 'serverStarted'].forEach(function (ph) { f.mods.forEach(function (m) { JVM.forgePhase(vm, m, ph); }); });
	JVM.forgePost(vm, FORGE + 'event/world/WorldEvent$Load', function (e) { e[':world'] = JVM.mc152.worldObj(vm); });
	f.tickHandlers.forEach(function (t) { t.wait = 0; });
};
JVM.forgeWorldStop = function (vm) {
	var f = vm.mcReg && vm.mcReg.forge;
	if (!f) return;
	JVM.forgePost(vm, FORGE + 'event/world/WorldEvent$Save', function (e) { e[':world'] = JVM.mc152.worldObj(vm); });
	JVM.forgePost(vm, FORGE + 'event/world/WorldEvent$Unload', function (e) { e[':world'] = JVM.mc152.worldObj(vm); });
	['serverStopping', 'serverStopped'].forEach(function (ph) { f.mods.forEach(function (m) { JVM.forgePhase(vm, m, ph); }); });
};
JVM.forgeWantsTick = function (vm) { var f = vm.mcReg && vm.mcReg.forge; return !!(f && f.tickHandlers.length); };
var TICK_ORDER = { SERVER: ['SERVER', 'WORLD', 'PLAYER'], CLIENT: ['CLIENT', 'WORLD', 'PLAYER'] };
JVM.forgeTick = function (vm) {
	var f = vm.mcReg && vm.mcReg.forge;
	if (!f || !f.tickHandlers.length) return;
	var TT = FML + 'common/TickType';
	f.tickHandlers.forEach(function (t) {
		if (t.scheduled) { if (t.wait-- > 0) return; }
		vm.currentMod = t.mod || vm.currentMod;
		JVM.run(vm, function () {
			var types = listOf(vm, vm.callVirtual(t.h, 'ticks', '()Ljava/util/EnumSet;', []));
			(TICK_ORDER[t.side] || TICK_ORDER.SERVER).forEach(function (name) {
				var ty = enumOf(vm, TT, name);
				if (types.indexOf(ty) < 0) return;
				var args = name === 'WORLD' ? [JVM.mc152.worldObj(vm)] : name === 'PLAYER' ? [JVM.mc152.playerObj(vm, null)] : [];
				var set = enumSetOf(vm, [ty]), arr = JVM.javaArray(vm, 'Ljava/lang/Object;', args);
				vm.callVirtual(t.h, 'tickStart', '(Ljava/util/EnumSet;[Ljava/lang/Object;)V', [set, arr]);
				vm.callVirtual(t.h, 'tickEnd', '(Ljava/util/EnumSet;[Ljava/lang/Object;)V', [set, arr]);
			});
			if (t.scheduled) t.wait = Math.max(0, vm.callVirtual(t.h, 'nextTickSpacing', '()I', []) - 1);
		});
	});
};
function generateWorld(vm, cx, cz, world) {
	var f = vm.mcReg && vm.mcReg.forge;
	if (!f || !f.worldGens.length) return;
	var seed = BigInt(vm.mcSeed | 0);
	var rnd = vm.newObject(vm.loadClass('java/util/Random'));
	vm.callVirtual(rnd, '<init>', '(J)V', [seed]);
	var xs = BigInt.asIntN(64, vm.callVirtual(rnd, 'nextLong', '()J', []) >> 3n);
	var zs = BigInt.asIntN(64, vm.callVirtual(rnd, 'nextLong', '()J', []) >> 3n);
	vm.callVirtual(rnd, 'setSeed', '(J)V', [BigInt.asIntN(64, BigInt.asIntN(64, xs * BigInt(cx) + zs * BigInt(cz)) ^ seed)]);
	var prov = vm.newObject(vm.loadClass(SRC + 'ChunkProviderGenerate'));
	f.worldGens.forEach(function (g) {
		vm.currentMod = g.$mod || vm.currentMod;
		JVM.run(vm, function () { vm.callVirtual(g, 'generate', '(Ljava/util/Random;IILnet/minecraft/src/World;Lnet/minecraft/src/IChunkProvider;Lnet/minecraft/src/IChunkProvider;)V', [rnd, cx, cz, world, prov, prov]); });
	});
}
JVM.forgeGenerate = function (vm, cx, cz) { generateWorld(vm, cx, cz, JVM.mc152.worldObj(vm)); };
JVM.forgeWantsGen = function (vm) { var f = vm.mcReg && vm.mcReg.forge; return !!(f && f.worldGens.length); };

function addIRecipe(vm, r) {
	if (!r) return;
	var cn = vm.classOf(r).name;
	if (r.$oreRecipe) reg(vm).recipes.push({ mod: vm.currentMod, shaped: r.$shaped, out: r.$out, args: r.$args, ore: true });
	else vm.warnOnce('recipe:' + cn, 'a recipe with its own matching code (' + cn.replace(/[/]/g, '.') + ') is not available here (left unplugged)');
}
function installForgeCommon(vm, def) {
	var C = FORGE + 'common/';
	def(C + 'MinecraftForge', {
		statics: { EVENT_BUS: null, TERRAIN_GEN_BUS: null, ORE_GEN_BUS: null, SEED_ENTRY: null },
		clinit: function (vm, c) { c.statics.EVENT_BUS = busObj(vm, 'EVENT_BUS'); c.statics.TERRAIN_GEN_BUS = busObj(vm, 'TERRAIN_GEN_BUS'); c.statics.ORE_GEN_BUS = busObj(vm, 'ORE_GEN_BUS'); },
		staticMethods: {
			'setBlockHarvestLevel(Lnet/minecraft/src/Block;Ljava/lang/String;I)V': function (vm, n, a) { if (a[0]) { a[0].$harvest = { tool: a[1], level: a[2] }; } },
			'setBlockHarvestLevel(Lnet/minecraft/src/Block;ILjava/lang/String;I)V': function (vm, n, a) { if (a[0] && (a[1] === 0 || !a[0].$harvest)) a[0].$harvest = { tool: a[2], level: a[3], meta: a[1] }; },
			'removeBlockEffectiveness(Lnet/minecraft/src/Block;Ljava/lang/String;)V': function (vm, n, a) { if (a[0]) a[0].$harvest = { tool: 'none', level: 0 }; },
			'removeBlockEffectiveness(Lnet/minecraft/src/Block;ILjava/lang/String;)V': function () {},
			'getBlockHarvestLevel(Lnet/minecraft/src/Block;ILjava/lang/String;)I': function (vm, n, a) { return a[0] && a[0].$harvest && a[0].$harvest.tool === a[2] ? a[0].$harvest.level : -1; },
			'setToolClass(Lnet/minecraft/src/Item;Ljava/lang/String;I)V': function (vm, n, a) { if (a[0]) a[0].$toolClass = { tool: a[1], level: a[2] }; },
			'addGrassSeed(Lnet/minecraft/src/ItemStack;I)V': function (vm) { vm.warnOnce('forge:seed', 'MinecraftForge.addGrassSeed is not available here (left unplugged)'); },
			'addGrassPlant(Lnet/minecraft/src/Block;II)V': function (vm) { vm.warnOnce('forge:plant', 'MinecraftForge.addGrassPlant is not available here (left unplugged)'); },
			'initialize()V': function () {},
		},
	});
	def(C + 'ForgeDirection', enumSpec(['DOWN', 'UP', 'NORTH', 'SOUTH', 'WEST', 'EAST', 'UNKNOWN'], function (vm, o, n, i) {
		var off = [[0, -1, 0], [0, 1, 0], [0, 0, -1], [0, 0, 1], [-1, 0, 0], [1, 0, 0], [0, 0, 0]][i];
		o[':offsetX'] = off[0]; o[':offsetY'] = off[1]; o[':offsetZ'] = off[2]; o[':flag'] = 1 << i;
	}));
	var FD = C + 'ForgeDirection';
	var fdSpec = vm.natives[FD];
	fdSpec.fields = { offsetX: 'I', offsetY: 'I', offsetZ: 'I', flag: 'I' };
	fdSpec.statics = Object.assign(fdSpec.statics, { VALID_DIRECTIONS: null, OPPOSITES: null, ROTATION_MATRIX: null });
	var ROT = [[0, 1, 4, 5, 3, 2, 6], [0, 1, 5, 4, 2, 3, 6], [5, 4, 2, 3, 0, 1, 6], [4, 5, 2, 3, 1, 0, 6], [2, 3, 1, 0, 4, 5, 6], [3, 2, 0, 1, 4, 5, 6], [0, 1, 2, 3, 4, 5, 6]];
	var fdClinit = fdSpec.clinit;
	fdSpec.clinit = function (vm, c) {
		fdClinit(vm, c);
		c.statics.VALID_DIRECTIONS = JVM.javaArray(vm, L(FD), c.$values.slice(0, 6));
		var opp = vm.newArray('I', 7); [1, 0, 3, 2, 5, 4, 6].forEach(function (v, i) { opp.a[i] = v; });
		c.statics.OPPOSITES = opp;
		var rm = vm.newArray('[I', 7);
		ROT.forEach(function (row, i) { var r = vm.newArray('I', 7); row.forEach(function (v, j) { r.a[j] = v; }); rm.a[i] = r; });
		c.statics.ROTATION_MATRIX = rm;
	};
	var fdVals = function (vm) { var c = vm.loadClass(FD); vm.initClass(c); return c.$values; };
	fdSpec.methods = {
		'getOpposite()Lnet/minecraftforge/common/ForgeDirection;': function (vm, self) { return fdVals(vm)[[1, 0, 3, 2, 5, 4, 6][self.$ordinal]]; },
		'getRotation(Lnet/minecraftforge/common/ForgeDirection;)Lnet/minecraftforge/common/ForgeDirection;': function (vm, self, a) { return fdVals(vm)[ROT[a[0].$ordinal][self.$ordinal]]; },
	};
	fdSpec.staticMethods = { 'getOrientation(I)Lnet/minecraftforge/common/ForgeDirection;': function (vm, n, a) { var v = fdVals(vm); return a[0] >= 0 && a[0] < 6 ? v[a[0]] : v[6]; } };
	enumStatics(vm, FD);

	var newConst = function (vm, cname, name, init) {
		var c = vm.loadClass(cname); vm.initClass(c);
		var o = vm.newObject(c);
		o.$name = name;
		o.$ordinal = c.$values ? c.$values.length : 0;
		if (init) init(o);
		if (c.$values) c.$values.push(o);
		return o;
	};
	def(C + 'EnumHelper', { staticMethods: {
		'addToolMaterial(Ljava/lang/String;IIFII)Lnet/minecraft/src/EnumToolMaterial;': function (vm, n, a) { return newConst(vm, SRC + 'EnumToolMaterial', a[0], function (o) { o.$m = [a[1], a[2], a[3], a[4], a[5]]; }); },
		'addArmorMaterial(Ljava/lang/String;I[II)Lnet/minecraft/src/EnumArmorMaterial;': function (vm, n, a) { return newConst(vm, SRC + 'EnumArmorMaterial', a[0], function (o) { o.$m = [a[1], Array.prototype.slice.call(a[2].a), a[3]]; }); },
		'addEnum(Ljava/lang/Class;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/Enum;': function (vm, n, a) { return newConst(vm, a[0].$cls.name, a[1], null); },
		'addEnum(Ljava/lang/Class;Ljava/lang/String;[Ljava/lang/Class;[Ljava/lang/Object;)Ljava/lang/Enum;': function (vm, n, a) { return newConst(vm, a[0].$cls.name, a[1], null); },
		'addCreatureType(Ljava/lang/String;Ljava/lang/Class;IZ)Lnet/minecraft/src/EnumCreatureType;': function (vm, n, a) { return newConst(vm, SRC + 'EnumCreatureType', a[0], null); },
		'addAction(Ljava/lang/String;)Lnet/minecraft/src/EnumAction;': function (vm, n, a) { return newConst(vm, SRC + 'EnumAction', a[0], null); },
		'addRarity(Ljava/lang/String;ILjava/lang/String;)Lnet/minecraft/src/EnumRarity;': function (vm, n, a) { return newConst(vm, SRC + 'EnumRarity', a[0], null); },
		'addEnchantmentType(Ljava/lang/String;)Lnet/minecraft/src/EnumEnchantmentType;': function (vm, n, a) { return newConst(vm, SRC + 'EnumEnchantmentType', a[0], null); },
		'addArt(Ljava/lang/String;Ljava/lang/String;IIII)Lnet/minecraft/src/EnumArt;': function (vm, n, a) { return newConst(vm, SRC + 'EnumArt', a[0], null); },
	} });
	def(C + 'AchievementPage', { methods: {
		'<init>(Ljava/lang/String;[Lnet/minecraft/src/Achievement;)V': function (vm, self, a) { self.$name = a[0]; self[':achievements'] = JVM.newList(vm, a[1] ? Array.prototype.slice.call(a[1].a) : []); },
		'getName()Ljava/lang/String;': function (vm, self) { return self.$name; },
		'getAchievements()Ljava/util/List;': function (vm, self) { return self[':achievements']; },
	}, staticMethods: {
		'registerAchievementPage(Lnet/minecraftforge/common/AchievementPage;)V': function (vm) { vm.warnOnce('forge:ach', 'achievements are not available here (left unplugged)'); },
		'getAchievementPage(I)Lnet/minecraftforge/common/AchievementPage;': function () { return null; },
		'getAchievementPages()Ljava/util/Set;': function (vm) { return vm.callStatic('java/util/Collections', 'emptySet', '()Ljava/util/Set;', []); },
		'isAchievementInPages(Lnet/minecraft/src/Achievement;)Z': function () { return 0; },
	} });
	def(C + 'DimensionManager', { staticMethods: {
		'getWorld(I)Lnet/minecraft/src/WorldServer;': function (vm, n, a) { return (vm.mcDim | 0) === a[0] && vm.game && vm.game.mode !== 'define' ? JVM.mc152.worldObj(vm) : null; },
		'getIDs()[Ljava/lang/Integer;': function (vm) { return JVM.javaArray(vm, 'Ljava/lang/Integer;', [0, -1, 1].map(function (d) { return JVM.box(vm, d, 'I'); })); },
		'isDimensionRegistered(I)Z': function (vm, n, a) { return a[0] === 0 || a[0] === -1 || a[0] === 1 ? 1 : 0; },
		'getNextFreeDimId()I': function () { return 2; },
		'registerDimension(II)V': function (vm) { vm.warnOnce('forge:dim', 'new dimensions are not available here (left unplugged)'); },
		'registerProviderType(ILjava/lang/Class;Z)Z': function () { return 0; },
	} });

	var O = FORGE + 'oredict/';
	var oreId = function (vm, name) { var f = forge(vm); var i = f.oreNames.indexOf(name); if (i < 0) { i = f.oreNames.length; f.oreNames.push(name); f.ores[name] = []; } return i; };
	var asStack = function (vm, o, meta) {
		if (!o) return null;
		if (vm.isInstance(o, vm.loadClass(SRC + 'ItemStack'))) return o;
		if (vm.isInstance(o, vm.loadClass(SRC + 'Block'))) return JVM.mc152.newStack(vm, o[':blockID'], 1, meta == null ? 32767 : meta);
		if (vm.isInstance(o, vm.loadClass(SRC + 'Item'))) return JVM.mc152.newStack(vm, o[':itemID'], 1, meta == null ? 32767 : meta);
		return null;
	};
	var regOre = function (vm, name, st) {
		if (!st) return;
		oreId(vm, name);
		var copy = JVM.mc152.newStack(vm, st[':itemID'], st[':stackSize'], st[':itemDamage']);
		forge(vm).ores[name].push(copy);
		JVM.forgePost(vm, O + 'OreDictionary$OreRegisterEvent', function (e) { e[':Name'] = name; e[':Ore'] = copy; });
	};
	def(O + 'OreDictionary', { statics: { WILDCARD_VALUE: 32767 }, staticMethods: {
		'registerOre(Ljava/lang/String;Lnet/minecraft/src/ItemStack;)V': function (vm, n, a) { regOre(vm, a[0], a[1]); },
		'registerOre(Ljava/lang/String;Lnet/minecraft/src/Item;)V': function (vm, n, a) { regOre(vm, a[0], asStack(vm, a[1])); },
		'registerOre(Ljava/lang/String;Lnet/minecraft/src/Block;)V': function (vm, n, a) { regOre(vm, a[0], asStack(vm, a[1])); },
		'registerOre(ILnet/minecraft/src/ItemStack;)V': function (vm, n, a) { regOre(vm, forge(vm).oreNames[a[0]], a[1]); },
		'getOreID(Ljava/lang/String;)I': function (vm, n, a) { return oreId(vm, a[0]); },
		'getOreID(Lnet/minecraft/src/ItemStack;)I': function (vm, n, a) {
			var f = forge(vm), s = a[0];
			if (!s) return -1;
			for (var i = 0; i < f.oreNames.length; i++) if (f.ores[f.oreNames[i]].some(function (o) { return o[':itemID'] === s[':itemID'] && (o[':itemDamage'] === 32767 || o[':itemDamage'] === s[':itemDamage']); })) return i;
			return -1;
		},
		'getOreName(I)Ljava/lang/String;': function (vm, n, a) { return forge(vm).oreNames[a[0]] || 'Unknown'; },
		'getOreNames()[Ljava/lang/String;': function (vm) { return JVM.javaArray(vm, 'Ljava/lang/String;', forge(vm).oreNames.slice()); },
		'getOres(Ljava/lang/String;)Ljava/util/ArrayList;': function (vm, n, a) { oreId(vm, a[0]); return JVM.newList(vm, forge(vm).ores[a[0]].slice()); },
		'getOres(Ljava/lang/Integer;)Ljava/util/ArrayList;': function (vm, n, a) { var nm = forge(vm).oreNames[JVM.unbox(a[0])]; return JVM.newList(vm, nm ? forge(vm).ores[nm].slice() : []); },
		'itemMatches(Lnet/minecraft/src/ItemStack;Lnet/minecraft/src/ItemStack;Z)Z': function (vm, n, a) {
			if (!a[0] || !a[1]) return a[0] === a[1] ? 1 : 0;
			return a[0][':itemID'] === a[1][':itemID'] && (a[0][':itemDamage'] === 32767 && !a[2] || a[0][':itemDamage'] === a[1][':itemDamage']) ? 1 : 0;
		},
		'initVanillaEntries()V': function () {},
	}, clinit: function (vm) {
		var B = function (n) { var c = vm.loadClass(SRC + 'Block'); vm.initClass(c); return c.statics[n]; };
		var I = function (n) { var c = vm.loadClass(SRC + 'Item'); vm.initClass(c); return c.statics[n]; };
		regOre(vm, 'logWood', asStack(vm, B('wood'), 32767));
		regOre(vm, 'plankWood', asStack(vm, B('planks'), 32767));
		regOre(vm, 'slabWood', asStack(vm, B('woodSingleSlab'), 32767));
		regOre(vm, 'stairWood', asStack(vm, B('stairsWoodOak'), 32767));
		regOre(vm, 'stairWood', asStack(vm, B('stairsWoodSpruce'), 32767));
		regOre(vm, 'stairWood', asStack(vm, B('stairsWoodBirch'), 32767));
		regOre(vm, 'stairWood', asStack(vm, B('stairsWoodJungle'), 32767));
		regOre(vm, 'stickWood', asStack(vm, I('stick'), 0));
		regOre(vm, 'treeSapling', asStack(vm, B('sapling'), 32767));
		regOre(vm, 'treeLeaves', asStack(vm, B('leaves'), 32767));
	} });
	def(O + 'OreDictionary$OreRegisterEvent', { super: FORGE + 'event/Event', fields: { Name: 'Ljava/lang/String;', Ore: L(SRC + 'ItemStack') } });
	var oreRecipe = function (shaped) {
		return function (vm, self, a) {
			self.$oreRecipe = true; self.$shaped = shaped;
			self.$out = asStack(vm, a[0], 0);
			self.$args = a[1] ? Array.prototype.slice.call(a[1].a) : [];
		};
	};
	var IR = SRC + 'IRecipe';
	def(O + 'ShapedOreRecipe', { interfaces: [IR], methods: {
		'<init>(Lnet/minecraft/src/ItemStack;[Ljava/lang/Object;)V': oreRecipe(true),
		'<init>(Lnet/minecraft/src/Item;[Ljava/lang/Object;)V': oreRecipe(true),
		'<init>(Lnet/minecraft/src/Block;[Ljava/lang/Object;)V': oreRecipe(true),
		'getRecipeOutput()Lnet/minecraft/src/ItemStack;': function (vm, self) { return self.$out; },
		'getRecipeSize()I': function (vm, self) { return 9; },
		'setMirrored(Z)Lnet/minecraftforge/oredict/ShapedOreRecipe;': function (vm, self) { return self; },
	} });
	def(O + 'ShapelessOreRecipe', { interfaces: [IR], methods: {
		'<init>(Lnet/minecraft/src/ItemStack;[Ljava/lang/Object;)V': oreRecipe(false),
		'<init>(Lnet/minecraft/src/Item;[Ljava/lang/Object;)V': oreRecipe(false),
		'<init>(Lnet/minecraft/src/Block;[Ljava/lang/Object;)V': oreRecipe(false),
		'getRecipeOutput()Lnet/minecraft/src/ItemStack;': function (vm, self) { return self.$out; },
		'getRecipeSize()I': function (vm, self) { return self.$args.length; },
	} });
	JVM.forgeOre = function (vm, name) { var f = vm.mcReg && vm.mcReg.forge; var l = f && f.ores[name]; return l && l.length ? l[0] : null; };
}

function installForge(vm) {
	var def = function (n, s) { vm.defineNative(n, s); };
	installConfig(vm, def);
	installEvents(vm, def);
	installFml(vm, def);
	installForgeCommon(vm, def);
	var mlSpec = vm.natives[SRC + 'ModLoader'];
	if (mlSpec) Object.assign(mlSpec.staticMethods, {
		'getPrivateValue(Ljava/lang/Class;Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/Object;': function (vm, n, a) { var r = findFieldByNames(vm, a[0].$cls, [a[2]]); if (!r) vm.throwNew('java/lang/NoSuchFieldException', a[2]); return JVM.reflect.boxAs(vm, getField(vm, r, a[1]), r.f.desc); },
		'getPrivateValue(Ljava/lang/Class;Ljava/lang/Object;I)Ljava/lang/Object;': function (vm, n, a) { var r = fieldIndex(a[0].$cls, a[2]); return r ? JVM.reflect.boxAs(vm, getField(vm, r, a[1]), r.f.desc) : null; },
		'setPrivateValue(Ljava/lang/Class;Ljava/lang/Object;Ljava/lang/String;Ljava/lang/Object;)V': function (vm, n, a) { var r = findFieldByNames(vm, a[0].$cls, [a[2]]); if (!r) vm.throwNew('java/lang/NoSuchFieldException', a[2]); setField(vm, r, a[1], JVM.reflect.unboxAs(a[3], r.f.desc)); },
		'setPrivateValue(Ljava/lang/Class;Ljava/lang/Object;ILjava/lang/Object;)V': function (vm, n, a) { var r = fieldIndex(a[0].$cls, a[2]); if (r) setField(vm, r, a[1], JVM.reflect.unboxAs(a[3], r.f.desc)); },
	});
}

JVM.installForge = installForge;
JVM.forgeState = function (vm) { return vm.mcReg && vm.mcReg.forge || null; };
})();

(function () {
'use strict';

var SRC = 'net/minecraft/src/', MS = 'net/minecraft/server/MinecraftServer';
function op(vm) { var g = vm.game; return g && (g.mode === 'run' || g.mode === 'gen') && g.op ? g.op.apply(null, Array.prototype.slice.call(arguments, 1)) : undefined; }
function running(vm) { return !!(vm.game && vm.game.mode === 'run'); }
function newStack(vm, id, n, d) { return JVM.mc152.newStack(vm, id, n, d); }

function aabb(vm, a) {
	var b = vm.newObject(vm.loadClass(SRC + 'AxisAlignedBB'));
	b[':minX'] = a[0]; b[':minY'] = a[1]; b[':minZ'] = a[2]; b[':maxX'] = a[3]; b[':maxY'] = a[4]; b[':maxZ'] = a[5];
	return b;
}
function bb(o) { return [o[':minX'], o[':minY'], o[':minZ'], o[':maxX'], o[':maxY'], o[':maxZ']]; }
function intersects(a, b) { return b[3] > a[0] && b[0] < a[3] && b[4] > a[1] && b[1] < a[4] && b[5] > a[2] && b[2] < a[5]; }
function entityBox(e) {
	var hw = (e[':width'] || 0.6) / 2, h = e[':height'] || 1.8, y = e[':posY'] - (e[':yOffset'] || 0);
	return [e[':posX'] - hw, y, e[':posZ'] - hw, e[':posX'] + hw, y + h, e[':posZ'] + hw];
}

function gameSlot(i, armor) { return armor ? -(3 - i) - 1 : i; }
function readSlot(vm, slot) {
	var s = op(vm, 'slot', slot);
	if (!s || !s.id) return null;
	return newStack(vm, s.id, s.count, s.data || 0);
}
function writeSlot(vm, slot, st) { op(vm, 'setslot', slot, st && st[':stackSize'] > 0 ? st[':itemID'] : 0, st ? st[':stackSize'] : 0, st ? st[':itemDamage'] : 0); }
function liveArray(vm, n, armor) {
	var cls = vm.loadClass('[L' + SRC + 'ItemStack;');
	var backing = new Array(n);
	var proxy = new Proxy(backing, {
		get: function (t, k) {
			if (k === 'length') return n;
			if (typeof k === 'string' && /^\d+$/.test(k)) { var i = +k; return i < n && running(vm) ? readSlot(vm, gameSlot(i, armor)) : null; }
			return t[k];
		},
		set: function (t, k, v) {
			if (typeof k === 'string' && /^\d+$/.test(k)) { if (+k < n && running(vm)) writeSlot(vm, gameSlot(+k, armor), v); return true; }
			t[k] = v; return true;
		},
	});
	return new JVM.JArray(cls, proxy);
}

function installServer(vm) {
	var def = function (n, s) { vm.defineNative(SRC + n, s); };
	var spec = function (n) { return vm.natives[SRC + n]; };
	var addTo = function (n, methods, statics) {
		var s = spec(n);
		s.methods = Object.assign({}, s.methods || {}, methods || {});
		if (statics) s.staticMethods = Object.assign({}, s.staticMethods || {}, statics);
	};
	var D6 = '(DDDDDD)Lnet/minecraft/src/AxisAlignedBB;', AB = 'Lnet/minecraft/src/AxisAlignedBB;';

	def('AxisAlignedBB', { fields: { minX: 'D', minY: 'D', minZ: 'D', maxX: 'D', maxY: 'D', maxZ: 'D' }, methods: {
		'setBounds(DDDDDD)Lnet/minecraft/src/AxisAlignedBB;': function (vm, self, a) { ['minX', 'minY', 'minZ', 'maxX', 'maxY', 'maxZ'].forEach(function (k, i) { self[':' + k] = a[i]; }); return self; },
		'addCoord(DDD)Lnet/minecraft/src/AxisAlignedBB;': function (vm, self, a) {
			var b = bb(self);
			for (var i = 0; i < 3; i++) { if (a[i] < 0) b[i] += a[i]; if (a[i] > 0) b[i + 3] += a[i]; }
			return aabb(vm, b);
		},
		'expand(DDD)Lnet/minecraft/src/AxisAlignedBB;': function (vm, self, a) { var b = bb(self); return aabb(vm, [b[0] - a[0], b[1] - a[1], b[2] - a[2], b[3] + a[0], b[4] + a[1], b[5] + a[2]]); },
		'contract(DDD)Lnet/minecraft/src/AxisAlignedBB;': function (vm, self, a) { var b = bb(self); return aabb(vm, [b[0] + a[0], b[1] + a[1], b[2] + a[2], b[3] - a[0], b[4] - a[1], b[5] - a[2]]); },
		'getOffsetBoundingBox(DDD)Lnet/minecraft/src/AxisAlignedBB;': function (vm, self, a) { var b = bb(self); return aabb(vm, [b[0] + a[0], b[1] + a[1], b[2] + a[2], b[3] + a[0], b[4] + a[1], b[5] + a[2]]); },
		'offset(DDD)Lnet/minecraft/src/AxisAlignedBB;': function (vm, self, a) { self[':minX'] += a[0]; self[':minY'] += a[1]; self[':minZ'] += a[2]; self[':maxX'] += a[0]; self[':maxY'] += a[1]; self[':maxZ'] += a[2]; return self; },
		'copy()Lnet/minecraft/src/AxisAlignedBB;': function (vm, self) { return aabb(vm, bb(self)); },
		'intersectsWith(Lnet/minecraft/src/AxisAlignedBB;)Z': function (vm, self, a) { return a[0] && intersects(bb(self), bb(a[0])) ? 1 : 0; },
		'isVecInside(Lnet/minecraft/src/Vec3;)Z': function (vm, self, a) { var v = a[0], b = bb(self); return v && v[':xCoord'] > b[0] && v[':xCoord'] < b[3] && v[':yCoord'] > b[1] && v[':yCoord'] < b[4] && v[':zCoord'] > b[2] && v[':zCoord'] < b[5] ? 1 : 0; },
		'getAverageEdgeLength()D': function (vm, self) { var b = bb(self); return (b[3] - b[0] + b[4] - b[1] + b[5] - b[2]) / 3; },
		'setBB(Lnet/minecraft/src/AxisAlignedBB;)V': function (vm, self, a) { var b = bb(a[0]); ['minX', 'minY', 'minZ', 'maxX', 'maxY', 'maxZ'].forEach(function (k, i) { self[':' + k] = b[i]; }); },
		'toString()Ljava/lang/String;': function (vm, self) { return 'box[' + bb(self).join(', ') + ']'; },
	}, staticMethods: {
		'getBoundingBox(DDDDDD)Lnet/minecraft/src/AxisAlignedBB;': function (vm, n, a) { return aabb(vm, a); },
		'getAABBPool()Lnet/minecraft/src/AABBPool;': function (vm) { return vm.mcAabbPool || (vm.mcAabbPool = vm.newObject(vm.loadClass(SRC + 'AABBPool'))); },
	} });
	def('AABBPool', { methods: { 'getAABB(DDDDDD)Lnet/minecraft/src/AxisAlignedBB;': function (vm, self, a) { return aabb(vm, a); }, 'cleanPool()V': function () {}, 'clearPool()V': function () {} } });
	def('Vec3', { fields: { xCoord: 'D', yCoord: 'D', zCoord: 'D' }, methods: {
		'addVector(DDD)Lnet/minecraft/src/Vec3;': function (vm, self, a) { return vec(vm, self[':xCoord'] + a[0], self[':yCoord'] + a[1], self[':zCoord'] + a[2]); },
		'distanceTo(Lnet/minecraft/src/Vec3;)D': function (vm, self, a) { var dx = a[0][':xCoord'] - self[':xCoord'], dy = a[0][':yCoord'] - self[':yCoord'], dz = a[0][':zCoord'] - self[':zCoord']; return Math.sqrt(dx * dx + dy * dy + dz * dz); },
		'squareDistanceTo(Lnet/minecraft/src/Vec3;)D': function (vm, self, a) { var dx = a[0][':xCoord'] - self[':xCoord'], dy = a[0][':yCoord'] - self[':yCoord'], dz = a[0][':zCoord'] - self[':zCoord']; return dx * dx + dy * dy + dz * dz; },
		'lengthVector()D': function (vm, self) { return Math.sqrt(self[':xCoord'] * self[':xCoord'] + self[':yCoord'] * self[':yCoord'] + self[':zCoord'] * self[':zCoord']); },
		'normalize()Lnet/minecraft/src/Vec3;': function (vm, self) { var l = Math.sqrt(self[':xCoord'] * self[':xCoord'] + self[':yCoord'] * self[':yCoord'] + self[':zCoord'] * self[':zCoord']); return l < 1e-4 ? vec(vm, 0, 0, 0) : vec(vm, self[':xCoord'] / l, self[':yCoord'] / l, self[':zCoord'] / l); },
		'subtract(Lnet/minecraft/src/Vec3;)Lnet/minecraft/src/Vec3;': function (vm, self, a) { return vec(vm, a[0][':xCoord'] - self[':xCoord'], a[0][':yCoord'] - self[':yCoord'], a[0][':zCoord'] - self[':zCoord']); },
		'dotProduct(Lnet/minecraft/src/Vec3;)D': function (vm, self, a) { return self[':xCoord'] * a[0][':xCoord'] + self[':yCoord'] * a[0][':yCoord'] + self[':zCoord'] * a[0][':zCoord']; },
	}, staticMethods: {
		'createVectorHelper(DDD)Lnet/minecraft/src/Vec3;': function (vm, n, a) { return vec(vm, a[0], a[1], a[2]); },
	} });
	function vec(vm, x, y, z) { var v = vm.newObject(vm.loadClass(SRC + 'Vec3')); v[':xCoord'] = x; v[':yCoord'] = y; v[':zCoord'] = z; return v; }
	def('Vec3Pool', { methods: { 'getVecFromPool(DDD)Lnet/minecraft/src/Vec3;': function (vm, self, a) { return vec(vm, a[0], a[1], a[2]); } } });

	var players = function (vm) { return running(vm) ? [JVM.mc152.playerObj(vm, null)] : []; };
	var within = function (vm, cls, box, except) {
		var b = bb(box);
		return players(vm).filter(function (p) { return p !== except && (!cls || vm.isInstance(p, cls)) && intersects(b, entityBox(p)); });
	};
	var EL = 'Ljava/util/List;';
	addTo('World', {
		'getEntitiesWithinAABB(Ljava/lang/Class;Lnet/minecraft/src/AxisAlignedBB;)Ljava/util/List;': function (vm, self, a) { return JVM.newList(vm, within(vm, a[0] && a[0].$cls, a[1], null)); },
		'getEntitiesWithinAABBExcludingEntity(Lnet/minecraft/src/Entity;Lnet/minecraft/src/AxisAlignedBB;)Ljava/util/List;': function (vm, self, a) { return JVM.newList(vm, within(vm, null, a[1], a[0])); },
		'selectEntitiesWithinAABB(Ljava/lang/Class;Lnet/minecraft/src/AxisAlignedBB;Lnet/minecraft/src/IEntitySelector;)Ljava/util/List;': function (vm, self, a) {
			return JVM.newList(vm, within(vm, a[0] && a[0].$cls, a[1], null).filter(function (e) { return !a[2] || vm.callVirtual(a[2], 'isEntityApplicable', '(Lnet/minecraft/src/Entity;)Z', [e]); }));
		},
		'getPlayerEntityByName(Ljava/lang/String;)Lnet/minecraft/src/EntityPlayer;': function (vm, self, a) { return players(vm).filter(function (p) { return p[':username'] === a[0]; })[0] || null; },
		'getClosestVulnerablePlayer(DDDD)Lnet/minecraft/src/EntityPlayer;': function (vm) { return players(vm)[0] || null; },
		'getCollidingBoundingBoxes(Lnet/minecraft/src/Entity;Lnet/minecraft/src/AxisAlignedBB;)Ljava/util/List;': function (vm) { return JVM.newList(vm, []); },
		'getWorldInfo()Lnet/minecraft/src/WorldInfo;': function (vm) { return worldInfo(vm); },
		'getSaveHandler()Lnet/minecraft/src/ISaveHandler;': function (vm) { return vm.mcSave || (vm.mcSave = vm.newObject(vm.loadClass(SRC + 'SaveHandler'))); },
		'getMinecraftServer()Lnet/minecraft/server/MinecraftServer;': function (vm) { return server(vm); },
		'getSpawnPoint()Lnet/minecraft/src/ChunkCoordinates;': function (vm) { var c = vm.newObject(vm.loadClass(SRC + 'ChunkCoordinates')); c[':posX'] = 0; c[':posY'] = 64; c[':posZ'] = 0; return c; },
		'getWorldVec3Pool()Lnet/minecraft/src/Vec3Pool;': function (vm) { return vm.mcVecPool || (vm.mcVecPool = vm.newObject(vm.loadClass(SRC + 'Vec3Pool'))); },
		'getBiomeGenForCoords(II)Lnet/minecraft/src/BiomeGenBase;': function (vm, self, a) { return JVM.biomeAt ? JVM.biomeAt(vm, a[0], a[1]) : null; },
		'canBlockSeeTheSky(III)Z': function (vm, self, a) { return op(vm, 'sky', a[0], a[1], a[2]) ? 1 : 0; },
		'getBlockLightValue(III)I': function (vm, self, a) { var v = op(vm, 'bright', a[0], a[1], a[2]); return v == null ? 15 : v | 0; },
		'getFullBlockLightValue(III)I': function (vm, self, a) { var v = op(vm, 'bright', a[0], a[1], a[2]); return v == null ? 15 : v | 0; },
		'isRaining()Z': function () { return 0; }, 'isThundering()Z': function () { return 0; },
		'getRainStrength(F)F': function () { return 0; }, 'canLightningStrikeAt(III)Z': function () { return 0; },
		'addWeatherEffect(Lnet/minecraft/src/Entity;)Z': function (vm) { vm.warnOnce('w:weather', 'lightning from mods is not available here (left unplugged)'); return 0; },
		'getActualHeight()I': function () { return 128; }, 'getHeight()I': function () { return 128; },
	});
	function worldInfo(vm) {
		var wi = vm.mcWorldInfo || (vm.mcWorldInfo = vm.newObject(vm.loadClass(SRC + 'WorldInfo')));
		return wi;
	}
	var winfo = function (vm) { return (running(vm) && op(vm, 'world')) || {}; };
	def('WorldInfo', { methods: {
		'getWorldName()Ljava/lang/String;': function (vm) { return winfo(vm).name || 'world'; },
		'getSeed()J': function (vm) { return BigInt(vm.mcSeed | 0); },
		'getWorldTime()J': function (vm) { return BigInt(op(vm, 'time') || 0); },
		'getWorldTotalTime()J': function (vm) { return BigInt(op(vm, 'time') || 0); },
		'isHardcoreModeEnabled()Z': function () { return 0; },
		'areCommandsAllowed()Z': function () { return 1; },
		'isRaining()Z': function () { return 0; }, 'isThundering()Z': function () { return 0; },
		'getGameType()Lnet/minecraft/src/EnumGameType;': function (vm) { var c = vm.loadClass(SRC + 'EnumGameType'); vm.initClass(c); return c.statics[winfo(vm).creative ? 'CREATIVE' : 'SURVIVAL'] || null; },
		'getSpawnX()I': function () { return 0; }, 'getSpawnY()I': function () { return 64; }, 'getSpawnZ()I': function () { return 0; },
		'getTerrainType()Lnet/minecraft/src/WorldType;': function () { return null; },
		'getDimension()I': function (vm) { return vm.mcDim | 0; },
	} });
	def('ISaveHandler', { access: JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC });
	def('SaveHandler', { interfaces: [SRC + 'ISaveHandler'], methods: {
		'getWorldDirectory()Ljava/io/File;': function (vm) { return JVM.fileObj(vm, 'world'); },
		'getWorldDirectoryName()Ljava/lang/String;': function () { return 'world'; },
		'getMapFileFromName(Ljava/lang/String;)Ljava/io/File;': function (vm, self, a) { return JVM.fileObj(vm, 'world/data/' + a[0] + '.dat'); },
		'getSaveDirectoryName()Ljava/lang/String;': function () { return 'world'; },
		'checkSessionLock()V': function () {},
		'getChunkLoader(Lnet/minecraft/src/WorldProvider;)Lnet/minecraft/src/IChunkLoader;': function (vm) {
			var l = vm.newObject(vm.loadClass(SRC + 'AnvilChunkLoader'));
			l[':chunkSaveLocation'] = JVM.fileObj(vm, 'world');
			return l;
		},
	} });
	def('IChunkLoader', { access: JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC });
	def('AnvilChunkLoader', { interfaces: [SRC + 'IChunkLoader'], fields: { chunkSaveLocation: 'Ljava/io/File;' }, methods: {} });
	def('ChunkCoordinates', { fields: { posX: 'I', posY: 'I', posZ: 'I' }, methods: {
		'<init>(III)V': function (vm, self, a) { self[':posX'] = a[0]; self[':posY'] = a[1]; self[':posZ'] = a[2]; },
		'<init>()V': function () {},
		'set(III)V': function (vm, self, a) { self[':posX'] = a[0]; self[':posY'] = a[1]; self[':posZ'] = a[2]; },
		'getDistanceSquared(III)F': function (vm, self, a) { var dx = self[':posX'] - a[0], dy = self[':posY'] - a[1], dz = self[':posZ'] - a[2]; return dx * dx + dy * dy + dz * dz; },
		'equals(Ljava/lang/Object;)Z': function (vm, self, a) { var o = a[0]; return o && o[':posX'] === self[':posX'] && o[':posY'] === self[':posY'] && o[':posZ'] === self[':posZ'] ? 1 : 0; },
		'hashCode()I': function (vm, self) { return (self[':posX'] + (self[':posZ'] << 8) + (self[':posY'] << 16)) | 0; },
	} });

	addTo('InventoryPlayer', {
		'getStackInSlot(I)Lnet/minecraft/src/ItemStack;': function (vm, self, a) { var i = a[0]; return i < 36 ? readSlot(vm, i) : i < 40 ? readSlot(vm, gameSlot(i - 36, true)) : null; },
		'setInventorySlotContents(ILnet/minecraft/src/ItemStack;)V': function (vm, self, a) { var i = a[0]; if (i < 36) writeSlot(vm, i, a[1]); else if (i < 40) writeSlot(vm, gameSlot(i - 36, true), a[1]); },
		'armorItemInSlot(I)Lnet/minecraft/src/ItemStack;': function (vm, self, a) { return a[0] >= 0 && a[0] < 4 ? readSlot(vm, gameSlot(a[0], true)) : null; },
		'getSizeInventory()I': function () { return 40; },
		'getInventoryStackLimit()I': function () { return 64; },
		'getFirstEmptyStack()I': function (vm) { for (var i = 0; i < 36; i++) if (!readSlot(vm, i)) return i; return -1; },
		'decrStackSize(II)Lnet/minecraft/src/ItemStack;': function (vm, self, a) {
			var i = a[0], slot = i < 36 ? i : gameSlot(i - 36, true), s = readSlot(vm, slot);
			if (!s) return null;
			var n = Math.min(a[1], s[':stackSize']);
			s[':stackSize'] -= n;
			writeSlot(vm, slot, s[':stackSize'] > 0 ? s : null);
			return newStack(vm, s[':itemID'], n, s[':itemDamage']);
		},
		'getTotalArmorValue()I': function (vm) {
			var t = 0;
			for (var i = 0; i < 4; i++) { var s = readSlot(vm, gameSlot(i, true)); var it = s && vm.callVirtual(s, 'getItem', '()Lnet/minecraft/src/Item;', []); if (it && it[':damageReduceAmount']) t += it[':damageReduceAmount']; }
			return t;
		},
		'hasItemStack(Lnet/minecraft/src/ItemStack;)Z': function (vm, self, a) { for (var i = 0; i < 40; i++) { var s = i < 36 ? readSlot(vm, i) : readSlot(vm, gameSlot(i - 36, true)); if (s && a[0] && s[':itemID'] === a[0][':itemID'] && s[':itemDamage'] === a[0][':itemDamage']) return 1; } return 0; },
		'onInventoryChanged()V': function () {},
	});
	addTo('EntityPlayer', {
		'getCurrentArmor(I)Lnet/minecraft/src/ItemStack;': function (vm, self, a) { return a[0] >= 0 && a[0] < 4 ? readSlot(vm, gameSlot(a[0], true)) : null; },
		'getTotalArmorValue()I': function (vm, self) { return vm.callVirtual(self[':inventory'], 'getTotalArmorValue', '()I', []); },
		'isUsingItem()Z': function () { return 0; },
		'isPlayerSleeping()Z': function () { return 0; },
		'getBedLocation()Lnet/minecraft/src/ChunkCoordinates;': function () { return null; },
		'isEntityAlive()Z': function (vm, self) { return self.$info && self.$info.health > 0 ? 1 : 0; },
	});
	JVM.mc152.onPlayer = function (vm, p) {
		var inv = p[':inventory'];
		if (inv && !inv.$live) {
			inv.$live = true;
			inv[':mainInventory'] = liveArray(vm, 36, false);
			inv[':armorInventory'] = liveArray(vm, 4, true);
		}
		if (inv) inv[':currentItem'] = p.$info && p.$info.slot != null ? p.$info.slot : 0;
		p[':inventorySlots'] = p[':inventorySlots'] || null;
		p[':width'] = 0.6; p[':height'] = 1.8; p[':yOffset'] = 1.62;
		var b = p[':boundingBox'] || (p[':boundingBox'] = aabb(vm, [0, 0, 0, 0, 0, 0]));
		var e = entityBox(p);
		['minX', 'minY', 'minZ', 'maxX', 'maxY', 'maxZ'].forEach(function (k, i) { b[':' + k] = e[i]; });
	};
	JVM.mc152.onWorld = function (vm, w) {
		if (!w[':playerEntities']) { w[':playerEntities'] = JVM.newList(vm, []); w[':loadedEntityList'] = JVM.newList(vm, []); }
		if (running(vm) && !vm.$fillingPlayers) {
			vm.$fillingPlayers = true;
			try {
				var ps = players(vm);
				[w[':playerEntities'], w[':loadedEntityList']].forEach(function (l) {
					vm.callVirtual(l, 'clear', '()V', []);
					ps.forEach(function (p) { vm.callVirtual(l, 'add', '(Ljava/lang/Object;)Z', [p]); });
				});
			} finally { vm.$fillingPlayers = false; }
		}
	};

	function server(vm) { return vm.mcServer || (vm.mcServer = vm.newObject(vm.loadClass(MS))); }
	function configManager(vm) { return vm.mcConfigMgr || (vm.mcConfigMgr = vm.newObject(vm.loadClass(SRC + 'ServerConfigurationManager'))); }
	vm.defineNative(MS, { methods: {
		'getConfigurationManager()Lnet/minecraft/src/ServerConfigurationManager;': function (vm) { return configManager(vm); },
		'worldServerForDimension(I)Lnet/minecraft/src/WorldServer;': function (vm, self, a) { return (vm.mcDim | 0) === a[0] ? JVM.mc152.worldObj(vm) : null; },
		'getEntityWorld()Lnet/minecraft/src/World;': function (vm) { return JVM.mc152.worldObj(vm); },
		'getTickCounter()I': function (vm) { return vm.mcTicks | 0; },
		'isSinglePlayer()Z': function () { return 1; },
		'isDedicatedServer()Z': function () { return 0; },
		'getServerOwner()Ljava/lang/String;': function (vm) { var p = running(vm) && op(vm, 'player'); return p && p.name || 'Player'; },
		'getMOTD()Ljava/lang/String;': function () { return ''; },
		'getFolderName()Ljava/lang/String;': function () { return 'world'; },
		'getWorldName()Ljava/lang/String;': function (vm) { return winfo(vm).name || 'world'; },
		'getMinecraftVersion()Ljava/lang/String;': function () { return '1.5.2'; },
		'getCurrentPlayerCount()I': function (vm) { return players(vm).length; },
		'getMaxPlayers()I': function () { return 8; },
		'getAllUsernames()[Ljava/lang/String;': function (vm) { return JVM.javaArray(vm, 'Ljava/lang/String;', players(vm).map(function (p) { return p[':username']; })); },
		'getDifficulty()I': function () { return 2; },
		'isPVPEnabled()Z': function () { return 1; },
		'canStructuresSpawn()Z': function () { return 1; },
		'getCommandManager()Lnet/minecraft/src/ICommandManager;': function (vm) { return vm.newObject(vm.loadClass(SRC + 'ServerCommandManager')); },
		'logInfo(Ljava/lang/String;)V': function (vm, self, a) { vm.log('out', a[0]); },
		'logWarning(Ljava/lang/String;)V': function (vm, self, a) { vm.log('warn', a[0]); },
		'logSevere(Ljava/lang/String;)V': function (vm, self, a) { vm.log('warn', a[0]); },
	}, staticMethods: {
		'getServer()Lnet/minecraft/server/MinecraftServer;': function (vm) { return server(vm); },
	}, statics: { worldServers: null }, clinit: function (vm, c) { c.statics.worldServers = JVM.javaArray(vm, 'L' + SRC + 'WorldServer;', []); } });
	def('ServerConfigurationManager', { methods: {
		'sendChatMsg(Ljava/lang/String;)V': function (vm, self, a) { op(vm, 'msg', a[0]); },
		'sendPacketToAllPlayers(Lnet/minecraft/src/Packet;)V': function () {},
		'sendPacketToAllPlayersInDimension(Lnet/minecraft/src/Packet;I)V': function () {},
		'getPlayerForUsername(Ljava/lang/String;)Lnet/minecraft/src/EntityPlayerMP;': function (vm, self, a) { return players(vm).filter(function (p) { return p[':username'] === a[0]; })[0] || null; },
		'getAllUsernames()[Ljava/lang/String;': function (vm) { return JVM.javaArray(vm, 'Ljava/lang/String;', players(vm).map(function (p) { return p[':username']; })); },
		'getCurrentPlayerCount()I': function (vm) { return players(vm).length; },
		'areCommandsAllowed(Ljava/lang/String;)Z': function () { return 1; },
		'isPlayerOpped(Ljava/lang/String;)Z': function () { return 1; },
		'getOps()Ljava/util/Set;': function (vm) { return vm.callStatic('java/util/Collections', 'emptySet', '()Ljava/util/Set;', []); },
	} });
	spec('ServerConfigurationManager').fields = { playerEntityList: 'Ljava/util/List;' };
	var mgrProto = vm.natives[SRC + 'ServerConfigurationManager'];
	mgrProto.methods['<init>()V'] = function () {};
	JVM.mc152.onServerList = function (vm) { var m = configManager(vm); m[':playerEntityList'] = JVM.newList(vm, players(vm)); return m; };
	vm.natives[MS].methods['getConfigurationManager()Lnet/minecraft/src/ServerConfigurationManager;'] = function (vm) { return JVM.mc152.onServerList(vm); };
}

JVM.installServer = installServer;
})();

(function () {
'use strict';

var SRC = 'net/minecraft/src/';
function reg(vm) { return JVM.mc152.reg(vm); }
function mobs(vm) { var r = reg(vm); return r.mobs || (r.mobs = { entities: [], spawns: [], renderers: [], mappings: [] }); }
function F(o, n) { return o ? o[':' + n] : undefined; }

var VANILLA = {
	EntityCreeper: ['ModelCreeper', 'mob/creeper.png'], EntityZombie: ['ModelZombie', 'mob/zombie.png'], EntitySkeleton: ['ModelSkeleton', 'mob/skeleton.png'],
	EntitySpider: ['ModelSpider', 'mob/spider.png'], EntityCaveSpider: ['ModelSpider', 'mob/cavespider.png'], EntityPig: ['ModelPig', 'mob/pig.png'],
	EntityCow: ['ModelCow', 'mob/cow.png'], EntityMooshroom: ['ModelCow', 'mob/redcow.png'], EntitySheep: ['ModelSheep2', 'mob/sheep.png'],
	EntityChicken: ['ModelChicken', 'mob/chicken.png'], EntityWolf: ['ModelWolf', 'mob/wolf.png'], EntityOcelot: ['ModelOcelot', 'mob/ozelot.png'],
	EntityVillager: ['ModelVillager', 'mob/villager/villager.png'], EntitySilverfish: ['ModelSilverfish', 'mob/silverfish.png'],
	EntityBlaze: ['ModelBlaze', 'mob/fire.png'], EntityEnderman: ['ModelEnderman', 'mob/enderman.png'], EntityIronGolem: ['ModelIronGolem', 'mob/villager_golem.png'],
	EntitySnowman: ['ModelSnowMan', 'mob/snowman.png'], EntitySquid: ['ModelSquid', 'mob/squid.png'], EntityGhast: ['ModelGhast', 'mob/ghast.png'],
	EntityBat: ['ModelBat', 'mob/bat.png'], EntityWitch: ['ModelWitch', 'mob/villager/witch.png'], EntitySlime: ['ModelSlime', 'mob/slime.png'],
	EntityMagmaCube: ['ModelMagmaCube', 'mob/lava.png'], EntityPigZombie: ['ModelZombie', 'mob/pigzombie.png'],
};
var STATS = {
	EntityCreeper: [0.6, 1.8, 20, 0.25, null, 'mob.creeper.say', 'mob.creeper.death'], EntityZombie: [0.6, 1.8, 20, 0.23, 'mob.zombie.say', 'mob.zombie.hurt', 'mob.zombie.death'],
	EntitySkeleton: [0.6, 1.8, 20, 0.25, 'mob.skeleton.say', 'mob.skeleton.hurt', 'mob.skeleton.death'], EntitySpider: [1.4, 0.9, 16, 0.8, 'mob.spider.say', 'mob.spider.say', 'mob.spider.death'],
	EntityCaveSpider: [0.7, 0.5, 12, 0.8, 'mob.spider.say', 'mob.spider.say', 'mob.spider.death'], EntityPig: [0.9, 0.9, 10, 0.25, 'mob.pig.say', 'mob.pig.say', 'mob.pig.death'],
	EntityCow: [0.9, 1.3, 10, 0.2, 'mob.cow.say', 'mob.cow.hurt', 'mob.cow.hurt'], EntityMooshroom: [0.9, 1.3, 10, 0.2, 'mob.cow.say', 'mob.cow.hurt', 'mob.cow.hurt'],
	EntitySheep: [0.9, 1.3, 8, 0.23, 'mob.sheep.say', 'mob.sheep.say', 'mob.sheep.say'], EntityChicken: [0.3, 0.7, 4, 0.25, 'mob.chicken.say', 'mob.chicken.hurt', 'mob.chicken.hurt'],
	EntityWolf: [0.6, 0.8, 8, 0.3, 'mob.wolf.bark', 'mob.wolf.hurt', 'mob.wolf.death'], EntityOcelot: [0.6, 0.8, 10, 0.3, null, 'mob.cat.hitt', 'mob.cat.hitt'],
	EntityVillager: [0.6, 1.8, 20, 0.5, 'mob.villager.default', 'mob.villager.defaulthurt', 'mob.villager.defaultdeath'], EntitySilverfish: [0.3, 0.7, 8, 0.6, 'mob.silverfish.say', 'mob.silverfish.hit', 'mob.silverfish.kill'],
	EntityBlaze: [0.6, 1.8, 20, 0.25, 'mob.blaze.breathe', 'mob.blaze.hit', 'mob.blaze.death'], EntityEnderman: [0.6, 2.9, 40, 0.2, 'mob.endermen.idle', 'mob.endermen.hit', 'mob.endermen.death'],
	EntityIronGolem: [1.4, 2.9, 100, 0.25, null, 'mob.irongolem.hit', 'mob.irongolem.death'], EntitySnowman: [0.4, 1.8, 4, 0.25, null, null, null],
	EntitySquid: [0.95, 0.95, 10, 0.25, null, null, null], EntityGhast: [4, 4, 10, 0.25, 'mob.ghast.moan', 'mob.ghast.scream', 'mob.ghast.death'],
	EntityBat: [0.5, 0.9, 6, 0.25, 'mob.bat.idle', 'mob.bat.hurt', 'mob.bat.death'], EntityWitch: [0.6, 1.8, 26, 0.25, null, null, null],
	EntitySlime: [2.04, 2.04, 16, 0.25, null, 'mob.slime.big', 'mob.slime.big'], EntityMagmaCube: [2.04, 2.04, 16, 0.25, null, 'mob.slime.big', 'mob.slime.big'],
	EntityPigZombie: [0.6, 1.8, 20, 0.5, 'mob.zombiepig.zpig', 'mob.zombiepig.zpighurt', 'mob.zombiepig.zpigdeath'],
};
var RENDER_MODEL = {
	RenderCreeper: 'ModelCreeper', RenderZombie: 'ModelZombie', RenderSkeleton: 'ModelSkeleton', RenderSpider: 'ModelSpider', RenderPig: 'ModelPig',
	RenderCow: 'ModelCow', RenderMooshroom: 'ModelCow', RenderSheep: 'ModelSheep2', RenderChicken: 'ModelChicken', RenderWolf: 'ModelWolf',
	RenderOcelot: 'ModelOcelot', RenderVillager: 'ModelVillager', RenderSilverfish: 'ModelSilverfish', RenderBlaze: 'ModelBlaze',
	RenderEnderman: 'ModelEnderman', RenderIronGolem: 'ModelIronGolem', RenderSnowMan: 'ModelSnowMan', RenderSquid: 'ModelSquid',
	RenderGhast: 'ModelGhast', RenderBat: 'ModelBat', RenderWitch: 'ModelWitch', RenderSlime: 'ModelSlime', RenderMagmaCube: 'ModelMagmaCube',
};
function vanillaModel(vm, name) {
	var c = vm.loadClass(SRC + name);
	var o = vm.newObject(c);
	var m = c.findDeclared('<init>()V') || c.findDeclared('<init>(F)V') || c.findDeclared('<init>(I)V');
	if (m) vm.invoke(m, o, m.sig.args.length ? [m.desc === '(I)V' ? 16 : 0] : []);
	return o;
}
function chainNames(c) { var out = []; for (var k = c; k; k = k.superClass) out.push(k.name.substring(k.name.lastIndexOf('/') + 1)); return out; }

function installMobs(vm) {
	var def = function (n, s) { vm.defineNative(SRC + n, s); };
	var addTo = function (n, methods, statics, extra) {
		var s = vm.natives[SRC + n];
		s.methods = Object.assign({}, s.methods || {}, methods || {});
		if (statics) s.staticMethods = Object.assign({}, s.staticMethods || {}, statics);
		if (extra) Object.assign(s, extra);
	};
	var isPlayer = function (o) { return !!(o && o.$info); };
	var op = function (vm) { var g = vm.game; return g && (g.mode === 'run' || g.mode === 'gen') && g.op ? g.op.apply(null, Array.prototype.slice.call(arguments, 1)) : undefined; };

	addTo('Entity', {
		'setSize(FF)V': function (vm, self, a) { self[':width'] = a[0]; self[':height'] = a[1]; self.$sized = true; },
		'getTexture()Ljava/lang/String;': function (vm, self) { return self[':texture'] || null; },
		'isImmuneToFire()Z': function (vm, self) { return self[':isImmuneToFire'] ? 1 : 0; },
		'getEntityName()Ljava/lang/String;': function (vm, self) { var e = mobs(vm).entities.filter(function (x) { return x.cls && vm.classOf(self).isSubclassOf(x.cls); })[0]; return e ? e.name : 'generic'; },
		'getEntityId()I': function (vm, self) { return self[':entityId'] | 0; },
		'setFire(I)V': function () {},
		'extinguish()V': function () {},
		'isBurning()Z': function () { return 0; },
		'isInWater()Z': function () { return 0; },
		'isWet()Z': function () { return 0; },
		'isEntityAlive()Z': function () { return 1; },
		'getBrightness(F)F': function () { return 1; },
		'getEyeHeight()F': function (vm, self) { return (self[':height'] || 1.8) * 0.85; },
		'setRotation(FF)V': function (vm, self, a) { self[':rotationYaw'] = a[0]; self[':rotationPitch'] = a[1]; },
	});
	var newOf = function (vm, cn) { return vm.newObject(vm.loadClass(cn)); };
	var initLiving = function (vm, self, world) {
		if (self.$livingInit) return;
		self.$livingInit = true;
		if (world) self[':worldObj'] = world;
		self[':texture'] = '/mob/char.png';
		self[':moveSpeed'] = 0.7;
		self[':width'] = 0.6; self[':height'] = 1.8;
		self[':experienceValue'] = 0;
		var rnd = newOf(vm, 'java/util/Random'); vm.callVirtual(rnd, '<init>', '()V', []);
		self[':rand'] = rnd;
		self[':tasks'] = newOf(vm, SRC + 'EntityAITasks');
		self[':targetTasks'] = newOf(vm, SRC + 'EntityAITasks');
		self[':tasks'].$list = []; self[':targetTasks'].$list = [];
		self[':navigator'] = newOf(vm, SRC + 'PathNavigate');
		self[':moveHelper'] = newOf(vm, SRC + 'EntityMoveHelper');
		self[':lookHelper'] = newOf(vm, SRC + 'EntityLookHelper');
		self[':jumpHelper'] = newOf(vm, SRC + 'EntityJumpHelper');
		self[':senses'] = newOf(vm, SRC + 'EntitySenses');
	};
	var player = function (fn, other) { return function (vm, self, a) { return isPlayer(self) ? fn(vm, self, a) : other(vm, self, a); }; };
	addTo('EntityLiving', {
		'heal(I)V': player(function (vm, self, a) { op(vm, 'heal', a[0]); }, function (vm, self, a) { self[':health'] = (self[':health'] | 0) + a[0]; }),
		'getHealth()I': player(function (vm) { var i = op(vm, 'player'); return i ? i.health : 20; }, function (vm, self) { return self[':health'] != null ? self[':health'] : vm.callVirtual(self, 'getMaxHealth', '()I', []); }),
		'setEntityHealth(I)V': player(function (vm, self, a) { op(vm, 'sethealth', a[0]); }, function (vm, self, a) { self[':health'] = a[0]; }),
		'<init>(Lnet/minecraft/src/World;)V': function (vm, self, a) { initLiving(vm, self, a[0]); },
		'getMaxHealth()I': function () { return 20; },
		'getNavigator()Lnet/minecraft/src/PathNavigate;': function (vm, self) { return self[':navigator'] || (self[':navigator'] = newOf(vm, SRC + 'PathNavigate')); },
		'getMoveHelper()Lnet/minecraft/src/EntityMoveHelper;': function (vm, self) { return self[':moveHelper'] || newOf(vm, SRC + 'EntityMoveHelper'); },
		'getLookHelper()Lnet/minecraft/src/EntityLookHelper;': function (vm, self) { return self[':lookHelper'] || newOf(vm, SRC + 'EntityLookHelper'); },
		'getJumpHelper()Lnet/minecraft/src/EntityJumpHelper;': function (vm, self) { return self[':jumpHelper'] || newOf(vm, SRC + 'EntityJumpHelper'); },
		'getEntitySenses()Lnet/minecraft/src/EntitySenses;': function (vm, self) { return self[':senses'] || newOf(vm, SRC + 'EntitySenses'); },
		'getAIMoveSpeed()F': function (vm, self) { return self[':landMovementFactor'] || self[':moveSpeed'] || 0.7; },
		'setAIMoveSpeed(F)V': function (vm, self, a) { self[':landMovementFactor'] = a[0]; },
		'isAIEnabled()Z': function () { return 0; },
		'getLivingSound()Ljava/lang/String;': function () { return null; },
		'getHurtSound()Ljava/lang/String;': function () { return 'damage.hit'; },
		'getDeathSound()Ljava/lang/String;': function () { return 'damage.hit'; },
		'getDropItemId()I': function () { return 0; },
		'getSoundVolume()F': function () { return 1; },
		'getTalkInterval()I': function () { return 80; },
		'canDespawn()Z': function () { return 1; },
		'getCreatureAttribute()Lnet/minecraft/src/EnumCreatureAttribute;': function () { return null; },
		'setCurrentItemOrArmor(ILnet/minecraft/src/ItemStack;)V': function (vm, self, a) { (self.$equip || (self.$equip = []))[a[0]] = a[1]; },
		'getCurrentItemOrArmor(I)Lnet/minecraft/src/ItemStack;': function (vm, self, a) { return self.$equip && self.$equip[a[0]] || null; },
		'getHeldItem()Lnet/minecraft/src/ItemStack;': player(function (vm) { return JVM.mc152.heldStack(vm); }, function (vm, self) { return self.$equip && self.$equip[0] || null; }),
	}, null, { anyInit: function (vm, self, args) { var w = args.filter(function (x) { return x && x.cls && vm.isInstance(x, vm.loadClass(SRC + 'World')); })[0]; initLiving(vm, self, w); } });
	var taskSpec = { methods: {
		'addTask(ILnet/minecraft/src/EntityAIBase;)V': function (vm, self, a) { (self.$list || (self.$list = [])).push(a[1]); },
		'removeTask(Lnet/minecraft/src/EntityAIBase;)V': function (vm, self, a) { if (self.$list) self.$list = self.$list.filter(function (t) { return t !== a[1] && t !== a[0]; }); },
		'onUpdateTasks()V': function () {},
	} };
	def('EntityAITasks', taskSpec);
	def('EnumCreatureType', { super: 'java/lang/Enum', statics: { monster: null, creature: null, ambient: null, waterCreature: null }, clinit: function (vm, c) {
		c.$values = ['monster', 'creature', 'ambient', 'waterCreature'].map(function (n, i) { var o = vm.newObject(c); o.$name = n; o.$ordinal = i; c.statics[n] = o; return o; });
	} });
	vm.natives[SRC + 'EnumCreatureType'].staticMethods = { 'values()[Lnet/minecraft/src/EnumCreatureType;': function (vm) { var c = vm.loadClass(SRC + 'EnumCreatureType'); vm.initClass(c); return JVM.javaArray(vm, 'L' + SRC + 'EnumCreatureType;', c.$values.slice()); } };
	var BIOMES = 'ocean Ocean,plains Plains,desert Desert,extremeHills Extreme Hills,forest Forest,taiga Taiga,swampland Swampland,river River,hell Hell,sky Sky,frozenOcean FrozenOcean,frozenRiver FrozenRiver,icePlains Ice Plains,iceMountains Ice Mountains,mushroomIsland MushroomIsland,mushroomIslandShore MushroomIslandShore,beach Beach,desertHills DesertHills,forestHills ForestHills,taigaHills TaigaHills,extremeHillsEdge Extreme Hills Edge,jungle Jungle,jungleHills JungleHills';
	var bstat = { biomeList: null };
	BIOMES.split(',').forEach(function (kv) { bstat[kv.split(' ')[0]] = null; });
	def('BiomeGenBase', { fields: { biomeName: 'Ljava/lang/String;', biomeID: 'I' }, statics: bstat, clinit: function (vm, c) {
		var list = vm.newArray('L' + SRC + 'BiomeGenBase;', 256);
		BIOMES.split(',').forEach(function (kv, i) {
			var p = kv.indexOf(' '), o = vm.newObject(c);
			o[':biomeName'] = kv.substring(p + 1); o[':biomeID'] = i;
			c.statics[kv.substring(0, p)] = o; list.a[i] = o;
		});
		c.statics.biomeList = list;
	}, methods: {
		'<init>(I)V': function (vm, self, a) { self[':biomeID'] = a[0]; self[':biomeName'] = 'Biome ' + a[0]; },
		'setBiomeName(Ljava/lang/String;)Lnet/minecraft/src/BiomeGenBase;': function (vm, self, a) { self[':biomeName'] = a[0]; return self; },
		'getSpawnableList(Lnet/minecraft/src/EnumCreatureType;)Ljava/util/List;': function (vm) { return JVM.newList(vm, []); },
		'getEnableSnow()Z': function () { return 0; },
		'canSpawnLightningBolt()Z': function () { return 1; },
		'getFloatTemperature()F': function () { return 0.5; },
		'getFloatRainfall()F': function () { return 0.5; },
	} });
	JVM.biomeAt = function (vm, x, z) {
		var n = op(vm, 'biome', x, z);
		var c = vm.loadClass(SRC + 'BiomeGenBase'); vm.initClass(c);
		var list = c.statics.biomeList.a;
		for (var i = 0; i < list.length; i++) if (list[i] && list[i][':biomeName'].toLowerCase().replace(/ /g, '_') === n) return list[i];
		return c.statics.plains;
	};

	var M = function (vm) { return mobs(vm); };
	var cls = function (a) { return a && a.$cls || null; };
	addTo('ModLoader', null, {
		'registerEntityID(Ljava/lang/Class;Ljava/lang/String;I)V': function (vm, n, a) { M(vm).entities.push({ cls: cls(a[0]), name: a[1], id: a[2], mod: vm.currentMod }); },
		'registerEntityID(Ljava/lang/Class;Ljava/lang/String;III)V': function (vm, n, a) { M(vm).entities.push({ cls: cls(a[0]), name: a[1], id: a[2], egg: [a[3], a[4]], mod: vm.currentMod }); },
		'addSpawn(Ljava/lang/Class;IIILnet/minecraft/src/EnumCreatureType;)V': function (vm, n, a) { M(vm).spawns.push({ cls: cls(a[0]), weight: a[1], min: a[2], max: a[3], type: a[4] && a[4].$name, biomes: null }); },
		'addSpawn(Ljava/lang/Class;IIILnet/minecraft/src/EnumCreatureType;[Lnet/minecraft/src/BiomeGenBase;)V': function (vm, n, a) { M(vm).spawns.push({ cls: cls(a[0]), weight: a[1], min: a[2], max: a[3], type: a[4] && a[4].$name, biomes: a[5] ? Array.prototype.slice.call(a[5].a) : null }); },
		'addSpawn(Ljava/lang/String;IIILnet/minecraft/src/EnumCreatureType;)V': function (vm, n, a) { M(vm).spawns.push({ name: a[0], weight: a[1], min: a[2], max: a[3], type: a[4] && a[4].$name, biomes: null }); },
		'addSpawn(Ljava/lang/String;IIILnet/minecraft/src/EnumCreatureType;[Lnet/minecraft/src/BiomeGenBase;)V': function (vm, n, a) { M(vm).spawns.push({ name: a[0], weight: a[1], min: a[2], max: a[3], type: a[4] && a[4].$name, biomes: a[5] ? Array.prototype.slice.call(a[5].a) : null }); },
	});
	def('EntityList', { staticMethods: {
		'addMapping(Ljava/lang/Class;Ljava/lang/String;I)V': function (vm, n, a) { M(vm).entities.push({ cls: cls(a[0]), name: a[1], id: a[2], mod: vm.currentMod }); },
		'addMapping(Ljava/lang/Class;Ljava/lang/String;III)V': function (vm, n, a) { M(vm).entities.push({ cls: cls(a[0]), name: a[1], id: a[2], egg: [a[3], a[4]], mod: vm.currentMod }); },
		'getEntityString(Lnet/minecraft/src/Entity;)Ljava/lang/String;': function (vm, n, a) { var e = M(vm).entities.filter(function (x) { return x.cls === vm.classOf(a[0]); })[0]; return e ? e.name : null; },
		'createEntityByName(Ljava/lang/String;Lnet/minecraft/src/World;)Lnet/minecraft/src/Entity;': function () { return null; },
	} });

	var RL = { methods: {
		'<init>(Lnet/minecraft/src/ModelBase;F)V': function (vm, self, a) { self[':mainModel'] = a[0]; self[':shadowSize'] = a[1]; },
		'setRenderPassModel(Lnet/minecraft/src/ModelBase;)V': function (vm, self, a) { self[':renderPassModel'] = a[0]; },
		'setRenderManager(Lnet/minecraft/src/RenderManager;)V': function () {},
		'loadTexture(Ljava/lang/String;)V': function () {},
		'doRender(Lnet/minecraft/src/Entity;DDDFF)V': function () {},
	}, anyInit: function (vm, self, args) {
		var m = args.filter(function (x) { return x && x.cls && vm.isInstance(x, vm.loadClass(SRC + 'ModelBase')); })[0];
		if (m) self[':mainModel'] = m;
	} };
	def('Render', { methods: { '<init>()V': function () {}, 'doRender(Lnet/minecraft/src/Entity;DDDFF)V': function () {}, 'loadTexture(Ljava/lang/String;)V': function () {} }, anyInit: function () {} });
	def('RenderLiving', Object.assign({ super: SRC + 'Render' }, RL));
	def('RenderBiped', { super: SRC + 'RenderLiving', methods: {
		'<init>(Lnet/minecraft/src/ModelBiped;F)V': function (vm, self, a) { self[':mainModel'] = a[0]; self[':modelBipedMain'] = a[0]; self[':shadowSize'] = a[1]; },
		'<init>(Lnet/minecraft/src/ModelBiped;FF)V': function (vm, self, a) { self[':mainModel'] = a[0]; self[':modelBipedMain'] = a[0]; self[':shadowSize'] = a[1]; },
	} });
	Object.keys(RENDER_MODEL).forEach(function (rn) {
		def(rn, { super: SRC + 'RenderLiving', methods: {}, anyInit: function (vm, self, args) {
			var m = args.filter(function (x) { return x && x.cls && vm.isInstance(x, vm.loadClass(SRC + 'ModelBase')); })[0];
			self[':mainModel'] = m || vanillaModel(vm, RENDER_MODEL[rn]);
		} });
	});
	var VANILLA_NAME = { EntityChicken: 'chicken', EntityCow: 'cow', EntityPig: 'pig', EntitySheep: 'sheep', EntityWolf: 'wolf', EntitySquid: 'squid',
		EntityZombie: 'zombie', EntityCreeper: 'creeper', EntitySkeleton: 'skeleton', EntitySpider: 'spider', EntityPigZombie: 'zombie_pigman',
		EntitySlime: 'slime', EntityGhast: 'ghast', EntityMooshroom: 'mooshroom', EntityOcelot: 'ocelot', EntityVillager: 'villager',
		EntitySnowman: 'snow_golem', EntityIronGolem: 'iron_golem', EntityBat: 'bat', EntityEnderman: 'enderman', EntityCaveSpider: 'cave_spider',
		EntitySilverfish: 'silverfish', EntityMagmaCube: 'magma_cube', EntityBlaze: 'blaze', EntityWitch: 'witch' };
	var wspec = vm.natives[SRC + 'World'];
	var prevSpawn = wspec.methods['spawnEntityInWorld(Lnet/minecraft/src/Entity;)Z'];
	wspec.methods = Object.assign({}, wspec.methods, {
		'spawnEntityInWorld(Lnet/minecraft/src/Entity;)Z': function (vm, self, a) {
			var e = a[0];
			if (e && !e.$stack && vm.isInstance(e, vm.loadClass(SRC + 'EntityLiving'))) {
				var keys = mobs(vm).keys, name = null;
				for (var c = e.cls; c && !name; c = c.superClass) name = (keys && keys.get(c)) || (c.native || c.absent ? VANILLA_NAME[c.name.split('/').pop()] : null) || null;
				if (name) { var id = op(vm, 'spawnmob', name, e[':posX'], e[':posY'], e[':posZ']); if (id) { e[':entityId'] = id; return 1; } return 0; }
			}
			return prevSpawn ? prevSpawn(vm, self, a) : 0;
		},
	});
	vm.natives[SRC + 'ModLoader'].staticMethods['registerEntityID?'] = null;
	delete vm.natives[SRC + 'ModLoader'].staticMethods['registerEntityID?'];
}

function jemOf(vm, model, entity) {
	var d = JVM.modelData(vm, model);
	if (!d || !d.parts.length) return null;
	var names = {};
	var fieldOf = new Map();
	Object.keys(model).forEach(function (k) {
		if (k[0] !== ':') return;
		var v = model[k];
		if (v && v.cls && v.cls.name === SRC + 'ModelRenderer' && !fieldOf.has(v)) fieldOf.set(v, k.substring(1));
		else if (v && v.a && v.cls && v.cls.name === '[L' + SRC + 'ModelRenderer;') Array.prototype.forEach.call(v.a, function (x, i) { if (x && !fieldOf.has(x)) fieldOf.set(x, k.substring(1) + i); });
	});
	var all = [];
	(function collect(l) { var arr = l ? Array.prototype.slice.call(vm.callVirtual(l, 'toArray', '()[Ljava/lang/Object;', []).a) : []; arr.forEach(function (r) { all.push(r); }); })(model[':boxList']);
	var nameFor = function (r, i) {
		var n = fieldOf.get(r) || r[':boxName'] || ('part' + i);
		n = String(n).replace(/^biped/, '').replace(/([a-z])([A-Z])/g, '$1_$2').toLowerCase();
		var k = n, j = 2;
		while (names[k]) k = n + '_' + j++;
		names[k] = true;
		return k;
	};
	var R = 180 / Math.PI;
	var childSet = new Set();
	all.forEach(function (r) { var l = r[':childModels']; if (l) Array.prototype.slice.call(vm.callVirtual(l, 'toArray', '()[Ljava/lang/Object;', []).a).forEach(function (c) { childSet.add(c); }); });
	var bb = function (x, y, z) { return [-x, 24 - y, z]; };
	var jem = function (r, i, parentAbs, parentO) {
		var rel = [r[':rotationPointX'] + (r[':offsetX'] || 0) * 16, r[':rotationPointY'] + (r[':offsetY'] || 0) * 16, r[':rotationPointZ'] + (r[':offsetZ'] || 0) * 16];
		var abs = [parentAbs[0] + rel[0], parentAbs[1] + rel[1], parentAbs[2] + rel[2]];
		var o = bb(abs[0], abs[1], abs[2]);
		var out = { id: nameFor(r, i), translate: [parentO[0] - o[0], parentO[1] - o[1], parentO[2] - o[2]],
			rotate: [r[':rotateAngleX'] * R, -r[':rotateAngleY'] * R, -r[':rotateAngleZ'] * R], boxes: [] };
		if (r[':showModel'] && !r[':isHidden']) r.$boxes.forEach(function (b) {
			var jx = abs[0] + b.x, jy = abs[1] + b.y, jz = abs[2] + b.z;
			var bx = -(jx + b.w), by = 24 - (jy + b.h), bz = jz;
			out.boxes.push({ coordinates: [bx - parentO[0], by - parentO[1], bz - parentO[2], b.w, b.h, b.d], textureOffset: [b.u, b.v], sizeAdd: b.inflate || 0 });
		});
		if (r[':mirror'] || r.$boxes.some(function (b) { return b.mirror; })) out.mirrorTexture = 'u';
		var kids = r[':childModels'] ? Array.prototype.slice.call(vm.callVirtual(r[':childModels'], 'toArray', '()[Ljava/lang/Object;', []).a) : [];
		if (kids.length) out.submodels = kids.map(function (k, j) { return jem(k, i + '_' + j, abs, o); });
		return out;
	};
	var root = [0, 0, 0], rootO = [0, 0, 0];
	var drawn = JVM.drawnParts ? JVM.drawnParts(vm, model, entity) : null;
	var tops = all.filter(function (r) { return !childSet.has(r) && (!drawn || drawn.indexOf(r) >= 0); });
	return { textureSize: [model[':textureWidth'] || 64, model[':textureHeight'] || 32], models: tops.map(function (r, i) { return jem(r, i, root, rootO); }) };
}
JVM.collectMobs = function (vm, modId, ref, safe) {
	var mb = mobs(vm), f = vm.mcReg && vm.mcReg.forge;
	var out = { mobs: {}, files: {}, skipped: [] };
	var ents = mb.entities.slice();
	if (f) f.entities.forEach(function (e) {
		var a = e.args;
		ents.push({ cls: a[0] && a[0].$cls, name: a[1], id: a[2], egg: e.kind === 'global' && a.length >= 5 ? [a[3], a[4]] : null, mod: e.mod });
	});
	var spawns = mb.spawns.slice();
	if (f) f.spawns.forEach(function (s) { var a = s.args; spawns.push({ cls: a[0] && a[0].$cls, name: typeof a[0] === 'string' ? a[0] : null, weight: a[1], min: a[2], max: a[3], type: a[4] && a[4].$name, biomes: a[5] ? Array.prototype.slice.call(a[5].a) : null }); });
	var renderers = new Map();
	if (f) f.renderers.forEach(function (r) { if (r.cls) renderers.set(r.cls, r.render); });
	reg(vm).mods.forEach(function (m) {
		if ((m.$mod || m.cls.source) !== modId && m.cls.source !== modId) return;
		safe(function () {
			var map = vm.newObject(vm.loadClass('java/util/HashMap')); vm.callVirtual(map, '<init>', '()V', []);
			vm.callVirtual(m, 'addRenderer', '(Ljava/util/Map;)V', [map]);
			var ks = vm.callVirtual(vm.callVirtual(map, 'keySet', '()Ljava/util/Set;', []), 'toArray', '()[Ljava/lang/Object;', []).a;
			Array.prototype.forEach.call(ks, function (k) { renderers.set(k.$cls, vm.callVirtual(map, 'get', '(Ljava/lang/Object;)Ljava/lang/Object;', [k])); });
		});
	});
	var living = vm.loadClass(SRC + 'EntityLiving');
	ents.forEach(function (e) {
		if (!e.cls || (e.mod || '') !== modId) return;
		if (!e.cls.isSubclassStrict(living) || e.cls === living) { out.skipped.push(e.name); return; }
		var key = String(e.name || e.cls.name.split('/').pop()).toLowerCase().replace(/[^a-z0-9_]+/g, '_');
		var world = JVM.mc152.worldObj(vm);
		var ent = safe(function () {
			var o = vm.newObject(e.cls);
			var k = e.cls.findDeclared('<init>(Lnet/minecraft/src/World;)V');
			if (k) vm.invoke(k, o, [world]);
			else JVM.run(vm, function () { vm.callVirtual(o, '<init>', '(Lnet/minecraft/src/World;)V', [world]); });
			return o;
		}, null);
		if (!ent) { out.skipped.push(e.name + ' (its constructor failed)'); return; }
		var chain = chainNames(e.cls);
		var vanilla = null;
		for (var i = 0; i < chain.length && !vanilla; i++) vanilla = VANILLA[chain[i]] || null;
		var has = function (n) { return chain.indexOf(n) >= 0; };
		var stats = null;
		for (var si = 0; si < chain.length && !stats; si++) stats = STATS[chain[si]] || null;
		var own = function (key) { var m = e.cls.findMethod(key); return !!(m && !m.cls.native); };
		if (stats && !ent.$sized) { ent[':width'] = ent[':width'] === 0.6 && ent[':height'] === 1.8 ? stats[0] : ent[':width']; ent[':height'] = ent[':height'] === 1.8 && ent[':width'] === stats[0] ? stats[1] : ent[':height']; }
		if (stats && ent[':moveSpeed'] === 0.7) ent[':moveSpeed'] = stats[3];
		var tasks = [].concat(ent[':tasks'] && ent[':tasks'].$list || [], ent[':targetTasks'] && ent[':targetTasks'].$list || []).map(function (t) { return t && t.cls ? t.cls.name.split('/').pop() : ''; });
		var spawn = spawns.filter(function (s) { return s.cls === e.cls || (s.name && s.name === e.name); });
		var stype = spawn[0] && spawn[0].type;
		var behaviour = has('EntityFlying') || has('EntityGhast') || has('EntityBat') || has('EntityBlaze') ? 'flying'
			: has('EntityWaterMob') || has('EntitySquid') || stype === 'waterCreature' ? 'swimming'
			: has('EntityTameable') || has('EntityIronGolem') || has('EntityPigZombie') || has('EntityWolf') ? 'neutral'
			: has('EntityMob') || stype === 'monster' || tasks.indexOf('EntityAIAttackOnCollide') >= 0 || tasks.indexOf('EntityAIArrowAttack') >= 0 ? 'hostile' : 'passive';
		var str = function (fn) { var v = safe(function () { return vm.callVirtual(ent, fn, '()Ljava/lang/String;', []); }, null); return typeof v === 'string' && v ? v : null; };
		var json = {
			name: (reg(vm).lang['entity.' + e.name + '.name']) || e.name,
			behaviour: behaviour,
			health: !own('getMaxHealth()I') && stats ? stats[2] : safe(function () { return vm.callVirtual(ent, 'getMaxHealth', '()I', []); }, 20),
			speed: Math.max(0.05, Math.min(1, +ent[':moveSpeed'] || 0.25)),
			size: [+ent[':width'] || 0.6, +ent[':height'] || 1.8],
			xp: ent[':experienceValue'] || (behaviour === 'hostile' ? 5 : 1),
		};
		if (behaviour === 'hostile' || behaviour === 'neutral') {
			var dmg = e.cls.findMethod('getAttackStrength(Lnet/minecraft/src/Entity;)I') ? safe(function () { return vm.callVirtual(ent, 'getAttackStrength', '(Lnet/minecraft/src/Entity;)I', [null]); }, 2) : (ent[':attackStrength'] || 2);
			json.damage = dmg;
		}
		if (ent[':isImmuneToFire']) json.fire_immune = true;
		if (has('EntityZombie') || has('EntitySkeleton')) json.burns_in_daylight = true;
		var snd = {
			ambient: own('getLivingSound()Ljava/lang/String;') || !stats ? str('getLivingSound') : stats[4],
			hurt: own('getHurtSound()Ljava/lang/String;') || !stats ? str('getHurtSound') : stats[5],
			death: own('getDeathSound()Ljava/lang/String;') || !stats ? str('getDeathSound') : stats[6] };
		Object.keys(snd).forEach(function (k) { if (!snd[k]) delete snd[k]; });
		if (Object.keys(snd).length) json.sounds = snd;
		var drop = safe(function () { return vm.callVirtual(ent, 'getDropItemId', '()I', []); }, 0);
		if (drop > 0) { var dr = ref(drop, 0); if (dr) json.drops = [{ item: dr, count: [0, 2] }]; }
		if (e.egg) json.egg = e.egg.map(function (c) { return '#' + ('00000' + ((c >>> 0) & 0xffffff).toString(16)).slice(-6); });
		else json.egg = false;
		json.spawn = spawn.map(function (s) {
			var r = { weight: s.weight || 10, group: [Math.max(1, s.min | 0), Math.max(1, s.max | 0)] };
			if (s.biomes && s.biomes.length) r.biomes = s.biomes.filter(Boolean).map(function (b) { return String(b[':biomeName'] || '').toLowerCase().replace(/ /g, '_'); });
			if (s.type === 'monster') r.light = [0, 7];
			return r;
		});
		var render = renderers.get(e.cls);
		for (var k2 = e.cls; !render && k2; k2 = k2.superClass) render = renderers.get(k2);
		var model = render && render[':mainModel'];
		if (!model && vanilla) model = safe(function () { return vanillaModel(vm, vanilla[0]); }, null);
		if (model && JVM.pose) JVM.pose(vm, model, ent);
		var jem = model ? safe(function () { return jemOf(vm, model, ent); }, null) : null;
		if (!jem) { out.skipped.push(e.name + ' (no model)'); return; }
		out.files['models/entity/' + key + '.jem'] = JSON.stringify(jem);
		json.model = 'models/entity/' + key + '.jem';
		var tex = safe(function () { return vm.callVirtual(ent, 'getTexture', '()Ljava/lang/String;', []); }, null) || ent[':texture'];
		if ((!tex || tex === '/mob/char.png') && vanilla) tex = '/' + vanilla[1];
		var tp = String(tex || '').replace(/^[/]+/, '');
		if (vm.resources[tp]) { out.files['textures/entity/' + key + '.png'] = vm.resources[tp]; json.texture = 'textures/entity/' + key + '.png'; }
		else if (/^mob[/]/.test(tp)) json.texture = 'minecraft:' + tp;
		else { out.skipped.push(e.name + ' (no texture ' + tex + ')'); return; }
		out.mobs[key] = json;
		(mb.keys || (mb.keys = new Map())).set(e.cls, modId + ':' + key);
	});
	return out;
};

JVM.installMobs = installMobs;
})();

(function () {
'use strict';

var SRC = 'net/minecraft/src/';
var LWJGL = { 1: 'Escape', 12: 'Minus', 13: 'Equal', 14: 'Backspace', 15: 'Tab', 26: 'BracketLeft', 27: 'BracketRight', 28: 'Enter', 29: 'ControlLeft',
	39: 'Semicolon', 40: 'Quote', 41: 'Backquote', 42: 'ShiftLeft', 43: 'Backslash', 51: 'Comma', 52: 'Period', 53: 'Slash', 54: 'ShiftRight',
	55: 'NumpadMultiply', 56: 'AltLeft', 57: 'Space', 58: 'CapsLock', 69: 'NumLock', 70: 'ScrollLock', 71: 'Numpad7', 72: 'Numpad8', 73: 'Numpad9',
	74: 'NumpadSubtract', 75: 'Numpad4', 76: 'Numpad5', 77: 'Numpad6', 78: 'NumpadAdd', 79: 'Numpad1', 80: 'Numpad2', 81: 'Numpad3', 82: 'Numpad0',
	83: 'NumpadDecimal', 87: 'F11', 88: 'F12', 156: 'NumpadEnter', 157: 'ControlRight', 181: 'NumpadDivide', 184: 'AltRight', 199: 'Home', 200: 'ArrowUp',
	201: 'PageUp', 203: 'ArrowLeft', 205: 'ArrowRight', 207: 'End', 208: 'ArrowDown', 209: 'PageDown', 210: 'Insert', 211: 'Delete' };
(function () {
	for (var i = 2; i <= 11; i++) LWJGL[i] = 'Digit' + (i === 11 ? 0 : i - 1);
	'QWERTYUIOP'.split('').forEach(function (c, i) { LWJGL[16 + i] = 'Key' + c; });
	'ASDFGHJKL'.split('').forEach(function (c, i) { LWJGL[30 + i] = 'Key' + c; });
	'ZXCVBNM'.split('').forEach(function (c, i) { LWJGL[44 + i] = 'Key' + c; });
	for (var f = 1; f <= 10; f++) LWJGL[58 + f] = 'F' + f;
})();
var CODE_TO_LWJGL = {};
Object.keys(LWJGL).forEach(function (k) { CODE_TO_LWJGL[LWJGL[k]] = +k; });
JVM.lwjglKey = function (n) { return LWJGL[n] || ''; };
JVM.keyToLwjgl = function (code) { return CODE_TO_LWJGL[code] || 0; };

function reg(vm) { return JVM.mc152.reg(vm); }
function keysOf(vm) { var r = reg(vm); return r.keys || (r.keys = []); }
function pretty(s) { s = String(s || ''); return s.charAt(0).toUpperCase() + s.slice(1); }

function installSettings(vm) {
	var def = function (n, s) { vm.defineNative(SRC + n, s); };
	def('KeyBinding', { fields: { keyDescription: 'Ljava/lang/String;', keyCode: 'I', pressed: 'Z' }, statics: { keybindArray: null, hash: null }, methods: {
		'<init>(Ljava/lang/String;I)V': function (vm, self, a) { self[':keyDescription'] = a[0]; self[':keyCode'] = a[1]; self[':pressed'] = 0; },
		'isPressed()Z': function (vm, self) { var p = self.$presses | 0; if (p) self.$presses = p - 1; return p ? 1 : 0; },
		'unpressKey()V': function (vm, self) { self[':pressed'] = 0; self.$presses = 0; },
	}, staticMethods: {
		'unPressAllKeys()V': function () {}, 'resetKeyBindingArrayAndHash()V': function () {},
		'setKeyBindState(IZ)V': function () {}, 'onTick(I)V': function () {},
	} });
	var ml = vm.natives[SRC + 'ModLoader'];
	ml.staticMethods['registerKey(Lnet/minecraft/src/BaseMod;Lnet/minecraft/src/KeyBinding;Z)V'] = function (vm, n, a) {
		if (a[1]) keysOf(vm).push({ mod: vm.currentMod, kind: 'ml', owner: a[0], kb: a[1], repeat: !!a[2] });
	};
	var fr = vm.natives['cpw/mods/fml/client/registry/KeyBindingRegistry'];
	if (fr) fr.staticMethods['registerKeyBinding(Lcpw/mods/fml/client/registry/KeyBindingRegistry$KeyHandler;)V'] = function (vm, n, a) {
		var h = a[0], kbs = h && vm.callVirtual(h, 'getKeyBindings', '()[Lnet/minecraft/src/KeyBinding;', []);
		if (kbs) Array.prototype.forEach.call(kbs.a, function (kb) { if (kb) keysOf(vm).push({ mod: vm.currentMod, kind: 'forge', owner: h, kb: kb }); });
	};
}

function propsParse(text) {
	var out = {};
	String(text || '').split(/\r?\n/).forEach(function (l) {
		if (/^\s*[#!]/.test(l)) return;
		var i = l.search(/[=:]/);
		if (i > 0) out[l.substring(0, i).trim()] = l.substring(i + 1).trim();
	});
	return out;
}
JVM.mlProps = function (vm, cls) {
	var r = reg(vm), list = r.mlprops || (r.mlprops = []);
	if (!cls.cf) return;
	var file = 'config/' + cls.name.split('/').pop() + '.cfg';
	var fields = Object.keys(cls.fields).filter(function (fn) { var f = cls.fields[fn]; return f.static && JVM.annotation(vm, f.annotations, SRC + 'MLProp'); });
	if (!fields.length) return;
	vm.initClass(cls);
	var have = vm.fs && vm.fs.read(file);
	var saved = have ? propsParse(new TextDecoder().decode(have)) : {};
	var lines = ['#' + cls.name.split('/').pop() + ' Config', '#' + new Date().toString()];
	fields.forEach(function (fn) {
		var f = cls.fields[fn], a = JVM.annotation(vm, f.annotations, SRC + 'MLProp');
		var g = function (k, d) { var e = a.values[k]; return e && e.v !== undefined ? e.v : d; };
		var name = g('name', '') || fn, info = g('info', ''), min = g('min', -Infinity), max = g('max', Infinity);
		var dflt = cls.statics[fn];
		var v = dflt;
		if (saved[name] !== undefined) {
			var s = saved[name];
			if (f.desc === 'Z') v = /^true$/i.test(s) ? 1 : 0;
			else if (/^[IJSB]$/.test(f.desc)) { var n = parseInt(s, 10); if (isFinite(n) && n >= min && n <= max) v = f.desc === 'J' ? BigInt(n) : n; }
			else if (/^[FD]$/.test(f.desc)) { var d = parseFloat(s); if (isFinite(d) && d >= min && d <= max) v = d; }
			else if (f.desc === 'Ljava/lang/String;') v = s;
			cls.statics[fn] = v;
		}
		if (info) lines.push('#' + info);
		lines.push(name + '=' + (f.desc === 'Z' ? (v ? 'true' : 'false') : String(v)));
		list.push({ mod: vm.currentMod, file: file, name: name, info: info, min: min, max: max, desc: f.desc,
			value: f.desc === 'Z' ? !!v : /^[IJSBFD]$/.test(f.desc) ? Number(v) : String(v), def: f.desc === 'Z' ? !!dflt : /^[IJSBFD]$/.test(f.desc) ? Number(dflt) : String(dflt) });
	});
	if (vm.fs) { vm.fs.mkdirs('config'); vm.fs.write(file, new TextEncoder().encode(lines.join('\n') + '\n')); }
};

JVM.javaSettings = function (vm, modId) {
	var out = [];
	var cfgs = JVM.forgeConfigs ? JVM.forgeConfigs(vm, modId) : [];
	cfgs.forEach(function (c) {
		c.cats.forEach(function (cat) {
			if (/^(block|item|blocks|items|ids?)$/i.test(cat.name)) return;
			var group = (cfgs.length > 1 ? c.path.split('/').pop().replace(/[.]cfg$/i, '') + ': ' : '') + cat.name.split('.').map(pretty).join(' > ');
			cat.props.forEach(function (p) {
				if (p.id || p.list) return;
				if (p.type === 'I' && /(^|[\s_.])(id|blockid|itemid)$/i.test(p.key)) return;
				var d = { id: 'cfg|' + c.path + '|' + cat.name + '|' + p.key, name: String(p.key).slice(0, 48), description: String(p.comment || '').slice(0, 200), group: group };
				if (p.type === 'B') { d.type = 'toggle'; d.default = /^true$/i.test(p.def != null ? p.def : p.value); }
				else if (p.type === 'I') { d.type = 'number'; d.min = -2147483648; d.max = 2147483647; d.step = 1; d.default = parseInt(p.def != null ? p.def : p.value, 10) || 0; }
				else if (p.type === 'D') { d.type = 'number'; d.min = -1e300; d.max = 1e300; d.step = 0; d.default = parseFloat(p.def != null ? p.def : p.value) || 0; }
				else { d.type = 'text'; d.default = String(p.def != null ? p.def : p.value); }
				d.current = p.type === 'B' ? /^true$/i.test(p.value) : p.type === 'I' ? parseInt(p.value, 10) || 0 : p.type === 'D' ? parseFloat(p.value) || 0 : String(p.value);
				out.push(d);
			});
		});
	});
	(reg(vm).mlprops || []).filter(function (p) { return p.mod === modId; }).forEach(function (p) {
		var d = { id: 'ml|' + p.file + '|' + p.name, name: String(p.name).slice(0, 48), description: String(p.info || '').slice(0, 200), group: 'Options' };
		if (p.desc === 'Z') d.type = 'toggle';
		else if (/^[IJSB]$/.test(p.desc)) { d.type = isFinite(p.min) && isFinite(p.max) && p.max - p.min <= 1000 ? 'slider' : 'number'; d.min = isFinite(p.min) ? p.min : -2147483648; d.max = isFinite(p.max) ? p.max : 2147483647; d.step = 1; }
		else if (/^[FD]$/.test(p.desc)) { d.type = 'number'; d.min = isFinite(p.min) ? p.min : -1e300; d.max = isFinite(p.max) ? p.max : 1e300; d.step = 0; }
		else d.type = 'text';
		d.default = p.def; d.current = p.value;
		out.push(d);
	});
	keysOf(vm).filter(function (k) { return k.mod === modId; }).forEach(function (k) {
		var desc = String(k.kb[':keyDescription'] || 'key');
		var label = reg(vm).lang[desc] || desc.replace(/^key[.]/, '');
		out.push({ id: 'key|' + desc, type: 'key', name: pretty(label).slice(0, 48), description: '', group: 'Controls', default: JVM.lwjglKey(k.kb[':keyCode'] | 0) });
	});
	return out;
};

function cfgPatch(text, cat, key, value) {
	var lines = String(text).split('\n'), stack = [], done = false;
	var unq = function (s) { s = s.trim(); return s[0] === '"' && s[s.length - 1] === '"' ? s.slice(1, -1) : s; };
	for (var i = 0; i < lines.length && !done; i++) {
		var l = lines[i].replace(/\r$/, ''), t = l.trim();
		if (!t || t[0] === '#') continue;
		var open = /^(.*)\{\s*$/.exec(t);
		if (open && t.indexOf('=') < 0) { stack.push(unq(open[1])); continue; }
		if (t === '}') { stack.pop(); continue; }
		var m = /^([SIBD]):("?)(.*?)\2=(.*)$/.exec(t);
		if (m && m[3] === key && stack.join('.').toLowerCase() === String(cat).toLowerCase()) {
			lines[i] = l.substring(0, l.indexOf(t)) + m[1] + ':' + m[2] + m[3] + m[2] + '=' + value + (/\r$/.test(lines[i]) ? '\r' : '');
			done = true;
		}
	}
	return done ? lines.join('\n') : null;
}
JVM.applyJavaSettings = function (fs, values) {
	var dec = new TextDecoder(), enc = new TextEncoder(), files = {};
	var get = function (path) { if (files[path] === undefined) { var b = fs.read(path); files[path] = b ? dec.decode(b) : null; } return files[path]; };
	Object.keys(values || {}).forEach(function (id) {
		var v = values[id], p = id.split('|');
		if (p[0] === 'cfg' && p.length >= 4) {
			var t = get(p[1]);
			if (t == null) return;
			var nt = cfgPatch(t, p[2], p.slice(3).join('|'), typeof v === 'boolean' ? (v ? 'true' : 'false') : String(v));
			if (nt != null) files[p[1]] = nt;
		} else if (p[0] === 'ml' && p.length >= 3) {
			var t2 = get(p[1]);
			if (t2 == null) return;
			var name = p.slice(2).join('|'), re = new RegExp('^' + name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&') + '=.*$', 'm');
			var val = typeof v === 'boolean' ? (v ? 'true' : 'false') : String(v);
			files[p[1]] = re.test(t2) ? t2.replace(re, name + '=' + val) : t2 + name + '=' + val + '\n';
		}
	});
	Object.keys(files).forEach(function (path) { if (files[path] != null) fs.write(path, enc.encode(files[path])); });
};

JVM.javaKey = function (vm, modId, settingId, down) {
	var desc = String(settingId).replace(/^key[|]/, '');
	keysOf(vm).filter(function (k) { return k.mod === modId && String(k.kb[':keyDescription']) === desc; }).forEach(function (k) {
		vm.currentMod = modId;
		k.kb[':pressed'] = down ? 1 : 0;
		if (down) k.kb.$presses = (k.kb.$presses | 0) + 1;
		JVM.run(vm, function () {
			if (k.kind === 'ml') { if (down) vm.callVirtual(k.owner, 'keyboardEvent', '(Lnet/minecraft/src/KeyBinding;)V', [k.kb]); }
			else {
				var tt = vm.loadClass('cpw/mods/fml/common/TickType'); vm.initClass(tt);
				var set = vm.callStatic('java/util/EnumSet', 'of', '(Ljava/lang/Enum;)Ljava/util/EnumSet;', [tt.statics.CLIENT]);
				if (down) vm.callVirtual(k.owner, 'keyDown', '(Ljava/util/EnumSet;Lnet/minecraft/src/KeyBinding;ZZ)V', [set, k.kb, 1, 0]);
				else vm.callVirtual(k.owner, 'keyUp', '(Ljava/util/EnumSet;Lnet/minecraft/src/KeyBinding;Z)V', [set, k.kb, 1]);
			}
		});
	});
};
JVM.javaKeysOf = function (vm) { return keysOf(vm).map(function (k) { return { mod: k.mod, id: 'key|' + k.kb[':keyDescription'] }; }); };

JVM.installSettings = installSettings;
})();

(function () {
'use strict';

var SRC = 'net/minecraft/src/';
function reg(vm) { return JVM.mc152.reg(vm); }
function tiles(vm) { var r = reg(vm); return r.tiles || (r.tiles = { classes: {}, names: new Map(), at: new Map(), ticking: [], dirty: false }); }
function K(x, y, z) { return (x | 0) + ',' + (y | 0) + ',' + (z | 0); }
function op(vm) { var g = vm.game; return g && (g.mode === 'run' || g.mode === 'gen') && g.op ? g.op.apply(null, Array.prototype.slice.call(arguments, 1)) : undefined; }

var TAG = { 1: 'NBTTagByte', 2: 'NBTTagShort', 3: 'NBTTagInt', 4: 'NBTTagLong', 5: 'NBTTagFloat', 6: 'NBTTagDouble', 7: 'NBTTagByteArray', 8: 'NBTTagString', 9: 'NBTTagList', 10: 'NBTTagCompound', 11: 'NBTTagIntArray' };
function tag(vm, t, v, name) {
	var o = vm.newObject(vm.loadClass(SRC + TAG[t]));
	o.$t = t; o.$v = v; o.$name = name || '';
	if (t === 10 && !v) o.$v = new Map();
	if (t === 9 && !v) { o.$v = []; o.$lt = 0; }
	setDataField(o);
	return o;
}
function setDataField(o) { if (o.$t !== 9 && o.$t !== 10) o[':data'] = o.$v; }
function compound(vm, name) { return tag(vm, 10, null, name); }
function cget(o, k) { return o && o.$v && o.$v.get(k); }
function cset(vm, o, k, t, v) { var x = tag(vm, t, v, k); o.$v.set(k, x); return x; }
JVM.nbtToJson = function (o) {
	if (!o) return null;
	switch (o.$t) {
	case 10: { var m = {}; o.$v.forEach(function (v, k) { m[k] = JVM.nbtToJson(v); }); return { t: 10, v: m }; }
	case 9: return { t: 9, lt: o.$lt | 0, v: o.$v.map(JVM.nbtToJson) };
	case 4: return { t: 4, v: String(o.$v) };
	case 7: case 11: return { t: o.$t, v: Array.prototype.slice.call(o.$v.a) };
	default: return { t: o.$t, v: o.$v };
	}
};
JVM.nbtFromJson = function (vm, j, name) {
	if (!j) return null;
	switch (j.t) {
	case 10: { var o = compound(vm, name); Object.keys(j.v).forEach(function (k) { o.$v.set(k, JVM.nbtFromJson(vm, j.v[k], k)); }); return o; }
	case 9: { var l = tag(vm, 9, j.v.map(function (x) { return JVM.nbtFromJson(vm, x, ''); }), name); l.$lt = j.lt; return l; }
	case 4: return tag(vm, 4, BigInt(j.v), name);
	case 7: { var b = vm.newArray('B', j.v.length); j.v.forEach(function (x, i) { b.a[i] = x; }); return tag(vm, 7, b, name); }
	case 11: { var a = vm.newArray('I', j.v.length); j.v.forEach(function (x, i) { a.a[i] = x; }); return tag(vm, 11, a, name); }
	default: return tag(vm, j.t, j.v, name);
	}
};

function installTiles(vm) {
	var def = function (n, s) { vm.defineNative(SRC + n, s); };
	var C = 'Lnet/minecraft/src/NBTTagCompound;', B = 'Lnet/minecraft/src/NBTBase;';
	def('NBTBase', { methods: {
		'getName()Ljava/lang/String;': function (vm, self) { return self.$name || ''; },
		'setName(Ljava/lang/String;)Lnet/minecraft/src/NBTBase;': function (vm, self, a) { self.$name = a[0]; return self; },
		'getId()B': function (vm, self) { return self.$t; },
		'copy()Lnet/minecraft/src/NBTBase;': function (vm, self) { return JVM.nbtFromJson(vm, JVM.nbtToJson(self), self.$name); },
		'toString()Ljava/lang/String;': function (vm, self) { return JSON.stringify(JVM.nbtToJson(self)); },
		'equals(Ljava/lang/Object;)Z': function (vm, self, a) { return a[0] && JSON.stringify(JVM.nbtToJson(a[0])) === JSON.stringify(JVM.nbtToJson(self)) ? 1 : 0; },
		'hashCode()I': function (vm, self) { return JVM.stringHash(JSON.stringify(JVM.nbtToJson(self))); },
	} });
	var prim = { 1: 'B', 2: 'S', 3: 'I', 4: 'J', 5: 'F', 6: 'D', 7: '[B', 8: 'Ljava/lang/String;', 11: '[I' };
	Object.keys(prim).forEach(function (t) {
		t = +t;
		var m = {};
		m['<init>(Ljava/lang/String;)V'] = function (vm, self, a) { self.$t = t; self.$name = a[0]; self.$v = t === 4 ? 0n : t === 8 ? '' : t === 7 || t === 11 ? vm.newArray(t === 7 ? 'B' : 'I', 0) : 0; setDataField(self); };
		m['<init>(Ljava/lang/String;' + prim[t] + ')V'] = function (vm, self, a) { self.$t = t; self.$name = a[0]; self.$v = a[1]; setDataField(self); };
		def(TAG[t], { super: SRC + 'NBTBase', fields: { data: prim[t] }, methods: m });
	});
	var getter = function (t, dflt) { return function (vm, self, a) { var x = cget(self, a[0]); if (!x) return typeof dflt === 'function' ? dflt(vm) : dflt; if (x.$t !== 9 && x.$t !== 10) x.$v = x[':data']; return x.$v; }; };
	var setter = function (t, conv) { return function (vm, self, a) { cset(vm, self, a[0], t, conv ? conv(a[1]) : a[1]); }; };
	def('NBTTagCompound', { super: SRC + 'NBTBase', methods: {
		'<init>()V': function (vm, self) { self.$t = 10; self.$v = new Map(); self.$name = ''; },
		'<init>(Ljava/lang/String;)V': function (vm, self, a) { self.$t = 10; self.$v = new Map(); self.$name = a[0]; },
		'setTag(Ljava/lang/String;Lnet/minecraft/src/NBTBase;)V': function (vm, self, a) { if (a[1]) { a[1].$name = a[0]; self.$v.set(a[0], a[1]); } },
		'setByte(Ljava/lang/String;B)V': setter(1), 'setShort(Ljava/lang/String;S)V': setter(2), 'setInteger(Ljava/lang/String;I)V': setter(3),
		'setLong(Ljava/lang/String;J)V': setter(4), 'setFloat(Ljava/lang/String;F)V': setter(5), 'setDouble(Ljava/lang/String;D)V': setter(6),
		'setString(Ljava/lang/String;Ljava/lang/String;)V': setter(8), 'setByteArray(Ljava/lang/String;[B)V': setter(7), 'setIntArray(Ljava/lang/String;[I)V': setter(11),
		'setBoolean(Ljava/lang/String;Z)V': setter(1, function (v) { return v ? 1 : 0; }),
		'setCompoundTag(Ljava/lang/String;Lnet/minecraft/src/NBTTagCompound;)V': function (vm, self, a) { if (a[1]) { a[1].$name = a[0]; self.$v.set(a[0], a[1]); } },
		'getTag(Ljava/lang/String;)Lnet/minecraft/src/NBTBase;': function (vm, self, a) { return cget(self, a[0]) || null; },
		'hasKey(Ljava/lang/String;)Z': function (vm, self, a) { return self.$v.has(a[0]) ? 1 : 0; },
		'removeTag(Ljava/lang/String;)V': function (vm, self, a) { self.$v.delete(a[0]); },
		'getByte(Ljava/lang/String;)B': getter(1, 0), 'getShort(Ljava/lang/String;)S': getter(2, 0), 'getInteger(Ljava/lang/String;)I': getter(3, 0),
		'getLong(Ljava/lang/String;)J': getter(4, 0n), 'getFloat(Ljava/lang/String;)F': getter(5, 0), 'getDouble(Ljava/lang/String;)D': getter(6, 0),
		'getString(Ljava/lang/String;)Ljava/lang/String;': getter(8, ''),
		'getByteArray(Ljava/lang/String;)[B': getter(7, function (vm) { return vm.newArray('B', 0); }),
		'getIntArray(Ljava/lang/String;)[I': getter(11, function (vm) { return vm.newArray('I', 0); }),
		'getBoolean(Ljava/lang/String;)Z': function (vm, self, a) { var x = cget(self, a[0]); return x && (x[':data'] !== undefined ? x[':data'] : x.$v) ? 1 : 0; },
		'getCompoundTag(Ljava/lang/String;)Lnet/minecraft/src/NBTTagCompound;': function (vm, self, a) { var x = cget(self, a[0]); return x && x.$t === 10 ? x : compound(vm, a[0]); },
		'getTagList(Ljava/lang/String;)Lnet/minecraft/src/NBTTagList;': function (vm, self, a) { var x = cget(self, a[0]); return x && x.$t === 9 ? x : tag(vm, 9, null, a[0]); },
		'getTags()Ljava/util/Collection;': function (vm, self) { return JVM.newList(vm, Array.from(self.$v.values())); },
		'hasNoTags()Z': function (vm, self) { return self.$v.size ? 0 : 1; },
		'copy()Lnet/minecraft/src/NBTBase;': function (vm, self) { return JVM.nbtFromJson(vm, JVM.nbtToJson(self), self.$name); },
	} });
	def('NBTTagList', { super: SRC + 'NBTBase', methods: {
		'<init>()V': function (vm, self) { self.$t = 9; self.$v = []; self.$lt = 0; self.$name = ''; },
		'<init>(Ljava/lang/String;)V': function (vm, self, a) { self.$t = 9; self.$v = []; self.$lt = 0; self.$name = a[0]; },
		'appendTag(Lnet/minecraft/src/NBTBase;)V': function (vm, self, a) { if (a[0]) { self.$lt = a[0].$t; self.$v.push(a[0]); } },
		'tagAt(I)Lnet/minecraft/src/NBTBase;': function (vm, self, a) { return self.$v[a[0]] || null; },
		'removeTag(I)Lnet/minecraft/src/NBTBase;': function (vm, self, a) { return self.$v.splice(a[0], 1)[0] || null; },
		'tagCount()I': function (vm, self) { return self.$v.length; },
	} });
	def('CompressedStreamTools', { staticMethods: {} });

	var IS = vm.natives[SRC + 'ItemStack'];
	IS.methods = Object.assign({}, IS.methods, {
		'writeToNBT(Lnet/minecraft/src/NBTTagCompound;)Lnet/minecraft/src/NBTTagCompound;': function (vm, self, a) {
			var c = a[0];
			cset(vm, c, 'id', 2, self[':itemID']); cset(vm, c, 'Count', 1, self[':stackSize']); cset(vm, c, 'Damage', 2, self[':itemDamage']);
			if (self[':stackTagCompound']) { self[':stackTagCompound'].$name = 'tag'; c.$v.set('tag', self[':stackTagCompound']); }
			return c;
		},
		'readFromNBT(Lnet/minecraft/src/NBTTagCompound;)V': function (vm, self, a) {
			var c = a[0], g = function (k) { var x = cget(c, k); return x ? x[':data'] : 0; };
			self[':itemID'] = g('id'); self[':stackSize'] = g('Count'); self[':itemDamage'] = Math.max(0, g('Damage'));
			var t = cget(c, 'tag'); if (t) self[':stackTagCompound'] = t;
		},
		'hasTagCompound()Z': function (vm, self) { return self[':stackTagCompound'] ? 1 : 0; },
		'getTagCompound()Lnet/minecraft/src/NBTTagCompound;': function (vm, self) { return self[':stackTagCompound'] || null; },
		'setTagCompound(Lnet/minecraft/src/NBTTagCompound;)V': function (vm, self, a) { self[':stackTagCompound'] = a[0]; },
		'getEnchantmentTagList()Lnet/minecraft/src/NBTTagList;': function (vm, self) { var t = self[':stackTagCompound']; var l = t && cget(t, 'ench'); return l || null; },
		'isItemEnchanted()Z': function (vm, self) { var t = self[':stackTagCompound']; return t && cget(t, 'ench') ? 1 : 0; },
	});
	IS.staticMethods = Object.assign({}, IS.staticMethods || {}, {
		'loadItemStackFromNBT(Lnet/minecraft/src/NBTTagCompound;)Lnet/minecraft/src/ItemStack;': function (vm, n, a) {
			var s = JVM.mc152.newStack(vm, 0, 0, 0);
			vm.callVirtual(s, 'readFromNBT', '(Lnet/minecraft/src/NBTTagCompound;)V', [a[0]]);
			return s[':itemID'] ? s : null;
		},
	});

	var W = 'Lnet/minecraft/src/World;';
	def('TileEntity', { fields: { worldObj: W, xCoord: 'I', yCoord: 'I', zCoord: 'I', tileEntityInvalid: 'Z', blockMetadata: 'I', blockType: 'Lnet/minecraft/src/Block;' }, methods: {
		'<init>()V': function (vm, self) { self[':blockMetadata'] = -1; },
		'readFromNBT(Lnet/minecraft/src/NBTTagCompound;)V': function (vm, self, a) { var g = function (k) { var x = cget(a[0], k); return x ? x[':data'] : 0; }; self[':xCoord'] = g('x'); self[':yCoord'] = g('y'); self[':zCoord'] = g('z'); },
		'writeToNBT(Lnet/minecraft/src/NBTTagCompound;)V': function (vm, self, a) {
			var name = tiles(vm).names.get(self.cls) || self.cls.name.split('/').pop();
			for (var c = self.cls; c && !tiles(vm).names.get(c); c = c.superClass) {}
			if (c) name = tiles(vm).names.get(c);
			cset(vm, a[0], 'id', 8, name); cset(vm, a[0], 'x', 3, self[':xCoord']); cset(vm, a[0], 'y', 3, self[':yCoord']); cset(vm, a[0], 'z', 3, self[':zCoord']);
		},
		'updateEntity()V': function () {},
		'getWorldObj()Lnet/minecraft/src/World;': function (vm, self) { return self[':worldObj']; },
		'setWorldObj(Lnet/minecraft/src/World;)V': function (vm, self, a) { self[':worldObj'] = a[0]; },
		'hasWorldObj()Z': function (vm, self) { return self[':worldObj'] ? 1 : 0; },
		'getBlockMetadata()I': function (vm, self) { var t = op(vm, 'tile', self[':xCoord'], self[':yCoord'], self[':zCoord']); return t ? t.data : 0; },
		'getBlockType()Lnet/minecraft/src/Block;': function (vm, self) { var t = op(vm, 'tile', self[':xCoord'], self[':yCoord'], self[':zCoord']); var bc = vm.loadClass(SRC + 'Block'); vm.initClass(bc); return t ? bc.statics.blocksList.a[t.id] || null : null; },
		'onInventoryChanged()V': function (vm) { tiles(vm).dirty = true; },
		'isInvalid()Z': function (vm, self) { return self[':tileEntityInvalid'] ? 1 : 0; },
		'invalidate()V': function (vm, self) { self[':tileEntityInvalid'] = 1; },
		'validate()V': function (vm, self) { self[':tileEntityInvalid'] = 0; },
		'updateContainingBlockInfo()V': function () {},
		'getDistanceFrom(DDD)D': function (vm, self, a) { var dx = self[':xCoord'] + 0.5 - a[0], dy = self[':yCoord'] + 0.5 - a[1], dz = self[':zCoord'] + 0.5 - a[2]; return dx * dx + dy * dy + dz * dz; },
		'getDescriptionPacket()Lnet/minecraft/src/Packet;': function () { return null; },
		'receiveClientEvent(II)Z': function () { return 0; },
		'canUpdate()Z': function () { return 1; },
		'shouldRefresh(IIIIILnet/minecraft/src/World;III)Z': function () { return 1; },
	}, staticMethods: {
		'addMapping(Ljava/lang/Class;Ljava/lang/String;)V': function (vm, n, a) { regTile(vm, a[0] && a[0].$cls, a[1]); },
		'createAndLoadEntity(Lnet/minecraft/src/NBTTagCompound;)Lnet/minecraft/src/TileEntity;': function (vm, n, a) { return loadTile(vm, a[0]); },
	} });
	def('ITileEntityProvider', { access: JVM.ACC_INTERFACE | JVM.ACC_ABSTRACT | JVM.ACC_PUBLIC });
	def('BlockContainer', { super: SRC + 'Block', interfaces: [SRC + 'ITileEntityProvider'], methods: {
		'<init>(ILnet/minecraft/src/Material;)V': function (vm, self, a) { vm.invoke(vm.loadClass(SRC + 'Block').methods['<init>(ILnet/minecraft/src/Material;)V'], self, a); self[':isBlockContainer'] = 1; },
		'onBlockAdded(Lnet/minecraft/src/World;III)V': function () {},
		'breakBlock(Lnet/minecraft/src/World;IIIII)V': function (vm, self, a) { removeTile(vm, a[1], a[2], a[3]); },
		'onBlockEventReceived(Lnet/minecraft/src/World;IIIII)Z': function () { return 0; },
	} });
	vm.natives[SRC + 'BlockContainer'].anyInit = function (vm, self, args, desc) { vm.natives[SRC + 'Block'].anyInit(vm, self, args, desc); self[':isBlockContainer'] = 1; };
	var BS = vm.natives[SRC + 'Block'];
	BS.methods = Object.assign({}, BS.methods, {
		'hasTileEntity(I)Z': function (vm, self) { return vm.isInstance(self, vm.loadClass(SRC + 'ITileEntityProvider')) ? 1 : 0; },
		'createTileEntity(Lnet/minecraft/src/World;I)Lnet/minecraft/src/TileEntity;': function (vm, self, a) { return vm.isInstance(self, vm.loadClass(SRC + 'ITileEntityProvider')) ? vm.callVirtual(self, 'createNewTileEntity', '(Lnet/minecraft/src/World;)Lnet/minecraft/src/TileEntity;', [a[0]]) : null; },
	});
	var ML = vm.natives[SRC + 'ModLoader'].staticMethods;
	ML['registerTileEntity(Ljava/lang/Class;Ljava/lang/String;)V'] = function (vm, n, a) { regTile(vm, a[0] && a[0].$cls, a[1]); };
	ML['registerTileEntity(Ljava/lang/Class;Ljava/lang/String;Lnet/minecraft/src/TileEntitySpecialRenderer;)V'] = function (vm, n, a) { regTile(vm, a[0] && a[0].$cls, a[1]); };
	[['cpw/mods/fml/common/registry/GameRegistry', 'registerTileEntity(Ljava/lang/Class;Ljava/lang/String;)V'],
	 ['cpw/mods/fml/common/registry/GameRegistry', 'registerTileEntityWithAlternatives(Ljava/lang/Class;Ljava/lang/String;[Ljava/lang/String;)V'],
	 ['cpw/mods/fml/client/registry/ClientRegistry', 'registerTileEntity(Ljava/lang/Class;Ljava/lang/String;Lnet/minecraft/src/TileEntitySpecialRenderer;)V']].forEach(function (p) {
		var sp = vm.natives[p[0]];
		if (!sp) return;
		var prev = sp.staticMethods[p[1]];
		sp.staticMethods[p[1]] = function (vm, n, a) { if (prev) prev(vm, n, a); regTile(vm, a[0] && a[0].$cls, a[1]); };
	});
	var WS = vm.natives[SRC + 'World'];
	WS.methods = Object.assign({}, WS.methods, {
		'getBlockTileEntity(III)Lnet/minecraft/src/TileEntity;': function (vm, self, a) { return tileAt(vm, a[0], a[1], a[2], true); },
		'setBlockTileEntity(IIILnet/minecraft/src/TileEntity;)V': function (vm, self, a) { putTile(vm, a[0], a[1], a[2], a[3]); },
		'removeBlockTileEntity(III)V': function (vm, self, a) { removeTile(vm, a[0], a[1], a[2]); },
		'markTileEntityChanged(IIILnet/minecraft/src/TileEntity;)V': function (vm) { tiles(vm).dirty = true; },
		'updateTileEntityChunkAndDoNothing(IIILnet/minecraft/src/TileEntity;)V': function (vm) { tiles(vm).dirty = true; },
		'addBlockEvent(IIIIII)V': function (vm, self, a) {
			var b = JVM.mc152.blockOf ? JVM.mc152.blockOf(vm, a[3]) : null;
			if (b) JVM.run(vm, function () { vm.callVirtual(b, 'onBlockEventReceived', '(Lnet/minecraft/src/World;IIIII)Z', [self, a[0], a[1], a[2], a[4], a[5]]); });
		},
	});
}

function regTile(vm, cls, name) { if (!cls || !name) return; var t = tiles(vm); t.classes[name] = cls; t.names.set(cls, name); }
JVM.registerTile = regTile;
function blockAt(vm, x, y, z) {
	var t = op(vm, 'tile', x, y, z);
	if (!t || !t.id) return null;
	var bc = vm.loadClass(SRC + 'Block'); vm.initClass(bc);
	var b = bc.statics.blocksList.a[t.id];
	return b && b.$mod ? { b: b, meta: t.data } : null;
}
function makeTile(vm, b, meta, world) {
	var te = null;
	JVM.run(vm, function () {
		if (vm.callVirtual(b, 'hasTileEntity', '(I)Z', [meta])) te = vm.callVirtual(b, 'createTileEntity', '(Lnet/minecraft/src/World;I)Lnet/minecraft/src/TileEntity;', [world, meta]);
	});
	return te;
}
function putTile(vm, x, y, z, te) {
	var t = tiles(vm);
	if (!te) return;
	te[':worldObj'] = JVM.mc152.worldObj(vm);
	te[':xCoord'] = x | 0; te[':yCoord'] = y | 0; te[':zCoord'] = z | 0;
	te[':tileEntityInvalid'] = 0;
	te.$mod = te.cls.source || vm.currentMod;
	t.at.set(K(x, y, z), te);
	var u = te.cls.findMethod('updateEntity()V');
	if (u && !u.cls.native && t.ticking.indexOf(te) < 0) t.ticking.push(te);
	t.dirty = true;
}
function tileAt(vm, x, y, z, create) {
	var t = tiles(vm), te = t.at.get(K(x, y, z));
	if (te || !create || !vm.game || vm.game.mode !== 'run') return te || null;
	var bm = blockAt(vm, x, y, z);
	if (!bm) return null;
	te = makeTile(vm, bm.b, bm.meta, JVM.mc152.worldObj(vm));
	if (te) putTile(vm, x, y, z, te);
	return te || null;
}
function removeTile(vm, x, y, z) {
	var t = tiles(vm), k = K(x, y, z), te = t.at.get(k);
	if (!te) return;
	te[':tileEntityInvalid'] = 1;
	t.at.delete(k);
	var i = t.ticking.indexOf(te);
	if (i >= 0) t.ticking.splice(i, 1);
	t.dirty = true;
}
function loadTile(vm, c) {
	var idTag = cget(c, 'id'), name = idTag && idTag[':data'];
	var cls = name && tiles(vm).classes[name];
	if (!cls) return null;
	var te = vm.newObject(cls), k = cls.findDeclared('<init>()V');
	if (k) vm.invoke(k, te, []);
	vm.callVirtual(te, 'readFromNBT', '(Lnet/minecraft/src/NBTTagCompound;)V', [c]);
	return te;
}

JVM.tilePlaced = function (vm, x, y, z) {
	if (tiles(vm).at.get(K(x, y, z))) return;
	var bm = blockAt(vm, x, y, z);
	if (!bm) return;
	var te = makeTile(vm, bm.b, bm.meta, JVM.mc152.worldObj(vm));
	if (te) putTile(vm, x, y, z, te);
};
JVM.tileBroken = function (vm, x, y, z) { removeTile(vm, x, y, z); };
JVM.tilesWantTick = function (vm) { var r = vm.mcReg; return !!(r && r.tiles && (r.tiles.ticking.length || Object.keys(r.tiles.classes).length)); };
JVM.tileTick = function (vm) {
	var t = vm.mcReg && vm.mcReg.tiles;
	if (!t || !t.ticking.length) return;
	t.ticking.slice().forEach(function (te) {
		if (te[':tileEntityInvalid']) return;
		vm.currentMod = te.$mod || vm.currentMod;
		JVM.run(vm, function () { vm.callVirtual(te, 'updateEntity', '()V', []); });
	});
	t.dirty = true;
};
JVM.tileSave = function (vm) {
	var t = vm.mcReg && vm.mcReg.tiles;
	if (!t || !vm.fs) return;
	var byMod = {};
	t.at.forEach(function (te) {
		var mod = te.$mod || '';
		JVM.run(vm, function () {
			var c = compound(vm, '');
			vm.callVirtual(te, 'writeToNBT', '(Lnet/minecraft/src/NBTTagCompound;)V', [c]);
			(byMod[mod] || (byMod[mod] = [])).push(JVM.nbtToJson(c));
		});
	});
	var prev = vm.currentMod;
	Object.keys(t.mods || {}).concat(Object.keys(byMod)).forEach(function (mod) {
		vm.currentMod = mod;
		vm.fs.write('world/tileentities.json', new TextEncoder().encode(JSON.stringify({ format: 1, tiles: byMod[mod] || [] })));
	});
	vm.currentMod = prev;
	t.dirty = false;
};
JVM.tileLoad = function (vm, mods) {
	var t = tiles(vm);
	t.at = new Map(); t.ticking = []; t.mods = {};
	if (!vm.fs) return;
	var prev = vm.currentMod;
	mods.forEach(function (mod) {
		t.mods[mod] = true;
		vm.currentMod = mod;
		var b = vm.fs.read('world/tileentities.json');
		if (!b) return;
		var j;
		try { j = JSON.parse(new TextDecoder().decode(b)); } catch (e) { vm.log('warn', mod + ': saved tile entities could not be read'); return; }
		(j.tiles || []).forEach(function (tj) {
			JVM.run(vm, function () {
				var c = JVM.nbtFromJson(vm, tj, '');
				var te = loadTile(vm, c);
				if (te) putTile(vm, te[':xCoord'], te[':yCoord'], te[':zCoord'], te);
			});
		});
	});
	vm.currentMod = prev;
	t.dirty = false;
};

JVM.installTiles = installTiles;
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
