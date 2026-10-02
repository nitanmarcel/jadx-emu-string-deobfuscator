package jadx.emu.ext.strings

import jadx.plugins.emu.exec.AbsHeap
import jadx.plugins.emu.exec.CallResolver
import jadx.plugins.emu.exec.graph.entryFrameRegs
import jadx.plugins.emu.exec.ExecHook
import jadx.plugins.emu.exec.ExecLimits
import jadx.plugins.emu.exec.Frame
import jadx.plugins.emu.exec.Interpreter
import jadx.plugins.emu.exec.MethodSource
import jadx.plugins.emu.exec.NotHandled
import jadx.plugins.emu.exec.DvmMethodHandle
import jadx.plugins.emu.exec.Vm
import jadx.plugins.emu.exec.runtime.DvmObject
import jadx.plugins.emu.exec.model.ArrayPayload
import jadx.plugins.emu.exec.model.DalvikInsn
import jadx.plugins.emu.exec.model.DexMethod
import jadx.plugins.emu.exec.model.FieldRef
import jadx.plugins.emu.exec.model.MethodRef
import jadx.plugins.emu.exec.model.StringRef
import jadx.plugins.emu.exec.model.SwitchPayload
import jadx.plugins.emu.exec.model.TypeRef
import jadx.plugins.emu.exec.runtime.UnknownVal
import jadx.api.plugins.input.insns.Opcode

data class StringSite(val offset: Int, val value: String, val deadOffsets: Set<Int>)

data class InsnAnnotation(val descriptor: String, val offset: Int, val text: String)

class StringDecryptor(
    private val source: MethodSource,
    private val limits: ExecLimits = ExecLimits(maxMillis = 2000),
    ctx: jadx.plugins.emu.exec.EngineContext? = null,
) {
    private val ctx = ctx ?: jadx.plugins.emu.exec.EngineContext(source, limits)
    private var predsMethod: DexMethod? = null
    private var predsCache: Map<Int, List<Int>>? = null

    fun recover(method: DexMethod): List<InsnAnnotation> =
        recoverMap(method).map { (k, v) -> InsnAnnotation(k.first, k.second, render(v)) }

    fun recoverRaw(method: DexMethod): Map<Int, String> =
        recoverMap(method).entries.associate { it.key.second to it.value }

    fun recoverSites(method: DexMethod): List<StringSite> {
        val idxByOffset = HashMap<Int, Int>()
        method.insns.forEachIndexed { i, ins -> idxByOffset[ins.offset] = i }
        return recoverMap(method).map { (k, v) ->
            val idx = idxByOffset[k.second]
            val dead = if (idx != null && isInvoke(method.insns[idx]))
                runCatching { deadSlice(method, idx) }.getOrDefault(emptySet()) else emptySet()
            StringSite(k.second, v, dead)
        }
    }

    private fun isInvoke(insn: DalvikInsn): Boolean =
        insn.opcode == Opcode.INVOKE_STATIC || insn.opcode == Opcode.INVOKE_STATIC_RANGE ||
            insn.opcode == Opcode.INVOKE_VIRTUAL || insn.opcode == Opcode.INVOKE_VIRTUAL_RANGE ||
            insn.opcode == Opcode.INVOKE_DIRECT || insn.opcode == Opcode.INVOKE_DIRECT_RANGE ||
            insn.opcode == Opcode.INVOKE_INTERFACE || insn.opcode == Opcode.INVOKE_INTERFACE_RANGE

    private fun deadSlice(method: DexMethod, callIndex: Int): Set<Int> {
        val dead = LinkedHashSet<Int>()
        val work = ArrayDeque<Pair<Int, Int>>()
        for (r in method.insns[callIndex].regs) work.addLast(callIndex to r)
        while (work.isNotEmpty()) {
            val (before, reg) = work.removeLast()
            for (d in reachingDefs(method, before, reg)) {
                if (d == NO_DEF || d in dead) continue
                val di = method.insns[d]
                if (di.opcode !in PURE_PRODUCERS) continue
                dead.add(d)
                for (i in 1 until di.regs.size) work.addLast(d to di.regs[i])
                if (di.opcode == Opcode.NEW_ARRAY) collectArrayFills(method, d, di.regs[0], callIndex, dead, work)
            }
        }
        for (k in dead) {
            val r = definesReg(method.insns[k]) ?: continue
            if (hasExternalReader(method, k, r, dead, callIndex)) return emptySet()
        }
        return dead.mapTo(HashSet()) { method.insns[it].offset }
    }

    private fun collectArrayFills(
        method: DexMethod, newIdx: Int, arrReg: Int, callIndex: Int,
        dead: MutableSet<Int>, work: ArrayDeque<Pair<Int, Int>>,
    ) {
        for (j in newIdx + 1 until callIndex) {
            val fj = method.insns[j]
            when {
                fj.opcode == Opcode.FILL_ARRAY_DATA && fj.regs.getOrNull(0) == arrReg -> dead.add(j)
                fj.opcode in APUTS && fj.regs.getOrNull(1) == arrReg -> {
                    dead.add(j); work.addLast(j to fj.regs[0]); work.addLast(j to fj.regs[2])
                }
                definesReg(fj) == arrReg -> return
            }
        }
    }

    private fun hasExternalReader(method: DexMethod, defIdx: Int, reg: Int, dead: Set<Int>, callIndex: Int): Boolean {
        for (j in method.insns.indices) {
            if (j == defIdx || j == callIndex || j in dead) continue
            val ins = method.insns[j]
            val srcStart = if (definesReg(ins) != null) 1 else 0
            var reads = false
            for (p in srcStart until ins.regs.size) if (ins.regs[p] == reg) { reads = true; break }
            if (reads && defIdx in reachingDefs(method, j, reg)) return true
        }
        return false
    }

    private fun recoverMap(method: DexMethod): Map<Pair<String, Int>, String> {
        val out = LinkedHashMap<Pair<String, Int>, String>()
        runCatching { reconstructCallSites(method, out) }
        runCatching { reconstructSideEffectCallSites(method, out) }
        runCatching { reconstructPoolReads(method, out) }
        runCatching { reconstructStringCtors(method, out) }
        val captured = HashMap<Pair<String, Int>, Any>()
        runCatching { callerRun(method, captured) }
        runCatching { forkCapture(method, captured) }
        for ((key, v) in captured) if (v is String && key !in out) out[key] = v
        return out
    }

    private fun capture(captured: MutableMap<Pair<String, Int>, Any>, method: DexMethod, key: Pair<String, Int>, value: String) {
        val idx = method.offsetToIndex[key.second] ?: return
        if (inLoop(method, idx)) return
        val prev = captured.putIfAbsent(key, value)
        if (prev != null && prev != value) captured[key] = CONFLICT
    }

    private fun inLoop(method: DexMethod, idx: Int): Boolean {
        val seen = HashSet<Int>()
        val stack = ArrayDeque<Int>().apply { successorIndices(method, idx).forEach { addLast(it) } }
        while (stack.isNotEmpty()) {
            val j = stack.removeLast()
            if (j == idx) return true
            if (seen.add(j)) successorIndices(method, j).forEach { stack.addLast(it) }
        }
        return false
    }

    fun recoverAll(methods: List<DexMethod>): List<InsnAnnotation> =
        methods.flatMap { runCatching { recover(it) }.getOrDefault(emptyList()) }

    private val decoderCache = HashMap<String, Boolean>()

    private val decoderInProgress = HashSet<String>()

    fun isDecoderMethod(m: DexMethod): Boolean {
        val key = "${m.declClass}->${m.ref.shortId}"
        decoderCache[key]?.let { return it }
        if (!decoderInProgress.add(key)) return false
        var result = false
        var hasXor = false
        var hasArith = false
        var hasArrayElem = false
        var buildsString = false
        val callees = ArrayList<MethodRef>()
        loop@ for (insn in m.insns) {
            when (insn.opcode) {
                Opcode.XOR_INT, Opcode.XOR_INT_LIT, Opcode.XOR_LONG -> { hasXor = true; hasArith = true }
                in TRANSFORM_ARITH -> hasArith = true
                in ARRAY_ELEM -> hasArrayElem = true
                else -> (insn.ref as? MethodRef)?.let { r ->
                    if (cryptoApi(r)) { result = true; break@loop }
                    if (buildsStringFromArray(r)) buildsString = true else callees.add(r)
                }
            }
            if (hasXor && hasArrayElem) { result = true; break@loop }
        }
        if (!result && hasArith && hasArrayElem && buildsString && m.ref.returnType == "Ljava/lang/String;") result = true
        if (!result) {
            for (r in callees) {
                if (isDispatcher(r)) continue
                val callee = source.method(r.declClass, r.shortId) ?: continue
                if (isDecoderMethod(callee)) { result = true; break }
            }
        }
        decoderInProgress.remove(key)
        decoderCache[key] = result
        return result
    }

    private fun isDispatcher(r: MethodRef): Boolean =
        r.argTypes.firstOrNull() == "I" && dispatcherHandles(r.declClass) != null

    private val handleCache = HashMap<String, List<DexMethod?>?>()

    private fun dispatcherHandles(cls: String): List<DexMethod?>? = handleCache.getOrPut(cls) {
        val vm = ctx.newVm(limits)
        runCatching { vm.ensureClinit(cls) }
        (vm.staticsOf(cls).values.firstOrNull { it is List<*> && it.isNotEmpty() && it.all { e -> e is DvmMethodHandle } } as? List<*>)
            ?.map { (it as? DvmMethodHandle)?.dexMethod }
    }

    private fun resolveTarget(callee: DexMethod, args: List<Any?>): DexMethod {
        if (!isDispatcher(callee.ref)) return callee
        val idx = args.getOrNull(0) as? Int ?: return callee
        return dispatcherHandles(callee.declClass)?.getOrNull(idx) ?: callee
    }

    private fun foldable(callee: DexMethod, args: List<Any?>): Boolean {
        val target = resolveTarget(callee, args)
        return isDecoderMethod(target) && !isStateful(target)
    }

    private val statefulCache = HashMap<String, Boolean>()

    private fun isStateful(m: DexMethod): Boolean = statefulCache.getOrPut("${m.declClass}->${m.ref.shortId}") {
        val seen = HashSet<String>()
        val work = ArrayDeque<DexMethod>().apply { add(m) }
        var stateful = false
        while (work.isNotEmpty() && !stateful) {
            val cur = work.removeFirst()
            if (!seen.add("${cur.declClass}->${cur.ref.shortId}")) continue
            val lazyInit = lazyInitFields(cur)
            for (insn in cur.insns) {
                when (insn.opcode) {
                    Opcode.SPUT -> {
                        val fr = insn.ref as? FieldRef ?: continue
                        if (source.classInfo(fr.declClass) != null && fr.key !in lazyInit) { stateful = true; break }
                    }
                    in INVOKE_OPCODES -> (insn.ref as? MethodRef)?.let { r -> source.method(r.declClass, r.shortId)?.let { work.add(it) } }
                    else -> {}
                }
            }
        }
        stateful
    }

    private fun lazyInitFields(m: DexMethod): Set<String> {
        val out = HashSet<String>()
        val insns = m.insns
        for (i in insns.indices) {
            val sget = insns[i]
            if (sget.opcode != Opcode.SGET) continue
            val fr = sget.ref as? FieldRef ?: continue
            val reg = sget.regs[0]
            for (j in i + 1 until insns.size) {
                val t = insns[j]
                if ((t.opcode == Opcode.IF_EQZ || t.opcode == Opcode.IF_NEZ) && t.regs[0] == reg) { out.add(fr.key); break }
                if (definesReg(t) == reg || t.opcode in IF_OPS || t.opcode == Opcode.GOTO || t.opcode in INVOKE_OPCODES) break
            }
        }
        return out
    }

    private fun plausible(s: String): Boolean {
        if (s.isEmpty()) return false
        val ctrl = s.count { it.isISOControl() && it != '\t' && it != '\n' && it != '\r' }
        return ctrl * 2 < s.length
    }

    private fun render(s: String) = "\"${s.replace("\\", "\\\\").replace("\"", "\\\"")}\""

    private fun reconstructCallSites(method: DexMethod, out: MutableMap<Pair<String, Int>, String>) {
        val desc = "${method.declClass}->${method.ref.shortId}"
        val insns = method.insns
        for (ci in insns.indices) {
            val insn = insns[ci]
            if (insn.opcode != Opcode.INVOKE_STATIC && insn.opcode != Opcode.INVOKE_STATIC_RANGE) continue
            val ref = insn.ref as? MethodRef ?: continue
            if (ref.returnType != "Ljava/lang/String;" && ref.returnType != "Ljava/lang/Object;") continue
            val callee = source.method(ref.declClass, ref.shortId) ?: continue
            val key = desc to insn.offset
            if (key in out) continue
            val args = reconstructStaticArgs(method, ci, ref, 0) ?: continue
            if (!foldable(callee, args)) continue
            val r = runCallee(callee, args, method.declClass)
            if (r is String && plausible(r)) out[key] = r
        }
    }

    private fun reconstructStaticArgs(method: DexMethod, callIndex: Int, ref: MethodRef, depth: Int): List<Any?>? {
        if (depth > 24) return null
        val regs = method.insns[callIndex].regs
        var i = 0
        val args = ArrayList<Any?>(ref.argTypes.size)
        for (t in ref.argTypes) {
            val reg = regs.getOrNull(i) ?: return null
            args.add(valueOf(method, callIndex, reg, depth) ?: return null)
            i += if (t == "J" || t == "D") 2 else 1
        }
        return args
    }

    private fun reconstructSideEffectCallSites(method: DexMethod, out: MutableMap<Pair<String, Int>, String>) {
        val desc = "${method.declClass}->${method.ref.shortId}"
        val insns = method.insns
        for (ci in insns.indices) {
            val insn = insns[ci]
            if (insn.opcode != Opcode.INVOKE_STATIC && insn.opcode != Opcode.INVOKE_STATIC_RANGE) continue
            val ref = insn.ref as? MethodRef ?: continue
            val hasBuilder = ref.argTypes.any { it == BUILDER || it == BUFFER }
            val hasArray = ref.argTypes.any { it.startsWith("[") }
            if (!hasBuilder || !hasArray) continue
            val callee = source.method(ref.declClass, ref.shortId) ?: continue
            val key = desc to insn.offset
            if (key in out) continue
            val (args, sinks) = reconstructMixedArgs(method, ci, ref) ?: continue
            runCallee(callee, args, method.declClass)
            val text = sinks.map { it.toString() }.firstOrNull { it.isNotEmpty() && it.any(Char::isLetterOrDigit) } ?: continue
            out[key] = text
        }
    }

    private fun reconstructMixedArgs(method: DexMethod, callIndex: Int, ref: MethodRef): Pair<List<Any?>, List<Any>>? {
        val regs = method.insns[callIndex].regs
        var i = 0
        val args = ArrayList<Any?>(ref.argTypes.size)
        val sinks = ArrayList<Any>()
        for (t in ref.argTypes) {
            val reg = regs.getOrNull(i) ?: return null
            val v: Any? = when (t) {
                BUILDER -> StringBuilder().also { sinks.add(it) }
                BUFFER -> StringBuffer().also { sinks.add(it) }
                "Ljava/lang/String;" -> valueOf(method, callIndex, reg, 0) ?: ""
                else -> valueOf(method, callIndex, reg, 0) ?: return null
            }
            args.add(v)
            i += if (t == "J" || t == "D") 2 else 1
        }
        return args to sinks
    }

    private fun valueOf(method: DexMethod, before: Int, reg: Int, depth: Int): Any? {
        if (depth > 24) return null
        val defs = reachingDefs(method, before, reg)
        if (defs.isEmpty() || NO_DEF in defs) return null
        var resolved: Any? = NO_VALUE
        for (d in defs) {
            val v = defValue(method, d, reg, before, depth) ?: return null
            if (resolved === NO_VALUE) resolved = v else if (!valEq(resolved, v)) return null
        }
        return if (resolved === NO_VALUE) null else resolved
    }

    private fun defValue(method: DexMethod, j: Int, reg: Int, before: Int, depth: Int): Any? {
        val insn = method.insns[j]
        return when (insn.opcode) {
            Opcode.CONST -> insn.literal.toInt()
            Opcode.CONST_WIDE -> insn.literal
            Opcode.CONST_STRING -> (insn.ref as? StringRef)?.value
            Opcode.MOVE, Opcode.MOVE_OBJECT, Opcode.MOVE_WIDE -> valueOf(method, j, insn.regs[1], depth + 1)
            Opcode.NEW_ARRAY -> reconstructArray(method, j, reg, before, depth)
            Opcode.SGET -> staticFieldValue(insn.ref as? FieldRef ?: return null)
            Opcode.AGET, Opcode.AGET_OBJECT, Opcode.AGET_BYTE, Opcode.AGET_BYTE_BOOLEAN,
            Opcode.AGET_BOOLEAN, Opcode.AGET_CHAR, Opcode.AGET_SHORT -> {
                val arr = valueOf(method, j, insn.regs[1], depth + 1) ?: return null
                val idx = valueOf(method, j, insn.regs[2], depth + 1) as? Int ?: return null
                runCatching { java.lang.reflect.Array.get(arr, idx) }.getOrNull()
            }
            Opcode.MOVE_RESULT -> {
                val inv = method.insns.getOrNull(j - 1) ?: return null
                if (inv.opcode != Opcode.INVOKE_STATIC && inv.opcode != Opcode.INVOKE_STATIC_RANGE) return null
                val iref = inv.ref as? MethodRef ?: return null
                val callee = source.method(iref.declClass, iref.shortId) ?: return null
                val a = reconstructStaticArgs(method, j - 1, iref, depth + 1) ?: return null
                runCallee(callee, a, method.declClass)
            }
            else -> null
        }
    }

    private fun reachingDefs(method: DexMethod, before: Int, reg: Int): Set<Int> {
        val preds = predsOf(method)
        val starts = preds[before]
        if (starts.isNullOrEmpty()) return setOf(NO_DEF)
        val result = HashSet<Int>()
        val visited = HashSet<Int>()
        val stack = ArrayDeque<Int>().apply { starts.forEach { addLast(it) } }
        while (stack.isNotEmpty()) {
            val j = stack.removeLast()
            if (!visited.add(j)) continue
            if (definesReg(method.insns[j]) == reg) { result.add(j); continue }
            val ps = preds[j]
            if (ps.isNullOrEmpty()) result.add(NO_DEF) else ps.forEach { stack.addLast(it) }
        }
        return result
    }

    private fun predsOf(method: DexMethod): Map<Int, List<Int>> {
        if (predsMethod === method) return predsCache!!
        val preds = HashMap<Int, MutableList<Int>>()
        for (i in method.insns.indices) for (s in successorIndices(method, i)) preds.getOrPut(s) { ArrayList() }.add(i)
        predsMethod = method
        predsCache = preds
        return preds
    }

    private fun successorIndices(method: DexMethod, i: Int): List<Int> {
        val insn = method.insns[i]
        val o2i = method.offsetToIndex
        val next = i + 1
        val out = ArrayList<Int>(2)
        fun add(off: Int) { o2i[off]?.let { out.add(it) } }
        fun fall() { if (next in method.insns.indices) out.add(next) }
        when (insn.opcode) {
            Opcode.RETURN, Opcode.RETURN_VOID, Opcode.THROW -> {}
            Opcode.GOTO -> add(insn.target)
            in IF_OPS -> { add(insn.target); fall() }
            Opcode.PACKED_SWITCH, Opcode.SPARSE_SWITCH -> {
                (insn.payload as? SwitchPayload)?.let { sw -> for (t in sw.targets) add(insn.offset + t) }
                fall()
            }
            else -> fall()
        }
        return out
    }

    private fun valEq(a: Any?, b: Any?): Boolean = when {
        a === b -> true
        a is ByteArray && b is ByteArray -> a.contentEquals(b)
        a is IntArray && b is IntArray -> a.contentEquals(b)
        a is CharArray && b is CharArray -> a.contentEquals(b)
        a is Array<*> && b is Array<*> -> a.contentEquals(b)
        else -> a == b
    }

    private fun reconstructArray(method: DexMethod, newIdx: Int, reg: Int, before: Int, depth: Int): Any? {
        val desc = (method.insns[newIdx].ref as? TypeRef)?.desc ?: return null
        val size = valueOf(method, newIdx, method.insns[newIdx].regs[1], depth + 1) as? Int ?: return null
        if (size < 0 || size > 1_000_000) return null
        val arr = newArray(desc, size) ?: return null
        val aliases = HashSet<Int>().apply { add(reg) }
        for (j in newIdx + 1 until before) {
            val insn = method.insns[j]
            when {
                insn.opcode == Opcode.FILL_ARRAY_DATA && insn.regs.getOrNull(0) in aliases ->
                    fillArray(arr, (insn.payload as? ArrayPayload)?.data ?: return null)
                insn.opcode in APUTS && insn.regs.getOrNull(1) in aliases -> {
                    val idx = valueOf(method, j, insn.regs[2], depth + 1) as? Int ?: return null
                    val v = valueOf(method, j, insn.regs[0], depth + 1) ?: return null
                    if (idx !in 0 until size) return null
                    aput(arr, idx, v)
                }
                (insn.opcode == Opcode.MOVE || insn.opcode == Opcode.MOVE_OBJECT) && insn.regs.size == 2 -> {
                    val (dst, src) = insn.regs[0] to insn.regs[1]
                    if (src in aliases) aliases.add(dst) else if (dst == reg) return null else aliases.remove(dst)
                }
                definesReg(insn) == reg -> return null
                definesReg(insn) in aliases -> aliases.remove(definesReg(insn))
            }
        }
        return arr
    }

    private fun reconstructStringCtors(method: DexMethod, out: MutableMap<Pair<String, Int>, String>) {
        val desc = "${method.declClass}->${method.ref.shortId}"
        for (i in method.insns.indices) {
            val insn = method.insns[i]
            if (insn.opcode != Opcode.INVOKE_DIRECT && insn.opcode != Opcode.INVOKE_DIRECT_RANGE) continue
            val ref = insn.ref as? MethodRef ?: continue
            if (ref.declClass != "Ljava/lang/String;" || ref.name != "<init>") continue
            if (ref.argTypes.none { it.startsWith("[") }) continue
            val key = desc to insn.offset
            if (key in out) continue
            val s = reconstructNewString(method, i, ref) ?: continue
            if (s.isNotEmpty() && s.any(Char::isLetterOrDigit)) out[key] = s
        }
    }

    private fun reconstructNewString(method: DexMethod, callIndex: Int, ref: MethodRef): String? {
        val regs = method.insns[callIndex].regs
        var i = 1
        val args = ArrayList<Any?>(ref.argTypes.size)
        for (t in ref.argTypes) {
            args.add(valueOf(method, callIndex, regs.getOrNull(i) ?: return null, 0) ?: return null)
            i += if (t == "J" || t == "D") 2 else 1
        }
        return ctx.newVm(limits).hostExec.construct("Ljava/lang/String;", ref, args) as? String
    }

    private fun runCallee(callee: DexMethod, args: List<Any?>, callerDecl: String): Any? {
        val vm = ctx.newVm(limits)
        vm.android.syntheticCaller = callerDecl.removePrefix("L").removeSuffix(";").replace('/', '.')
        return runCatching { vm.invoke(callee, args) }.getOrNull()
    }

    private fun staticFieldValue(fr: FieldRef): Any? {
        val vm = ctx.newVm(limits)
        runCatching { vm.ensureClinit(fr.declClass) }
        return if (source.classInfo(fr.declClass) != null) vm.staticsOf(fr.declClass)["${fr.declClass}.${fr.name}"]
        else vm.hostStaticField(fr.declClass, fr.name).let { if (it !== NotHandled) it else null }
    }

    private fun reconstructPoolReads(method: DexMethod, out: MutableMap<Pair<String, Int>, String>) {
        val desc = "${method.declClass}->${method.ref.shortId}"
        for (i in method.insns.indices) {
            val insn = method.insns[i]
            if (insn.opcode != Opcode.AGET_OBJECT) continue
            val key = desc to insn.offset
            if (key in out) continue
            val arr = valueOf(method, i, insn.regs[1], 0) as? Array<*> ?: continue
            val idx = valueOf(method, i, insn.regs[2], 0) as? Int ?: continue
            val el = arr.getOrNull(idx) as? String ?: continue
            if (el.isNotEmpty()) out[key] = el
        }
    }

    private fun definesReg(insn: DalvikInsn): Int? = if (insn.opcode in NON_DEFINING) null else insn.regs.getOrNull(0)

    private fun newArray(desc: String, len: Int): Any? = when (desc) {
        "[B" -> ByteArray(len); "[I" -> IntArray(len); "[C" -> CharArray(len); "[S" -> ShortArray(len)
        "[Z" -> BooleanArray(len); "[J" -> LongArray(len); "[F" -> FloatArray(len); "[D" -> DoubleArray(len)
        "[Ljava/lang/String;" -> arrayOfNulls<String>(len)
        "[Ljava/lang/Object;" -> arrayOfNulls<Any?>(len)
        else -> null
    }

    private fun fillArray(arr: Any, data: Any) {
        val n = java.lang.reflect.Array.getLength(data)
        for (k in 0 until n) {
            val x = java.lang.reflect.Array.get(data, k) as Number
            when (arr) {
                is ByteArray -> arr[k] = x.toByte(); is IntArray -> arr[k] = x.toInt(); is ShortArray -> arr[k] = x.toShort()
                is CharArray -> arr[k] = x.toInt().toChar(); is BooleanArray -> arr[k] = x.toInt() != 0; is LongArray -> arr[k] = x.toLong()
                is FloatArray -> arr[k] = Float.fromBits(x.toInt()); is DoubleArray -> arr[k] = Double.fromBits(x.toLong())
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    private fun aput(arr: Any, idx: Int, v: Any?) {
        when (arr) {
            is ByteArray -> arr[idx] = ci(v).toByte(); is IntArray -> arr[idx] = ci(v); is CharArray -> arr[idx] = ci(v).toChar()
            is ShortArray -> arr[idx] = ci(v).toShort(); is BooleanArray -> arr[idx] = ci(v) != 0; is LongArray -> arr[idx] = (v as? Long) ?: ci(v).toLong()
            is FloatArray -> arr[idx] = (v as? Float) ?: 0f; is DoubleArray -> arr[idx] = (v as? Double) ?: 0.0
            is Array<*> -> (arr as Array<Any?>)[idx] = v
        }
    }

    private fun ci(v: Any?): Int = when (v) { is Int -> v; is Byte -> v.toInt(); is Short -> v.toInt(); is Char -> v.code; is Boolean -> if (v) 1 else 0; is Long -> v.toInt(); else -> 0 }

    private fun callerRun(method: DexMethod, out: MutableMap<Pair<String, Int>, Any>) {
        if (method.insns.none { isCaptureCandidate(it) }) return
        val hook = Capture(method, out)
        val vm = ctx.newVm(limits, hook = hook)
        val recv = if (method.isStatic) null else UnknownVal(method.declClass)
        val args = method.ref.argTypes.map { UnknownVal(it) }
        runCatching { vm.invoke(method, args, recv) }
    }

    private fun forkCapture(method: DexMethod, out: MutableMap<Pair<String, Int>, Any>) {
        val insns = method.insns
        if (insns.none { isCaptureCandidate(it) }) return
        val desc = "${method.declClass}->${method.ref.shortId}"
        val vm = ctx.newVm(limits)
        val interp = Interpreter(vm)
        runCatching { vm.ensureClinit(method.declClass) }
        val heap = object : AbsHeap {
            override fun newInstance(site: String, type: String): Any? = if (source.classInfo(type) != null) DvmObject(type) else UnknownVal(type)
            override fun iget(obj: Any?, key: String, type: String): Any? = (obj as? DvmObject)?.fields?.get(key) ?: UnknownVal(type)
            override fun iput(obj: Any?, key: String, v: Any?) { (obj as? DvmObject)?.fields?.put(key, v) }
            override fun sget(declClass: String, key: String, type: String): Any? = vm.staticsOf(declClass)[key] ?: UnknownVal(type)
            override fun sput(declClass: String, key: String, v: Any?) { vm.staticsOf(declClass)[key] = v }
        }
        val resolver = CallResolver { insn, frame ->
            val ref = insn.ref as MethodRef
            val hasReceiver = insn.opcode != Opcode.INVOKE_STATIC && insn.opcode != Opcode.INVOKE_STATIC_RANGE
            val (recv, args) = interp.gatherArgs(insn, frame, ref, hasReceiver)
            val res = if ((hasReceiver && recv is UnknownVal) || args.any { it is UnknownVal }) UnknownVal(ref.returnType)
            else runCatching {
                val target = if (hasReceiver) interp.resolveVirtualFor((recv as? DvmObject)?.type ?: ref.declClass, ref.shortId)
                else source.method(ref.declClass, ref.shortId)
                when {
                    target != null -> vm.call(target, args, recv)
                    hasReceiver -> vm.hostExec.invokeInstance(ref, recv, args)
                    else -> vm.hostExec.invokeStatic(ref, args)
                }
            }.getOrElse { UnknownVal(ref.returnType) }
            if (res is String && plausible(res)) {
                val callee = source.method(ref.declClass, ref.shortId)
                if (callee != null && foldable(callee, args)) capture(out, method, desc to insn.offset, res)
            }
            res to ref.returnType
        }
        val visited = HashSet<Long>()
        val wl = ArrayDeque<ForkSt>()
        wl.add(ForkSt(0, entryFrameRegs(method), null, null))
        var steps = 0
        val cap = (insns.size + 4) * 64 + 2048
        while (wl.isNotEmpty()) {
            if (steps++ > cap || vm.deadlineExceeded()) break
            val st = wl.removeFirst()
            if (!visited.add(forkKey(st))) continue
            val frame = Frame(st.regs.size)
            System.arraycopy(st.regs, 0, frame.regs, 0, st.regs.size)
            frame.result = st.result; frame.resultType = st.resultType
            val res = runCatching { interp.absStep(method, insns[st.pc], frame, st.pc, resolver, heap) }.getOrNull() ?: continue
            if (res.returns) continue
            for (succOff in res.successors) {
                val si = method.offsetToIndex[succOff] ?: continue
                wl.add(ForkSt(si, frame.regs.copyOf(), frame.result, frame.resultType))
            }
        }
    }

    private fun isCaptureCandidate(insn: DalvikInsn): Boolean {
        if (insn.opcode !in INVOKE_OPCODES) return false
        val ref = insn.ref as? MethodRef ?: return false
        return (ref.returnType == "Ljava/lang/String;" || ref.returnType == "Ljava/lang/Object;") && source.method(ref.declClass, ref.shortId) != null
    }

    private class ForkSt(val pc: Int, val regs: Array<Any?>, val result: Any?, val resultType: String?)

    private fun forkKey(st: ForkSt): Long {
        var h = st.pc.toLong() shl 40
        for (v in st.regs) h = 31 * h + forkSlot(v)
        return 31 * h + forkSlot(st.result)
    }

    private fun forkSlot(v: Any?): Long = when (v) {
        null -> 0; is UnknownVal -> 1; is String -> v.hashCode().toLong()
        is Int -> v.toLong() * 7 + 3; is Long -> v * 11 + 5; is Boolean -> if (v) 13 else 17; is Char -> v.code.toLong() * 19
        else -> 2
    }

    private inner class Capture(private val target: DexMethod, private val out: MutableMap<Pair<String, Int>, Any>) : ExecHook {
        override fun onStep(method: DexMethod, insn: DalvikInsn, frame: Frame, pc: Int) {
            if (insn.opcode != Opcode.MOVE_RESULT || method !== target) return
            val desc = "${method.declClass}->${method.ref.shortId}"
            val r = frame.result
            if (r !is String || !plausible(r)) return
            val prev = method.insns.getOrNull(pc - 1) ?: return
            if (prev.opcode !in INVOKE_OPCODES) return
            val ref = prev.ref as? MethodRef ?: return
            val callee = source.method(ref.declClass, ref.shortId) ?: return
            if (foldable(callee, prev.regs.map { frame.regs.getOrNull(it) })) capture(out, method, desc to prev.offset, r)
        }
    }

    companion object {
        private val CONFLICT = Any()
        private val INVOKE_OPCODES = setOf(
            Opcode.INVOKE_STATIC, Opcode.INVOKE_STATIC_RANGE, Opcode.INVOKE_DIRECT, Opcode.INVOKE_DIRECT_RANGE,
            Opcode.INVOKE_VIRTUAL, Opcode.INVOKE_VIRTUAL_RANGE, Opcode.INVOKE_INTERFACE, Opcode.INVOKE_INTERFACE_RANGE,
            Opcode.INVOKE_SUPER, Opcode.INVOKE_SUPER_RANGE,
        )

        fun buildsStringFromArray(r: MethodRef): Boolean =
            r.declClass == "Ljava/lang/String;" && (r.name == "<init>" || r.name == "valueOf" || r.name == "copyValueOf") &&
                r.argTypes.firstOrNull()?.startsWith("[") == true

        private val TRANSFORM_ARITH = setOf(
            Opcode.ADD_INT, Opcode.ADD_INT_LIT, Opcode.SUB_INT, Opcode.RSUB_INT, Opcode.MUL_INT, Opcode.MUL_INT_LIT,
            Opcode.REM_INT, Opcode.REM_INT_LIT, Opcode.AND_INT, Opcode.AND_INT_LIT, Opcode.OR_INT, Opcode.OR_INT_LIT,
            Opcode.SHL_INT, Opcode.SHL_INT_LIT, Opcode.SHR_INT, Opcode.SHR_INT_LIT, Opcode.USHR_INT, Opcode.USHR_INT_LIT,
            Opcode.NOT_INT, Opcode.NEG_INT,
        )

        fun cryptoApi(r: MethodRef): Boolean {
            val c = r.declClass
            return c.startsWith("Ljavax/crypto/") || c.startsWith("Ljava/security/") ||
                c.startsWith("Landroid/util/Base64") || c.startsWith("Ljava/util/Base64") ||
                c == "Ljava/util/zip/Inflater;" || c == "Ljava/util/zip/GZIPInputStream;"
        }

        private const val BUILDER = "Ljava/lang/StringBuilder;"
        private const val BUFFER = "Ljava/lang/StringBuffer;"
        private const val NO_DEF = -1
        private val NO_VALUE = Any()
        private val IF_OPS = setOf(
            Opcode.IF_EQ, Opcode.IF_NE, Opcode.IF_LT, Opcode.IF_GE, Opcode.IF_GT, Opcode.IF_LE,
            Opcode.IF_EQZ, Opcode.IF_NEZ, Opcode.IF_LTZ, Opcode.IF_GEZ, Opcode.IF_GTZ, Opcode.IF_LEZ,
        )
        private val PURE_PRODUCERS = setOf(
            Opcode.CONST, Opcode.CONST_WIDE, Opcode.CONST_STRING, Opcode.NEW_ARRAY,
            Opcode.MOVE, Opcode.MOVE_OBJECT, Opcode.MOVE_WIDE,
        )
        private val APUTS = setOf(
            Opcode.APUT, Opcode.APUT_BOOLEAN, Opcode.APUT_BYTE, Opcode.APUT_BYTE_BOOLEAN, Opcode.APUT_CHAR,
            Opcode.APUT_SHORT, Opcode.APUT_OBJECT, Opcode.APUT_WIDE,
        )
        private val ARRAY_ELEM = APUTS + setOf(
            Opcode.AGET, Opcode.AGET_BOOLEAN, Opcode.AGET_BYTE, Opcode.AGET_BYTE_BOOLEAN, Opcode.AGET_CHAR,
            Opcode.AGET_SHORT, Opcode.AGET_OBJECT, Opcode.AGET_WIDE,
        )
        private val NON_DEFINING = setOf(
            Opcode.NOP, Opcode.GOTO, Opcode.RETURN, Opcode.RETURN_VOID, Opcode.THROW,
            Opcode.MONITOR_ENTER, Opcode.MONITOR_EXIT, Opcode.CHECK_CAST, Opcode.FILL_ARRAY_DATA,
            Opcode.PACKED_SWITCH, Opcode.SPARSE_SWITCH,
            Opcode.IF_EQ, Opcode.IF_NE, Opcode.IF_LT, Opcode.IF_GE, Opcode.IF_GT, Opcode.IF_LE,
            Opcode.IF_EQZ, Opcode.IF_NEZ, Opcode.IF_LTZ, Opcode.IF_GEZ, Opcode.IF_GTZ, Opcode.IF_LEZ,
            Opcode.APUT, Opcode.APUT_BOOLEAN, Opcode.APUT_BYTE, Opcode.APUT_BYTE_BOOLEAN, Opcode.APUT_CHAR,
            Opcode.APUT_SHORT, Opcode.APUT_OBJECT, Opcode.APUT_WIDE,
            Opcode.IPUT, Opcode.SPUT,
            Opcode.INVOKE_STATIC, Opcode.INVOKE_STATIC_RANGE, Opcode.INVOKE_DIRECT, Opcode.INVOKE_DIRECT_RANGE,
            Opcode.INVOKE_VIRTUAL, Opcode.INVOKE_VIRTUAL_RANGE, Opcode.INVOKE_INTERFACE, Opcode.INVOKE_INTERFACE_RANGE,
            Opcode.INVOKE_SUPER, Opcode.INVOKE_SUPER_RANGE,
        )
    }
}
