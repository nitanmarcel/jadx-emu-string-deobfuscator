package jadx.emu.ext.strings

import jadx.api.plugins.pass.JadxPassInfo
import jadx.api.plugins.pass.impl.OrderedJadxPassInfo
import jadx.api.plugins.pass.types.JadxDecompilePass
import jadx.core.dex.attributes.AFlag
import jadx.core.dex.attributes.AType
import jadx.core.dex.instructions.ConstStringNode
import jadx.core.dex.instructions.InsnType
import jadx.core.dex.instructions.InvokeNode
import jadx.core.dex.instructions.args.ArgType
import jadx.core.dex.instructions.args.InsnArg
import jadx.core.dex.instructions.args.RegisterArg
import jadx.core.dex.nodes.BlockNode
import jadx.core.dex.nodes.ClassNode
import jadx.core.dex.nodes.InsnNode
import jadx.core.dex.nodes.MethodNode
import jadx.core.dex.nodes.RootNode
import jadx.core.utils.BlockUtils
import jadx.core.utils.InsnRemover
import jadx.plugins.emu.api.EmuExtensionContext
import java.util.concurrent.ConcurrentHashMap

class StringRewritePass(private val ctx: EmuExtensionContext, private val options: StringsOptions) : JadxDecompilePass {

    private val decryptor by lazy { StringDecryptor(ctx.emu.source, ctx.emu.limits, ctx.emu.engine) }
    private val sitesByClass = ConcurrentHashMap<String, Map<String, List<StringSite>>>()

    override fun getInfo(): JadxPassInfo =
        OrderedJadxPassInfo("EmuStringDecrypt", "Replace string decryptor calls with their result")
            .after("SSATransform")
            .before("ConstructorVisitor")

    override fun init(root: RootNode) {
        sitesByClass.clear()
    }

    override fun visit(cls: ClassNode): Boolean = true

    override fun visit(mth: MethodNode) {
        val sites = sitesFor(mth) ?: return
        if (sites.isEmpty()) return
        val blocks = mth.basicBlocks ?: return
        val byOffset = sites.associateBy { it.offset }
        val folded = LinkedHashMap<Int, String>()
        val unfolded = LinkedHashMap<Int, String>()

        if (options.rewrite) {
            for (block in blocks) {
                for (insn in block.instructions.toList()) {
                    val site = byOffset[insn.offset] ?: continue
                    if (fold(mth, block, insn, site.value)) folded[site.offset] = site.value
                }
            }
        }
        for (site in sites) if (site.offset !in folded) unfolded[site.offset] = site.value

        if (options.comment && (folded.isNotEmpty() || unfolded.isNotEmpty())) {
            val text = (folded + unfolded).entries.sortedBy { it.key }.joinToString("; ") { (off, s) -> "0x%x=%s".format(off, quote(s)) }
            mth.addCodeComment("jadx-emu strings: $text")
        }
        if (options.log) {
            for ((off, s) in folded) ctx.log.info("{} @0x{}: {}", mth, Integer.toHexString(off), quote(s))
            for ((off, s) in unfolded) ctx.log.info("{} @0x{}: {} (not rewritten)", mth, Integer.toHexString(off), quote(s))
        }
    }

    private fun sitesFor(mth: MethodNode): List<StringSite>? {
        val cls = mth.parentClass
        val perClass = sitesByClass.computeIfAbsent(cls.classInfo.rawName) { raw ->
            val desc = ctx.emu.descriptorOf(raw)
            val methods = ctx.emu.source.methodsOf(desc)
            if (methods.isEmpty()) return@computeIfAbsent emptyMap()
            val out = HashMap<String, List<StringSite>>()
            synchronized(decryptor) {
                for (m in methods) {
                    val s = runCatching { decryptor.recoverSites(m) }
                        .onFailure { ctx.log.warn("{}->{}: recovery failed", desc, m.ref.shortId, it) }
                        .getOrDefault(emptyList())
                    if (s.isNotEmpty()) out[m.ref.shortId] = s
                }
            }
            out
        }
        return perClass[mth.methodInfo.shortId]
    }

    private fun fold(mth: MethodNode, block: BlockNode, insn: InsnNode, value: String): Boolean = when {
        insn.type == InsnType.INVOKE && insn.result != null -> replaceWithConst(mth, block, insn, value)
        insn.type == InsnType.INVOKE && isStringInit(insn) -> foldStringInit(mth, block, insn as InvokeNode, value)
        (insn.type == InsnType.AGET || insn.type == InsnType.SGET) && insn.result != null -> replaceWithConst(mth, block, insn, value)
        else -> false
    }

    private fun replaceWithConst(mth: MethodNode, block: BlockNode, insn: InsnNode, value: String): Boolean {
        val result = insn.result ?: return false
        val args = insn.arguments.toList()
        val cs = ConstStringNode(value)
        cs.result = result.duplicate(ArgType.STRING)
        cs.offset = insn.offset
        if (!BlockUtils.replaceInsn(mth, block, insn, cs)) return false
        cs.remove(AType.METHOD_DETAILS)
        collapseTrailingCast(mth, cs, value)
        args.forEach { removeIfDead(it) }
        return true
    }

    private fun isStringInit(insn: InsnNode): Boolean {
        val call = (insn as? InvokeNode)?.callMth ?: return false
        return call.isConstructor && call.declClass.fullName == "java.lang.String"
    }

    private fun foldStringInit(mth: MethodNode, block: BlockNode, init: InvokeNode, value: String): Boolean {
        val instance = init.getArg(0) as? RegisterArg ?: return false
        val newInstance = instance.sVar?.assignInsn ?: return false
        if (newInstance.type != InsnType.NEW_INSTANCE) return false
        val newBlock = BlockUtils.getBlockByInsn(mth, newInstance) ?: return false
        val args = init.arguments.drop(1)
        val cs = ConstStringNode(value)
        cs.result = newInstance.result!!.duplicate(ArgType.STRING)
        cs.offset = init.offset
        if (!BlockUtils.replaceInsn(mth, newBlock, newInstance, cs)) return false
        InsnRemover.remove(mth, block, init)
        args.forEach { removeIfDead(it) }
        return true
    }

    private fun collapseTrailingCast(mth: MethodNode, cs: ConstStringNode, value: String) {
        val sv = cs.result?.sVar ?: return
        val cast = sv.useList.mapNotNull { it.parentInsn }.distinct().singleOrNull() ?: return
        if (cast.type != InsnType.CHECK_CAST || cast.result == null) return
        val castBlock = BlockUtils.getBlockByInsn(mth, cast) ?: return
        val cs2 = ConstStringNode(value)
        cs2.result = cast.result!!.duplicate(ArgType.STRING)
        cs2.offset = cast.offset
        if (BlockUtils.replaceInsn(mth, castBlock, cast, cs2)) {
            cs2.remove(AType.METHOD_DETAILS)
            cs.add(AFlag.DONT_GENERATE)
        }
    }

    private fun removeIfDead(arg: InsnArg) {
        val reg = arg as? RegisterArg ?: return
        val sv = reg.sVar ?: return
        val def = sv.assignInsn ?: return
        if (def.type !in REMOVABLE) return
        val uses = sv.useList.map { it.parentInsn }
        if (uses.any { it == null || (it.type !in WRITE_ONLY && !it.contains(AFlag.DONT_GENERATE)) }) return
        def.add(AFlag.DONT_GENERATE)
        uses.forEach { it!!.add(AFlag.DONT_GENERATE) }
        def.arguments.forEach { removeIfDead(it) }
    }

    private fun quote(s: String): String = "\"" + s.replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n") + "\""

    private companion object {
        val REMOVABLE = setOf(
            InsnType.CONST, InsnType.CONST_STR, InsnType.CONST_CLASS, InsnType.ARITH, InsnType.NEG,
            InsnType.NOT, InsnType.CAST, InsnType.MOVE, InsnType.FILLED_NEW_ARRAY, InsnType.NEW_ARRAY,
            InsnType.ARRAY_LENGTH, InsnType.CMP_L, InsnType.CMP_G, InsnType.INSTANCE_OF, InsnType.SGET,
        )
        val WRITE_ONLY = setOf(InsnType.FILL_ARRAY, InsnType.FILL_ARRAY_DATA, InsnType.APUT)
    }
}
