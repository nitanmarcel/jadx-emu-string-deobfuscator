package jadx.emu.ext.strings

import jadx.plugins.emu.api.EmuExtension
import jadx.plugins.emu.api.EmuExtensionContext
import jadx.plugins.emu.api.EmuExtensionInfo
import jadx.plugins.emu.api.ExtensionMode

class StringsExtension : EmuExtension {

    private val options = StringsOptions()

    override fun info(): EmuExtensionInfo = EmuExtensionInfo(
        id = "strings",
        name = "String decryption",
        description = "Replaces string decryptor calls with the decrypted string",
        mode = ExtensionMode.AUTO,
        requiredEmuVersion = "0.1.0",
    )

    override fun init(ctx: EmuExtensionContext) {
        ctx.registerOptions(options)
        ctx.addPass(StringRewritePass(ctx, options))
    }
}
