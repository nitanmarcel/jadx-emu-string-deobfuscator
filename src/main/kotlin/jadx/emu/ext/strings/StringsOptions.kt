package jadx.emu.ext.strings

import jadx.api.plugins.options.impl.BasePluginOptionsBuilder

class StringsOptions : BasePluginOptionsBuilder() {

    var rewrite: Boolean = true
        private set

    var comment: Boolean = false
        private set

    var log: Boolean = true
        private set

    override fun registerOptions() {
        boolOption("rewrite")
            .description("Replace decryptor calls with the decrypted string")
            .defaultValue(true)
            .setter { rewrite = it }

        boolOption("comment")
            .description("Add a comment listing the decrypted strings of each method")
            .defaultValue(false)
            .setter { comment = it }

        boolOption("log")
            .description("Log decrypted strings")
            .defaultValue(true)
            .setter { log = it }
    }
}
