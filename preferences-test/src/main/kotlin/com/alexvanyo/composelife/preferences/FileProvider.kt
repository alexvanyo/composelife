package com.alexvanyo.composelife.preferences

import java.io.File
import javax.inject.Provider

/**
 * A simple alias for a [Provider] of a [File], since Dagger won't let injecting one directly.
 */
fun interface FileProvider : Provider<File>
