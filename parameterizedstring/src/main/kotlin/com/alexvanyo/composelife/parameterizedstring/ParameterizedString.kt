package com.alexvanyo.composelife.parameterizedstring

import android.content.Context
import android.content.res.Resources
import androidx.annotation.StringRes
import androidx.compose.runtime.Composable
import androidx.compose.runtime.ReadOnlyComposable
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.platform.LocalContext

/**
 * A nestable representation of a [stringRes] with optional formatting arguments [args].
 *
 * [args] can be empty, or contain other [ParameterizedString]s (in which case resolution will be recursive).
 */
data class ParameterizedString(
    @StringRes val stringRes: Int,
    val args: List<Any>,
) {
    /**
     * A convenience varargs constructor.
     */
    constructor(
        @StringRes stringRes: Int,
        vararg args: Any,
    ) : this(
        stringRes = stringRes,
        args = args.toList()
    )
}

/**
 * Resolves the [ParameterizedString] to a [String] using the current [Context].
 */
fun Context.getParameterizedString(parameterizedString: ParameterizedString): String =
    resources.getParameterizedString(parameterizedString)

/**
 * Resolves the [ParameterizedString] to a [String] using the current [Resources].
 */
fun Resources.getParameterizedString(parameterizedString: ParameterizedString): String {
    val resolvedArgs = parameterizedString.args.map { arg ->
        when (arg) {
            is ParameterizedString -> getParameterizedString(arg)
            else -> arg
        }
    }.toTypedArray()

    @Suppress("SpreadOperator")
    return getString(
        parameterizedString.stringRes,
        *resolvedArgs
    )
}

/**
 * Resolves the [ParameterizedString] to a [String] using the local [Context].
 */
@Composable
@ReadOnlyComposable
fun parameterizedStringResource(parameterizedString: ParameterizedString): String {
    LocalConfiguration.current
    return LocalContext.current.getParameterizedString(parameterizedString)
}
