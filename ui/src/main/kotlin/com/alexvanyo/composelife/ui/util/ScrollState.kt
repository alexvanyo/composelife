package com.alexvanyo.composelife.ui.util

import androidx.compose.foundation.ScrollState

/**
 * `true` if it is possible to scroll up.
 */
val ScrollState.canScrollUp: Boolean get() =
    value > 0

/**
 * `true` if it is possible to scroll down.
 */
val ScrollState.canScrollDown: Boolean get() =
    maxValue != Int.MAX_VALUE && value < maxValue
