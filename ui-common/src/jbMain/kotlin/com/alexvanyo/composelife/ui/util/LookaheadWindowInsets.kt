package com.alexvanyo.composelife.ui.util

import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.displayCutout
import androidx.compose.foundation.layout.safeDrawing
import androidx.compose.foundation.layout.systemBars
import androidx.compose.foundation.layout.union
import androidx.compose.foundation.layout.windowInsetsBottomHeight
import androidx.compose.foundation.layout.windowInsetsTopHeight
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.layoutId
import com.alexvanyo.composelife.ui.util.LookaheadSafeDrawingHeightLayoutTypes.CurrentInsets
import com.alexvanyo.composelife.ui.util.LookaheadSafeDrawingHeightLayoutTypes.LookaheadInsets
import com.livefront.sealedenum.GenSealedEnum
import com.livefront.sealedenum.SealedEnum
import kotlin.math.max

@get:Composable
expect val WindowInsets.Companion.imeAnimationTarget: WindowInsets

@get:Composable
expect val WindowInsets.Companion.imeAnimationSource: WindowInsets

@Composable
fun LookaheadSafeDrawingBottomHeight(
    modifier: Modifier = Modifier,
) {
    Layout(
        layoutIdTypes = LookaheadSafeDrawingHeightLayoutTypes._sealedEnum,
        modifier = modifier,
        content = {
            Spacer(
                modifier = Modifier
                    .windowInsetsBottomHeight(WindowInsets.safeDrawing)
                    .layoutId(CurrentInsets)
            )
            Spacer(
                modifier = Modifier
                    .windowInsetsBottomHeight(
                        WindowInsets.systemBars
                            .union(WindowInsets.displayCutout)
                            .union(WindowInsets.imeAnimationTarget)
                    )
                    .layoutId(LookaheadInsets)
            )
        },
        measurePolicy = { measurables, constraints ->
            val currentInsetsPlaceable = measurables.getValue(CurrentInsets).measure(constraints)
            val lookaheadInsetsPlaceable = measurables.getValue(LookaheadInsets).measure(constraints)

            val width: Int
            val height: Int

            if (isLookingAhead) {
                width = max(currentInsetsPlaceable.width, lookaheadInsetsPlaceable.width)
                height = max(currentInsetsPlaceable.height, lookaheadInsetsPlaceable.height)
            } else {
                width = currentInsetsPlaceable.width
                height = currentInsetsPlaceable.height
            }
            layout(width, height) {
                currentInsetsPlaceable.place(0, 0)
                lookaheadInsetsPlaceable.place(0, 0)
            }
        }
    )
}

@Composable
fun LookaheadSafeDrawingTopHeight(
    modifier: Modifier = Modifier,
) {
    Layout(
        layoutIdTypes = LookaheadSafeDrawingHeightLayoutTypes._sealedEnum,
        modifier = modifier,
        content = {
            Spacer(
                modifier = Modifier
                    .windowInsetsTopHeight(WindowInsets.safeDrawing)
                    .layoutId(CurrentInsets)
            )
            Spacer(
                modifier = Modifier
                    .windowInsetsTopHeight(
                        WindowInsets.systemBars
                            .union(WindowInsets.displayCutout)
                            .union(WindowInsets.imeAnimationTarget)
                    )
                    .layoutId(LookaheadInsets)
            )
        },
        measurePolicy = { measurables, constraints ->
            val currentInsetsPlaceable = measurables.getValue(CurrentInsets).measure(constraints)
            val lookaheadInsetsPlaceable = measurables.getValue(LookaheadInsets).measure(constraints)

            val width: Int
            val height: Int

            if (isLookingAhead) {
                width = max(currentInsetsPlaceable.width, lookaheadInsetsPlaceable.width)
                height = max(currentInsetsPlaceable.height, lookaheadInsetsPlaceable.height)
            } else {
                width = currentInsetsPlaceable.width
                height = currentInsetsPlaceable.height
            }
            layout(width, height) {
                currentInsetsPlaceable.place(0, 0)
                lookaheadInsetsPlaceable.place(0, 0)
            }
        }
    )
}

internal sealed interface LookaheadSafeDrawingHeightLayoutTypes {
    data object CurrentInsets : LookaheadSafeDrawingHeightLayoutTypes
    data object LookaheadInsets : LookaheadSafeDrawingHeightLayoutTypes

    @GenSealedEnum
    companion object
}

internal expect val LookaheadSafeDrawingHeightLayoutTypes.Companion._sealedEnum:
    SealedEnum<LookaheadSafeDrawingHeightLayoutTypes>
