package com.alexvanyo.composelife.ui.cells

import android.content.res.Configuration.UI_MODE_NIGHT_NO
import android.content.res.Configuration.UI_MODE_NIGHT_YES
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.selection.toggleable
import androidx.compose.material.ripple.rememberRipple
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.CornerRadius
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.semantics.Role
import androidx.compose.ui.semantics.contentDescription
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme

/**
 * An individual cell that is interactable.
 *
 * This cell has no inherent size, which must be specified via [modifier].
 *
 * The cell is alive if [isAlive] is true, and [onValueChange] will be called when the living state should be toggled.
 */
@Composable
fun InteractableCell(
    modifier: Modifier,
    isAlive: Boolean,
    shape: CurrentShape,
    contentDescription: String,
    onValueChange: (isAlive: Boolean) -> Unit,
) {
    val aliveColor = ComposeLifeTheme.aliveCellColor
    val deadColor = ComposeLifeTheme.deadCellColor

    val rippleColor = if (isAlive) {
        deadColor
    } else {
        aliveColor
    }

    Canvas(
        modifier = modifier
            .semantics {
                this.contentDescription = contentDescription
            }
            .toggleable(
                value = isAlive,
                interactionSource = remember { MutableInteractionSource() },
                indication = rememberRipple(color = rippleColor),
                role = Role.Switch,
                onValueChange = onValueChange,
            )
    ) {
        if (isAlive) {
            when (shape) {
                is CurrentShape.RoundRectangle -> {
                    drawRoundRect(
                        color = aliveColor,
                        topLeft = Offset(
                            size.width * (1f - shape.sizeFraction) / 2f,
                            size.height * (1f - shape.sizeFraction) / 2f,
                        ),
                        size = size * shape.sizeFraction,
                        cornerRadius = CornerRadius(
                            size.width * shape.sizeFraction * shape.cornerFraction
                        )
                    )
                }
            }
        }
    }
}

@Preview(
    name = "Alive cell light mode",
    uiMode = UI_MODE_NIGHT_NO
)
@Preview(
    name = "Alive cell dark mode",
    uiMode = UI_MODE_NIGHT_YES
)
@Composable
fun AliveCellPreview() {
    ComposeLifeTheme {
        InteractableCell(
            modifier = Modifier.size(50.dp),
            isAlive = true,
            shape = CurrentShape.RoundRectangle(
                sizeFraction = 1f,
                cornerFraction = 0f
            ),
            contentDescription = "test cell",
            onValueChange = {}
        )
    }
}

@Preview(
    name = "Dead cell light mode",
    uiMode = UI_MODE_NIGHT_NO
)
@Preview(
    name = "Dead cell dark mode",
    uiMode = UI_MODE_NIGHT_YES
)
@Composable
fun DeadCellPreview() {
    ComposeLifeTheme {
        InteractableCell(
            modifier = Modifier.size(50.dp),
            isAlive = false,
            shape = CurrentShape.RoundRectangle(
                sizeFraction = 1f,
                cornerFraction = 0f
            ),
            contentDescription = "test cell",
            onValueChange = {}
        )
    }
}
