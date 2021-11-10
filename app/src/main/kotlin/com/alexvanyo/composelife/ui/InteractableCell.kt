package com.alexvanyo.composelife.ui

import android.content.res.Configuration.UI_MODE_NIGHT_NO
import android.content.res.Configuration.UI_MODE_NIGHT_YES
import androidx.compose.foundation.background
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.selection.toggleable
import androidx.compose.material.MaterialTheme
import androidx.compose.material.Switch
import androidx.compose.material.ripple.rememberRipple
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.compose.ui.semantics.Role
import androidx.compose.ui.semantics.contentDescription
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.util.ExcludeFromJacocoGeneratedReport

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
    contentDescription: String,
    onValueChange: (isAlive: Boolean) -> Unit,
) {
    val cellColor = if (isAlive) {
        MaterialTheme.colors.onBackground
    } else {
        MaterialTheme.colors.background
    }
    val rippleColor = if (isAlive) {
        MaterialTheme.colors.background
    } else {
        MaterialTheme.colors.onBackground
    }

    Box(
        modifier = modifier
            .background(cellColor)
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
    )
}

@ExcludeFromJacocoGeneratedReport
private class InteractableCellPreviews {

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
                contentDescription = "test cell",
                onValueChange = {}
            )
        }
    }
}
