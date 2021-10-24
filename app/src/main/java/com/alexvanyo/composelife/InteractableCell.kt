package com.alexvanyo.composelife

import android.content.res.Configuration.UI_MODE_NIGHT_NO
import android.content.res.Configuration.UI_MODE_NIGHT_YES
import androidx.compose.foundation.layout.PaddingValues
import androidx.compose.foundation.layout.size
import androidx.compose.material.Button
import androidx.compose.material.ButtonDefaults
import androidx.compose.material.MaterialTheme
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.RectangleShape
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme

/**
 * An individual cell that is interactable.
 *
 * This cell has no inherent size, which must be specified via [modifier].
 *
 * The cell is alive if [isAlive] is true, and [onClick] will be called when the living state should be toggled.
 */
@Composable
fun InteractableCell(
    modifier: Modifier,
    isAlive: Boolean,
    onClick: (Boolean) -> Unit,
) {
    val cellColor = if (isAlive) {
        MaterialTheme.colors.onBackground
    } else {
        MaterialTheme.colors.background
    }

    Button(
        modifier = modifier,
        shape = RectangleShape,
        colors = ButtonDefaults.buttonColors(
            backgroundColor = cellColor,
            contentColor = cellColor,
            disabledBackgroundColor = cellColor,
            disabledContentColor = cellColor,
        ),
        contentPadding = PaddingValues(0.dp),
        onClick = { onClick(!isAlive) }
    ) {}
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
            onClick = {}
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
            onClick = {}
        )
    }
}
