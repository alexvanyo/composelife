package com.alexvanyo.composelife

import androidx.compose.foundation.layout.PaddingValues
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material.Button
import androidx.compose.material.ButtonDefaults
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.dp

@Composable
fun InteractableCell(
    modifier: Modifier,
    isAlive: Boolean,
    onClick: (Boolean) -> Unit,
) {
    val cellColor = if (isAlive) {
        Color(0xFFFFFFFF)
    } else {
        Color(0xFF000000)
    }

    Button(
        modifier = modifier,
        shape = RoundedCornerShape(0.dp),
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

@Preview
@Composable
fun AliveCellPreview() {
    InteractableCell(
        modifier = Modifier.size(50.dp),
        isAlive = true,
        onClick = {}
    )
}

@Preview
@Composable
fun DeadCellPreview() {
    InteractableCell(
        modifier = Modifier.size(50.dp),
        isAlive = false,
        onClick = {}
    )
}
