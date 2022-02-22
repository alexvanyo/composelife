package com.alexvanyo.composelife.preferences

sealed interface CurrentShape {
    val type: CurrentShapeType

    data class RoundRectangle(
        val sizeFraction: Float,
        val cornerFraction: Float,
    ) : CurrentShape {
        override val type: CurrentShapeType = CurrentShapeType.RoundRectangle
    }
}
