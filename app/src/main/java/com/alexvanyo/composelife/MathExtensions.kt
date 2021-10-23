package com.alexvanyo.composelife

/**
 * Rounds this [Int] up the the nearest odd integer.
 */
fun Int.ceilToOdd(): Int = if (this.rem(2) == 0) {
    this + 1
} else {
    this
}
