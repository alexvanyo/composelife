/*
 * Copyright 2026 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.alexvanyo.composelife.mosaiccalculator

/** Binary arithmetic operators supported by the terminal calculator. */
enum class CalculatorOp(val symbol: String) {
    Add("+"),
    Sub("-"),
    Mul("*"),
    Div("/"),
}

/** Explicit terminal calculator failure states. */
enum class CalculatorError {
    DivideByZero,
    Overflow,
}

/** Symbolic keypad/keyboard inputs accepted by the calculator. */
sealed interface CalculatorKey {
    data class Digit(val digit: Int) : CalculatorKey
    data class Op(val op: CalculatorOp) : CalculatorKey
    data object Equals : CalculatorKey
    data object Clear : CalculatorKey
    data object Backspace : CalculatorKey
}

/** Immutable calculator state displayed in the terminal UI. */
data class CalculatorState(
    val displayValue: Long = 0L,
    val pendingOperand: Long? = null,
    val pendingOp: CalculatorOp? = null,
    val enteringNewNumber: Boolean = true,
    val error: CalculatorError? = null,
) {
    companion object {
        val Initial = CalculatorState()
    }
}

sealed interface CheckedEvalResult {
    data class Value(val value: Long) : CheckedEvalResult
    data class Error(val error: CalculatorError) : CheckedEvalResult
}

internal fun checkedAdd(a: Long, b: Long): CheckedEvalResult {
    val res = a + b
    return if (((a xor res) and (b xor res)) < 0L) {
        CheckedEvalResult.Error(CalculatorError.Overflow)
    } else {
        CheckedEvalResult.Value(res)
    }
}

internal fun checkedSub(a: Long, b: Long): CheckedEvalResult {
    val res = a - b
    return if (((a xor b) and (a xor res)) < 0L) {
        CheckedEvalResult.Error(CalculatorError.Overflow)
    } else {
        CheckedEvalResult.Value(res)
    }
}

@Suppress("ComplexCondition", "ReturnCount")
internal fun checkedMul(a: Long, b: Long): CheckedEvalResult {
    if (a == 0L || b == 0L) return CheckedEvalResult.Value(0L)
    if ((a == Long.MIN_VALUE && b == -1L) || (b == Long.MIN_VALUE && a == -1L)) {
        return CheckedEvalResult.Error(CalculatorError.Overflow)
    }
    val res = a * b
    return if (res / b != a) {
        CheckedEvalResult.Error(CalculatorError.Overflow)
    } else {
        CheckedEvalResult.Value(res)
    }
}

internal fun checkedDiv(a: Long, b: Long): CheckedEvalResult = when {
    b == 0L -> CheckedEvalResult.Error(CalculatorError.DivideByZero)
    a == Long.MIN_VALUE && b == -1L -> CheckedEvalResult.Error(CalculatorError.Overflow)
    else -> CheckedEvalResult.Value(a / b)
}

fun applyOp(lhs: Long, op: CalculatorOp, rhs: Long): CheckedEvalResult = when (op) {
    CalculatorOp.Add -> checkedAdd(lhs, rhs)
    CalculatorOp.Sub -> checkedSub(lhs, rhs)
    CalculatorOp.Mul -> checkedMul(lhs, rhs)
    CalculatorOp.Div -> checkedDiv(lhs, rhs)
}

/** Pure state transition function for the terminal calculator. */
@Suppress("CyclomaticComplexMethod", "LongMethod", "ReturnCount")
fun reduceCalculatorState(state: CalculatorState, key: CalculatorKey): CalculatorState {
    if (key is CalculatorKey.Clear) {
        return CalculatorState.Initial
    }
    if (state.error != null) {
        return state
    }
    return when (key) {
        is CalculatorKey.Digit -> {
            val d = key.digit.toLong()
            if (state.enteringNewNumber) {
                state.copy(
                    displayValue = d,
                    enteringNewNumber = false,
                )
            } else {
                when (val mul = checkedMul(state.displayValue, 10L)) {
                    is CheckedEvalResult.Error -> state.copy(error = mul.error)

                    is CheckedEvalResult.Value -> {
                        val next = if (state.displayValue < 0L) {
                            checkedSub(mul.value, d)
                        } else {
                            checkedAdd(mul.value, d)
                        }
                        when (next) {
                            is CheckedEvalResult.Error -> state.copy(error = next.error)
                            is CheckedEvalResult.Value -> state.copy(displayValue = next.value)
                        }
                    }
                }
            }
        }

        CalculatorKey.Backspace -> {
            if (state.enteringNewNumber) {
                state
            } else {
                state.copy(displayValue = state.displayValue / 10L)
            }
        }

        is CalculatorKey.Op -> {
            val pendingOperand = state.pendingOperand
            val pendingOp = state.pendingOp
            if (pendingOperand != null && pendingOp != null && !state.enteringNewNumber) {
                when (val res = applyOp(pendingOperand, pendingOp, state.displayValue)) {
                    is CheckedEvalResult.Error -> state.copy(
                        pendingOperand = null,
                        pendingOp = null,
                        enteringNewNumber = true,
                        error = res.error,
                    )

                    is CheckedEvalResult.Value -> state.copy(
                        displayValue = res.value,
                        pendingOperand = res.value,
                        pendingOp = key.op,
                        enteringNewNumber = true,
                    )
                }
            } else {
                state.copy(
                    pendingOperand = state.displayValue,
                    pendingOp = key.op,
                    enteringNewNumber = true,
                )
            }
        }

        CalculatorKey.Equals -> {
            val pendingOperand = state.pendingOperand
            val pendingOp = state.pendingOp
            if (pendingOperand != null && pendingOp != null) {
                when (val res = applyOp(pendingOperand, pendingOp, state.displayValue)) {
                    is CheckedEvalResult.Error -> CalculatorState(
                        error = res.error,
                    )

                    is CheckedEvalResult.Value -> CalculatorState(
                        displayValue = res.value,
                    )
                }
            } else {
                state.copy(enteringNewNumber = true)
            }
        }

        CalculatorKey.Clear -> CalculatorState.Initial
    }
}

/** Maps a Mosaic terminal key string to a [CalculatorKey], or `null` if unhandled. */
@Suppress("CyclomaticComplexMethod")
fun mapTerminalKey(key: String): CalculatorKey? = when (key) {
    "0" -> CalculatorKey.Digit(0)
    "1" -> CalculatorKey.Digit(1)
    "2" -> CalculatorKey.Digit(2)
    "3" -> CalculatorKey.Digit(3)
    "4" -> CalculatorKey.Digit(4)
    "5" -> CalculatorKey.Digit(5)
    "6" -> CalculatorKey.Digit(6)
    "7" -> CalculatorKey.Digit(7)
    "8" -> CalculatorKey.Digit(8)
    "9" -> CalculatorKey.Digit(9)
    "+" -> CalculatorKey.Op(CalculatorOp.Add)
    "-" -> CalculatorKey.Op(CalculatorOp.Sub)
    "*" -> CalculatorKey.Op(CalculatorOp.Mul)
    "/" -> CalculatorKey.Op(CalculatorOp.Div)
    "=", "Enter" -> CalculatorKey.Equals
    "c", "C", "Escape" -> CalculatorKey.Clear
    "Backspace" -> CalculatorKey.Backspace
    else -> null
}

/** Formats the calculator readout string rendered by the terminal UI. */
fun formatDisplayLine(state: CalculatorState): String = when (state.error) {
    CalculatorError.DivideByZero -> "ERR: DIV BY ZERO"

    CalculatorError.Overflow -> "ERR: OVERFLOW"

    null -> {
        val op = state.pendingOp
        val lhs = state.pendingOperand
        if (op != null && lhs != null) {
            "$lhs ${op.symbol} ${state.displayValue}"
        } else {
            state.displayValue.toString()
        }
    }
}
