/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.util

import androidx.compose.foundation.text.KeyboardOptions
import androidx.compose.foundation.text.input.InputTransformation
import androidx.compose.foundation.text.input.TextFieldBuffer
import androidx.compose.foundation.text.input.then
import androidx.compose.ui.text.input.KeyboardType

fun InputTransformation.nonNegativeDouble(): InputTransformation =
    this.trimWhitespace().then(NonNegativeDouble)

private object NonNegativeDouble : InputTransformation {
    override val keyboardOptions: KeyboardOptions =
        KeyboardOptions(
            keyboardType = KeyboardType.Decimal,
        )

    override fun TextFieldBuffer.transformInput() {
        val charSequence = asCharSequence()
        if (charSequence.isNotEmpty()) {
            val double = charSequence.toString().toDoubleOrNull()
            if (double == null || double < 0f) {
                revertAllChanges()
            }
        }
    }
}