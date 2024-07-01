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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.runtime.Composable
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString

/**
 * An option in a [TextFieldDropdown].
 */
interface DropdownOption {
    /**
     * The text to display for the [DropdownOption].
     */
    val displayText: ParameterizedString

    /**
     * The leading icon (if any) to display for the [DropdownOption].
     */
    val leadingIcon: (@Composable () -> Unit)? get() = null
}
