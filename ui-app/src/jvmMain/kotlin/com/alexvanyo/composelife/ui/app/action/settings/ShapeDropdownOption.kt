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

package com.alexvanyo.composelife.ui.app.action.settings

import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.ui.app.component.DropdownOption
import com.alexvanyo.composelife.ui.app.resources.RoundRectangle
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.livefront.sealedenum.GenSealedEnum

sealed interface ShapeDropdownOption : DropdownOption {
    data object RoundRectangle : ShapeDropdownOption {
        override val displayText: ParameterizedString = Strings.RoundRectangle
    }

    @GenSealedEnum
    companion object
}

expect val ShapeDropdownOption.Companion._values: List<ShapeDropdownOption>
