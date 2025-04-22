/*
 * Copyright 2022 The Android Open Source Project
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

package com.alexvanyo.composelife.preferences

import com.livefront.sealedenum.GenSealedEnum

sealed interface QuickAccessSetting {
    data object AlgorithmImplementation : QuickAccessSetting
    data object DarkThemeConfig : QuickAccessSetting
    data object CellShapeConfig : QuickAccessSetting
    data object SynchronizePatternCollectionsOnMeteredNetwork : QuickAccessSetting
    data object PatternCollectionsSynchronizationPeriod : QuickAccessSetting
    data object DisableAGSL : QuickAccessSetting
    data object DisableOpenGL : QuickAccessSetting
    data object DoNotKeepProcess : QuickAccessSetting
    data object EnableClipboardWatching : QuickAccessSetting
    data object ClipboardWatchingOnboardingCompleted : QuickAccessSetting
    data object EnableWindowShapeClipping : QuickAccessSetting

    @GenSealedEnum
    companion object
}
