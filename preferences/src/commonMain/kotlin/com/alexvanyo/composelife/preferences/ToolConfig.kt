/*
 * Copyright 2023 The Android Open Source Project
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

import com.alexvanyo.composelife.preferences.proto.ToolConfigProto

sealed interface ToolConfig {
    data object Pan : ToolConfig
    data object Draw : ToolConfig
    data object Erase : ToolConfig
    data object Select : ToolConfig
    data object None : ToolConfig
}

internal fun ToolConfig.toProto(): ToolConfigProto =
    when (this) {
        ToolConfig.Pan -> ToolConfigProto.PAN
        ToolConfig.Draw -> ToolConfigProto.DRAW
        ToolConfig.Erase -> ToolConfigProto.ERASE
        ToolConfig.None -> ToolConfigProto.NONE
        ToolConfig.Select -> ToolConfigProto.SELECT
    }
