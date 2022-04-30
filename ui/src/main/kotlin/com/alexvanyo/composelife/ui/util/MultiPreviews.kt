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

package com.alexvanyo.composelife.ui.util

import android.content.res.Configuration
import androidx.compose.ui.tooling.preview.Preview

@Preview(
    name = "Light mode phone",
    uiMode = Configuration.UI_MODE_NIGHT_NO,
    device = "spec:shape=Normal,width=360,height=640,unit=dp,dpi=480",
)
@Preview(
    name = "Dark mode phone",
    uiMode = Configuration.UI_MODE_NIGHT_YES,
    device = "spec:shape=Normal,width=360,height=640,unit=dp,dpi=480",
)
@Preview(
    name = "Light mode foldable",
    uiMode = Configuration.UI_MODE_NIGHT_NO,
    device = "spec:shape=Normal,width=673,height=841,unit=dp,dpi=480",
)
@Preview(
    name = "Dark mode foldable",
    uiMode = Configuration.UI_MODE_NIGHT_YES,
    device = "spec:shape=Normal,width=673,height=841,unit=dp,dpi=480",
)
@Preview(
    name = "Light mode tablet",
    uiMode = Configuration.UI_MODE_NIGHT_NO,
    device = "spec:shape=Normal,width=1280,height=800,unit=dp,dpi=480",
)
@Preview(
    name = "Dark mode tablet",
    uiMode = Configuration.UI_MODE_NIGHT_YES,
    device = "spec:shape=Normal,width=1280,height=800,unit=dp,dpi=480",
)
annotation class SizePreviews

@Preview(
    name = "Light mode",
    uiMode = Configuration.UI_MODE_NIGHT_NO,
)
@Preview(
    name = "Dark mode",
    uiMode = Configuration.UI_MODE_NIGHT_YES,
)
annotation class ThemePreviews
