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

package com.alexvanyo.composelife

import android.app.Activity
import com.alexvanyo.composelife.scopes.AndroidUiComponent
import com.alexvanyo.composelife.scopes.Ui
import com.alexvanyo.composelife.ui.app.ClipboardCellStateParserProvider
import me.tatarka.inject.annotations.Component

@Suppress("UnnecessaryAbstractClass")
@Component
abstract class ComposeLifeUiComponent(
    @Component override val applicationComponent: ComposeLifeApplicationComponent,
    activity: Activity,
) : AndroidUiComponent<ComposeLifeApplicationEntryPoint, ComposeLifeUiEntryPoint>(
    activity,
    applicationComponent,
),
    ClipboardCellStateParserProvider {
    override val entryPoint: ComposeLifeUiEntryPoint get() =
        object :
            ComposeLifeUiEntryPoint,
            ComposeLifeApplicationEntryPoint by applicationComponent.entryPoint,
            ClipboardCellStateParserProvider by this {}
}

interface ComposeLifeUiEntryPoint :
    ComposeLifeApplicationEntryPoint,
    MainActivityInjectEntryPoint
