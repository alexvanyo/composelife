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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.app

import android.app.Activity
import com.alexvanyo.composelife.scopes.UiComponent
import me.tatarka.inject.annotations.Component

@Component
actual abstract class TestComposeLifeUiComponent(
    @Component override val applicationComponent: TestComposeLifeApplicationComponent,
    activity: Activity,
) : UiComponent<TestComposeLifeApplicationComponent, TestComposeLifeUiEntryPoint>(activity, applicationComponent),
    ClipboardCellStateParserProvider {
    actual override val entryPoint: TestComposeLifeUiEntryPoint get() =
        object :
            TestComposeLifeUiEntryPoint,
            TestComposeLifeApplicationEntryPoint by applicationComponent.entryPoint,
            ClipboardCellStateParserProvider by this {}

    actual companion object
}
