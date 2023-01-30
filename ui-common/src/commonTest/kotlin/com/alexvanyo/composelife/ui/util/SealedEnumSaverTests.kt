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

package com.alexvanyo.composelife.ui.util

import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.text.BasicText
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.kmpstaterestorationtester.KmpStateRestorationTester
import com.livefront.sealedenum.createSealedEnumFromEnum
import org.junit.runner.RunWith
import kotlin.test.Test

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class SealedEnumSaverTests {

    @Test
    fun sealed_enum_saver_is_correct() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        stateRestorationTester.setContent {
            var value by rememberSaveable(stateSaver = sealedEnumSaver(testEnumSealedEnum)) {
                mutableStateOf(TestEnum.First)
            }
            Column {
                BasicText("Current Value: ${testEnumSealedEnum.nameOf(value)}")
                BasicText(
                    "Change to Third",
                    modifier = Modifier.clickable {
                        value = TestEnum.Third
                    },
                )
            }
        }

        onNodeWithText("Change to Third").performClick()

        stateRestorationTester.emulateSavedInstanceStateRestore()

        onNodeWithText("Current Value: Third").assertExists()
    }
}

private enum class TestEnum {
    First, Second, Third
}

private val testEnumSealedEnum = createSealedEnumFromEnum<TestEnum>()
