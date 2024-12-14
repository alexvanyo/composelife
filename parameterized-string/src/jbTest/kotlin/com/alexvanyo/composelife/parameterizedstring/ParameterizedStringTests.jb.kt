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

package com.alexvanyo.composelife.parameterizedstring

import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.kmpstaterestorationtester.KmpStateRestorationTester
import org.junit.runner.RunWith
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class ParameterizedStringTests {

    @Test
    fun composable_parameterized_string_resource_is_correct() = runComposeUiTest {
        lateinit var string: String

        setContent {
            string = parameterizedStringResource(
                parameterizedString = ParameterizedString(
                    "Three: (%s) (%s) (%s)",
                    ParameterizedString(
                        "Two: (%s) (%s)",
                        "a",
                        "b",
                    ),
                    ParameterizedString(
                        "One: (%s)",
                        ParameterizedString(
                            "One: (%s)",
                            "c",
                        ),
                    ),
                    ParameterizedString(
                        "One: (%s)",
                        ParameterizedString(
                            "One: (%s)",
                            ParameterizedString(
                                "One: (%s)",
                                "d",
                            ),
                        ),
                    ),
                ),
            )
        }

        assertEquals(
            "Three: (Two: (a) (b)) (One: (One: (c))) (One: (One: (One: (d))))",
            string,
        )
    }

    @Test
    fun composable_resolver_is_correct() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
        }

        assertEquals(
            "Three: (Two: (a) (b)) (One: (One: (c))) (One: (One: (One: (d))))",
            resolver.invoke(
                ParameterizedString(
                    "Three: (%s) (%s) (%s)",
                    ParameterizedString(
                        "Two: (%s) (%s)",
                        "a",
                        "b",
                    ),
                    ParameterizedString(
                        "One: (%s)",
                        ParameterizedString(
                            "One: (%s)",
                            "c",
                        ),
                    ),
                    ParameterizedString(
                        "One: (%s)",
                        ParameterizedString(
                            "One: (%s)",
                            ParameterizedString(
                                "One: (%s)",
                                "d",
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    @Test
    fun saver_is_correct_for_basic_string() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        var parameterizedString: ParameterizedString? = null

        stateRestorationTester.setContent {
            parameterizedString = rememberSaveable(saver = ParameterizedString.Saver) {
                ParameterizedString("Two: (%s) (%s)", Random.nextInt().toString(), Random.nextInt().toString())
            }
        }

        val initial = parameterizedString

        assertNotNull(initial)

        stateRestorationTester.emulateSavedInstanceStateRestore()

        val restored = parameterizedString

        assertEquals(initial, restored)
    }

    @Test
    fun saver_is_correct_for_nested_parameterized_string() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        var parameterizedString: ParameterizedString? = null

        stateRestorationTester.setContent {
            parameterizedString = rememberSaveable(saver = ParameterizedString.Saver) {
                ParameterizedString(
                    "Three: (%s) (%s) (%s)",
                    ParameterizedString(
                        "Two: (%s) (%s)",
                        "a",
                        "b",
                    ),
                    ParameterizedString(
                        "One: (%s)",
                        ParameterizedString(
                            "One: (%s)",
                            "c",
                        ),
                    ),
                    ParameterizedString(
                        "One: (%s)",
                        ParameterizedString(
                            "One: (%s)",
                            ParameterizedString(
                                "One: (%s)",
                                "d",
                            ),
                        ),
                    ),
                )
            }
        }

        val initial = parameterizedString

        assertNotNull(initial)

        stateRestorationTester.emulateSavedInstanceStateRestore()

        val restored = parameterizedString

        assertEquals(initial, restored)
    }
}
