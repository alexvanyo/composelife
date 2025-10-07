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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.parameterizedstring

import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.BaseKmpTest
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalTestApi::class)
class ParameterizedStringTests : BaseKmpTest() {

    @Test
    fun composable_parameterized_string_resource_is_correct() {
        runComposeUiTest {
            lateinit var string: String

            setContent {
                string = parameterizedStringResource(
                    parameterizedString = ParameterizedString(
                        "Three: (%s) (%s) (%s)",
                        ParameterizedStringArgument(
                            ParameterizedString(
                                "Two: (%s) (%s)",
                                ParameterizedStringArgument("a"),
                                ParameterizedStringArgument("b"),
                            ),
                        ),
                        ParameterizedStringArgument(
                            ParameterizedString(
                                "One: (%s)",
                                ParameterizedStringArgument(
                                    ParameterizedString(
                                        "One: (%s)",
                                        ParameterizedStringArgument("c"),
                                    ),
                                ),
                            ),
                        ),
                        ParameterizedStringArgument(
                            ParameterizedString(
                                "One: (%s)",
                                ParameterizedStringArgument(
                                    ParameterizedString(
                                        "One: (%s)",
                                        ParameterizedStringArgument(
                                            ParameterizedString(
                                                "One: (%s)",
                                                ParameterizedStringArgument("d"),
                                            ),
                                        ),
                                    ),
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
    }

    @Test
    fun composable_resolver_is_correct() {
        runComposeUiTest {
            lateinit var resolver: (ParameterizedString) -> String

            setContent {
                resolver = parameterizedStringResolver()
            }

            assertEquals(
                "Three: (Two: (a) (b)) (One: (One: (c))) (One: (One: (One: (d))))",
                resolver.invoke(
                    ParameterizedString(
                        "Three: (%s) (%s) (%s)",
                        ParameterizedStringArgument(
                            ParameterizedString(
                                "Two: (%s) (%s)",
                                ParameterizedStringArgument("a"),
                                ParameterizedStringArgument("b"),
                            ),
                        ),
                        ParameterizedStringArgument(
                            ParameterizedString(
                                "One: (%s)",
                                ParameterizedStringArgument(
                                    ParameterizedString(
                                        "One: (%s)",
                                        ParameterizedStringArgument("c"),
                                    ),
                                ),
                            ),
                        ),
                        ParameterizedStringArgument(
                            ParameterizedString(
                                "One: (%s)",
                                ParameterizedStringArgument(
                                    ParameterizedString(
                                        "One: (%s)",
                                        ParameterizedStringArgument(
                                            ParameterizedString(
                                                "One: (%s)",
                                                ParameterizedStringArgument("d"),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            )
        }
    }
}
