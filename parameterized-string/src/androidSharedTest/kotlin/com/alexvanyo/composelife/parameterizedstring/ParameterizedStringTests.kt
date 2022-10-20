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

import android.content.Context
import androidx.activity.ComponentActivity
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.parameterizedstring.test.R
import org.junit.Rule
import org.junit.runner.RunWith
import java.util.MissingFormatArgumentException
import kotlin.test.Test
import kotlin.test.assertEquals

@RunWith(AndroidJUnit4::class)
class ParameterizedStringTests {

    @get:Rule
    val composeTestRule = createAndroidComposeRule<ComponentActivity>()

    private val context: Context get() = composeTestRule.activity

    @Test
    fun zero_arg_string_is_correct() {
        assertEquals(
            "Zero",
            context.getParameterizedString(ParameterizedString(R.string.no_arg_string)),
        )
    }

    @Test
    fun quantity_arg_string_with_number_is_correct_for_zero() {
        assertEquals(
            "0 things",
            context.getParameterizedString(ParameterizedQuantityString(R.plurals.plural_string_with_number, 0, 0)),
        )
    }

    @Test
    fun quantity_arg_string_with_number_is_correct_for_one() {
        assertEquals(
            "1 thing",
            context.getParameterizedString(ParameterizedQuantityString(R.plurals.plural_string_with_number, 1, 1)),
        )
    }

    @Test
    fun quantity_arg_string_with_number_is_correct_for_two() {
        assertEquals(
            "2 things",
            context.getParameterizedString(ParameterizedQuantityString(R.plurals.plural_string_with_number, 2, 2)),
        )
    }

    @Test
    fun quantity_arg_string_without_number_is_correct_for_zero() {
        assertEquals(
            "things",
            context.getParameterizedString(ParameterizedQuantityString(R.plurals.plural_string_without_number, 0)),
        )
    }

    @Test
    fun quantity_arg_string_without_number_is_correct_for_one() {
        assertEquals(
            "thing",
            context.getParameterizedString(ParameterizedQuantityString(R.plurals.plural_string_without_number, 1)),
        )
    }

    @Test
    fun quantity_arg_string_without_number_is_correct_for_two() {
        assertEquals(
            "things",
            context.getParameterizedString(ParameterizedQuantityString(R.plurals.plural_string_without_number, 2)),
        )
    }

    @Test
    fun one_arg_string_is_correct() {
        assertEquals(
            "One: (a)",
            context.getParameterizedString(ParameterizedString(R.string.one_arg_string, "a")),
        )
    }

    @Test
    fun two_arg_string_is_correct() {
        assertEquals(
            "Two: (a) (b)",
            context.getParameterizedString(ParameterizedString(R.string.two_arg_string, "a", "b")),
        )
    }

    @Test
    fun three_arg_string_is_correct() {
        assertEquals(
            "Three: (a) (b) (c)",
            context.getParameterizedString(ParameterizedString(R.string.three_arg_string, "a", "b", "c")),
        )
    }

    @Test(expected = MissingFormatArgumentException::class)
    fun three_arg_string_with_two_args_throws() {
        context.getParameterizedString(ParameterizedString(R.string.three_arg_string, "a", "b"))
    }

    @Test
    fun nested_two_arg_string_is_correct() {
        assertEquals(
            "Two: (One: (a)) (One: (b))",
            context.getParameterizedString(
                ParameterizedString(
                    R.string.two_arg_string,
                    ParameterizedString(
                        R.string.one_arg_string,
                        "a",
                    ),
                    ParameterizedString(
                        R.string.one_arg_string,
                        "b",
                    ),
                ),
            ),
        )
    }

    @Test
    fun nested_three_arg_string_is_correct() {
        assertEquals(
            "Three: (Two: (a) (b)) (One: (One: (c))) (One: (One: (2 things)))",
            context.getParameterizedString(
                ParameterizedString(
                    R.string.three_arg_string,
                    ParameterizedString(
                        R.string.two_arg_string,
                        "a",
                        "b",
                    ),
                    ParameterizedString(
                        R.string.one_arg_string,
                        ParameterizedString(
                            R.string.one_arg_string,
                            "c",
                        ),
                    ),
                    ParameterizedString(
                        R.string.one_arg_string,
                        ParameterizedString(
                            R.string.one_arg_string,
                            ParameterizedQuantityString(
                                R.plurals.plural_string_with_number,
                                2,
                                2,
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    @Test
    fun composable_parameterized_string_resource_is_correct() {
        lateinit var string: String

        composeTestRule.setContent {
            string = parameterizedStringResource(
                parameterizedString = ParameterizedString(
                    R.string.three_arg_string,
                    ParameterizedString(
                        R.string.two_arg_string,
                        "a",
                        "b",
                    ),
                    ParameterizedString(
                        R.string.one_arg_string,
                        ParameterizedString(
                            R.string.one_arg_string,
                            "c",
                        ),
                    ),
                    ParameterizedString(
                        R.string.one_arg_string,
                        ParameterizedString(
                            R.string.one_arg_string,
                            ParameterizedString(
                                R.string.one_arg_string,
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
}
