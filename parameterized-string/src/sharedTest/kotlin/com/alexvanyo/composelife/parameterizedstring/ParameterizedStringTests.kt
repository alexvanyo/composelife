package com.alexvanyo.composelife.parameterizedstring

import android.app.Application
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.test.core.app.ApplicationProvider
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.parameterizedstring.test.R
import kotlin.test.assertEquals
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import java.util.MissingFormatArgumentException

@RunWith(AndroidJUnit4::class)
class ParameterizedStringTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    private val applicationContext = ApplicationProvider.getApplicationContext<Application>()

    @Test
    fun zero_arg_string_is_correct() {
        assertEquals(
            "Zero",
            applicationContext.getParameterizedString(ParameterizedString(R.string.no_arg_string))
        )
    }

    @Test
    fun one_arg_string_is_correct() {
        assertEquals(
            "One: (a)",
            applicationContext.getParameterizedString(ParameterizedString(R.string.one_arg_string, "a"))
        )
    }

    @Test
    fun two_arg_string_is_correct() {
        assertEquals(
            "Two: (a) (b)",
            applicationContext.getParameterizedString(ParameterizedString(R.string.two_arg_string, "a", "b"))
        )
    }

    @Test
    fun three_arg_string_is_correct() {
        assertEquals(
            "Three: (a) (b) (c)",
            applicationContext.getParameterizedString(ParameterizedString(R.string.three_arg_string, "a", "b", "c"))
        )
    }

    @Test(expected = MissingFormatArgumentException::class)
    fun three_arg_string_with_two_args_throws() {
        applicationContext.getParameterizedString(ParameterizedString(R.string.three_arg_string, "a", "b"))
    }

    @Test
    fun nested_two_arg_string_is_correct() {
        assertEquals(
            "Two: (One: (a)) (One: (b))",
            applicationContext.getParameterizedString(
                ParameterizedString(
                    R.string.two_arg_string,
                    ParameterizedString(
                        R.string.one_arg_string,
                        "a"
                    ),
                    ParameterizedString(
                        R.string.one_arg_string,
                        "b"
                    )
                )
            )
        )
    }

    @Test
    fun nested_three_arg_string_is_correct() {
        assertEquals(
            "Three: (Two: (a) (b)) (One: (One: (c))) (One: (One: (One: (d))))",
            applicationContext.getParameterizedString(
                ParameterizedString(
                    R.string.three_arg_string,
                    ParameterizedString(
                        R.string.two_arg_string,
                        "a",
                        "b"
                    ),
                    ParameterizedString(
                        R.string.one_arg_string,
                        ParameterizedString(
                            R.string.one_arg_string,
                            "c"
                        )
                    ),
                    ParameterizedString(
                        R.string.one_arg_string,
                        ParameterizedString(
                            R.string.one_arg_string,
                            ParameterizedString(
                                R.string.one_arg_string,
                                "d"
                            )
                        )
                    )
                )
            )
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
                        "b"
                    ),
                    ParameterizedString(
                        R.string.one_arg_string,
                        ParameterizedString(
                            R.string.one_arg_string,
                            "c"
                        )
                    ),
                    ParameterizedString(
                        R.string.one_arg_string,
                        ParameterizedString(
                            R.string.one_arg_string,
                            ParameterizedString(
                                R.string.one_arg_string,
                                "d"
                            )
                        )
                    )
                )
            )
        }

        assertEquals(
            "Three: (Two: (a) (b)) (One: (One: (c))) (One: (One: (One: (d))))",
            string
        )
    }
}
