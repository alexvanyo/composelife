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

package com.alexvanyo.composelife.test

import android.os.Build
import androidx.activity.ComponentActivity
import androidx.compose.ui.test.AndroidComposeUiTest
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.v2.AndroidComposeUiTestEnvironment
import androidx.test.core.app.ActivityScenario
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.ApplicationGraphArguments
import kotlinx.coroutines.test.TestResult
import kotlinx.coroutines.test.TestScope
import kotlinx.coroutines.test.runTest
import leakcanary.DetectLeaksAfterTestSuccess
import org.junit.Rule
import org.junit.rules.TestRule
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

/**
 * A base class for testing an [ComponentActivity] that depends on injected classes.
 *
 * Subclasses must call [runAppTest] instead of [runTest] to properly initialize dependencies.
 */
@Suppress("UnnecessaryAbstractClass")
abstract class BaseActivityInjectTest<A : ComponentActivity>(
    applicationGraphCreator: (ApplicationGraphArguments) -> ApplicationGraph,
    private val clazz: Class<A>,
) : BaseInjectTest(applicationGraphCreator) {

    @get:Rule(order = 0)
    val outerLeakRule = createLeakRule("Outer")

    @Deprecated("Testing with BaseUiInjectTest should call runUiTest instead of runAppTest")
    override fun runAppTest(
        context: CoroutineContext,
        timeout: Duration,
        testBody: suspend TestScope.() -> Unit,
    ): TestResult = super.runAppTest(context, timeout, testBody)

    @OptIn(ExperimentalTestApi::class)
    fun runUiTest(
        appTestContext: CoroutineContext = EmptyCoroutineContext,
        timeout: Duration = 60.seconds,
        testBody: suspend AndroidComposeUiTest<A>.(ActivityScenario<A>) -> Unit,
    ): TestResult {
        var scenario: ActivityScenario<A>? = null

        val environment = AndroidComposeUiTestEnvironment(
            effectContext = generalTestDispatcher,
            runTestContext = generalTestDispatcher + appTestContext,
            testTimeout = timeout,
            activityProvider = {
                var activity: A? = null
                scenario!!.onActivity { activity = it }
                activity
            },
        )

        try {
            return environment.runTest {
                scenario = ActivityScenario.launch(clazz)
                var blockException: Throwable? = null
                try {
                    // Run the test
                    testBody(this, scenario!!)
                } catch (t: Throwable) {
                    blockException = t
                }

                // Throw the aggregate exception. May be from the test body or from the cleanup.
                blockException?.let { throw it }
            }
        } finally {
            // Close the scenario outside runTest to avoid getting stuck.
            //
            // ActivityScenario.close() calls Instrumentation.waitForIdleSync(), which would time out
            // if there is an infinite self-invalidating measure, layout, or draw loop. If the
            // Compose content was set through the test's setContent method, it will remove the
            // AndroidComposeView from the view hierarchy which breaks this loop, which is why we
            // call close() outside the runTest lambda. This will not help if the content is not set
            // through the test's setContent method though, in which case we'll still time out here.
            scenario?.close()
        }
    }
}

private fun createLeakRule(tag: String) =
    if (Build.FINGERPRINT.lowercase() == "robolectric") {
        TestRule { base, _ -> base }
    } else {
        DetectLeaksAfterTestSuccess(tag)
    }
