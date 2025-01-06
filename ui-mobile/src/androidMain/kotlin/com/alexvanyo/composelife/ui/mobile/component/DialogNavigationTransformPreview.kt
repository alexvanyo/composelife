/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.mobile.component

import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material3.Button
import androidx.compose.material3.Surface
import androidx.compose.material3.Switch
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.movableContentOf
import androidx.compose.runtime.mutableIntStateOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.saveable.rememberSaveableStateHolder
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.window.Dialog
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.BackstackValueSaverFactory
import com.alexvanyo.composelife.navigation.RenderableNavigationState
import com.alexvanyo.composelife.navigation.associateWithRenderablePanes
import com.alexvanyo.composelife.navigation.canNavigateBack
import com.alexvanyo.composelife.navigation.navigate
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.segmentingNavigationTransform
import com.alexvanyo.composelife.serialization.uuidSaver
import com.alexvanyo.composelife.ui.util.AnimatedVisibility
import com.alexvanyo.composelife.ui.util.MaterialPredictiveNavigationFrame
import com.alexvanyo.composelife.ui.util.RepeatablePredictiveBackHandler
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.rememberRepeatablePredictiveBackStateHolder
import kotlinx.coroutines.delay
import kotlin.uuid.Uuid

private class TestPaneState(
    private val previous: TestPaneState?,
    initialCount: Int = 0,
    initialIsDialog: Boolean = false,
) : DialogableEntry {
    var count by mutableIntStateOf(initialCount)
        private set

    val canIncrementPrevious: Boolean get() = previous != null

    override var isDialog: Boolean by mutableStateOf(initialIsDialog)

    fun increment() {
        count++
    }

    fun incrementPrevious() {
        check(canIncrementPrevious)
        @Suppress("UnsafeCallOnNullableType")
        previous!!.increment()
    }

    companion object : BackstackValueSaverFactory<TestPaneState> {
        override fun create(previous: BackstackEntry<TestPaneState>?): Saver<TestPaneState, Any> =
            listSaver(
                save = {
                    listOf(
                        it.count,
                        it.isDialog,
                    )
                },
                restore = {
                    TestPaneState(
                        previous = previous?.value,
                        initialCount = it[0] as Int,
                        initialIsDialog = it[1] as Boolean,
                    )
                },
            )
    }
}

@Suppress("LongMethod")
@Preview
@Composable
private fun DialogNavigationTransformPreview() {
    val navController = rememberMutableBackstackNavigationController(
        initialBackstackEntries = listOf(
            BackstackEntry(
                value = TestPaneState(null),
                previous = null,
            ),
        ),
        backstackValueSaverFactory = TestPaneState,
    )

    val renderableNavigationState: RenderableNavigationState<
        BackstackEntry<TestPaneState>,
        BackstackState<TestPaneState>,
        > = associateWithRenderablePanes(
        navController,
    ) { entry ->
        Surface {
            Column(
                Modifier.verticalScroll(rememberScrollState()),
            ) {
                Text("id: ${entry.id}")
                Text("count: ${entry.value.count}")
                Button(
                    onClick = {
                        entry.value.increment()
                    },
                ) {
                    Text("increment current")
                }
                if (entry.value.canIncrementPrevious) {
                    Button(
                        onClick = {
                            entry.value.incrementPrevious()
                        },
                    ) {
                        Text("increment previous")
                    }
                }
                Switch(
                    checked = entry.value.isDialog,
                    onCheckedChange = { entry.value.isDialog = it },
                )
                if (navController.canNavigateBack) {
                    Button(
                        onClick = {
                            navController.popBackstack()
                        },
                    ) {
                        Text("navigate back")
                    }
                }
                Button(
                    onClick = {
                        navController.navigate(
                            valueFactory = { previous ->
                                TestPaneState(
                                    previous = previous.value,
                                    initialIsDialog = false,
                                )
                            },
                        )
                    },
                ) {
                    Text("navigate forward")
                }
            }
        }
    }

    val repeatablePredictiveBackStateHolder = rememberRepeatablePredictiveBackStateHolder()

    RepeatablePredictiveBackHandler(
        repeatablePredictiveBackStateHolder = repeatablePredictiveBackStateHolder,
        enabled = navController.canNavigateBack,
    ) {
        navController.popBackstack()
    }

    MaterialPredictiveNavigationFrame(
        renderableNavigationState = dialogNavigationTransform<TestPaneState>(navController::popBackstack).invoke(
            segmentingNavigationTransform<TestPaneState>().invoke(
                renderableNavigationState,
            ),
        ),
        repeatablePredictiveBackState = repeatablePredictiveBackStateHolder.value,
        modifier = Modifier.fillMaxSize(),
    )
}

@Preview
@Composable
private fun DialogMovableContent() {
    val saveableStateHolder = rememberSaveableStateHolder()

    val movableContent = remember {
        movableContentOf {
            saveableStateHolder.SaveableStateProvider(1) {
                val uuid = rememberSaveable(saver = uuidSaver) { Uuid.random() }
                Text(uuid.toString())
            }
        }
    }

    var flag by remember { mutableStateOf(false) }

    LaunchedEffect(flag) {
        delay(2000)
        flag = !flag
    }

    Box {
        if (flag) {
            movableContent()
        }
        if (!flag) {
            Dialog(
                onDismissRequest = {},
            ) {
                AnimatedVisibility(TargetState.Single(!flag)) {
                    if (!flag) {
                        movableContent()
                    }
                }
            }
        }
    }
}
