/*
 * Copyright 2025 The Android Open Source Project
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

import androidx.compose.animation.SharedTransitionLayout
import androidx.compose.foundation.background
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.material3.Button
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.collectAsState
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSerializable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.tooling.preview.Preview
import androidx.navigation3.scene.Scene
import androidx.navigationevent.NavigationEventInfo
import androidx.navigationevent.NavigationEventTransitionState
import androidx.navigationevent.compose.LocalNavigationEventDispatcherOwner
import androidx.navigationevent.compose.NavigationBackHandler
import androidx.navigationevent.compose.rememberNavigationEventState
import com.alexvanyo.composelife.logging.Logger
import com.alexvanyo.composelife.logging.d
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackValueSaverFactory
import com.alexvanyo.composelife.navigation.MaterialPredictiveNavDisplay
import com.alexvanyo.composelife.navigation.navigate
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.navigation.popUpTo
import com.alexvanyo.composelife.navigation.rememberDecoratedNavEntries
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation3.scene.rememberSceneState
import com.alexvanyo.composelife.ui.util.LocalNavigationSharedTransitionScope
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.builtins.serializer
import kotlin.random.Random
import kotlin.reflect.KClass
import kotlin.uuid.Uuid

private sealed interface ListDetailSceneStrategyPreviewNavEntry {
    companion object : BackstackValueSaverFactory<ListDetailSceneStrategyPreviewNavEntry> {
        override fun create(
            previous: BackstackEntry<ListDetailSceneStrategyPreviewNavEntry>?,
        ): Saver<ListDetailSceneStrategyPreviewNavEntry, Any> =
            listSaver(
                save = {
                    listOf(
                        when (it) {
                            is DetailPreviewEntry -> 2
                            is EmptyPreviewEntry -> 0
                            is ListPreviewEntry -> 1
                        },
                    )
                },
                restore = { list ->
                    val type = list.first()
                    when (type) {
                        0 -> EmptyPreviewEntry()
                        1 -> ListPreviewEntry()
                        2 -> DetailPreviewEntry(
                            requireNotNull(previous).value as ListDetailInfo,
                        )
                        else -> error("Unknown type!")
                    }
                },
            )
    }
}

private class ListPreviewEntry : ListDetailSceneStrategyPreviewNavEntry, ListEntry {
    override val isListVisible: Boolean
        get() = true
    override val isDetailVisible: Boolean
        get() = true
}

private class DetailPreviewEntry(
    listDetailInfo: ListDetailInfo,
) : ListDetailSceneStrategyPreviewNavEntry, ListDetailInfo by listDetailInfo, DetailEntry

private class EmptyPreviewEntry : ListDetailSceneStrategyPreviewNavEntry

@Suppress("LongMethod")
@Preview
@Composable
private fun ListDetailSceneStrategyPreview() {
    SharedTransitionLayout {
        CompositionLocalProvider(LocalNavigationSharedTransitionScope provides this) {
            val backstack = rememberMutableBackstackNavigationController(
                initialBackstackEntries = listOf(
                    BackstackEntry(
                        value = EmptyPreviewEntry(),
                        previous = null,
                    ),
                ),
                backstackValueSaverFactory = ListDetailSceneStrategyPreviewNavEntry,
            )

            val detailUuids = rememberSerializable(
                serializer = ListSerializer(Uuid.serializer()),
            ) {
                List(5) { Uuid.random() }
            }

            val navEntries = rememberDecoratedNavEntries(
                backstack,
            ) { entry ->
                Logger.d { "Rendering entry $entry" }
                when (val value = entry.value) {
                    is EmptyPreviewEntry -> {
                        Surface(
                            modifier = Modifier.fillMaxSize(),
                        ) {
                            Box(
                                Modifier.fillMaxSize(),
                                contentAlignment = Alignment.Center,
                            ) {
                                Button(
                                    onClick = {
                                        backstack.navigate(valueFactory = {
                                            ListPreviewEntry()
                                        })
                                        backstack.navigate(valueFactory = {
                                            DetailPreviewEntry(
                                                listDetailInfo = it.value as ListPreviewEntry,
                                            )
                                        }, id = detailUuids.first())
                                    },
                                ) {
                                    Text("Go to list")
                                }
                            }
                        }
                    }

                    is DetailPreviewEntry -> {
                        val random = remember(entry.id) { Random(entry.id.hashCode()) }
                        val color = remember(random) {
                            Color(
                                red = random.nextInt(256),
                                green = random.nextInt(256),
                                blue = random.nextInt(256),
                            )
                        }
                        Surface(
                            modifier = Modifier.fillMaxSize(),
                        ) {
                            Column(
                                modifier = Modifier.fillMaxSize().background(color),
                                verticalArrangement = Arrangement.Center,
                            ) {
                                Text("Detail: ${entry.id}")
                                Button(
                                    onClick = {
                                        backstack.navigate(valueFactory = {
                                            EmptyPreviewEntry()
                                        })
                                    },
                                ) {
                                    Text("Go to empty")
                                }
                            }
                        }
                    }

                    is ListPreviewEntry -> {
                        Surface(
                            modifier = Modifier.fillMaxSize(),
                        ) {
                            Column(
                                modifier = Modifier.fillMaxSize(),
                                verticalArrangement = Arrangement.Center,
                            ) {
                                detailUuids.forEach { uuid ->
                                    Button(
                                        onClick = {
                                            backstack.popUpTo(entry.id, inclusive = false)
                                            backstack.navigate(valueFactory = { previous ->
                                                DetailPreviewEntry(listDetailInfo = previous.value as ListPreviewEntry)
                                            }, id = uuid)
                                        },
                                    ) {
                                        Text("Go to detail $uuid")
                                    }
                                }
                            }
                        }
                    }
                }
            }

            val sceneState = rememberSceneState(
                entries = navEntries,
                sceneStrategy = ListDetailSceneStrategy(),
                onBack = backstack::popBackstack,
            )

            val dispatcher = requireNotNull(
                LocalNavigationEventDispatcherOwner.current,
            ).navigationEventDispatcher
            val navigationEventHistory by dispatcher.history.collectAsState()
            val currentInfo = navigationEventHistory.mergedHistory.getOrNull(
                navigationEventHistory.currentIndex,
            )

            val navigationEventTransitionState =
                if (currentInfo is ListDetailSceneStrategyPreviewNavigationEventInfo &&
                    currentInfo.sceneKey == sceneState.currentScene.key
                ) {
                    dispatcher.transitionState.collectAsState().value
                } else {
                    NavigationEventTransitionState.Idle
                }

            NavigationBackHandler(
                state = rememberNavigationEventState(
                    currentInfo = ListDetailSceneStrategyPreviewNavigationEventInfo(
                        sceneState.currentScene::class to sceneState.currentScene.key,
                    ),
                    backInfo = sceneState.previousScenes.map {
                        ListDetailSceneStrategyPreviewNavigationEventInfo(it::class to it.key)
                    },
                ),
                isBackEnabled = sceneState.currentScene.previousEntries.isNotEmpty(),
                onBackCompleted = {
                    backstack.popUpTo(sceneState.currentScene.previousEntries.last().contentKey as Uuid)
                },
            )

            MaterialPredictiveNavDisplay(
                sceneState = sceneState,
                navigationEventTransitionState = navigationEventTransitionState,
            )
        }
    }
}

private data class ListDetailSceneStrategyPreviewNavigationEventInfo(
    val sceneKey: Pair<KClass<out Scene<*>>, Any>,
) : NavigationEventInfo()
