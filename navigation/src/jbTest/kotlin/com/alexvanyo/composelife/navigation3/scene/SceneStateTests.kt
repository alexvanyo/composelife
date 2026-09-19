/*
 * Copyright 2026 The Android Open Source Project
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

package com.alexvanyo.composelife.navigation3.scene

import androidx.compose.runtime.Composable
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.navigation3.runtime.NavEntry
import androidx.navigation3.scene.OverlayScene
import androidx.navigation3.scene.Scene
import com.alexvanyo.composelife.kmpandroidrunner.BaseKmpTest
import com.alexvanyo.composelife.test.runComposeUiTest
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNotEquals
import kotlin.test.assertTrue

@OptIn(ExperimentalTestApi::class)
@Suppress("TooManyFunctions")
class SceneStateTests : BaseKmpTest() {

    private val entry1 = NavEntry<String>(
        key = "key1",
        content = {},
    )
    private val entry2 = NavEntry<String>(
        key = "key2",
        content = {},
    )

    private val scene1 = TestScene("scene1")
    private val scene2 = TestScene("scene2")

    private val overlayScene1 = TestOverlayScene("overlay1")
    private val overlayScene2 = TestOverlayScene("overlay2")

    @Test
    fun equals_and_hashCode_are_correct() {
        val sceneState1 = SceneState(
            entries = listOf(entry1),
            overlayScenes = listOf(overlayScene1),
            currentScene = scene1,
            previousScenes = listOf(scene2),
        )

        val sceneState1Copy = SceneState(
            entries = listOf(entry1),
            overlayScenes = listOf(overlayScene1),
            currentScene = scene1,
            previousScenes = listOf(scene2),
        )

        val sceneStateDifferentEntries = SceneState(
            entries = listOf(entry2),
            overlayScenes = listOf(overlayScene1),
            currentScene = scene1,
            previousScenes = listOf(scene2),
        )

        val sceneStateDifferentOverlay = SceneState(
            entries = listOf(entry1),
            overlayScenes = listOf(overlayScene2),
            currentScene = scene1,
            previousScenes = listOf(scene2),
        )

        val sceneStateDifferentCurrentScene = SceneState(
            entries = listOf(entry1),
            overlayScenes = listOf(overlayScene1),
            currentScene = scene2,
            previousScenes = listOf(scene2),
        )

        val sceneStateDifferentPreviousScenes = SceneState(
            entries = listOf(entry1),
            overlayScenes = listOf(overlayScene1),
            currentScene = scene1,
            previousScenes = listOf(scene1),
        )

        assertEquals(sceneState1, sceneState1Copy)
        assertEquals(sceneState1.hashCode(), sceneState1Copy.hashCode())

        assertNotEquals(sceneState1, sceneStateDifferentEntries)
        assertNotEquals(sceneState1, sceneStateDifferentOverlay)
        assertNotEquals(sceneState1, sceneStateDifferentCurrentScene)
        assertNotEquals(sceneState1, sceneStateDifferentPreviousScenes)
        assertNotEquals<Any?>(sceneState1, null)
        assertNotEquals<Any?>(sceneState1, "different type")
    }

    @Test
    fun toString_is_correct() {
        val sceneState = SceneState(
            entries = listOf(entry1),
            overlayScenes = listOf(overlayScene1),
            currentScene = scene1,
            previousScenes = listOf(scene2),
        )

        assertEquals(
            "SceneState(entries=[$entry1], overlayScenes=[$overlayScene1], " +
                "currentScene=$scene1, previousScenes=[$scene2])",
            sceneState.toString(),
        )
    }

    @Test
    fun remember_scene_state_with_single_pane_fallback_is_correct() = runComposeUiTest {
        lateinit var state: SceneState<String>

        setContent {
            state = rememberSceneState(
                entries = listOf(entry1),
                sceneStrategy = SinglePaneSceneStrategy(),
                onBack = {},
            )
        }

        assertEquals(1, state.entries.size)
        assertEquals("key1", state.entries.first().contentKey)
        assertEquals(emptyList(), state.overlayScenes)
        assertEquals(emptyList(), state.previousScenes)
        assertEquals("key1", state.currentScene.key)
    }

    @Test
    fun remember_scene_state_with_overlay_scene_is_correct() = runComposeUiTest {
        lateinit var state: SceneState<String>
        val overlayScene = TestOverlayScene(
            key = "overlay",
            overlaidEntries = listOf(entry2),
        )
        val baseScene = TestScene(key = "base")

        val strategy = SceneStrategy<String> { entries ->
            when {
                entries.any { it.contentKey == "key1" } -> overlayScene
                entries.any { it.contentKey == "key2" } -> baseScene
                else -> null
            }
        }

        setContent {
            state = rememberSceneState(
                entries = listOf(entry1),
                sceneStrategy = strategy,
                onBack = {},
            )
        }

        assertEquals(listOf(overlayScene), state.overlayScenes)
        assertEquals(baseScene, state.currentScene)
        assertEquals(listOf(overlayScene), state.previousScenes)
    }

    @Test
    fun remember_scene_state_with_empty_overlaid_entries_throws_exception() = runComposeUiTest {
        val emptyOverlayScene = TestOverlayScene(
            key = "emptyOverlay",
            overlaidEntries = emptyList(),
        )

        val strategy = SceneStrategy<String> {
            emptyOverlayScene
        }

        assertFailsWith<IllegalArgumentException> {
            setContent {
                rememberSceneState(
                    entries = listOf(entry1),
                    sceneStrategy = strategy,
                    onBack = {},
                )
            }
        }
    }

    @Test
    fun remember_scene_state_with_previous_entries_is_correct() = runComposeUiTest {
        lateinit var state: SceneState<String>
        val previousScene = TestScene(key = "prev")
        val currentScene = TestScene(
            key = "current",
            previousEntries = listOf(entry1),
        )

        val strategy = SceneStrategy<String> { entries ->
            when {
                entries.any { it.contentKey == "key2" } -> currentScene
                entries.any { it.contentKey == "key1" } -> previousScene
                else -> null
            }
        }

        setContent {
            state = rememberSceneState(
                entries = listOf(entry2),
                sceneStrategy = strategy,
                onBack = {},
            )
        }

        assertEquals(currentScene, state.currentScene)
        assertEquals(listOf(previousScene), state.previousScenes)
        assertEquals(emptyList(), state.overlayScenes)
    }

    @Test
    fun remember_scene_state_on_back_invoked_via_scope() = runComposeUiTest {
        var onBackCalled = false
        val strategy = SceneStrategy<String> {
            onBack()
            TestScene(key = "scene")
        }

        setContent {
            rememberSceneState(
                entries = listOf(entry1),
                sceneStrategy = strategy,
                onBack = { onBackCalled = true },
            )
        }

        assertTrue(onBackCalled)
    }

    private class TestScene(
        override val key: Any,
        override val previousEntries: List<NavEntry<String>> = emptyList(),
        override val entries: List<NavEntry<String>> = emptyList(),
    ) : Scene<String> {
        override val content: @Composable () -> Unit = {}
        override fun toString(): String = "TestScene(key=$key)"
    }

    private class TestOverlayScene(
        override val key: Any,
        override val overlaidEntries: List<NavEntry<String>> = emptyList(),
        override val previousEntries: List<NavEntry<String>> = emptyList(),
        override val entries: List<NavEntry<String>> = emptyList(),
    ) : OverlayScene<String> {
        override val content: @Composable () -> Unit = {}
        override fun toString(): String = "TestOverlayScene(key=$key)"
    }
}
