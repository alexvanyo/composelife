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
import androidx.navigation3.runtime.NavEntry
import androidx.navigation3.scene.OverlayScene
import androidx.navigation3.scene.Scene
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotEquals

class SceneStateTests {

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

    private class TestScene(
        override val key: Any,
    ) : Scene<String> {
        override val previousEntries: List<NavEntry<String>> = emptyList()
        override val entries: List<NavEntry<String>> = emptyList()
        override val content: @Composable () -> Unit = {}
        override fun toString(): String = "TestScene(key=$key)"
    }

    private class TestOverlayScene(
        override val key: Any,
    ) : OverlayScene<String> {
        override val previousEntries: List<NavEntry<String>> = emptyList()
        override val entries: List<NavEntry<String>> = emptyList()
        override val content: @Composable () -> Unit = {}
        override val overlaidEntries: List<NavEntry<String>> = emptyList()
        override fun toString(): String = "TestOverlayScene(key=$key)"
    }
}
