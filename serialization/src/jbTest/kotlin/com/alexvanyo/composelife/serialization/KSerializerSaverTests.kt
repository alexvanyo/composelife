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

package com.alexvanyo.composelife.serialization

import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runComposeUiTest
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.kmpstaterestorationtester.KmpStateRestorationTester
import kotlinx.serialization.Serializable
import org.junit.runner.RunWith
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class KSerializerSaverTests {

    @Test
    fun kserializer_saver_is_correct() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        var value: SealedClass? = null

        stateRestorationTester.setContent {
            value = rememberSaveable(saver = SealedClass.Saver) {
                A(
                    string = Random.nextInt().toString(),
                    intOffset = IntOffset(
                        x = Random.nextInt(),
                        y = Random.nextInt(),
                    ),
                    rect = Rect(
                        left = Random.nextFloat(),
                        top = Random.nextFloat(),
                        right = Random.nextFloat(),
                        bottom = Random.nextFloat(),
                    ),
                )
            }
        }

        val initialValue = value
        value = null

        stateRestorationTester.emulateSavedInstanceStateRestore()

        val restoredValue = value

        assertEquals(initialValue, restoredValue)
    }
}

@Serializable
private sealed class SealedClass {
    companion object {
        val Saver get() = serializer().saver
    }
}

@Serializable
private data class A(
    val string: String,
    @Serializable(with = IntOffsetSerializer::class)
    val intOffset: IntOffset,
    @Serializable(with = RectSerializer::class)
    val rect: Rect,
) : SealedClass() {
    companion object {
        val Saver get() = serializer().saver
    }
}

@Serializable
private data class B(
    val int: Int,
) : SealedClass() {
    companion object {
        val Saver get() = serializer().saver
    }
}
