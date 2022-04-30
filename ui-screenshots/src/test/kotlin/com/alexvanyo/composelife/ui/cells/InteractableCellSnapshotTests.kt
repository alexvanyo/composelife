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

package com.alexvanyo.composelife.ui.cells

import com.alexvanyo.composelife.ui.util.BasePaparazziTest
import org.junit.Test

class InteractableCellSnapshotTests : BasePaparazziTest() {

    @Test
    fun alive_cell_preview() {
        snapshot {
            AliveCellPreview()
        }
    }

    @Test
    fun dead_cell_preview() {
        snapshot {
            DeadCellPreview()
        }
    }
}
