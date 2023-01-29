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
import kotlin.test.Test

class CellWindowSnapshotTests : BasePaparazziTest() {

    @Test
    fun navigable_immutable_cell_window_preview() {
        snapshot {
            NavigableImmutableCellWindowPreview()
        }
    }

    @Test
    fun tracking_immutable_cell_window_preview() {
        snapshot {
            TrackingImmutableCellWindowPreview()
        }
    }

    @Test
    fun navigable_mutable_cell_window_preview() {
        snapshot {
            NavigableMutableCellWindowPreview()
        }
    }

    @Test
    fun tracking_mutable_cell_window_preview() {
        snapshot {
            TrackingMutableCellWindowPreview()
        }
    }
}
