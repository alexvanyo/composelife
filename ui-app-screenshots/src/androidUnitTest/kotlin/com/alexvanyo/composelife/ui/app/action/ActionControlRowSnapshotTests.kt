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

package com.alexvanyo.composelife.ui.app.action

import com.alexvanyo.composelife.ui.app.util.BaseRoborazziTest
import com.alexvanyo.composelife.ui.app.util.RoborazziParameterization
import kotlin.test.Test

class ActionControlRowSnapshotTests(
    roborazziParameterization: RoborazziParameterization,
) : BaseRoborazziTest(roborazziParameterization) {

    @Test
    fun collapsed_paused_action_control_row_preview() {
        snapshot {
            CollapsedPausedActionControlRowPreview()
        }
    }

    @Test
    fun collapsed_running_action_control_row_preview() {
        snapshot {
            CollapsedRunningActionControlRowPreview()
        }
    }

    @Test
    fun viewport_tracking_action_control_row_preview() {
        snapshot {
            ViewportTrackingActionControlRowPreview()
        }
    }

    @Test
    fun expanded_action_control_row_preview() {
        snapshot {
            ExpandedActionControlRowPreview()
        }
    }

    @Test
    fun selecting_box_action_control_row_preview() {
        snapshot {
            SelectingBoxActionControlRowPreview()
        }
    }

    @Test
    fun selection_action_control_row_preview() {
        snapshot {
            SelectionActionControlRowPreview()
        }
    }

    @Test
    fun elevated_expanded_action_control_row_preview() {
        snapshot {
            ElevatedExpandedActionControlRowPreview()
        }
    }
}
