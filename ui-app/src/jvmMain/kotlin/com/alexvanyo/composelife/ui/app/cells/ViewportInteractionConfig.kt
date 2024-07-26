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

package com.alexvanyo.composelife.ui.app.cells

/**
 * The configuration type for the viewport of an interactive cell universe.
 */
sealed interface ViewportInteractionConfig {

    /**
     * The [MutableCellWindowViewportState]s (if any) to sync the currently displayed cell window state back to.
     */
    val syncableMutableCellWindowViewportStates: List<MutableCellWindowViewportState>

    /**
     * The viewport is fixed, and can only be changed programmatically and not by the user (via gestures or
     * accessibility actions)
     */
    class Fixed(
        val cellWindowViewportState: CellWindowViewportState,
        override val syncableMutableCellWindowViewportStates: List<MutableCellWindowViewportState> = emptyList(),
    ) : ViewportInteractionConfig

    /**
     * The viewport is navigable, and can be panned and zoomed by the user into [mutableCellWindowViewportState].
     */
    class Navigable(
        val mutableCellWindowViewportState: MutableCellWindowViewportState,
        override val syncableMutableCellWindowViewportStates: List<MutableCellWindowViewportState> = emptyList(),
    ) : ViewportInteractionConfig

    /**
     * The viewport is tracking the pattern in an auto-fit manner driven by [trackingCellWindowViewportState].
     * The resulting offset and scale will be synced back to [syncableMutableCellWindowViewportStates] to keep
     * consistency.
     */
    class Tracking(
        val trackingCellWindowViewportState: TrackingCellWindowViewportState,
        override val syncableMutableCellWindowViewportStates: List<MutableCellWindowViewportState> = emptyList(),
    ) : ViewportInteractionConfig
}
