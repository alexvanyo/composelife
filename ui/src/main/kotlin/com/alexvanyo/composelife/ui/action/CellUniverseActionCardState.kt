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

package com.alexvanyo.composelife.ui.action

import androidx.compose.runtime.Composable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackMap
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.canNavigateBack
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.navigate
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.withExpectedActor
import com.alexvanyo.composelife.ui.action.settings.SettingsCategory
import java.util.UUID

/**
 * The persistable state describing the [CellUniverseActionCard].
 */
interface CellUniverseActionCardState {

    /**
     * `true` if the card is expanded.
     */
    var isExpanded: Boolean

    /**
     * `true` if the card is fullscreen.
     */
    val isFullscreen: Boolean

    /**
     * The navigation state of the card.
     */
    val navigationState: BackstackState<out ActionCardNavigation>

    /**
     * `true` if the card can navigate back.
     */
    val canNavigateBack: Boolean

    fun onSpeedClicked(actorBackstackEntryId: UUID? = null)

    fun onEditClicked(actorBackstackEntryId: UUID? = null)

    fun onSettingsClicked(actorBackstackEntryId: UUID? = null)

    fun onSeeMoreSettingsClicked(actorBackstackEntryId: UUID? = null)

    fun onBackPressed(actorBackstackEntryId: UUID? = null)

    companion object {
        const val defaultIsExpanded: Boolean = false
    }
}

/**
 * Remembers the a default implementation of [CellUniverseActionCardState].
 */
@Suppress("LongMethod")
@Composable
fun rememberCellUniverseActionCardState(
    initialIsExpanded: Boolean = CellUniverseActionCardState.defaultIsExpanded,
): CellUniverseActionCardState {
    val isExpanded = rememberSaveable { mutableStateOf(initialIsExpanded) }

    var currentBackstack by rememberSaveable(
        stateSaver = ActionCardBackstack.Saver,
    ) {
        mutableStateOf(ActionCardBackstack.Speed)
    }

    val speedNavController = rememberMutableBackstackNavigationController(
        initialBackstackEntries = listOf(
            BackstackEntry(
                value = ActionCardNavigation.Speed.Inline,
                previous = null,
            ),
        ),
        saver = ActionCardNavigation.Speed.Saver,
    )

    val editNavController = rememberMutableBackstackNavigationController(
        initialBackstackEntries = listOf(
            BackstackEntry(
                value = ActionCardNavigation.Edit.Inline,
                previous = null,
            ),
        ),
        saver = ActionCardNavigation.Edit.Saver,
    )

    val settingsNavController = rememberMutableBackstackNavigationController(
        initialBackstackEntries = listOf(
            BackstackEntry(
                value = ActionCardNavigation.Settings.Inline,
                previous = null,
            ),
        ),
        saver = ActionCardNavigation.Settings.Saver,
    )

    val currentNavController by remember {
        derivedStateOf {
            when (currentBackstack) {
                ActionCardBackstack.Speed -> speedNavController
                ActionCardBackstack.Edit -> editNavController
                ActionCardBackstack.Settings -> settingsNavController
            }
        }
    }

    return remember {
        object : CellUniverseActionCardState {
            @Suppress("VarCouldBeVal")
            override var isExpanded: Boolean by isExpanded

            override val navigationState = object : BackstackState<ActionCardNavigation> {
                override val entryMap: BackstackMap<out ActionCardNavigation>
                    get() = speedNavController.entryMap +
                        editNavController.entryMap +
                        settingsNavController.entryMap

                override val currentEntryId: UUID
                    get() = currentNavController.currentEntryId
            }

            override val canNavigateBack: Boolean get() =
                currentNavController.canNavigateBack || when (currentBackstack) {
                    ActionCardBackstack.Speed -> false
                    ActionCardBackstack.Edit,
                    ActionCardBackstack.Settings,
                    -> true
                }

            override val isFullscreen: Boolean get() =
                this.isExpanded && navigationState.currentEntry.value.isFullscreen

            override fun onSpeedClicked(actorBackstackEntryId: UUID?) {
                currentNavController.withExpectedActor(actorBackstackEntryId) {
                    currentBackstack = ActionCardBackstack.Speed
                }
            }

            override fun onEditClicked(actorBackstackEntryId: UUID?) {
                currentNavController.withExpectedActor(actorBackstackEntryId) {
                    currentBackstack = ActionCardBackstack.Edit
                }
            }

            override fun onSettingsClicked(actorBackstackEntryId: UUID?) {
                currentNavController.withExpectedActor(actorBackstackEntryId) {
                    currentBackstack = ActionCardBackstack.Settings
                }
            }

            override fun onSeeMoreSettingsClicked(actorBackstackEntryId: UUID?) {
                currentNavController.withExpectedActor(actorBackstackEntryId) {
                    check(currentNavController === settingsNavController)
                    settingsNavController.navigate(
                        ActionCardNavigation.Settings.Fullscreen(
                            initialSettingsCategory = SettingsCategory.Algorithm,
                            initialShowDetails = false,
                        ),
                    )
                }
            }

            override fun onBackPressed(actorBackstackEntryId: UUID?) {
                currentNavController.withExpectedActor(actorBackstackEntryId) {
                    if (currentNavController.canNavigateBack) {
                        currentNavController.popBackstack()
                    } else {
                        currentBackstack = ActionCardBackstack.Speed
                    }
                }
            }
        }
    }
}
