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
import com.alexvanyo.composelife.navigation.previousEntry
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.withExpectedActor
import com.alexvanyo.composelife.ui.app.action.settings.Setting
import com.alexvanyo.composelife.ui.app.action.settings.SettingsCategory
import com.alexvanyo.composelife.ui.util.PredictiveBackState
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.predictiveBackHandler
import java.util.UUID

/**
 * The persistable state describing the [CellUniverseActionCard].
 */
interface CellUniverseActionCardState {

    /**
     * Sets if the card is expanded.
     */
    fun setIsExpanded(isExpanded: Boolean)

    /**
     * The target state for whether the card is expanded.
     */
    val expandedTargetState: TargetState<Boolean>

    /**
     * The [TargetState] for whether the card is fullscreen.
     */
    val fullscreenTargetState: TargetState<Boolean>

    /**
     * The navigation state of the card.
     */
    val navigationState: BackstackState<out ActionCardNavigation>

    /**
     * The [PredictiveBackState] for the internal navigation of the [CellUniverseActionCard].
     */
    val predictiveBackState: PredictiveBackState

    /**
     * `true` if the card can navigate back.
     */
    val canNavigateBack: Boolean

    fun onSpeedClicked(actorBackstackEntryId: UUID? = null)

    fun onEditClicked(actorBackstackEntryId: UUID? = null)

    fun onSettingsClicked(actorBackstackEntryId: UUID? = null)

    fun onSeeMoreSettingsClicked(actorBackstackEntryId: UUID? = null)

    fun onOpenInSettingsClicked(
        setting: Setting,
        actorBackstackEntryId: UUID? = null,
    )

    fun onBackPressed(actorBackstackEntryId: UUID? = null)
}

/**
 * Remembers the a default implementation of [CellUniverseActionCardState].
 */
@Suppress("LongMethod", "CyclomaticComplexMethod")
@Composable
fun rememberCellUniverseActionCardState(
    enableBackHandler: Boolean,
    setIsExpanded: (Boolean) -> Unit,
    expandedTargetState: TargetState<Boolean>,
): CellUniverseActionCardState {
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

    val canNavigateBack by remember {
        derivedStateOf {
            currentNavController.canNavigateBack || when (currentBackstack) {
                ActionCardBackstack.Speed -> false
                ActionCardBackstack.Edit,
                ActionCardBackstack.Settings,
                -> true
            }
        }
    }

    val navigationState = remember {
        object : BackstackState<ActionCardNavigation> {
            override val entryMap: BackstackMap<out ActionCardNavigation>
                get() = speedNavController.entryMap +
                    editNavController.entryMap +
                    settingsNavController.entryMap

            override val currentEntryId: UUID
                get() = currentNavController.currentEntryId

            override val previousEntryId: UUID?
                get() = if (currentNavController.canNavigateBack) {
                    currentNavController.previousEntryId
                } else {
                    when (currentBackstack) {
                        ActionCardBackstack.Speed -> null
                        ActionCardBackstack.Edit,
                        ActionCardBackstack.Settings,
                        -> speedNavController.currentEntryId
                    }
                }
        }
    }

    val onBackPressed = { actorBackstackEntryId: UUID? ->
        currentNavController.withExpectedActor(actorBackstackEntryId) {
            if (currentNavController.canNavigateBack) {
                currentNavController.popBackstack()
            } else {
                currentBackstack = ActionCardBackstack.Speed
            }
        }
    }

    val predictiveBackState = if (enableBackHandler && expandedTargetState.current && canNavigateBack) {
        predictiveBackHandler {
            onBackPressed(navigationState.currentEntryId)
        }
    } else {
        PredictiveBackState.NotRunning
    }

    return object : CellUniverseActionCardState {

        override fun setIsExpanded(isExpanded: Boolean) {
            setIsExpanded(isExpanded)
        }

        override val expandedTargetState: TargetState<Boolean>
            get() = expandedTargetState

        override val navigationState get() = navigationState

        override val predictiveBackState get() = predictiveBackState

        override val canNavigateBack: Boolean get() = canNavigateBack

        override val fullscreenTargetState: TargetState<Boolean> get() =
            when (predictiveBackState) {
                PredictiveBackState.NotRunning ->
                    TargetState.Single(
                        this.expandedTargetState.current && navigationState.currentEntry.value.isFullscreen,
                    )
                is PredictiveBackState.Running ->
                    if (this.expandedTargetState.current) {
                        val currentIsFullscreen = navigationState.currentEntry.value.isFullscreen
                        when (val previousIsFullscreen = navigationState.previousEntry?.value?.isFullscreen) {
                            null -> TargetState.Single(currentIsFullscreen)
                            currentIsFullscreen -> TargetState.Single(currentIsFullscreen)
                            else -> TargetState.InProgress(
                                current = currentIsFullscreen,
                                provisional = previousIsFullscreen,
                                progress = predictiveBackState.progress,
                            )
                        }
                    } else {
                        TargetState.Single(false)
                    }
            }

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
                check(this === settingsNavController)
                settingsNavController.navigate(
                    ActionCardNavigation.Settings.Fullscreen(
                        initialSettingsCategory = SettingsCategory.Algorithm,
                        initialShowDetails = false,
                        initialSettingToScrollTo = null,
                    ),
                )
            }
        }

        override fun onOpenInSettingsClicked(setting: Setting, actorBackstackEntryId: UUID?) {
            currentNavController.withExpectedActor(actorBackstackEntryId) {
                check(this === settingsNavController)
                settingsNavController.navigate(
                    ActionCardNavigation.Settings.Fullscreen(
                        initialSettingsCategory = setting.category,
                        initialShowDetails = true,
                        initialSettingToScrollTo = setting,
                    ),
                )
            }
        }

        override fun onBackPressed(actorBackstackEntryId: UUID?) {
            onBackPressed(actorBackstackEntryId)
        }
    }
}
