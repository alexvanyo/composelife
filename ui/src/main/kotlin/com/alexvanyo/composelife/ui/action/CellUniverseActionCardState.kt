package com.alexvanyo.composelife.ui.action

import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.canNavigateBack
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.navigate
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.navigation.popUpTo
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.withExpectedActor
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
    val navigationState: BackstackState<ActionCardNavigation>

    /**
     * `true` if the card can navigate back.
     */
    val canNavigateBack: Boolean

    fun onSpeedClicked(actorBackstackEntryId: UUID? = null)

    fun onEditClicked(actorBackstackEntryId: UUID? = null)

    fun onPaletteClicked(actorBackstackEntryId: UUID? = null)

    fun onSettingsClicked(actorBackstackEntryId: UUID? = null)

    fun onBackPressed(actorBackstackEntryId: UUID? = null)

    companion object {
        const val defaultIsExpanded: Boolean = false
    }
}

/**
 * Remembers the a default implementation of [CellUniverseActionCardState].
 */
@Composable
fun rememberCellUniverseActionCardState(
    initialIsExpanded: Boolean = CellUniverseActionCardState.defaultIsExpanded,
    initialBackstackEntries: List<BackstackEntry<ActionCardNavigation>> = listOf(
        BackstackEntry(
            value = ActionCardNavigation.Speed,
            previous = null
        )
    )
): CellUniverseActionCardState {
    val isExpanded = rememberSaveable { mutableStateOf(initialIsExpanded) }

    val navController = rememberMutableBackstackNavigationController(
        initialBackstackEntries = initialBackstackEntries,
        saver = ActionCardNavigation.Saver
    )

    return remember {
        object : CellUniverseActionCardState {
            override var isExpanded: Boolean by isExpanded

            override val navigationState get() = navController

            override val canNavigateBack: Boolean get() = navController.canNavigateBack

            override val isFullscreen: Boolean get() =
                this.isExpanded && when (navigationState.currentEntry.value) {
                    ActionCardNavigation.Speed,
                    ActionCardNavigation.Edit,
                    ActionCardNavigation.Palette -> false
                    ActionCardNavigation.Settings -> true
                }

            override fun onSpeedClicked(actorBackstackEntryId: UUID?) {
                navController.withExpectedActor(actorBackstackEntryId) {
                    popUpToSpeed()
                }
            }

            override fun onEditClicked(actorBackstackEntryId: UUID?) {
                navController.withExpectedActor(actorBackstackEntryId) {
                    if (currentEntry.value !is ActionCardNavigation.Edit) {
                        popUpToSpeed()
                        navController.navigate(ActionCardNavigation.Edit)
                    }
                }
            }

            override fun onPaletteClicked(actorBackstackEntryId: UUID?) {
                navController.withExpectedActor(actorBackstackEntryId) {
                    if (currentEntry.value !is ActionCardNavigation.Palette) {
                        popUpToSpeed()
                        navController.navigate(ActionCardNavigation.Palette)
                    }
                }
            }

            override fun onSettingsClicked(actorBackstackEntryId: UUID?) {
                navController.withExpectedActor(actorBackstackEntryId) {
                    if (currentEntry.value !is ActionCardNavigation.Settings) {
                        popUpToSpeed()
                        navController.navigate(ActionCardNavigation.Settings)
                    }
                }
            }

            override fun onBackPressed(actorBackstackEntryId: UUID?) {
                navController.withExpectedActor(actorBackstackEntryId) {
                    navController.popBackstack()
                }
            }

            private fun popUpToSpeed() {
                navController.popUpTo(
                    predicate = { value: ActionCardNavigation ->
                        when (value) {
                            ActionCardNavigation.Speed -> true
                            ActionCardNavigation.Edit,
                            ActionCardNavigation.Palette,
                            ActionCardNavigation.Settings -> false
                        }
                    }
                )
            }
        }
    }
}
