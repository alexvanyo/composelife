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

import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.rememberScrollState
import androidx.compose.runtime.Composable
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.Immutable
import androidx.compose.runtime.collectAsState
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.saveable.rememberSerializable
import androidx.compose.runtime.setValue
import androidx.navigationevent.NavigationEventInfo
import androidx.navigationevent.NavigationEventTransitionState
import androidx.navigationevent.compose.LocalNavigationEventDispatcherOwner
import androidx.navigationevent.compose.NavigationBackHandler
import androidx.navigationevent.compose.rememberNavigationEventState
import androidx.savedstate.compose.serialization.serializers.SnapshotStateMapSerializer
import coil3.request.Disposable
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackMap
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.canNavigateBack
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.withExpectedActor
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseEditingState
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseState
import com.alexvanyo.composelife.ui.cells.SelectionState
import com.alexvanyo.composelife.ui.settings.InlineSettingsPaneCtx
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.isInProgress
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.launch
import kotlinx.serialization.KSerializer
import kotlinx.serialization.builtins.MapSerializer
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlin.math.exp
import kotlin.uuid.Uuid

// region templated-ctx
@Immutable
@Inject
class CellUniverseActionCardCtx(
    internal val inlineEditPaneCtx: InlineEditPaneCtx,
    internal val inlineSettingsPaneCtx: InlineSettingsPaneCtx,
) {
    companion object
}
// endregion templated-ctx

/**
 * The persistable state describing the [CellUniverseActionCard].
 */
interface CellUniverseActionCardState {

    val editingState: InteractiveCellUniverseEditingState

    val actionControlRowState: ActionControlRowState

    /**
     * The target state for whether the card is expanded.
     */
    val expandedTargetState: TargetState<Boolean, *>

    /**
     * The inline navigation state of the card.
     */
    val inlineNavigationState: BackstackState<InlineActionCardNavigation>

    /**
     * The [NavigationEventTransitionState] for the inline navigation of the [CellUniverseActionCard].
     */
    val inlineNavigationEventTransitionState: NavigationEventTransitionState

    /**
     * `true` if the card can navigate back.
     */
    val canNavigateBack: Boolean

    val contentScrollStateMap: Map<Uuid, ScrollState>

    fun onSpeedClicked(actorBackstackEntryId: Uuid? = null)

    fun onEditClicked(actorBackstackEntryId: Uuid? = null)

    fun onSettingsClicked(actorBackstackEntryId: Uuid? = null)

    fun inlineOnBackPressed(inlineActorBackstackEntryId: Uuid? = null)
}

/**
 * Remembers the a default implementation of [CellUniverseActionCardState].
 */
@Suppress("LongMethod", "CyclomaticComplexMethod", "LongParameterList")
@Composable
fun rememberCellUniverseActionCardState(
    enableBackHandler: Boolean,
    isViewportTracking: Boolean,
    setIsViewportTracking: (Boolean) -> Unit,
    showImmersiveModeControl: Boolean,
    isImmersiveMode: Boolean,
    setIsImmersiveMode: (Boolean) -> Unit,
    showFullSpaceModeControl: Boolean,
    isFullSpaceMode: Boolean,
    setIsFullSpaceMode: (Boolean) -> Unit,
    isExpanded: Boolean,
    setIsExpanded: (Boolean) -> Unit,
    expandedTargetState: TargetState<Boolean, *>,
    temporalGameOfLifeState: TemporalGameOfLifeState,
    editingState: InteractiveCellUniverseEditingState,
): CellUniverseActionCardState {
    var currentInlineBackstack: InlineActionCardBackstack by rememberSaveable(
        stateSaver = InlineActionCardBackstack.Saver,
    ) {
        mutableStateOf(InlineActionCardBackstack.Speed)
    }

    val speedNavController = rememberMutableBackstackNavigationController(
        initialBackstackEntries = listOf(
            BackstackEntry(
                value = InlineActionCardNavigation.Speed,
                previous = null,
            ),
        ),
        backstackValueSaverFactory = InlineActionCardNavigation.SaverFactory,
    )

    val editNavController = rememberMutableBackstackNavigationController(
        initialBackstackEntries = listOf(
            BackstackEntry(
                value = InlineActionCardNavigation.Edit,
                previous = null,
            ),
        ),
        backstackValueSaverFactory = InlineActionCardNavigation.SaverFactory,
    )

    val settingsNavController = rememberMutableBackstackNavigationController(
        initialBackstackEntries = listOf(
            BackstackEntry(
                value = InlineActionCardNavigation.Settings,
                previous = null,
            ),
        ),
        backstackValueSaverFactory = InlineActionCardNavigation.SaverFactory,
    )

    val currentInlineNavController by remember {
        derivedStateOf {
            when (currentInlineBackstack) {
                InlineActionCardBackstack.Speed -> speedNavController
                InlineActionCardBackstack.Edit -> editNavController
                InlineActionCardBackstack.Settings -> settingsNavController
            }
        }
    }

    val canNavigateBack by remember {
        derivedStateOf {
            currentInlineNavController.canNavigateBack || when (currentInlineBackstack) {
                InlineActionCardBackstack.Speed -> false
                InlineActionCardBackstack.Edit,
                InlineActionCardBackstack.Settings,
                -> true
            }
        }
    }

    val inlineNavigationState = remember {
        object : BackstackState<InlineActionCardNavigation> {
            override val entryMap: BackstackMap<InlineActionCardNavigation>
                get() = speedNavController.entryMap +
                    editNavController.entryMap +
                    settingsNavController.entryMap

            override val currentEntryId: Uuid
                get() = currentInlineNavController.currentEntryId

            override val previousEntryId: Uuid?
                get() = if (currentInlineNavController.canNavigateBack) {
                    currentInlineNavController.previousEntryId
                } else {
                    when (currentInlineBackstack) {
                        InlineActionCardBackstack.Speed -> null
                        InlineActionCardBackstack.Edit,
                        InlineActionCardBackstack.Settings,
                        -> speedNavController.currentEntryId
                    }
                }
        }
    }

    val onBackPressed = remember {
        { inlineActorBackstackEntryId: Uuid? ->
            currentInlineNavController.withExpectedActor(inlineActorBackstackEntryId) {
                if (currentInlineNavController.canNavigateBack) {
                    currentInlineNavController.popBackstack()
                } else {
                    currentInlineBackstack = InlineActionCardBackstack.Speed
                }
            }
        }
    }

    val contentScrollStateMap = rememberSerializable(
        serializer = SnapshotStateMapSerializer(
            Uuid.serializer(),
            object : KSerializer<ScrollState> {

                override val descriptor: SerialDescriptor
                    get() = SerialDescriptor(
                        "androidx.compose.foundation.ScrollState",
                        Int.serializer().descriptor,
                    )

                override fun serialize(
                    encoder: Encoder,
                    value: ScrollState,
                ) {
                    encoder.encodeInt(value.value)
                }

                override fun deserialize(decoder: Decoder): ScrollState =
                    ScrollState(decoder.decodeInt())
            }
        )
    ) {
        mutableStateMapOf()
    }
    val currentEntryKeys = inlineNavigationState.entryMap.keys.toSet()
    currentEntryKeys.forEach {
        if (it !in contentScrollStateMap) {
            contentScrollStateMap[it] = ScrollState(initial = Int.MAX_VALUE)
        }
    }
    DisposableEffect(currentEntryKeys) {
        contentScrollStateMap.keys.forEach {
            if (it !in currentEntryKeys) {
                contentScrollStateMap.remove(it)
            }
        }
        onDispose {}
    }
    val currentScrollState = contentScrollStateMap.getValue(inlineNavigationState.currentEntryId)

    val dispatcher = requireNotNull(LocalNavigationEventDispatcherOwner.current).navigationEventDispatcher
    val navigationEventHistory by dispatcher.history.collectAsState()
    val currentInfo = navigationEventHistory.mergedHistory.getOrNull(navigationEventHistory.currentIndex)

    val navigationEventTransitionState =
        if (currentInfo is CellUniverseActionCardNavigationEventInfo &&
            currentInfo.entryId == inlineNavigationState.currentEntryId) {
            dispatcher.transitionState.collectAsState().value
        } else {
            NavigationEventTransitionState.Idle
        }

    NavigationBackHandler(
        state = rememberNavigationEventState(
            currentInfo = CellUniverseActionCardNavigationEventInfo(inlineNavigationState.currentEntryId),
            backInfo = listOfNotNull(
                inlineNavigationState.previousEntryId?.let(::CellUniverseActionCardNavigationEventInfo),
            ),
        ),
        isBackEnabled = enableBackHandler && expandedTargetState.current && canNavigateBack,
        onBackCompleted = {
            onBackPressed(inlineNavigationState.currentEntryId)
        },
    )

    val coroutineScope = rememberCoroutineScope()

    return remember(
        editingState,
        expandedTargetState,
        currentScrollState,
        temporalGameOfLifeState,
        isExpanded,
        setIsExpanded,
        isViewportTracking,
        setIsViewportTracking,
        showImmersiveModeControl,
        isImmersiveMode,
        setIsImmersiveMode,
        showFullSpaceModeControl,
        isFullSpaceMode,
        setIsFullSpaceMode,
        coroutineScope,
        inlineNavigationState,
        contentScrollStateMap,
    ) {
        object : CellUniverseActionCardState {
            override val editingState: InteractiveCellUniverseEditingState
                get() = editingState

            override val actionControlRowState: ActionControlRowState = object : ActionControlRowState {
                override val isElevated: Boolean
                    get() = !expandedTargetState.isInProgress() &&
                            expandedTargetState.current &&
                            currentScrollState.canScrollForward
                override var isRunning: Boolean
                    get() =
                        when (temporalGameOfLifeState.status) {
                            TemporalGameOfLifeState.EvolutionStatus.Paused -> false
                            is TemporalGameOfLifeState.EvolutionStatus.Running -> true
                        }
                    set(value) {
                        temporalGameOfLifeState.setIsRunning(value)
                    }
                override var isExpanded: Boolean
                    get() = isExpanded
                    set(value) {
                        setIsExpanded(value)
                    }
                override var isViewportTracking: Boolean
                    get() = isViewportTracking
                    set(value) {
                        setIsViewportTracking(value)
                    }
                override val showImmersiveModeControl: Boolean
                    get() = showImmersiveModeControl
                override var isImmersiveMode: Boolean
                    get() = isImmersiveMode
                    set(value) {
                        setIsImmersiveMode(value)
                    }
                override val showFullSpaceModeControl: Boolean
                    get() = showFullSpaceModeControl
                override var isFullSpaceMode: Boolean
                    get() = isFullSpaceMode
                    set(value) {
                        setIsFullSpaceMode(value)
                    }
                override val selectionState: SelectionState
                    get() = editingState.selectionState

                override fun onStep() {
                    coroutineScope.launch {
                        temporalGameOfLifeState.step()
                    }
                }

                override fun onClearSelection() {
                    editingState.onClearSelection()
                }

                override fun onCopy() {
                    editingState.onCopy()
                }

                override fun onCut() {
                    editingState.onCut()
                }

                override fun onPaste() {
                    editingState.onPaste()
                }

                override fun onApplyPaste() {
                    editingState.onApplyPaste()
                }
            }

            override val expandedTargetState: TargetState<Boolean, *>
                get() = expandedTargetState

            override val inlineNavigationState get() = inlineNavigationState

            override val inlineNavigationEventTransitionState get() = navigationEventTransitionState

            override val canNavigateBack: Boolean get() = canNavigateBack

            override val contentScrollStateMap get() = contentScrollStateMap

            override fun onSpeedClicked(actorBackstackEntryId: Uuid?) {
                currentInlineNavController.withExpectedActor(actorBackstackEntryId) {
                    currentInlineBackstack = InlineActionCardBackstack.Speed
                }
            }

            override fun onEditClicked(actorBackstackEntryId: Uuid?) {
                currentInlineNavController.withExpectedActor(actorBackstackEntryId) {
                    currentInlineBackstack = InlineActionCardBackstack.Edit
                }
            }

            override fun onSettingsClicked(actorBackstackEntryId: Uuid?) {
                currentInlineNavController.withExpectedActor(actorBackstackEntryId) {
                    currentInlineBackstack = InlineActionCardBackstack.Settings
                }
            }

            override fun inlineOnBackPressed(inlineActorBackstackEntryId: Uuid?) {
                onBackPressed(inlineActorBackstackEntryId)
            }
        }
    }
}

private data class CellUniverseActionCardNavigationEventInfo(
    val entryId: Uuid,
): NavigationEventInfo()
