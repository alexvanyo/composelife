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
import androidx.compose.runtime.Composable
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.Immutable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.saveable.rememberSerializable
import androidx.compose.runtime.setValue
import androidx.savedstate.compose.serialization.serializers.SnapshotStateMapSerializer
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.MutableBackstackMap
import com.alexvanyo.composelife.navigation.NavigationState
import com.alexvanyo.composelife.navigation.rememberBackstackMap
import com.alexvanyo.composelife.navigation.withExpectedActor
import com.alexvanyo.composelife.serialization.uuidSaver
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseEditingState
import com.alexvanyo.composelife.ui.cells.SelectionState
import com.alexvanyo.composelife.ui.settings.InlineSettingsPaneCtx
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.isInProgress
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.launch
import kotlinx.serialization.KSerializer
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
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
    val inlineNavigationState: NavigationState<BackstackEntry<InlineActionCardNavigation>>

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
    val initialSpeedEntry: BackstackEntry<InlineActionCardNavigation> = BackstackEntry(
        value = InlineActionCardNavigation.Speed,
        previous = null,
        id = InlineActionCardNavigation.Speed.entryId,
    )

    val inlineBackstackMap = rememberBackstackMap(
        initialBackstackEntries = listOf(
            initialSpeedEntry,
            BackstackEntry(
                value = InlineActionCardNavigation.Edit,
                previous = initialSpeedEntry,
                id = InlineActionCardNavigation.Edit.entryId,
            ),
            BackstackEntry(
                value = InlineActionCardNavigation.Settings,
                previous = initialSpeedEntry,
                id = InlineActionCardNavigation.Settings.entryId,
            ),
        ),
        backstackValueSaverFactory = InlineActionCardNavigation.SaverFactory,
    )

    var currentBackstackEntryId by rememberSerializable {
        mutableStateOf(InlineActionCardNavigation.Speed.entryId)
    }

    val inlineNavigationState = remember {
        object : NavigationState<BackstackEntry<InlineActionCardNavigation>> {
            override val entryMap: MutableBackstackMap<InlineActionCardNavigation> get() = inlineBackstackMap

            override var currentEntryId: Uuid
                get() = currentBackstackEntryId
                set(value) {
                    currentBackstackEntryId = value
                }
        }
    }

    val onBackPressed = remember {
        { inlineActorBackstackEntryId: Uuid? ->
            inlineNavigationState.withExpectedActor(inlineActorBackstackEntryId) { entry ->
                currentEntryId = when (entry.value) {
                    InlineActionCardNavigation.Edit,
                    InlineActionCardNavigation.Settings,
                    -> InlineActionCardNavigation.Speed.entryId
                    InlineActionCardNavigation.Speed -> error("Shouldn't be navigating back from speed")
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
            },
        ),
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

    val coroutineScope = rememberCoroutineScope()

    return remember(
        enableBackHandler,
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

            override val canNavigateBack: Boolean get() =
                enableBackHandler &&
                    expandedTargetState.current &&
                    inlineNavigationState.currentEntryId != InlineActionCardNavigation.Speed.entryId

            override val contentScrollStateMap get() = contentScrollStateMap

            override fun onSpeedClicked(actorBackstackEntryId: Uuid?) {
                inlineNavigationState.withExpectedActor(actorBackstackEntryId) {
                    currentEntryId = InlineActionCardNavigation.Speed.entryId
                }
            }

            override fun onEditClicked(actorBackstackEntryId: Uuid?) {
                inlineNavigationState.withExpectedActor(actorBackstackEntryId) {
                    currentEntryId = InlineActionCardNavigation.Edit.entryId
                }
            }

            override fun onSettingsClicked(actorBackstackEntryId: Uuid?) {
                inlineNavigationState.withExpectedActor(actorBackstackEntryId) {
                    currentEntryId = InlineActionCardNavigation.Settings.entryId
                }
            }

            override fun inlineOnBackPressed(inlineActorBackstackEntryId: Uuid?) {
                onBackPressed(inlineActorBackstackEntryId)
            }
        }
    }
}
