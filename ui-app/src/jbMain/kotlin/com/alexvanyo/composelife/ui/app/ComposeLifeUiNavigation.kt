/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app

import androidx.compose.runtime.Composable
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.unit.DpSize
import androidx.compose.ui.unit.dp
import androidx.window.core.layout.WindowHeightSizeClass
import androidx.window.core.layout.WindowSizeClass
import androidx.window.core.layout.WindowWidthSizeClass
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackMap
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.ui.mobile.component.DetailEntry
import com.alexvanyo.composelife.ui.mobile.component.DialogableEntry
import com.alexvanyo.composelife.ui.mobile.component.ListDetailInfo
import com.alexvanyo.composelife.ui.mobile.component.ListEntry
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsDetailPaneState
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsListPaneState
import com.alexvanyo.composelife.ui.settings.Setting
import com.alexvanyo.composelife.ui.settings.SettingsCategory
import kotlin.uuid.Uuid

/**
 * The ui-scoped navigation destination types.
 *
 * These are mapped from the plain [ComposeLifeNavigation] types using [toComposeLifeUiNavigation].
 */
@Stable
sealed interface ComposeLifeUiNavigation {

    data object CellUniverse : ComposeLifeUiNavigation

    class FullscreenSettingsList(
        val nav: ComposeLifeNavigation.FullscreenSettingsList,
        val windowSizeClass: WindowSizeClass,
        windowSize: DpSize,
        isDetailPresent: Boolean,
    ) : ComposeLifeUiNavigation, FullscreenSettingsListPaneState, ListEntry, DialogableEntry {
        override val settingsCategory: SettingsCategory
            get() = nav.settingsCategory

        override val isDetailVisible: Boolean =
            isDetailPresent || windowSizeClass.windowWidthSizeClass != WindowWidthSizeClass.COMPACT

        override val isListVisible: Boolean =
            !isDetailPresent || windowSizeClass.windowWidthSizeClass != WindowWidthSizeClass.COMPACT

        override val isDialog =
            windowSize.width >= 1200.dp &&
                windowSizeClass.windowHeightSizeClass != WindowHeightSizeClass.COMPACT
    }

    class FullscreenSettingsDetail(
        val nav: ComposeLifeNavigation.FullscreenSettingsDetail,
        windowSizeClass: WindowSizeClass,
        windowSize: DpSize,
        listDetailInfo: ListDetailInfo,
    ) : ComposeLifeUiNavigation,
        FullscreenSettingsDetailPaneState,
        DetailEntry,
        ListDetailInfo by listDetailInfo,
        DialogableEntry {
        override val settingsCategory: SettingsCategory
            get() = nav.settingsCategory
        override val settingToScrollTo: Setting?
            get() = nav.settingToScrollTo

        override fun onFinishedScrollingToSetting() = nav.onFinishedScrollingToSetting()

        override val isDialog =
            windowSize.width >= 1200.dp &&
                windowSizeClass.windowHeightSizeClass != WindowHeightSizeClass.COMPACT
    }

    class DeserializationInfo(
        val nav: ComposeLifeNavigation.DeserializationInfo,
        val windowSizeClass: WindowSizeClass,
    ) : ComposeLifeUiNavigation, DialogableEntry {
        override val isDialog =
            windowSizeClass.windowWidthSizeClass != WindowWidthSizeClass.COMPACT ||
                windowSizeClass.windowHeightSizeClass != WindowHeightSizeClass.COMPACT
    }
}

/**
 * Converts a [BackstackState] of plain [ComposeLifeNavigation] destinations to a [BackstackState] of
 * [ComposeLifeUiNavigation].
 */
@Composable
fun BackstackState<ComposeLifeNavigation>.toComposeLifeUiNavigation(
    windowSizeClass: WindowSizeClass,
    windowSize: DpSize,
): BackstackState<ComposeLifeUiNavigation> =
    remember(entryMap.keys.toSet(), currentEntryId, windowSizeClass, windowSize) {
        /**
         * The result entry map of [ComposeLifeUiNavigation].
         */
        val map = mutableMapOf<Uuid, BackstackEntry<ComposeLifeUiNavigation>>()

        /**
         * A set of [Uuid]s representing list destinations that are known to be paired with existing detail
         * destinations.
         */
        val listsPairedWithDetails = mutableSetOf<Uuid>()

        /**
         * The resulting current entry id for the transformed backstack state.
         *
         * This is initially the [currentEntryId], but may be updated in the mapping.
         */
        var transformedCurrentEntryId by mutableStateOf(currentEntryId)

        @Suppress("LongMethod")
        fun createEntry(nav: BackstackEntry<ComposeLifeNavigation>): BackstackEntry<ComposeLifeUiNavigation> =
            map.getOrPut(nav.id) {
                when (val value = nav.value) {
                    ComposeLifeNavigation.CellUniverse -> BackstackEntry(
                        value = ComposeLifeUiNavigation.CellUniverse,
                        previous = nav.previous?.let(::createEntry),
                        id = nav.id,
                    )
                    is ComposeLifeNavigation.FullscreenSettingsDetail -> {
                        val previous = nav.previous
                        requireNotNull(previous)
                        require(previous.value is ComposeLifeNavigation.FullscreenSettingsList)
                        listsPairedWithDetails.add(previous.id)
                        val listEntry = previous.let(::createEntry)
                        val listNavEntry = listEntry.value as ListDetailInfo
                        BackstackEntry(
                            value = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                                nav = value,
                                windowSizeClass = windowSizeClass,
                                windowSize = windowSize,
                                listDetailInfo = listNavEntry,
                            ),
                            previous = listEntry,
                            id = nav.id,
                        )
                    }
                    is ComposeLifeNavigation.FullscreenSettingsList -> {
                        val isDetailPresent = nav.id in listsPairedWithDetails
                        val newEntryValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                            nav = value,
                            windowSizeClass = windowSizeClass,
                            windowSize = windowSize,
                            isDetailPresent = isDetailPresent,
                        )
                        val newEntry = BackstackEntry(
                            value = newEntryValue,
                            previous = nav.previous?.let(::createEntry),
                            id = nav.id,
                        )
                        if (!isDetailPresent && windowSizeClass.windowWidthSizeClass != WindowWidthSizeClass.COMPACT) {
                            map.put(
                                value.transientDetailId,
                                BackstackEntry(
                                    value = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                                        nav = value.transientFullscreenSettingsDetail,
                                        windowSizeClass = windowSizeClass,
                                        windowSize = windowSize,
                                        listDetailInfo = newEntryValue,
                                    ),
                                    previous = newEntry,
                                    id = value.transientDetailId,
                                ),
                            )
                            transformedCurrentEntryId = value.transientDetailId
                        }
                        newEntry
                    }
                    is ComposeLifeNavigation.DeserializationInfo -> BackstackEntry(
                        value = ComposeLifeUiNavigation.DeserializationInfo(
                            nav = value,
                            windowSizeClass = windowSizeClass,
                        ),
                        previous = nav.previous?.let(::createEntry),
                        id = nav.id,
                    )
                }
            }

        // First, generate entries iterating through the current backstack hierarchy with the previous pointers
        generateSequence(currentEntry, BackstackEntry<ComposeLifeNavigation>::previous).forEach(::createEntry)

        // Second, iterate through all of the entries, to generate any missing entries that are not part of the current
        // backstack hierarchy
        entryMap.values.forEach {
            createEntry(it)
        }

        object : BackstackState<ComposeLifeUiNavigation> {
            override val entryMap: BackstackMap<ComposeLifeUiNavigation>
                get() = map
            override val currentEntryId: Uuid
                get() = transformedCurrentEntryId
        }
    }
