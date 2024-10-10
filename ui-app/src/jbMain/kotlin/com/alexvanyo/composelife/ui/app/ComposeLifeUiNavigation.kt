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
import androidx.window.core.layout.WindowSizeClass
import androidx.window.core.layout.WindowWidthSizeClass
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackMap
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.ui.app.component.DetailEntry
import com.alexvanyo.composelife.ui.app.component.ListDetailInfo
import com.alexvanyo.composelife.ui.app.component.ListEntry
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
        private val isDetailPresent: Boolean,
    ) : ComposeLifeUiNavigation, ListEntry {
        override val isDetailVisible: Boolean
            get() = isDetailPresent || windowSizeClass.windowWidthSizeClass != WindowWidthSizeClass.COMPACT

        override val isListVisible: Boolean
            get() = !isDetailPresent || windowSizeClass.windowWidthSizeClass != WindowWidthSizeClass.COMPACT
    }

    class FullscreenSettingsDetail(
        val nav: ComposeLifeNavigation.FullscreenSettingsDetail,
        listDetailInfo: ListDetailInfo,
    ) : ComposeLifeUiNavigation, DetailEntry, ListDetailInfo by listDetailInfo
}

/**
 * Converts a [BackstackState] of plain [ComposeLifeNavigation] destinations to a [BackstackState] of
 * [ComposeLifeUiNavigation].
 */
@Composable
fun BackstackState<ComposeLifeNavigation>.toComposeLifeUiNavigation(
    windowSizeClass: WindowSizeClass,
): BackstackState<ComposeLifeUiNavigation> =
    remember(entryMap.keys.toSet(), currentEntryId, windowSizeClass) {
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

        fun createEntry(nav: BackstackEntry<ComposeLifeNavigation>): BackstackEntry<ComposeLifeUiNavigation> =
            map.getOrPut(nav.id) {
                when (val value = nav.value) {
                    ComposeLifeNavigation.CellUniverse -> BackstackEntry(
                        ComposeLifeUiNavigation.CellUniverse,
                        nav.previous?.let(::createEntry),
                        nav.id,
                    )
                    is ComposeLifeNavigation.FullscreenSettingsDetail -> {
                        val previous = nav.previous
                        requireNotNull(previous)
                        require(previous.value is ComposeLifeNavigation.FullscreenSettingsList)
                        listsPairedWithDetails.add(previous.id)
                        val listEntry = previous.let(::createEntry)
                        val listNavEntry = listEntry.value as ListDetailInfo
                        BackstackEntry(
                            ComposeLifeUiNavigation.FullscreenSettingsDetail(value, listNavEntry),
                            listEntry,
                            nav.id,
                        )
                    }
                    is ComposeLifeNavigation.FullscreenSettingsList -> {
                        val isDetailPresent = nav.id in listsPairedWithDetails
                        val newEntryValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                            value,
                            windowSizeClass,
                            isDetailPresent,
                        )
                        val newEntry = BackstackEntry(
                            newEntryValue,
                            nav.previous?.let(::createEntry),
                            nav.id,
                        )
                        if (!isDetailPresent && windowSizeClass.windowWidthSizeClass != WindowWidthSizeClass.COMPACT) {
                            map.put(
                                value.transientDetailId,
                                BackstackEntry(
                                    value = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                                        nav = value.transientFullscreenSettingsDetail,
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
