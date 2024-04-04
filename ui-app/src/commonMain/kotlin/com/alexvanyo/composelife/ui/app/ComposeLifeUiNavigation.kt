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

import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.material3.windowsizeclass.WindowWidthSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.runtime.Stable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackMap
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.BackstackValueSaverFactory
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.ui.app.action.settings.Setting
import com.alexvanyo.composelife.ui.app.action.settings.SettingsCategory
import com.alexvanyo.composelife.ui.util.DetailMarker
import com.alexvanyo.composelife.ui.util.ListDetailInfo
import com.alexvanyo.composelife.ui.util.ListMarker
import com.alexvanyo.composelife.ui.util.sealedEnumSaver
import com.livefront.sealedenum.GenSealedEnum
import java.util.UUID

@Stable
sealed interface ComposeLifeUiNavigation {

    data object CellUniverse : ComposeLifeUiNavigation

    class FullscreenSettingsList(
        val nav: ComposeLifeNavigation.FullscreenSettingsList,
        val windowSizeClass: WindowSizeClass,
        private val isDetailPresent: Boolean,
    ) : ComposeLifeUiNavigation, ListMarker {
        override val isDetailVisible: Boolean
            get() = isDetailPresent || windowSizeClass.widthSizeClass >= WindowWidthSizeClass.Medium

        override val isListVisible: Boolean
            get() = !isDetailPresent || windowSizeClass.widthSizeClass >= WindowWidthSizeClass.Medium
    }

    class FullscreenSettingsDetail(
        val nav: ComposeLifeNavigation.FullscreenSettingsDetail,
        listDetailInfo: ListDetailInfo,
    ) : ComposeLifeUiNavigation, DetailMarker, ListDetailInfo by listDetailInfo
}

@Composable
fun BackstackState<ComposeLifeNavigation>.toComposeLifeUiNavigation(
    windowSizeClass: WindowSizeClass,
): BackstackState<ComposeLifeUiNavigation> =
    remember(entryMap.keys.toSet(), currentEntryId, windowSizeClass) {
        val map = mutableMapOf<UUID, BackstackEntry<ComposeLifeUiNavigation>>()

        val listsPairedWithDetails = mutableSetOf<UUID>()

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
                            isDetailPresent
                        ).also { println("vanyo: isDetailPresent $isDetailPresent") }
                        val newEntry = BackstackEntry(
                            newEntryValue,
                            nav.previous?.let(::createEntry),
                            nav.id,
                        )
                        if (!isDetailPresent) {
                            map.put(
                                value.transientDetailId,
                                BackstackEntry(
                                    value = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                                        nav = value.transientFullscreenSettingsDetail,
                                        listDetailInfo = newEntryValue,
                                    ),
                                    previous = newEntry,
                                    id = value.transientDetailId,
                                )
                            )
                            transformedCurrentEntryId = value.transientDetailId
                        }
                        newEntry
                    }
                }
            }

        generateSequence(currentEntry, BackstackEntry<ComposeLifeNavigation>::previous).forEach(::createEntry)

        entryMap.values.forEach {
            createEntry(it)
        }

        object : BackstackState<ComposeLifeUiNavigation> {
            override val entryMap: BackstackMap<ComposeLifeUiNavigation>
                get() = map
            override val currentEntryId: UUID
                get() = transformedCurrentEntryId

        }
    }
