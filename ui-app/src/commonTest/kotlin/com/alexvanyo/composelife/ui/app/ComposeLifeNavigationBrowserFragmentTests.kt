/*
 * Copyright 2026 The Android Open Source Project
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

import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackMapSerializer
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.ui.settings.Setting
import com.alexvanyo.composelife.ui.settings.SettingsCategory
import kotlinx.serialization.json.Json
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertNotNull
import kotlin.test.assertNull

class ComposeLifeNavigationBrowserFragmentTests {

    @Test
    fun cell_universe_maps_to_empty_fragment_and_parses_back() {
        val entry = BackstackEntry<ComposeLifeNavigation>(
            value = ComposeLifeNavigation.CellUniverse,
            previous = null,
        )
        assertEquals("", entry.toBrowserFragment())

        val parsed = parseComposeLifeBrowserFragment("")
        assertNotNull(parsed)
        assertEquals(1, parsed.size)
        assertEquals(ComposeLifeNavigation.CellUniverse, parsed.single().value)
    }

    @Test
    fun settings_list_maps_to_settings_fragment_and_parses_back() {
        val root = BackstackEntry<ComposeLifeNavigation>(
            value = ComposeLifeNavigation.CellUniverse,
            previous = null,
        )
        val list = BackstackEntry<ComposeLifeNavigation>(
            value = ComposeLifeNavigation.FullscreenSettingsList(SettingsCategory.Algorithm),
            previous = root,
        )
        assertEquals("settings", list.toBrowserFragment())

        val parsed = parseComposeLifeBrowserFragment("#settings")
        assertNotNull(parsed)
        assertEquals(2, parsed.size)
        assertEquals(ComposeLifeNavigation.CellUniverse, parsed[0].value)
        val listValue = assertIs<ComposeLifeNavigation.FullscreenSettingsList>(parsed[1].value)
        assertEquals(SettingsCategory.Algorithm, listValue.settingsCategory)
    }

    @Test
    fun settings_detail_maps_to_category_fragment_and_parses_back() {
        val root = BackstackEntry<ComposeLifeNavigation>(
            value = ComposeLifeNavigation.CellUniverse,
            previous = null,
        )
        val list = BackstackEntry<ComposeLifeNavigation>(
            value = ComposeLifeNavigation.FullscreenSettingsList(SettingsCategory.Visual),
            previous = root,
        )
        val detail = BackstackEntry<ComposeLifeNavigation>(
            value = ComposeLifeNavigation.FullscreenSettingsDetail(SettingsCategory.Visual, null),
            previous = list,
        )
        assertEquals("settings/visual", detail.toBrowserFragment())

        val parsed = parseComposeLifeBrowserFragment("settings/visual")
        assertNotNull(parsed)
        assertEquals(3, parsed.size)
        assertEquals(ComposeLifeNavigation.CellUniverse, parsed[0].value)
        val listValue = assertIs<ComposeLifeNavigation.FullscreenSettingsList>(parsed[1].value)
        assertEquals(SettingsCategory.Visual, listValue.settingsCategory)
        val detailValue = assertIs<ComposeLifeNavigation.FullscreenSettingsDetail>(parsed[2].value)
        assertEquals(SettingsCategory.Visual, detailValue.settingsCategory)
        assertNull(detailValue.settingToScrollTo)
    }

    @Test
    fun all_settings_categories_round_trip() {
        val categories = listOf(
            SettingsCategory.Algorithm,
            SettingsCategory.Visual,
            SettingsCategory.PatternCollections,
            SettingsCategory.FeatureFlags,
        )
        categories.forEach { category ->
            val root = BackstackEntry<ComposeLifeNavigation>(
                value = ComposeLifeNavigation.CellUniverse,
                previous = null,
            )
            val list = BackstackEntry<ComposeLifeNavigation>(
                value = ComposeLifeNavigation.FullscreenSettingsList(category),
                previous = root,
            )
            val detail = BackstackEntry<ComposeLifeNavigation>(
                value = ComposeLifeNavigation.FullscreenSettingsDetail(category, null),
                previous = list,
            )
            val fragment = detail.toBrowserFragment()
            val parsed = parseComposeLifeBrowserFragment(fragment)
            assertNotNull(parsed)
            val detailValue = assertIs<ComposeLifeNavigation.FullscreenSettingsDetail>(parsed.last().value)
            assertEquals(category, detailValue.settingsCategory)
        }
    }

    @Test
    fun unknown_fragment_returns_null() {
        assertNull(parseComposeLifeBrowserFragment("unknown/route"))
        assertNull(parseComposeLifeBrowserFragment("settings/unknown"))
        assertNull(parseComposeLifeBrowserFragment("deserialization-info"))
    }

    @Test
    fun backstack_map_serialization_round_trips_all_destinations() {
        val serializer = BackstackMapSerializer(ComposeLifeNavigation::surrogate)
        val root = BackstackEntry<ComposeLifeNavigation>(
            value = ComposeLifeNavigation.CellUniverse,
            previous = null,
        )
        val list = BackstackEntry<ComposeLifeNavigation>(
            value = ComposeLifeNavigation.FullscreenSettingsList(SettingsCategory.Algorithm),
            previous = root,
        )
        val detail = BackstackEntry<ComposeLifeNavigation>(
            value = ComposeLifeNavigation.FullscreenSettingsDetail(
                settingsCategory = SettingsCategory.Visual,
                initialSettingToScrollTo = Setting.DarkThemeConfig,
            ),
            previous = list,
        )
        val deserializationInfoUnsuccessful = BackstackEntry<ComposeLifeNavigation>(
            value = ComposeLifeNavigation.DeserializationInfo(
                deserializationResult = DeserializationResult.Unsuccessful(
                    warnings = emptyList(),
                    errors = listOf(ParameterizedString("Invalid pattern")),
                ),
            ),
            previous = root,
        )
        val deserializationInfoSuccessful = BackstackEntry<ComposeLifeNavigation>(
            value = ComposeLifeNavigation.DeserializationInfo(
                deserializationResult = DeserializationResult.Successful(
                    warnings = emptyList(),
                    cellState = """
                        |O.O
                        |.OO
                        |.O.
                    """.toCellState(),
                    format = CellStateFormat.FixedFormat.Plaintext,
                ),
            ),
            previous = root,
        )

        val map = mutableMapOf(
            root.id to root,
            list.id to list,
            detail.id to detail,
            deserializationInfoUnsuccessful.id to deserializationInfoUnsuccessful,
            deserializationInfoSuccessful.id to deserializationInfoSuccessful,
        )

        val encoded = Json.encodeToString(serializer, map)
        val decoded = Json.decodeFromString(serializer, encoded)

        assertEquals(5, decoded.size)
        assertEquals(ComposeLifeNavigation.CellUniverse, decoded.getValue(root.id).value)
        val decodedList = assertIs<ComposeLifeNavigation.FullscreenSettingsList>(decoded.getValue(list.id).value)
        assertEquals(SettingsCategory.Algorithm, decodedList.settingsCategory)
        val decodedDetail = assertIs<ComposeLifeNavigation.FullscreenSettingsDetail>(decoded.getValue(detail.id).value)
        assertEquals(SettingsCategory.Visual, decodedDetail.settingsCategory)
        assertEquals(Setting.DarkThemeConfig, decodedDetail.settingToScrollTo)
        assertIs<ComposeLifeNavigation.DeserializationInfo>(
            decoded.getValue(deserializationInfoUnsuccessful.id).value,
        )
        val decodedSuccessful = assertIs<ComposeLifeNavigation.DeserializationInfo>(
            decoded.getValue(deserializationInfoSuccessful.id).value,
        )
        val result = assertIs<DeserializationResult.Successful>(decodedSuccessful.deserializationResult)
        assertEquals(CellStateFormat.FixedFormat.Plaintext, result.format)
        assertEquals(5, result.cellState.aliveCells.size)
    }
}
