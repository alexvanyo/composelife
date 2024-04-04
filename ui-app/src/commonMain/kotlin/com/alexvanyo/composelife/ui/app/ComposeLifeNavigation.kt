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

import androidx.compose.runtime.Stable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackValueSaverFactory
import com.alexvanyo.composelife.ui.app.action.settings.Setting
import com.alexvanyo.composelife.ui.app.action.settings.SettingsCategory
import com.alexvanyo.composelife.ui.util.sealedEnumSaver
import com.livefront.sealedenum.GenSealedEnum
import java.util.UUID

@Stable
sealed interface ComposeLifeNavigation {
    /**
     * The type of the destination.
     */
    val type: ComposeLifeNavigationType

    data object CellUniverse : ComposeLifeNavigation {

        override val type = Companion

        object Companion : ComposeLifeNavigationType {
            override fun saverFactory(
                previous: BackstackEntry<ComposeLifeNavigation>?,
            ): Saver<CellUniverse, Any> = Saver(
                save = { 0 },
                restore = { CellUniverse },
            )
        }
    }

    class FullscreenSettingsList(
        initialSettingsCategory: SettingsCategory,
    ) : ComposeLifeNavigation {
        /**
         * The currently selected settings category.
         */
        var settingsCategory: SettingsCategory by mutableStateOf(initialSettingsCategory)

        val transientDetailId by derivedStateOf {
            settingsCategory
            UUID.randomUUID()
        }

        val transientFullscreenSettingsDetail by derivedStateOf {
            transientDetailId
            FullscreenSettingsDetail(settingsCategory, null)
        }

        override val type = Companion

        companion object : ComposeLifeNavigationType {
            @Suppress("UnsafeCallOnNullableType")
            override fun saverFactory(
                previous: BackstackEntry<ComposeLifeNavigation>?,
            ): Saver<FullscreenSettingsList, Any> =
                Saver(
                    save = { nav ->
                        with(SettingsCategory.Saver) { save(nav.settingsCategory) }
                    },
                    restore = {
                        FullscreenSettingsList(
                            initialSettingsCategory = SettingsCategory.Saver.restore(it)!!,
                        )
                    },
                )
        }
    }

    class FullscreenSettingsDetail(
        val settingsCategory: SettingsCategory,
        initialSettingToScrollTo: Setting?,
    ) : ComposeLifeNavigation {

        /**
         * If non-null, a [Setting] to scroll to immediately.
         */
        var settingToScrollTo: Setting? by mutableStateOf(initialSettingToScrollTo)
            private set

        /**
         * A callback that [settingToScrollTo] has been scrolled to, and shouldn't be scrolled to again.
         */
        fun onFinishedScrollingToSetting() {
            settingToScrollTo = null
        }

        override val type = Companion

        companion object : ComposeLifeNavigationType {
            @Suppress("UnsafeCallOnNullableType")
            override fun saverFactory(
                previous: BackstackEntry<ComposeLifeNavigation>?,
            ): Saver<FullscreenSettingsDetail, Any> =
                listSaver(
                    save = { nav ->
                        listOf(
                            with(SettingsCategory.Saver) { save(nav.settingsCategory) },
                            nav.settingToScrollTo?.let { with(Setting.Saver) { save(it) } },
                        )
                    },
                    restore = {
                        FullscreenSettingsDetail(
                            settingsCategory = SettingsCategory.Saver.restore(it[0] as Int)!!,
                            initialSettingToScrollTo = (it[1] as Int?)?.let(Setting.Saver::restore),
                        )
                    },
                )
        }
    }

    companion object {
        @Suppress("UnsafeCallOnNullableType")
        val SaverFactory: BackstackValueSaverFactory<ComposeLifeNavigation> = BackstackValueSaverFactory { previous ->
            listSaver(
                save = { composeLifeNavigation ->
                    listOf(
                        with(ComposeLifeNavigationType.Saver) { save(composeLifeNavigation.type) },
                        when (composeLifeNavigation) {
                            is CellUniverse ->
                                with(composeLifeNavigation.type.saverFactory(previous)) {
                                    save(composeLifeNavigation)
                                }

                            is FullscreenSettingsList ->
                                with(composeLifeNavigation.type.saverFactory(previous)) {
                                    save(composeLifeNavigation)
                                }

                            is FullscreenSettingsDetail ->
                                with(composeLifeNavigation.type.saverFactory(previous)) {
                                    save(composeLifeNavigation)
                                }
                        },
                    )
                },
                restore = { list ->
                    val type = ComposeLifeNavigationType.Saver.restore(list[0] as Int)!!
                    type.saverFactory(previous).restore(list[1]!!)
                },
            )
        }
    }
}

/**
 * The type for each [ComposeLifeNavigation].
 *
 * These classes must be objects, since they need to statically be able to save and restore concrete
 * [ComposeLifeNavigation] types.
 */
sealed interface ComposeLifeNavigationType {
    fun saverFactory(previous: BackstackEntry<ComposeLifeNavigation>?): Saver<out ComposeLifeNavigation, Any>

    @GenSealedEnum
    companion object {
        val Saver = sealedEnumSaver(sealedEnum)
    }
}
