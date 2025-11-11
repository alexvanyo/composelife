/*
 * Copyright 2025 The Android Open Source Project
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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.scopes

import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.Provides
import kotlinx.browser.document
import kotlinx.browser.localStorage
import kotlinx.browser.sessionStorage
import kotlinx.browser.window
import org.w3c.dom.Document
import org.w3c.dom.Navigator
import org.w3c.dom.Storage
import org.w3c.dom.Window

@ContributesTo(AppScope::class)
@BindingContainer
interface WebApplicationBindings {

    companion object {
        @Provides
        internal fun bindDocument(): Document = document

        @Provides
        internal fun bindWindow(): Window = window

        @Provides
        internal fun bindNavigator(window: Window): Navigator = window.navigator

        @Provides
        @LocalStorage
        internal fun bindLocalStorage(): Storage = localStorage

        @Provides
        @SessionStorage
        internal fun bindSessionStorage(): Storage = sessionStorage
    }
}
