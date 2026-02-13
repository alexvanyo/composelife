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

package com.alexvanyo.composelife.ui.util.di

import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.ui.util.ClipboardReaderWriter
import com.alexvanyo.composelife.ui.util.ClipboardReaderWriterImpl
import com.alexvanyo.composelife.ui.util.NonAndroidFakeClipboardReaderWriter
import com.alexvanyo.composelife.ui.util.WebClipboardReader
import com.alexvanyo.composelife.ui.util.WebClipboardWriter
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.Provides

@ContributesTo(
    UiScope::class,
    replaces = [ClipboardReaderWriterImpl::class, WebClipboardReader::class, WebClipboardWriter::class],
)
@BindingContainer
interface WebFakeClipboardReaderWriterBindings {
    companion object {
        @Provides
        fun bindsClipboardReaderWriter(
            nonAndroidFakeClipboardReaderWriter: NonAndroidFakeClipboardReaderWriter,
        ): ClipboardReaderWriter = nonAndroidFakeClipboardReaderWriter
    }
}
