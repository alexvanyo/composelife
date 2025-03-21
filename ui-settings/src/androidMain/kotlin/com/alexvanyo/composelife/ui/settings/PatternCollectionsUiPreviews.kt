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

package com.alexvanyo.composelife.ui.settings

import androidx.compose.runtime.Composable
import com.airbnb.android.showkase.annotation.ShowkaseComposable
import com.alexvanyo.composelife.data.model.PatternCollection
import com.alexvanyo.composelife.database.PatternCollectionId
import com.alexvanyo.composelife.ui.settings.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.util.ThemePreviews
import kotlinx.datetime.Clock
import kotlinx.datetime.Instant
import kotlin.time.Duration.Companion.hours
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.seconds

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun PatternCollectionPreviewNoSuccessfulSynchronization() {
    WithPreviewDependencies {
        PatternCollection(
            patternCollection = PatternCollection(
                id = PatternCollectionId(0),
                sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                lastSuccessfulSynchronizationTimestamp = null,
            ),
            onDelete = {},
        )
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun PatternCollectionPreviewSuccessfulSynchronizationNow() {
    val referenceInstant = Instant.fromEpochMilliseconds(1741463473365L)
    WithPreviewDependencies(
        clock = object : Clock {
            override fun now() = referenceInstant
        },
    ) {
        PatternCollection(
            patternCollection = PatternCollection(
                id = PatternCollectionId(0),
                sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                lastSuccessfulSynchronizationTimestamp = referenceInstant,
            ),
            onDelete = {},
        )
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun PatternCollectionPreviewSuccessfulSynchronization55SecondsAgo() {
    val referenceInstant = Instant.fromEpochMilliseconds(1741463473365L)
    WithPreviewDependencies(
        clock = object : Clock {
            override fun now() = referenceInstant
        },
    ) {
        PatternCollection(
            patternCollection = PatternCollection(
                id = PatternCollectionId(0),
                sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                lastSuccessfulSynchronizationTimestamp = referenceInstant - 55.seconds,
            ),
            onDelete = {},
        )
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun PatternCollectionPreviewSuccessfulSynchronization60SecondsAgo() {
    val referenceInstant = Instant.fromEpochMilliseconds(1741463473365L)
    WithPreviewDependencies(
        clock = object : Clock {
            override fun now() = referenceInstant
        },
    ) {
        PatternCollection(
            patternCollection = PatternCollection(
                id = PatternCollectionId(0),
                sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                lastSuccessfulSynchronizationTimestamp = referenceInstant - 60.seconds,
            ),
            onDelete = {},
        )
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun PatternCollectionPreviewSuccessfulSynchronization65SecondsAgo() {
    val referenceInstant = Instant.fromEpochMilliseconds(1741463473365L)
    WithPreviewDependencies(
        clock = object : Clock {
            override fun now() = referenceInstant
        },
    ) {
        PatternCollection(
            patternCollection = PatternCollection(
                id = PatternCollectionId(0),
                sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                lastSuccessfulSynchronizationTimestamp = referenceInstant - 65.seconds,
            ),
            onDelete = {},
        )
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun PatternCollectionPreviewSuccessfulSynchronization65MinutesAgo() {
    val referenceInstant = Instant.fromEpochMilliseconds(1741463473365L)
    WithPreviewDependencies(
        clock = object : Clock {
            override fun now() = referenceInstant
        },
    ) {
        PatternCollection(
            patternCollection = PatternCollection(
                id = PatternCollectionId(0),
                sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                lastSuccessfulSynchronizationTimestamp = referenceInstant - 65.minutes,
            ),
            onDelete = {},
        )
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun PatternCollectionPreviewSuccessfulSynchronization25HoursAgo() {
    val referenceInstant = Instant.fromEpochMilliseconds(1741463473365L)
    WithPreviewDependencies(
        clock = object : Clock {
            override fun now() = referenceInstant
        },
    ) {
        PatternCollection(
            patternCollection = PatternCollection(
                id = PatternCollectionId(0),
                sourceUrl = "https://alex.vanyo.dev/composelife/patterns.zip",
                lastSuccessfulSynchronizationTimestamp = referenceInstant - 25.hours,
            ),
            onDelete = {},
        )
    }
}
