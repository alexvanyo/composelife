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

package com.alexvanyo.composelife.ui.settings

import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.text.KeyboardOptions
import androidx.compose.foundation.text.input.TextFieldLineLimits
import androidx.compose.foundation.text.input.TextFieldState
import androidx.compose.foundation.text.input.clearText
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Delete
import androidx.compose.material3.Button
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.PlainTooltip
import androidx.compose.material3.Text
import androidx.compose.material3.TextField
import androidx.compose.material3.TooltipBox
import androidx.compose.material3.TooltipDefaults
import androidx.compose.material3.rememberTooltipState
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.key
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.text.input.ImeAction
import androidx.compose.ui.text.input.KeyboardType
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.compose.LocalLifecycleOwner
import androidx.lifecycle.repeatOnLifecycle
import com.alexvanyo.composelife.clock.di.ClockProvider
import com.alexvanyo.composelife.data.di.PatternCollectionRepositoryProvider
import com.alexvanyo.composelife.data.model.PatternCollection
import com.alexvanyo.composelife.database.PatternCollectionId
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.settings.resources.Delete
import com.alexvanyo.composelife.ui.settings.resources.Strings
import com.alexvanyo.composelife.ui.util.currentTimeZone
import com.alexvanyo.composelife.ui.util.dateComponentInWholeUnits
import com.alexvanyo.composelife.ui.util.progressivePeriodUntil
import com.alexvanyo.composelife.ui.util.timeComponentInWholeUnits
import kotlinx.coroutines.launch
import kotlinx.datetime.DateTimeUnit

interface PatternCollectionsUiInjectEntryPoint :
    PatternCollectionRepositoryProvider,
    ClockProvider

interface PatternCollectionsUiLocalEntryPoint :
    LoadedComposeLifePreferencesProvider

context(injectEntryPoint: PatternCollectionsUiInjectEntryPoint, _: PatternCollectionsUiLocalEntryPoint)
@Composable
fun PatternCollectionsUi(
    modifier: Modifier = Modifier,
) {
    val lifecycleOwner = LocalLifecycleOwner.current
    LaunchedEffect(lifecycleOwner, injectEntryPoint.patternCollectionRepository) {
        lifecycleOwner.repeatOnLifecycle(Lifecycle.State.STARTED) {
            injectEntryPoint.patternCollectionRepository.observePatternCollections()
        }
    }

    PatternCollectionsUi(
        patternCollections = injectEntryPoint.patternCollectionRepository.collections,
        addPatternCollection = injectEntryPoint.patternCollectionRepository::addPatternCollection,
        deletePatternCollection = injectEntryPoint.patternCollectionRepository::deletePatternCollection,
        modifier = modifier,
    )
}

context(_: ClockProvider)
@OptIn(ExperimentalMaterial3Api::class)
@Composable
fun PatternCollectionsUi(
    patternCollections: ResourceState<List<PatternCollection>>,
    addPatternCollection: suspend (String) -> Unit,
    deletePatternCollection: suspend (PatternCollectionId) -> Unit,
    modifier: Modifier = Modifier,
) {
    val coroutineScope = rememberCoroutineScope()
    Column(modifier = modifier) {
        when (patternCollections) {
            is ResourceState.Failure -> {
                // TODO
            }
            ResourceState.Loading -> {
                // TODO
            }
            is ResourceState.Success -> {
                patternCollections.value.forEach { patternCollection ->
                    key(patternCollection.id) {
                        PatternCollection(
                            patternCollection = patternCollection,
                            onDelete = {
                                coroutineScope.launch {
                                    deletePatternCollection(patternCollection.id)
                                }
                            },
                        )
                    }
                }
            }
        }
        AddPatternCollection(
            addPatternCollection = addPatternCollection,
        )
    }
}

context(clockProvider: ClockProvider)
@OptIn(ExperimentalMaterial3Api::class)
@Composable
fun PatternCollection(
    patternCollection: PatternCollection,
    onDelete: () -> Unit,
    modifier: Modifier = Modifier,
) {
    Row(
        modifier = modifier,
        verticalAlignment = Alignment.CenterVertically,
    ) {
        Column(modifier = Modifier.weight(1f)) {
            Text("Source:")
            Text(patternCollection.sourceUrl)
            Text("Last successful sync:")

            val lastSuccessfulSynchronizationTimestamp = patternCollection.lastSuccessfulSynchronizationTimestamp
            if (lastSuccessfulSynchronizationTimestamp == null) {
                Text("Never")
            } else {
                val (unit, period) = lastSuccessfulSynchronizationTimestamp.progressivePeriodUntil(
                    clock = clockProvider.clock,
                    unitProgression = listOf(
                        DateTimeUnit.DAY,
                        DateTimeUnit.HOUR,
                        DateTimeUnit.MINUTE,
                        DateTimeUnit.SECOND,
                    ),
                    timeZone = currentTimeZone(),
                )
                val amountOfUnit = when (unit) {
                    is DateTimeUnit.DateBased -> period.dateComponentInWholeUnits(unit).toLong()
                    is DateTimeUnit.TimeBased -> period.timeComponentInWholeUnits(unit)
                }
                val unitName = when (unit) {
                    DateTimeUnit.DAY -> "day(s)"
                    DateTimeUnit.HOUR -> "hour(s)"
                    DateTimeUnit.MINUTE -> "minute(s)"
                    DateTimeUnit.SECOND -> "second(s)"
                    else -> error("Unknown unit")
                }
                Text("$amountOfUnit $unitName ago")
            }
        }

        TooltipBox(
            positionProvider = TooltipDefaults.rememberTooltipPositionProvider(),
            tooltip = {
                PlainTooltip {
                    Text(parameterizedStringResource(Strings.Delete))
                }
            },
            state = rememberTooltipState(),
        ) {
            IconButton(
                onClick = onDelete,
            ) {
                Icon(
                    imageVector = Icons.Default.Delete,
                    contentDescription = parameterizedStringResource(Strings.Delete),
                )
            }
        }
    }
}

@Composable
fun AddPatternCollection(
    modifier: Modifier = Modifier,
    addPatternCollection: suspend (String) -> Unit,
) {
    Column(
        modifier = modifier,
        horizontalAlignment = Alignment.CenterHorizontally,
    ) {
        val coroutineScope = rememberCoroutineScope()
        val textFieldState = rememberSaveable(saver = TextFieldState.Saver) { TextFieldState() }

        val add = {
            textFieldState.clearText()
            coroutineScope.launch {
                addPatternCollection(textFieldState.text.toString())
            }
        }

        TextField(
            state = textFieldState,
            label = { Text("Source URL") },
            lineLimits = TextFieldLineLimits.SingleLine,
            keyboardOptions = KeyboardOptions(
                keyboardType = KeyboardType.Uri,
                imeAction = ImeAction.Go,
            ),
            onKeyboardAction = { add() },
            modifier = Modifier.fillMaxWidth(),
        )

        Button(
            onClick = { add() },
        ) {
            Text("Add pattern collection")
        }
    }
}
