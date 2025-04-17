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

import androidx.compose.animation.AnimatedVisibility
import androidx.compose.animation.core.MutableTransitionState
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.text.KeyboardOptions
import androidx.compose.foundation.text.input.TextFieldLineLimits
import androidx.compose.foundation.text.input.TextFieldState
import androidx.compose.foundation.text.input.clearText
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Delete
import androidx.compose.material3.Button
import androidx.compose.material3.Card
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.HorizontalDivider
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.LinearProgressIndicator
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.PlainTooltip
import androidx.compose.material3.Text
import androidx.compose.material3.TextField
import androidx.compose.material3.TooltipBox
import androidx.compose.material3.TooltipDefaults
import androidx.compose.material3.rememberTooltipState
import androidx.compose.runtime.Composable
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.text.input.ImeAction
import androidx.compose.ui.text.input.KeyboardType
import androidx.compose.ui.unit.dp
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
import com.alexvanyo.composelife.ui.settings.resources.AddPatternCollection
import com.alexvanyo.composelife.ui.settings.resources.Delete
import com.alexvanyo.composelife.ui.settings.resources.SourceUrlLabel
import com.alexvanyo.composelife.ui.settings.resources.LastSuccessfulSync
import com.alexvanyo.composelife.ui.settings.resources.LastUnsuccessfulSync
import com.alexvanyo.composelife.ui.settings.resources.Strings
import com.alexvanyo.composelife.ui.settings.resources.DayUnit
import com.alexvanyo.composelife.ui.settings.resources.HourUnit
import com.alexvanyo.composelife.ui.settings.resources.MinuteUnit
import com.alexvanyo.composelife.ui.settings.resources.Never
import com.alexvanyo.composelife.ui.settings.resources.SecondUnit
import com.alexvanyo.composelife.ui.settings.resources.Sources
import com.alexvanyo.composelife.ui.util.AnimatedContent
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.currentTimeZone
import com.alexvanyo.composelife.ui.util.dateComponentInWholeUnits
import com.alexvanyo.composelife.ui.util.progressivePeriodUntil
import com.alexvanyo.composelife.ui.util.timeComponentInWholeUnits
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.launch
import kotlinx.datetime.DateTimeUnit
import kotlin.collections.component1
import kotlin.collections.component2

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
        patternCollectionsState = injectEntryPoint.patternCollectionRepository.collections,
        addPatternCollection = injectEntryPoint.patternCollectionRepository::addPatternCollection,
        deletePatternCollection = injectEntryPoint.patternCollectionRepository::deletePatternCollection,
        modifier = modifier,
    )
}

context(_: ClockProvider)
@OptIn(ExperimentalMaterial3Api::class)
@Composable
fun PatternCollectionsUi(
    patternCollectionsState: ResourceState<List<PatternCollection>>,
    addPatternCollection: suspend (String) -> Unit,
    deletePatternCollection: suspend (PatternCollectionId) -> Unit,
    modifier: Modifier = Modifier,
) {
    val coroutineScope = rememberCoroutineScope()
    Column(modifier = modifier) {
        HorizontalDivider(
            modifier = Modifier.fillMaxWidth(),
            color = MaterialTheme.colorScheme.outline.copy(alpha = 0.5f),
        )

        Text(
            parameterizedStringResource(Strings.Sources),
            style = MaterialTheme.typography.headlineSmall,
            modifier = Modifier.padding(
                top = 8.dp,
                bottom = 12.dp,
            )
        )

        when (patternCollectionsState) {
            is ResourceState.Failure -> {
                // TODO
            }
            ResourceState.Loading -> {
                // TODO
            }
            is ResourceState.Success -> {
                val patternCollections = patternCollectionsState.value.associateBy { it.id }

                /**
                 * The list of previously known animatable pattern collections, used to smoothly animate out upon
                 * removing and in upon appearing.
                 *
                 * These are initialized to be visible, with no appearing animation
                 */
                var previouslyAnimatablePatternCollections by remember {
                    mutableStateOf(
                        patternCollections.keys.associateWith { MutableTransitionState(true) },
                    )
                }

                /**
                 * The list of currently animatable pattern collections. The order of the [Map.plus] is important
                 * here, to preserve any ongoing animation state.
                 */
                val animatablePatternCollections =
                    patternCollections.keys.associateWith {
                        MutableTransitionState(false).apply { targetState = true }
                    } + previouslyAnimatablePatternCollections

                DisposableEffect(animatablePatternCollections, patternCollections) {
                    animatablePatternCollections.forEach { (patternCollectionId, visibleState) ->
                        // Update the target state based on whether the pattern collection should currently be visible
                        visibleState.targetState = patternCollectionId in patternCollections
                    }
                    onDispose {}
                }

                val animatingPatternCollection = animatablePatternCollections

                animatingPatternCollection.forEach { (patternCollectionId, visibleState) ->
                    key(patternCollectionId) {
                        AnimatedVisibility(
                            visibleState = visibleState,
                        ) {
                            PatternCollection(
                                patternCollection = remember {
                                    mutableStateOf(patternCollections.getValue(patternCollectionId))
                                }.apply {
                                    patternCollections[patternCollectionId]?.let { value = it }
                                }.value,
                                onDelete = {
                                    coroutineScope.launch {
                                        deletePatternCollection(patternCollectionId)
                                    }
                                },
                                modifier = Modifier.padding(vertical = 4.dp),
                            )
                        }
                    }
                }

                // Sync all of the known pattern collections back to `previouslyAnimatablePatternCollections`,
                // removing any that have finished disappearing
                LaunchedEffect(animatablePatternCollections) {
                    snapshotFlow {
                        animatablePatternCollections.values.firstOrNull {
                            it.isIdle && !it.targetState
                        }
                    }
                        // Intentionally ignore the pattern collection that has animated out, we're just using it to
                        // trigger updating `previouslyAnimatablePatternCollections` in its entirety.
                        .map {}
                        .onEach {
                            previouslyAnimatablePatternCollections = animatablePatternCollections.filterValues {
                                // Only keep those that are visible, or are currently animating
                                !it.isIdle || it.targetState
                            }
                        }
                        .collect()
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
    Card(
        modifier = modifier,
    ) {
        Box {
            Row(
                verticalAlignment = Alignment.CenterVertically,
                modifier = Modifier.padding(8.dp),
            ) {
                Column(modifier = Modifier.weight(1f)) {
                    Text(patternCollection.sourceUrl)
                    Text(parameterizedStringResource(Strings.LastSuccessfulSync))

                    val lastSuccessfulSynchronizationTimestamp =
                        patternCollection.lastSuccessfulSynchronizationTimestamp
                    if (lastSuccessfulSynchronizationTimestamp == null) {
                        Text(parameterizedStringResource(Strings.Never))
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
                            DateTimeUnit.DAY -> parameterizedStringResource(Strings.DayUnit)
                            DateTimeUnit.HOUR -> parameterizedStringResource(Strings.HourUnit)
                            DateTimeUnit.MINUTE -> parameterizedStringResource(Strings.MinuteUnit)
                            DateTimeUnit.SECOND -> parameterizedStringResource(Strings.SecondUnit)
                            else -> error("Unknown unit")
                        }
                        Text("$amountOfUnit $unitName ago")
                    }

                    AnimatedContent(
                        targetState = TargetState.Single(patternCollection.lastUnsuccessfulSynchronizationTimestamp),
                    ) { lastUnsuccessfulSynchronizationTimestamp ->
                        if (lastUnsuccessfulSynchronizationTimestamp != null) {
                            Column {
                                Text(parameterizedStringResource(Strings.LastUnsuccessfulSync))
                                val (unit, period) = lastUnsuccessfulSynchronizationTimestamp.progressivePeriodUntil(
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
                                val synchronizationFailureMessage = patternCollection.synchronizationFailureMessage
                                if (synchronizationFailureMessage != null) {
                                    Text(synchronizationFailureMessage)
                                }
                            }
                        } else {
                            Spacer(Modifier.fillMaxWidth())
                        }
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
            if (patternCollection.isSynchronizing) {
                LinearProgressIndicator(
                    modifier = Modifier
                        .align(Alignment.BottomCenter)
                        .fillMaxWidth(),
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
            val text = textFieldState.text.toString()
            textFieldState.clearText()
            coroutineScope.launch {
                addPatternCollection(text)
            }
        }

        TextField(
            state = textFieldState,
            label = { Text(parameterizedStringResource(Strings.SourceUrlLabel)) },
            lineLimits = TextFieldLineLimits.SingleLine,
            keyboardOptions = KeyboardOptions(
                keyboardType = KeyboardType.Uri,
                imeAction = ImeAction.Go,
            ),
            onKeyboardAction = { add() },
            modifier = Modifier.fillMaxWidth(),
        )

        Button(
            enabled = textFieldState.text.isNotBlank(),
            onClick = { add() },
        ) {
            Text(parameterizedStringResource(Strings.AddPatternCollection))
        }
    }
}
