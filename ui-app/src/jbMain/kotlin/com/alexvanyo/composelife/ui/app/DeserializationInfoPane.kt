/*
 * Copyright 2024 The Android Open Source Project
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

import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.ExperimentalLayoutApi
import androidx.compose.foundation.layout.MutableWindowInsets
import androidx.compose.foundation.layout.PaddingValues
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.WindowInsetsSides
import androidx.compose.foundation.layout.asPaddingValues
import androidx.compose.foundation.layout.consumeWindowInsets
import androidx.compose.foundation.layout.exclude
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.onConsumedWindowInsetsChanged
import androidx.compose.foundation.layout.only
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.safeDrawing
import androidx.compose.foundation.lazy.LazyColumn
import androidx.compose.foundation.lazy.LazyItemScope
import androidx.compose.foundation.lazy.LazyListScope
import androidx.compose.foundation.lazy.items
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.automirrored.filled.ArrowBack
import androidx.compose.material.icons.filled.Close
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.PlainTooltip
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.material3.TooltipBox
import androidx.compose.material3.TopAppBar
import androidx.compose.material3.TopAppBarDefaults
import androidx.compose.material3.TopAppBarScrollBehavior
import androidx.compose.material3.rememberTooltipState
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.RectangleShape
import androidx.compose.ui.graphics.vector.ImageVector
import androidx.compose.ui.input.nestedscroll.nestedScroll
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.isSuccessful
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.ui.app.resources.Back
import com.alexvanyo.composelife.ui.app.resources.Close
import com.alexvanyo.composelife.ui.app.resources.DeserializationFailed
import com.alexvanyo.composelife.ui.app.resources.DeserializationSucceeded
import com.alexvanyo.composelife.ui.app.resources.Errors
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.app.resources.Warnings
import com.alexvanyo.composelife.ui.mobile.component.rememberTooltipPositionProvider
import com.alexvanyo.composelife.ui.util.plus

@OptIn(ExperimentalMaterial3Api::class, ExperimentalLayoutApi::class)
@Composable
fun DeserializationInfoPane(
    navEntryValue: ComposeLifeUiNavigation.DeserializationInfo,
    onBackButtonPressed: () -> Unit,
    modifier: Modifier = Modifier,
) {
    val deserializationResult = navEntryValue.nav.deserializationResult

    Surface(
        modifier = modifier
            .then(
                if (navEntryValue.isDialog) {
                    val paddingValues = PaddingValues(vertical = 48.dp)
                    Modifier
                        .padding(paddingValues)
                        .consumeWindowInsets(paddingValues)
                } else {
                    Modifier
                        .fillMaxSize()
                },
            ),
        shape = if (navEntryValue.isDialog) MaterialTheme.shapes.large else RectangleShape,
    ) {
        val scrollBehavior = TopAppBarDefaults.pinnedScrollBehavior()
        Column(Modifier.nestedScroll(scrollBehavior.nestedScrollConnection)) {
            DeserializationInfoTopAppBar(
                isSuccessful = deserializationResult.isSuccessful(),
                isDialog = navEntryValue.isDialog,
                scrollBehavior = scrollBehavior,
                onBackButtonPressed = onBackButtonPressed,
            )

            val consumedWindowInsets = remember { MutableWindowInsets() }

            LazyColumn(
                contentPadding = WindowInsets.safeDrawing
                    .exclude(consumedWindowInsets)
                    .only(WindowInsetsSides.Horizontal + WindowInsetsSides.Bottom)
                    .asPaddingValues() + PaddingValues(start = 16.dp, end = 16.dp, bottom = 16.dp),
                modifier = Modifier.onConsumedWindowInsetsChanged {
                    consumedWindowInsets.insets = it
                },
            ) {
                when (deserializationResult) {
                    is DeserializationResult.Successful -> Unit
                    is DeserializationResult.Unsuccessful -> {
                        if (deserializationResult.errors.isNotEmpty()) {
                            deserializationSection(
                                title = Strings.Errors,
                                messages = deserializationResult.errors,
                            )
                        }
                    }
                }
                if (deserializationResult.warnings.isNotEmpty()) {
                    deserializationSection(
                        title = Strings.Warnings,
                        messages = deserializationResult.warnings,
                    )
                }
            }
        }
    }
}

@Composable
@OptIn(ExperimentalMaterial3Api::class)
fun DeserializationInfoTopAppBar(
    isSuccessful: Boolean,
    isDialog: Boolean,
    scrollBehavior: TopAppBarScrollBehavior,
    onBackButtonPressed: () -> Unit,
    modifier: Modifier = Modifier,
) {
    TopAppBar(
        title = {
            Text(
                parameterizedStringResource(
                    if (isSuccessful) {
                        Strings.DeserializationSucceeded
                    } else {
                        Strings.DeserializationFailed
                    },
                ),
            )
        },
        navigationIcon = {
            val text: ParameterizedString
            val icon: ImageVector

            if (isDialog) {
                text = Strings.Close
                icon = Icons.Default.Close
            } else {
                text = Strings.Back
                icon = Icons.AutoMirrored.Default.ArrowBack
            }

            TooltipBox(
                positionProvider = rememberTooltipPositionProvider(),
                tooltip = {
                    PlainTooltip {
                        Text(parameterizedStringResource(text))
                    }
                },
                state = rememberTooltipState(),
            ) {
                IconButton(
                    onClick = onBackButtonPressed,
                ) {
                    Icon(
                        icon,
                        contentDescription = parameterizedStringResource(text),
                    )
                }
            }
        },
        scrollBehavior = scrollBehavior,
        modifier = modifier,
    )
}

private fun LazyListScope.deserializationSection(
    title: ParameterizedString,
    messages: List<ParameterizedString>,
) {
    item {
        Text(
            text = parameterizedStringResource(title),
            style = MaterialTheme.typography.headlineMedium,
        )
    }
    items(
        items = messages,
    ) { message ->
        DeserializationMessage(message)
    }
}

@Composable
private fun LazyItemScope.DeserializationMessage(
    parameterizedString: ParameterizedString,
) {
    Text(parameterizedStringResource(parameterizedString))
}
