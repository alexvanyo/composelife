package com.alexvanyo.composelife.ui

import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.padding
import androidx.compose.material3.Button
import androidx.compose.material3.CircularProgressIndicator
import androidx.compose.material3.DropdownMenu
import androidx.compose.material3.DropdownMenuItem
import androidx.compose.material3.Slider
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import androidx.hilt.navigation.compose.hiltViewModel
import com.alexvanyo.composelife.R
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.entrypoints.ComposeLifePreferencesEntryPoint
import kotlinx.coroutines.launch

@Suppress("LongMethod")
@Composable
fun PaletteScreen() {
    var retryCount by remember { mutableStateOf(0) }

    val preferences = hiltViewModel<ComposeLifePreferencesEntryPoint>().composeLifePreferences

    val currentShapeState = preferences.currentShapeState

    Column(
        modifier = Modifier.padding(horizontal = 16.dp)
    ) {
        when (currentShapeState) {
            ResourceState.Loading -> {
                CircularProgressIndicator()
            }
            is ResourceState.Failure -> {
                Button(onClick = { retryCount++ }) {
                    Text(text = stringResource(id = R.string.retry))
                }
            }
            is ResourceState.Success -> {
                val currentShape = currentShapeState.value
                val coroutineScope = rememberCoroutineScope()

                var isShowingDropdownMenu by remember { mutableStateOf(false) }

                Box(
                    modifier = Modifier
                        .fillMaxWidth()
                        .clickable {
                            isShowingDropdownMenu = true
                        }
                ) {
                    Text(
                        text = stringResource(
                            id = when (currentShape) {
                                is CurrentShape.RoundRectangle -> R.string.round_rectangle
                            }
                        )
                    )

                    DropdownMenu(
                        expanded = isShowingDropdownMenu,
                        onDismissRequest = { isShowingDropdownMenu = false }
                    ) {
                        DropdownMenuItem(
                            text = { Text(stringResource(id = R.string.round_rectangle)) },
                            onClick = {
                                coroutineScope.launch {
                                    preferences.setCurrentShapeType(CurrentShapeType.RoundRectangle)
                                    isShowingDropdownMenu = false
                                }
                            }
                        )
                    }
                }

                when (currentShape) {
                    is CurrentShape.RoundRectangle -> {
                        var sizeFraction by remember { mutableStateOf(currentShape.sizeFraction) }
                        var cornerFraction by remember { mutableStateOf(currentShape.cornerFraction) }

                        LaunchedEffect(sizeFraction, cornerFraction) {
                            preferences.setRoundRectangleConfig { roundRectangle ->
                                roundRectangle.copy(
                                    sizeFraction = sizeFraction,
                                    cornerFraction = cornerFraction
                                )
                            }
                        }

                        Slider(
                            value = sizeFraction,
                            valueRange = 0.1f..1f,
                            onValueChange = { sizeFraction = it },
                        )

                        Slider(
                            value = cornerFraction,
                            valueRange = 0f..0.5f,
                            onValueChange = { cornerFraction = it },
                        )
                    }
                }
            }
        }
    }
}
