/*
 * Copyright 2022 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.runtime.Composable
import com.airbnb.android.showkase.annotation.ShowkaseComposable
import com.alexvanyo.composelife.ui.app.ctxs.PreviewCtx
import com.alexvanyo.composelife.ui.app.ctxs.WithPreviewDependencies
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun GameOfLifeProgressIndicatorBlinkerPreview() {
    WithPreviewDependencies {
        contextOf<PreviewCtx>().testRandom.setSeed(6)
        ComposeLifeTheme {
            with(contextOf<PreviewCtx>().gameOfLifeProgressIndicatorCtx) {
                GameOfLifeProgressIndicator()
            }
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun GameOfLifeProgressIndicatorToadPreview() {
    WithPreviewDependencies {
        contextOf<PreviewCtx>().testRandom.setSeed(2)
        ComposeLifeTheme {
            with(contextOf<PreviewCtx>().gameOfLifeProgressIndicatorCtx) {
                GameOfLifeProgressIndicator()
            }
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun GameOfLifeProgressIndicatorBeaconPreview() {
    WithPreviewDependencies {
        contextOf<PreviewCtx>().testRandom.setSeed(1)
        ComposeLifeTheme {
            with(contextOf<PreviewCtx>().gameOfLifeProgressIndicatorCtx) {
                GameOfLifeProgressIndicator()
            }
        }
    }
}

@ShowkaseComposable
@ThemePreviews
@Composable
internal fun GameOfLifeProgressIndicatorPulsarPreview() {
    WithPreviewDependencies {
        contextOf<PreviewCtx>().testRandom.setSeed(0)
        ComposeLifeTheme {
            with(contextOf<PreviewCtx>().gameOfLifeProgressIndicatorCtx) {
                GameOfLifeProgressIndicator()
            }
        }
    }
}
