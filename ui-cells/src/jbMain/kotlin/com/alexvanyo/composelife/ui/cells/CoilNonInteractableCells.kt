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

package com.alexvanyo.composelife.ui.cells

import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.graphics.Canvas
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.graphics.drawscope.CanvasDrawScope
import androidx.compose.ui.graphics.drawscope.translate
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.LocalLayoutDirection
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.LayoutDirection
import coil3.BitmapImage
import coil3.ImageLoader
import coil3.compose.AsyncImage
import coil3.decode.DataSource
import coil3.fetch.FetchResult
import coil3.fetch.Fetcher
import coil3.fetch.ImageFetchResult
import coil3.request.Options
import com.alexvanyo.composelife.imageloader.di.ImageLoaderProvider
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import me.tatarka.inject.annotations.Inject
import kotlin.math.roundToInt

context(ImageLoaderProvider)
@Suppress("LongParameterList")
@Composable
fun CoilNonInteractableCells(
    gameOfLifeState: GameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: CellWindow,
    shape: CurrentShape,
    pixelOffsetFromCenter: Offset,
    modifier: Modifier = Modifier,
) {
    val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

    val aliveColor = ComposeLifeTheme.aliveCellColor
    val deadColor = ComposeLifeTheme.deadCellColor

    AsyncImage(
        model = CellsCoilModel(
            gameOfLifeState = gameOfLifeState,
            density = LocalDensity.current,
            layoutDirection = LocalLayoutDirection.current,
            aliveColor = aliveColor,
            deadColor = deadColor,
            cellWindow = cellWindow,
            scaledCellPixelSize = scaledCellPixelSize,
            pixelOffsetFromCenter = pixelOffsetFromCenter,
            shape = shape,
        ),
        contentDescription = null,
        imageLoader = imageLoader,
        contentScale = ContentScale.None,
        modifier = modifier,
    )
}

data class CellsCoilModel(
    val gameOfLifeState: GameOfLifeState,
    val density: Density,
    val layoutDirection: LayoutDirection,
    val aliveColor: Color,
    val deadColor: Color,
    val cellWindow: CellWindow,
    val scaledCellPixelSize: Float,
    val pixelOffsetFromCenter: Offset,
    val shape: CurrentShape,
)

class CellsFetcher(
    private val cellsCoilModel: CellsCoilModel,
) : Fetcher {

    override suspend fun fetch(): FetchResult {
        val width = cellsCoilModel.scaledCellPixelSize * cellsCoilModel.cellWindow.width
        val height = cellsCoilModel.scaledCellPixelSize * cellsCoilModel.cellWindow.height
        val imageBitmap = ImageBitmap(width.roundToInt(), height.roundToInt())

        CanvasDrawScope().draw(
            cellsCoilModel.density,
            cellsCoilModel.layoutDirection,
            Canvas(imageBitmap),
            Size(width, height),
        ) {
            translate(
                left = -cellsCoilModel.pixelOffsetFromCenter.x,
                top = -cellsCoilModel.pixelOffsetFromCenter.y,
            ) {
                drawCells(
                    cellsCoilModel.gameOfLifeState,
                    cellsCoilModel.aliveColor,
                    cellsCoilModel.deadColor,
                    cellsCoilModel.cellWindow,
                    cellsCoilModel.scaledCellPixelSize,
                    cellsCoilModel.shape,
                )
            }
        }

        return ImageFetchResult(
            image = imageBitmap.asCoilBitmapImage(),
            isSampled = false,
            dataSource = DataSource.MEMORY,
        )
    }

    @Inject
    class Factory : Fetcher.Factory<CellsCoilModel> {
        override fun create(data: CellsCoilModel, options: Options, imageLoader: ImageLoader): Fetcher =
            CellsFetcher(data)
    }
}

expect fun ImageBitmap.asCoilBitmapImage(): BitmapImage
