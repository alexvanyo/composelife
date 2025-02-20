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

import androidx.compose.foundation.layout.requiredSize
import androidx.compose.runtime.Composable
import androidx.compose.runtime.MutableState
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshots.SnapshotStateMap
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.graphics.Canvas
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.graphics.drawscope.CanvasDrawScope
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.layout.ContentScale
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.LocalLayoutDirection
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.LayoutDirection
import coil3.BitmapImage
import coil3.ImageLoader
import coil3.compose.AsyncImage
import coil3.compose.AsyncImagePainter
import coil3.compose.LocalPlatformContext
import coil3.decode.DataSource
import coil3.fetch.FetchResult
import coil3.fetch.Fetcher
import coil3.fetch.ImageFetchResult
import coil3.key.Keyer
import coil3.memory.MemoryCache
import coil3.request.ImageRequest
import coil3.request.Options
import coil3.size.Scale
import com.alexvanyo.composelife.imageloader.di.ImageLoaderProvider
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import me.tatarka.inject.annotations.Inject
import kotlin.math.roundToInt

context(imageLoaderProvider: ImageLoaderProvider)
@Suppress("LongParameterList", "LongMethod")
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

    val model = CellsCoilModel(
        cellState = gameOfLifeState.cellState,
        density = LocalDensity.current,
        layoutDirection = LocalLayoutDirection.current,
        aliveColor = aliveColor,
        deadColor = deadColor,
        cellWindow = cellWindow,
        scaledCellPixelSize = scaledCellPixelSize,
        shape = shape,
    )

    var state: AsyncImagePainter.State by remember { mutableStateOf(AsyncImagePainter.State.Empty) }
    var previousCacheKey: MemoryCache.Key? by remember { mutableStateOf(null) }
    val previousPixelOffsetsFromCenter: MutableMap<String, MutableState<Offset>> =
        remember<SnapshotStateMap<String, MutableState<Offset>>> { mutableStateMapOf() }
            .apply {
                get(model.cacheKey())?.value = pixelOffsetFromCenter
            }

    AsyncImage(
        model = ImageRequest.Builder(LocalPlatformContext.current)
            .data(model)
            .size(coil3.size.Size.ORIGINAL)
            .scale(Scale.FILL)
            .placeholderMemoryCacheKey(previousCacheKey)
            .build(),
        contentDescription = null,
        imageLoader = imageLoaderProvider.imageLoader,
        contentScale = ContentScale.None,
        onState = {
            state = it
            when (it) {
                AsyncImagePainter.State.Empty,
                is AsyncImagePainter.State.Loading,
                -> Unit
                is AsyncImagePainter.State.Error -> {
                    previousCacheKey = null
                    previousPixelOffsetsFromCenter.clear()
                }
                is AsyncImagePainter.State.Success -> {
                    val memoryCacheKey = it.result.memoryCacheKey
                    previousCacheKey = memoryCacheKey
                    previousPixelOffsetsFromCenter.clear()
                    if (memoryCacheKey != null) {
                        @Suppress("ComposeRememberMissing")
                        previousPixelOffsetsFromCenter[memoryCacheKey.key] =
                            mutableStateOf(pixelOffsetFromCenter)
                    }
                }
            }
        },
        modifier = modifier
            .graphicsLayer {
                when (state) {
                    AsyncImagePainter.State.Empty -> Unit
                    is AsyncImagePainter.State.Error -> Unit
                    is AsyncImagePainter.State.Loading -> {
                        previousCacheKey?.key?.let(previousPixelOffsetsFromCenter::get)?.let {
                            translationX = -it.value.x
                            translationY = -it.value.y
                        }
                    }
                    is AsyncImagePainter.State.Success -> {
                        translationX = -pixelOffsetFromCenter.x
                        translationY = -pixelOffsetFromCenter.y
                    }
                }
            }
            .requiredSize(
                scaledCellDpSize * cellWindow.width,
                scaledCellDpSize * cellWindow.height,
            ),
    )
}

data class CellsCoilModel(
    val cellState: CellState,
    val density: Density,
    val layoutDirection: LayoutDirection,
    val aliveColor: Color,
    val deadColor: Color,
    val cellWindow: CellWindow,
    val scaledCellPixelSize: Float,
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
            drawCells(
                cellsCoilModel.cellState,
                cellsCoilModel.aliveColor,
                cellsCoilModel.deadColor,
                cellsCoilModel.cellWindow,
                cellsCoilModel.scaledCellPixelSize,
                cellsCoilModel.shape,
            )
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

fun CellsCoilModel.cacheKey(): String =
    "com.alexvanyo.composelife.CellsCoilModel(" +
        "cellState: $cellState, " +
        "density: ${density.density}, " +
        "layoutDirection: $layoutDirection, " +
        "aliveColor: $aliveColor, " +
        "deadColor: $deadColor, " +
        "cellWindow: $cellWindow, " +
        "scaledCellPixelSize: $scaledCellPixelSize, " +
        "shape: $shape)"

@Inject
class CellsKeyer : Keyer<CellsCoilModel> {
    override fun key(data: CellsCoilModel, options: Options): String =
        data.cacheKey()
}

expect fun ImageBitmap.asCoilBitmapImage(): BitmapImage
