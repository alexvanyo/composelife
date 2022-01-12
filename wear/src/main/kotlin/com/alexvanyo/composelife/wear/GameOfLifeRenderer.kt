package com.alexvanyo.composelife.wear

import android.content.Context
import android.graphics.Rect
import android.text.format.DateFormat
import android.view.SurfaceHolder
import androidx.compose.runtime.snapshots.Snapshot
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.graphics.Canvas
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.drawscope.CanvasDrawScope
import androidx.compose.ui.graphics.toComposeRect
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.LayoutDirection
import androidx.compose.ui.unit.toOffset
import androidx.wear.watchface.CanvasType
import androidx.wear.watchface.Renderer
import androidx.wear.watchface.WatchState
import androidx.wear.watchface.style.CurrentUserStyleRepository
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.model.emptyCellState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.util.containedPoints
import java.time.LocalTime
import java.time.ZonedDateTime
import kotlin.random.Random

class GameOfLifeRenderer(
    context: Context,
    surfaceHolder: SurfaceHolder,
    currentUserStyleRepository: CurrentUserStyleRepository,
    private val watchState: WatchState,
    private val temporalGameOfLifeState: TemporalGameOfLifeState
) : Renderer.CanvasRenderer(
    surfaceHolder = surfaceHolder,
    currentUserStyleRepository = currentUserStyleRepository,
    watchState = watchState,
    canvasType = CanvasType.HARDWARE,
    interactiveDrawModeUpdateDelayMillis = 200L
) {
    private val density = Density(context = context)

    private val cellWindow = IntRect(IntOffset(0, 0), IntSize(99, 99))

    private val use24HourFormat = DateFormat.is24HourFormat(context)

    private var previousLocalTime = LocalTime.MIN

    override fun render(canvas: android.graphics.Canvas, bounds: Rect, zonedDateTime: ZonedDateTime) {
        val previousSeedCellState = temporalGameOfLifeState.seedCellState

        val localTime = zonedDateTime.toLocalTime()

        if (previousLocalTime.hour != localTime.hour || previousLocalTime.minute != localTime.minute) {
            temporalGameOfLifeState.cellState = createTimeCellState(createTimeDigits(localTime, use24HourFormat))
        }

        val cellSize = bounds.width().toFloat() / cellWindow.width

        Snapshot.sendApplyNotifications()

        val cellState = temporalGameOfLifeState.cellState

        CanvasDrawScope().draw(density, LayoutDirection.Ltr, Canvas(c = canvas), bounds.toComposeRect().size) {
            drawRect(color = Color.Black)

            cellWindow.containedPoints().intersect(cellState.aliveCells).forEach { cell ->
                val windowOffset = (cell - cellWindow.topLeft).toOffset() * cellSize

                drawRect(
                    color = Color.White,
                    topLeft = windowOffset,
                    size = Size(cellSize, cellSize)
                )
            }
        }

        if (zonedDateTime.toEpochSecond() * 1000 == watchState.digitalPreviewReferenceTimeMillis) {
            temporalGameOfLifeState.cellState = previousSeedCellState
        } else {
            previousLocalTime = localTime
        }
    }

    override fun renderHighlightLayer(canvas: android.graphics.Canvas, bounds: Rect, zonedDateTime: ZonedDateTime) {
        // TODO
    }
}

private fun createTimeCellState(timeDigits: TimeDigits): CellState {
    val timeCellState = timeDigits.firstDigit.cellState
        .union(timeDigits.secondDigit.cellState.offsetBy(IntOffset(19, 0)))
        .union(timeDigits.thirdDigit.cellState.offsetBy(IntOffset(40, 0)))
        .union(timeDigits.fourthDigit.cellState.offsetBy(IntOffset(59, 0)))
        .union(
            """
                |XX
                |XX
                |
                |
                |XX
                |XX
            """.toCellState(IntOffset(35, 9))
        )
        .offsetBy(IntOffset(14, 38))

    val randomPoints = CellState(
        randomPointPool.filter { Random.nextFloat() < 0.2 }.toSet()
    )

    return timeCellState.union(randomPoints)
}

val randomPointPool =
    IntRect(
        IntOffset(20, 10),
        IntOffset(80, 25)
    )
        .containedPoints()
        .union(
            IntRect(
                IntOffset(20, 75),
                IntOffset(80, 90)
            )
                .containedPoints()
        )

fun createTimeDigits(localTime: LocalTime, use24HourFormat: Boolean): TimeDigits {
    val clockHour = localTime.hour.rem(12)
    val displayHour = if (use24HourFormat) {
        localTime.hour
    } else if (clockHour == 0) {
        12
    } else {
        clockHour
    }

    val hourTensPlace = displayHour / 10
    val firstDigit = if (hourTensPlace == 0 && !use24HourFormat) {
        GameOfLifeSegmentChar.Blank
    } else {
        GameOfLifeSegmentChar.fromChar(hourTensPlace)
    }
    val secondDigit = GameOfLifeSegmentChar.fromChar(displayHour.rem(10))
    val thirdDigit = GameOfLifeSegmentChar.fromChar(localTime.minute / 10)
    val fourthDigit = GameOfLifeSegmentChar.fromChar(localTime.minute.rem(10))

    return TimeDigits(
        firstDigit = firstDigit,
        secondDigit = secondDigit,
        thirdDigit = thirdDigit,
        fourthDigit = fourthDigit
    )
}

data class TimeDigits(
    val firstDigit: GameOfLifeSegmentChar,
    val secondDigit: GameOfLifeSegmentChar,
    val thirdDigit: GameOfLifeSegmentChar,
    val fourthDigit: GameOfLifeSegmentChar,
)

sealed class GameOfLifeSegmentChar(
    val cellState: CellState
) {
    object Zero : GameOfLifeSegmentChar(segA.union(segB).union(segC).union(segD).union(segE).union(segF))
    object One : GameOfLifeSegmentChar(segB.union(segC))
    object Two : GameOfLifeSegmentChar(segA.union(segB).union(segD).union(segE).union(segG))
    object Three : GameOfLifeSegmentChar(segA.union(segB).union(segC).union(segD).union(segG))
    object Four : GameOfLifeSegmentChar(segB.union(segC).union(segF).union(segG))
    object Five : GameOfLifeSegmentChar(segA.union(segC).union(segD).union(segF).union(segG))
    object Six : GameOfLifeSegmentChar(segA.union(segC).union(segD).union(segE).union(segF).union(segG))
    object Seven : GameOfLifeSegmentChar(segA.union(segB).union(segC))
    object Eight : GameOfLifeSegmentChar(segA.union(segB).union(segC).union(segD).union(segE).union(segF).union(segG))
    object Nine : GameOfLifeSegmentChar(segA.union(segB).union(segC).union(segD).union(segF).union(segG))
    object Blank : GameOfLifeSegmentChar(emptyCellState())

    companion object {
        fun fromChar(digit: Int): GameOfLifeSegmentChar {
            return when (digit) {
                0 -> Zero
                1 -> One
                2 -> Two
                3 -> Three
                4 -> Four
                5 -> Five
                6 -> Six
                7 -> Seven
                8 -> Eight
                9 -> Nine
                else -> throw IllegalArgumentException("input wasn't a digit!")
            }
        }
    }
}

private val segA = """
    |XX  XX XX  XX
    |XX  XX XX  XX
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
""".toCellState()

private val segB = """
    |           XX
    |           XX
    |
    |
    |           XX
    |           XX
    |
    |           XX
    |           XX
    |
    |
    |           XX
    |           XX
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
""".toCellState()

private val segC = """
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |           XX
    |           XX
    |
    |
    |           XX
    |           XX
    |
    |           XX
    |           XX
    |
    |
    |           XX
    |           XX
""".toCellState()

private val segD = """
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |XX  XX XX  XX
    |XX  XX XX  XX
""".toCellState()

private val segE = """
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |XX
    |XX
    |
    |
    |XX
    |XX
    |
    |XX
    |XX
    |
    |
    |XX
    |XX
""".toCellState()

private val segF = """
    |XX
    |XX
    |
    |
    |XX
    |XX
    |
    |XX
    |XX
    |
    |
    |XX
    |XX
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
""".toCellState()

private val segG = """
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |XX  XX XX  XX
    |XX  XX XX  XX
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
    |
""".toCellState()
