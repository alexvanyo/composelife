/*
 * Copyright 2023 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.alexvanyo.composelife.ui.util

import androidx.compose.foundation.MutatePriority
import androidx.compose.foundation.MutatorMutex
import androidx.compose.foundation.gestures.awaitFirstDown
import androidx.compose.foundation.gestures.drag
import androidx.compose.foundation.interaction.DragInteraction
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.input.pointer.AwaitPointerEventScope
import androidx.compose.ui.input.pointer.PointerEvent
import androidx.compose.ui.input.pointer.PointerEventPass
import androidx.compose.ui.input.pointer.PointerId
import androidx.compose.ui.input.pointer.PointerInputChange
import androidx.compose.ui.input.pointer.PointerType
import androidx.compose.ui.input.pointer.SuspendingPointerInputModifierNode
import androidx.compose.ui.input.pointer.changedToUpIgnoreConsumed
import androidx.compose.ui.input.pointer.positionChange
import androidx.compose.ui.input.pointer.positionChangeIgnoreConsumed
import androidx.compose.ui.input.pointer.util.VelocityTracker
import androidx.compose.ui.input.pointer.util.addPointerInputChange
import androidx.compose.ui.node.CompositionLocalConsumerModifierNode
import androidx.compose.ui.node.DelegatingNode
import androidx.compose.ui.node.ModifierNodeElement
import androidx.compose.ui.node.PointerInputModifierNode
import androidx.compose.ui.node.currentValueOf
import androidx.compose.ui.platform.InspectorInfo
import androidx.compose.ui.platform.LocalViewConfiguration
import androidx.compose.ui.platform.ViewConfiguration
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.Velocity
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.util.DragEvent.DragCancelled
import com.alexvanyo.composelife.ui.util.DragEvent.DragDelta
import com.alexvanyo.composelife.ui.util.DragEvent.DragStarted
import com.alexvanyo.composelife.ui.util.DragEvent.DragStopped
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.channels.SendChannel
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.isActive
import kotlinx.coroutines.launch
import kotlin.math.sign

/**
 * State of Draggable2D. Allows for granular control of how deltas are consumed by the user as well
 * as to write custom drag methods using [drag] suspend function.
 */
interface Draggable2DState {
    /**
     * Call this function to take control of drag logic.
     *
     * All actions that change the logical drag position must be performed within a [drag]
     * block (even if they don't call any other methods on this object) in order to guarantee
     * that mutual exclusion is enforced.
     *
     * If [drag] is called from elsewhere with the [dragPriority] higher or equal to ongoing
     * drag, ongoing drag will be canceled.
     *
     * @param dragPriority of the drag operation
     * @param block to perform drag in
     */
    suspend fun drag(
        dragPriority: MutatePriority = MutatePriority.Default,
        block: suspend Drag2DScope.() -> Unit
    )

    /**
     * Dispatch drag delta in pixels avoiding all drag related priority mechanisms.
     *
     * **Note:** unlike [drag], dispatching any delta with this method will bypass scrolling of
     * any priority. This method will also ignore `reverseDirection` and other parameters set in
     * draggable2D.
     *
     * This method is used internally for low level operations, allowing implementers of
     * [Draggable2DState] influence the consumption as suits them.
     * Manually dispatching delta via this method will likely result in a bad user experience,
     * you must prefer [drag] method over this one.
     *
     * @param delta amount of scroll dispatched in the nested drag process
     */
    fun dispatchRawDelta(delta: Offset)
}

/**
 * Scope used for suspending drag blocks
 */
interface Drag2DScope {
    /**
     * Attempts to drag by [pixels] px.
     */
    fun dragBy(pixels: Offset)
}

/**
 * Default implementation of [Draggable2DState] interface that allows to pass a simple action that
 * will be invoked when the drag occurs.
 *
 * This is the simplest way to set up a draggable2D modifier. When constructing this
 * [Draggable2DState], you must provide a [onDelta] lambda, which will be invoked whenever
 * drag happens (by gesture input or a custom [Draggable2DState.drag] call) with the delta in
 * pixels.
 *
 * If you are creating [Draggable2DState] in composition, consider using [rememberDraggable2DState].
 *
 * @param onDelta callback invoked when drag occurs. The callback receives the delta in pixels.
 */
@Suppress("PrimitiveInLambda")
fun Draggable2DState(onDelta: (Offset) -> Unit): Draggable2DState =
    DefaultDraggable2DState(onDelta)

/**
 * Create and remember default implementation of [Draggable2DState] interface that allows to pass a
 * simple action that will be invoked when the drag occurs.
 *
 * This is the simplest way to set up a [draggable] modifier. When constructing this
 * [Draggable2DState], you must provide a [onDelta] lambda, which will be invoked whenever
 * drag happens (by gesture input or a custom [Draggable2DState.drag] call) with the delta in
 * pixels.
 *
 * @param onDelta callback invoked when drag occurs. The callback receives the delta in pixels.
 */
@Suppress("PrimitiveInLambda")
@Composable
fun rememberDraggable2DState(onDelta: (Offset) -> Unit): Draggable2DState {
    val onDeltaState = rememberUpdatedState(onDelta)
    return remember { Draggable2DState { onDeltaState.value.invoke(it) } }
}

/**
 * Configure touch dragging for the UI element in both orientations. The drag distance
 * reported to [Draggable2DState], allowing users to react to the drag delta and update their state.
 *
 * The common common usecase for this component is when you need to be able to drag something
 * inside the component on the screen and represent this state via one float value
 *
 * If you are implementing dragging in a single orientation, consider using [draggable].
 *
 * @param state [Draggable2DState] state of the draggable2D. Defines how drag events will be
 * interpreted by the user land logic.
 * @param enabled whether or not drag is enabled
 * @param interactionSource [MutableInteractionSource] that will be used to emit
 * [DragInteraction.Start] when this draggable is being dragged.
 * @param startDragImmediately when set to true, draggable2D will start dragging immediately and
 * prevent other gesture detectors from reacting to "down" events (in order to block composed
 * press-based gestures). This is intended to allow end users to "catch" an animating widget by
 * pressing on it. It's useful to set it when value you're dragging is settling / animating.
 * @param onDragStarted callback that will be invoked when drag is about to start at the starting
 * position, allowing user to suspend and perform preparation for drag, if desired.This suspend
 * function is invoked with the draggable2D scope, allowing for async processing, if desired. Note
 * that the scope used here is the onw provided by the draggable2D node, for long running work that
 * needs to outlast the modifier being in the composition you should use a scope that fits the
 * lifecycle needed.
 * @param onDragStopped callback that will be invoked when drag is finished, allowing the
 * user to react on velocity and process it. This suspend function is invoked with the draggable2D
 * scope, allowing for async processing, if desired. Note that the scope used here is the onw
 * provided by the draggable2D scope, for long running work that needs to outlast the modifier being
 * in the composition you should use a scope that fits the lifecycle needed.
 * @param reverseDirection reverse the direction of the scroll, so top to bottom scroll will
 * behave like bottom to top and left to right will behave like right to left.
 */
@Suppress("PrimitiveInLambda")
fun Modifier.draggable2D(
    state: Draggable2DState,
    enabled: Boolean = true,
    interactionSource: MutableInteractionSource? = null,
    startDragImmediately: Boolean = false,
    onDragStarted: suspend CoroutineScope.(startedPosition: Offset) -> Unit = {},
    onDragStopped: suspend CoroutineScope.(velocity: Velocity) -> Unit = {},
    reverseDirection: Boolean = false
): Modifier = this then Draggable2DElement(
    state = state,
    enabled = enabled,
    interactionSource = interactionSource,
    startDragImmediately = { startDragImmediately },
    onDragStarted = onDragStarted,
    onDragStopped = onDragStopped,
    reverseDirection = reverseDirection,
    canDrag = { true }
)

@Suppress("PrimitiveInLambda")
private class Draggable2DElement(
    private val state: Draggable2DState,
    private val canDrag: (PointerInputChange) -> Boolean,
    private val enabled: Boolean,
    private val interactionSource: MutableInteractionSource?,
    private val startDragImmediately: () -> Boolean,
    private val onDragStarted: suspend CoroutineScope.(startedPosition: Offset) -> Unit,
    private val onDragStopped: suspend CoroutineScope.(velocity: Velocity) -> Unit,
    private val reverseDirection: Boolean,
) : ModifierNodeElement<Draggable2DNode>() {
    override fun create(): Draggable2DNode = Draggable2DNode(
        state,
        canDrag,
        enabled,
        interactionSource,
        startDragImmediately,
        onDragStarted,
        onDragStopped,
        reverseDirection
    )

    override fun update(node: Draggable2DNode) {
        node.update(
            state,
            canDrag,
            enabled,
            interactionSource,
            startDragImmediately,
            onDragStarted,
            onDragStopped,
            reverseDirection
        )
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other === null) return false
        if (this::class != other::class) return false

        other as Draggable2DElement

        if (state != other.state) return false
        if (canDrag != other.canDrag) return false
        if (enabled != other.enabled) return false
        if (interactionSource != other.interactionSource) return false
        if (startDragImmediately != other.startDragImmediately) return false
        if (onDragStarted != other.onDragStarted) return false
        if (onDragStopped != other.onDragStopped) return false
        if (reverseDirection != other.reverseDirection) return false

        return true
    }

    override fun hashCode(): Int {
        var result = state.hashCode()
        result = 31 * result + canDrag.hashCode()
        result = 31 * result + enabled.hashCode()
        result = 31 * result + (interactionSource?.hashCode() ?: 0)
        result = 31 * result + startDragImmediately.hashCode()
        result = 31 * result + onDragStarted.hashCode()
        result = 31 * result + onDragStopped.hashCode()
        result = 31 * result + reverseDirection.hashCode()
        return result
    }

    override fun InspectorInfo.inspectableProperties() {
        name = "draggable2D"
        properties["canDrag"] = canDrag
        properties["enabled"] = enabled
        properties["interactionSource"] = interactionSource
        properties["startDragImmediately"] = startDragImmediately
        properties["onDragStarted"] = onDragStarted
        properties["onDragStopped"] = onDragStopped
        properties["reverseDirection"] = reverseDirection
        properties["state"] = state
    }
}

@Suppress("PrimitiveInLambda")
private class Draggable2DNode(
    private var state: Draggable2DState,
    canDrag: (PointerInputChange) -> Boolean,
    enabled: Boolean,
    interactionSource: MutableInteractionSource?,
    startDragImmediately: () -> Boolean,
    onDragStarted: suspend CoroutineScope.(startedPosition: Offset) -> Unit,
    onDragStopped: suspend CoroutineScope.(velocity: Velocity) -> Unit,
    reverseDirection: Boolean
) : AbstractDraggableNode(
    canDrag,
    enabled,
    interactionSource,
    startDragImmediately,
    onDragStarted,
    onDragStopped,
    reverseDirection
) {
    var drag2DScope: Drag2DScope = NoOpDrag2DScope

    private val abstractDragScope = object : AbstractDragScope {
        override fun dragBy(pixels: Offset) {
            drag2DScope.dragBy(pixels)
        }
    }

    override suspend fun drag(block: suspend AbstractDragScope.() -> Unit) {
        state.drag(MutatePriority.UserInput) {
            drag2DScope = this
            block.invoke(abstractDragScope)
        }
    }

    override suspend fun AbstractDragScope.draggingBy(dragDelta: DragDelta) {
        dragBy(dragDelta.delta)
    }

    override val pointerDirectionConfig = BidirectionalPointerDirectionConfig

    @Suppress("PrimitiveInLambda")
    fun update(
        state: Draggable2DState,
        canDrag: (PointerInputChange) -> Boolean,
        enabled: Boolean,
        interactionSource: MutableInteractionSource?,
        startDragImmediately: () -> Boolean,
        onDragStarted: suspend CoroutineScope.(startedPosition: Offset) -> Unit,
        onDragStopped: suspend CoroutineScope.(velocity: Velocity) -> Unit,
        reverseDirection: Boolean
    ) {
        var resetPointerInputHandling = false
        if (this.state != state) {
            this.state = state
            resetPointerInputHandling = true
        }
        this.canDrag = canDrag
        if (this.enabled != enabled) {
            this.enabled = enabled
            if (!enabled) {
                disposeInteractionSource()
            }
            resetPointerInputHandling = true
        }
        if (this.interactionSource != interactionSource) {
            disposeInteractionSource()
            this.interactionSource = interactionSource
        }
        this.startDragImmediately = startDragImmediately
        this.onDragStarted = onDragStarted
        this.onDragStopped = onDragStopped
        if (this.reverseDirection != reverseDirection) {
            this.reverseDirection = reverseDirection
            resetPointerInputHandling = true
        }
        if (resetPointerInputHandling) {
            pointerInputNode.resetPointerInputHandler()
        }
    }
}

private val NoOpDrag2DScope: Drag2DScope = object : Drag2DScope {
    override fun dragBy(pixels: Offset) {}
}

@Suppress("PrimitiveInLambda")
private class DefaultDraggable2DState(val onDelta: (Offset) -> Unit) : Draggable2DState {
    private val drag2DScope: Drag2DScope = object : Drag2DScope {
        override fun dragBy(pixels: Offset) = onDelta(pixels)
    }

    private val drag2DMutex = MutatorMutex()

    override suspend fun drag(
        dragPriority: MutatePriority,
        block: suspend Drag2DScope.() -> Unit
    ): Unit = coroutineScope {
        drag2DMutex.mutateWith(drag2DScope, dragPriority, block)
    }

    override fun dispatchRawDelta(delta: Offset) {
        return onDelta(delta)
    }
}

private interface AbstractDragScope {
    fun dragBy(pixels: Offset)
}

@Suppress("PrimitiveInLambda")
private abstract class AbstractDraggableNode(
    var canDrag: (PointerInputChange) -> Boolean,
    var enabled: Boolean,
    var interactionSource: MutableInteractionSource?,
    var startDragImmediately: () -> Boolean,
    var onDragStarted: suspend CoroutineScope.(startedPosition: Offset) -> Unit,
    var onDragStopped: suspend CoroutineScope.(velocity: Velocity) -> Unit,
    var reverseDirection: Boolean
) : DelegatingNode(), PointerInputModifierNode, CompositionLocalConsumerModifierNode {

    // Use wrapper lambdas here to make sure that if these properties are updated while we suspend,
    // we point to the new reference when we invoke them.
    private val _canDrag: (PointerInputChange) -> Boolean = { canDrag(it) }
    private val _startDragImmediately: () -> Boolean = { startDragImmediately() }
    private val velocityTracker = VelocityTracker()
    private var isListeningForEvents = false

    /**
     * Passes the drag method from the state.
     */
    abstract suspend fun drag(block: suspend AbstractDragScope.() -> Unit)

    /**
     * Performs dragging by calling the scope's dragBy method
     */
    abstract suspend fun AbstractDragScope.draggingBy(dragDelta: DragDelta)

    /**
     * Returns the pointerDirectionConfig which specifies the main and cross axis deltas. This is
     * important when observing the delta change for Draggable, as we want to observe the change
     * in the main axis only.
     */
    abstract val pointerDirectionConfig: PointerDirectionConfig

    private fun startListeningForEvents() {
        isListeningForEvents = true

        /**
         * To preserve the original behavior we had (before the Modifier.Node migration) we need to
         * scope the DragStopped and DragCancel methods to the node's coroutine scope instead of using
         * the one provided by the pointer input modifier, this is to ensure that even when the pointer
         * input scope is reset we will continue any coroutine scope scope that we started from these
         * methods while the pointer input scope was active.
         */
        coroutineScope.launch {
            while (isActive) {
                var event = channel.receive()
                if (event !is DragStarted) continue
                processDragStart(event)
                try {
                    drag {
                        while (event !is DragStopped && event !is DragCancelled) {
                            (event as? DragDelta)?.let { draggingBy(event as DragDelta) }
                            event = channel.receive()
                        }
                    }
                    if (event is DragStopped) {
                        processDragStop(event as DragStopped)
                    } else if (event is DragCancelled) {
                        processDragCancel()
                    }
                } catch (c: CancellationException) {
                    processDragCancel()
                }
            }
        }
    }

    val pointerInputNode = delegate(SuspendingPointerInputModifierNode {
        // TODO: conditionally undelegate when aosp/2462416 lands?
        if (!enabled) return@SuspendingPointerInputModifierNode
        coroutineScope {
            try {
                awaitPointerEventScope {
                    while (isActive) {
                        awaitDownAndSlop(
                            _canDrag,
                            _startDragImmediately,
                            velocityTracker,
                            pointerDirectionConfig
                        )?.let {
                            /**
                             * The gesture crossed the touch slop, events are now relevant
                             * and should be propagated
                             */
                            /**
                             * The gesture crossed the touch slop, events are now relevant
                             * and should be propagated
                             */
                            if (!isListeningForEvents) {
                                startListeningForEvents()
                            }
                            var isDragSuccessful = false
                            try {
                                isDragSuccessful = awaitDrag(
                                    it.first,
                                    it.second,
                                    velocityTracker,
                                    channel,
                                    reverseDirection
                                ) { event ->
                                    pointerDirectionConfig.calculateDeltaChange(
                                        event.positionChangeIgnoreConsumed()
                                    ) != 0f
                                }
                            } catch (cancellation: CancellationException) {
                                isDragSuccessful = false
                                if (!isActive) throw cancellation
                            } finally {
                                val maximumVelocity = currentValueOf(LocalViewConfiguration)
                                    .maxFlingVelocity.toFloat()
                                val event = if (isDragSuccessful) {
                                    val velocity = velocityTracker.calculateVelocity(
                                        Velocity(maximumVelocity, maximumVelocity)
                                    )
                                    velocityTracker.resetTracking()
                                    DragStopped(velocity * if (reverseDirection) -1f else 1f)
                                } else {
                                    DragCancelled
                                }
                                channel.trySend(event)
                            }
                        }
                    }
                }
            } catch (exception: CancellationException) {
                if (!isActive) {
                    throw exception
                }
            }
        }
    })

    private val channel = Channel<DragEvent>(capacity = Channel.UNLIMITED)
    private var dragInteraction: DragInteraction.Start? = null

    override fun onDetach() {
        isListeningForEvents = false
        disposeInteractionSource()
    }

    override fun onPointerEvent(
        pointerEvent: PointerEvent,
        pass: PointerEventPass,
        bounds: IntSize
    ) {
        pointerInputNode.onPointerEvent(pointerEvent, pass, bounds)
    }

    override fun onCancelPointerInput() {
        pointerInputNode.onCancelPointerInput()
    }

    private suspend fun CoroutineScope.processDragStart(event: DragStarted) {
        dragInteraction?.let { oldInteraction ->
            interactionSource?.emit(DragInteraction.Cancel(oldInteraction))
        }
        val interaction = DragInteraction.Start()
        interactionSource?.emit(interaction)
        dragInteraction = interaction
        onDragStarted.invoke(this, event.startPoint)
    }

    private suspend fun CoroutineScope.processDragStop(event: DragStopped) {
        dragInteraction?.let { interaction ->
            interactionSource?.emit(DragInteraction.Stop(interaction))
            dragInteraction = null
        }
        onDragStopped.invoke(this, event.velocity)
    }

    private suspend fun CoroutineScope.processDragCancel() {
        dragInteraction?.let { interaction ->
            interactionSource?.emit(DragInteraction.Cancel(interaction))
            dragInteraction = null
        }
        onDragStopped.invoke(this, Velocity.Zero)
    }

    fun disposeInteractionSource() {
        dragInteraction?.let { interaction ->
            interactionSource?.tryEmit(DragInteraction.Cancel(interaction))
            dragInteraction = null
        }
    }
}

@Suppress("PrimitiveInLambda")
private suspend fun AwaitPointerEventScope.awaitDownAndSlop(
    canDrag: (PointerInputChange) -> Boolean,
    startDragImmediately: () -> Boolean,
    velocityTracker: VelocityTracker,
    pointerDirectionConfig: PointerDirectionConfig
): Pair<PointerInputChange, Offset>? {
    val initialDown =
        awaitFirstDown(requireUnconsumed = false, pass = PointerEventPass.Initial)
    return if (!canDrag(initialDown)) {
        null
    } else if (startDragImmediately()) {
        initialDown.consume()
        velocityTracker.addPointerInputChange(initialDown)
        // since we start immediately we don't wait for slop and the initial delta is 0
        initialDown to Offset.Zero
    } else {
        val down = awaitFirstDown(requireUnconsumed = false)
        velocityTracker.addPointerInputChange(down)
        var initialDelta = Offset.Zero
        val postPointerSlop = { event: PointerInputChange, offset: Offset ->
            velocityTracker.addPointerInputChange(event)
            event.consume()
            initialDelta = offset
        }

        val afterSlopResult = awaitPointerSlopOrCancellation(
            down.id,
            down.type,
            pointerDirectionConfig = pointerDirectionConfig,
            onPointerSlopReached = postPointerSlop
        )

        if (afterSlopResult != null) afterSlopResult to initialDelta else null
    }
}

private suspend fun AwaitPointerEventScope.awaitDrag(
    startEvent: PointerInputChange,
    initialDelta: Offset,
    velocityTracker: VelocityTracker,
    channel: SendChannel<DragEvent>,
    reverseDirection: Boolean,
    hasDragged: (PointerInputChange) -> Boolean,
): Boolean {

    val overSlopOffset = initialDelta
    val xSign = sign(startEvent.position.x)
    val ySign = sign(startEvent.position.y)
    val adjustedStart = startEvent.position -
            Offset(overSlopOffset.x * xSign, overSlopOffset.y * ySign)
    channel.trySend(DragStarted(adjustedStart))

    channel.trySend(DragDelta(if (reverseDirection) initialDelta * -1f else initialDelta))

    return onDragOrUp(hasDragged, startEvent.id) { event ->
        // Velocity tracker takes all events, even UP
        velocityTracker.addPointerInputChange(event)

        // Dispatch only MOVE events
        if (!event.changedToUpIgnoreConsumed()) {
            val delta = event.positionChange()
            event.consume()
            channel.trySend(DragDelta(if (reverseDirection) delta * -1f else delta))
        }
    }
}

private suspend fun AwaitPointerEventScope.onDragOrUp(
    hasDragged: (PointerInputChange) -> Boolean,
    pointerId: PointerId,
    onDrag: (PointerInputChange) -> Unit
): Boolean {
    return drag(
        pointerId = pointerId,
        onDrag = onDrag,
        hasDragged = hasDragged,
        motionConsumed = { it.isConsumed }
    )?.let(onDrag) != null
}

/**
 * Waits for drag motion along one axis when [pointerDirectionConfig] is
 * [HorizontalPointerDirectionConfig] or [VerticalPointerDirectionConfig], and drag motion along
 * any axis when using [BidirectionalPointerDirectionConfig]. It passes [pointerId] as the pointer
 * to examine. If [pointerId] is raised, another pointer from those that are down will be chosen to
 * lead the gesture, and if none are down, `null` is returned. If [pointerId] is not down when
 * [awaitPointerSlopOrCancellation] is called, then `null` is returned.
 *
 * When pointer slop is detected, [onPointerSlopReached] is called with the change and the distance
 * beyond the pointer slop. [PointerDirectionConfig.calculateDeltaChange] should return the position
 * change in the direction of the drag axis. If [onPointerSlopReached] does not consume the
 * position change, pointer slop will not have been considered detected and the detection will
 * continue or, if it is consumed, the [PointerInputChange] that was consumed will be returned.
 *
 * This works with [awaitTouchSlopOrCancellation] for the other axis to ensure that only horizontal
 * or vertical dragging is done, but not both. It also works for dragging in two ways when using
 * [awaitTouchSlopOrCancellation]
 *
 * @return The [PointerInputChange] of the event that was consumed in [onPointerSlopReached] or
 * `null` if all pointers are raised or the position change was consumed by another gesture
 * detector.
 */
private suspend inline fun AwaitPointerEventScope.awaitPointerSlopOrCancellation(
    pointerId: PointerId,
    pointerType: PointerType,
    pointerDirectionConfig: PointerDirectionConfig,
    onPointerSlopReached: (PointerInputChange, Offset) -> Unit,
): PointerInputChange? {
    if (currentEvent.isPointerUp(pointerId)) {
        return null // The pointer has already been lifted, so the gesture is canceled
    }
    val touchSlop = viewConfiguration.pointerSlop(pointerType)
    var pointer: PointerId = pointerId
    var totalPositionChange = Offset.Zero

    while (true) {
        val event = awaitPointerEvent()
        val dragEvent = event.changes.firstOrNull { it.id == pointer } ?: return null
        if (dragEvent.isConsumed) {
            return null
        } else if (dragEvent.changedToUpIgnoreConsumed()) {
            val otherDown = event.changes.firstOrNull { it.pressed }
            if (otherDown == null) {
                // This is the last "up"
                return null
            } else {
                pointer = otherDown.id
            }
        } else {
            val currentPosition = dragEvent.position
            val previousPosition = dragEvent.previousPosition

            val positionChange = currentPosition - previousPosition

            totalPositionChange += positionChange

            val inDirection = pointerDirectionConfig.calculateDeltaChange(
                totalPositionChange
            )

            if (inDirection < touchSlop) {
                // verify that nothing else consumed the drag event
                awaitPointerEvent(PointerEventPass.Final)
                if (dragEvent.isConsumed) {
                    return null
                }
            } else {
                val postSlopOffset = pointerDirectionConfig.calculatePostSlopOffset(
                    totalPositionChange,
                    touchSlop
                )

                onPointerSlopReached(
                    dragEvent,
                    postSlopOffset
                )
                if (dragEvent.isConsumed) {
                    return dragEvent
                } else {
                    totalPositionChange = Offset.Zero
                }
            }
        }
    }
}

private sealed class DragEvent {
    class DragStarted(val startPoint: Offset) : DragEvent()
    class DragStopped(val velocity: Velocity) : DragEvent()
    object DragCancelled : DragEvent()
    class DragDelta(val delta: Offset) : DragEvent()
}

/**
 * Configures the calculations to get the change amount depending on the dragging type.
 * [calculatePostSlopOffset] will return the post offset slop when the touchSlop is reached.
 */
private interface PointerDirectionConfig {
    fun calculateDeltaChange(offset: Offset): Float
    fun calculatePostSlopOffset(
        totalPositionChange: Offset,
        touchSlop: Float
    ): Offset
}

/**
 * Used for monitoring changes on both X and Y axes.
 */
private val BidirectionalPointerDirectionConfig = object : PointerDirectionConfig {
    override fun calculateDeltaChange(offset: Offset): Float = offset.getDistance()

    override fun calculatePostSlopOffset(
        totalPositionChange: Offset,
        touchSlop: Float
    ): Offset {
        val touchSlopOffset =
            totalPositionChange / calculateDeltaChange(totalPositionChange) * touchSlop
        return totalPositionChange - touchSlopOffset
    }
}

private fun PointerEvent.isPointerUp(pointerId: PointerId): Boolean =
    changes.firstOrNull { it.id == pointerId }?.pressed != true

// This value was determined using experiments and common sense.
// We can't use zero slop, because some hypothetical desktop/mobile devices can send
// pointer events with a very high precision (but I haven't encountered any that send
// events with less than 1px precision)
private val mouseSlop = 0.125.dp
private val defaultTouchSlop = 18.dp // The default touch slop on Android devices
private val mouseToTouchSlopRatio = mouseSlop / defaultTouchSlop

// TODO(demin): consider this as part of ViewConfiguration class after we make *PointerSlop*
//  functions public (see the comment at the top of the file).
//  After it will be a public API, we should get rid of `touchSlop / 144` and return absolute
//  value 0.125.dp.toPx(). It is not possible right now, because we can't access density.
private fun ViewConfiguration.pointerSlop(pointerType: PointerType): Float {
    return when (pointerType) {
        PointerType.Mouse -> touchSlop * mouseToTouchSlopRatio
        else -> touchSlop
    }
}

/**
 * Computes the estimated velocity of the pointer at the time of the last provided data point.
 *
 * The method allows specifying the maximum absolute value for the calculated
 * velocity. If the absolute value of the calculated velocity exceeds the specified
 * maximum, the return value will be clamped down to the maximum. For example, if
 * the absolute maximum velocity is specified as "20", a calculated velocity of "25"
 * will be returned as "20", and a velocity of "-30" will be returned as "-20".
 *
 * @param maximumVelocity the absolute values of the X and Y maximum velocities to
 * be returned in units/second. `units` is the units of the positions provided to this
 * VelocityTracker.
 */
private fun VelocityTracker.calculateVelocity(maximumVelocity: Velocity): Velocity {
    check(maximumVelocity.x > 0f && maximumVelocity.y > 0) {
        "maximumVelocity should be a positive value. You specified=$maximumVelocity"
    }
    val velocity = calculateVelocity()

    val velocityX = velocity.x
    val velocityY = velocity.y

    val clampedVelocityX = if (velocityX >= 0f) {
        velocityX.coerceAtMost(maximumVelocity.x)
    } else {
        velocityX.coerceAtLeast(-maximumVelocity.x)
    }
    val clampedVelocityY = if (velocityY >= 0f) {
        velocityY.coerceAtMost(maximumVelocity.y)
    } else {
        velocityY.coerceAtLeast(-maximumVelocity.y)
    }

    return Velocity(clampedVelocityX, clampedVelocityY)
}

/**
 * Continues to read drag events until all pointers are up or the drag event is canceled.
 * The initial pointer to use for driving the drag is [pointerId]. [hasDragged]
 * passes the result whether a change was detected from the drag function or not. [onDrag] is called
 * whenever the pointer moves and [hasDragged] returns non-zero.
 *
 * @return The last pointer input event change when gesture ended with all pointers up
 * and null when the gesture was canceled.
 */
private suspend inline fun AwaitPointerEventScope.drag(
    pointerId: PointerId,
    onDrag: (PointerInputChange) -> Unit,
    hasDragged: (PointerInputChange) -> Boolean,
    motionConsumed: (PointerInputChange) -> Boolean
): PointerInputChange? {
    if (currentEvent.isPointerUp(pointerId)) {
        return null // The pointer has already been lifted, so the gesture is canceled
    }
    var pointer = pointerId
    while (true) {
        val change = awaitDragOrUp(pointer, hasDragged) ?: return null

        if (motionConsumed(change)) {
            return null
        }

        if (change.changedToUpIgnoreConsumed()) {
            return change
        }

        onDrag(change)
        pointer = change.id
    }
}

/**
 * Waits for a single drag in one axis, final pointer up, or all pointers are up.
 * When [pointerId] has lifted, another pointer that is down is chosen to be the finger
 * governing the drag. When the final pointer is lifted, that [PointerInputChange] is
 * returned. When a drag is detected, that [PointerInputChange] is returned. A drag is
 * only detected when [hasDragged] returns `true`.
 *
 * `null` is returned if there was an error in the pointer input stream and the pointer
 * that was down was dropped before the 'up' was received.
 */
private suspend inline fun AwaitPointerEventScope.awaitDragOrUp(
    pointerId: PointerId,
    hasDragged: (PointerInputChange) -> Boolean
): PointerInputChange? {
    var pointer = pointerId
    while (true) {
        val event = awaitPointerEvent()
        val dragEvent = event.changes.firstOrNull { it.id == pointer } ?: return null
        if (dragEvent.changedToUpIgnoreConsumed()) {
            val otherDown = event.changes.firstOrNull { it.pressed }
            if (otherDown == null) {
                // This is the last "up"
                return dragEvent
            } else {
                pointer = otherDown.id
            }
        } else if (hasDragged(dragEvent)) {
            return dragEvent
        }
    }
}
