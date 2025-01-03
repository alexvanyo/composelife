/*
 * Copyright 2023 The Android Open Source Project
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

@file:Suppress("TooManyFunctions")

package com.alexvanyo.composelife.ui.util

import androidx.compose.animation.core.AnimationSpec
import androidx.compose.animation.core.VectorConverter
import androidx.compose.animation.core.animate
import androidx.compose.animation.core.calculateTargetValue
import androidx.compose.animation.core.exponentialDecay
import androidx.compose.foundation.ExperimentalFoundationApi
import androidx.compose.foundation.MutatePriority
import androidx.compose.foundation.MutatorMutex
import androidx.compose.foundation.gestures.Drag2DScope
import androidx.compose.foundation.gestures.Draggable2DState
import androidx.compose.foundation.gestures.Orientation
import androidx.compose.foundation.gestures.anchoredDraggable
import androidx.compose.foundation.gestures.awaitEachGesture
import androidx.compose.foundation.gestures.awaitFirstDown
import androidx.compose.foundation.gestures.draggable
import androidx.compose.foundation.interaction.DragInteraction
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.foundation.layout.offset
import androidx.compose.runtime.Stable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.isSpecified
import androidx.compose.ui.geometry.isUnspecified
import androidx.compose.ui.input.pointer.AwaitPointerEventScope
import androidx.compose.ui.input.pointer.PointerEvent
import androidx.compose.ui.input.pointer.PointerEventPass
import androidx.compose.ui.input.pointer.PointerId
import androidx.compose.ui.input.pointer.PointerInputChange
import androidx.compose.ui.input.pointer.PointerInputScope
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
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.Velocity
import androidx.compose.ui.util.fastFirstOrNull
import com.alexvanyo.composelife.ui.util.DragEvent.DragCancelled
import com.alexvanyo.composelife.ui.util.DragEvent.DragDelta
import com.alexvanyo.composelife.ui.util.DragEvent.DragStarted
import com.alexvanyo.composelife.ui.util.DragEvent.DragStopped
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.CoroutineStart
import kotlinx.coroutines.Job
import kotlinx.coroutines.cancel
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.isActive
import kotlinx.coroutines.launch

/**
 * Structure that represents the anchors of a [AnchoredDraggable2DState].
 *
 * See the DraggableAnchors factory method to construct drag anchors using a default implementation.
 */
interface DraggableAnchors2D<T> {

    /**
     * Get the anchor position for an associated [anchor]
     *
     * @param anchor The value to look up
     *
     * @return The position of the anchor, or [Offset.Unspecified] if the anchor does not exist
     */
    fun positionOf(anchor: T): Offset

    /**
     * Whether there is an anchor position associated with the [anchor]
     *
     * @param anchor The value to look up
     *
     * @return true if there is an anchor for this value, false if there is no anchor for this value
     */
    fun hasPositionFor(anchor: T): Boolean

    /**
     * Find the closest anchor to the [position].
     *
     * @param position The position to start searching from
     *
     * @return The closest anchor or null if the anchors are empty
     */
    fun closestAnchor(position: Offset): T?

    /**
     * The amount of anchors
     */
    val size: Int
}

/**
 * [DraggableAnchors2DConfig] stores a mutable configuration anchors, comprised of values of [T] and
 * corresponding [Offset] positions. This [DraggableAnchors2DConfig] is used to construct an immutable
 * [DraggableAnchors2D] instance later on.
 */
class DraggableAnchors2DConfig<T> {

    internal val anchors = mutableMapOf<T, Offset>()

    /**
     * Set the anchor position for [this] anchor.
     *
     * @param position The anchor position.
     */
    @Suppress("BuilderSetStyle")
    infix fun T.at(position: Offset) {
        anchors[this] = position
    }
}

/**
 * Create a new [DraggableAnchors2D] instance using a builder function.
 *
 * @param builder A function with a [DraggableAnchors2DConfig] that offers APIs to configure anchors
 * @return A new [DraggableAnchors2D] instance with the anchor positions set by the `builder`
 * function.
 */
fun <T : Any> DraggableAnchors2D(
    builder: DraggableAnchors2DConfig<T>.() -> Unit,
): DraggableAnchors2D<T> = MapDraggableAnchors2D(DraggableAnchors2DConfig<T>().apply(builder).anchors)

/**
 * Enable drag gestures between a set of predefined values.
 *
 * When a drag is detected, the offset of the [AnchoredDraggable2DState] will be updated with the drag
 * delta. You should use this offset to move your content accordingly (see [Modifier.offset]).
 * When the drag ends, the offset will be animated to one of the anchors and when that anchor is
 * reached, the value of the [AnchoredDraggable2DState] will also be updated to the value
 * corresponding to the new anchor.
 *
 * Dragging is constrained between the minimum and maximum anchors.
 *
 * @param state The associated [AnchoredDraggable2DState].
 * @param enabled Whether this [anchoredDraggable] is enabled and should react to the user's input.
 * @param reverseDirection Whether to reverse the direction of the drag, so a top to bottom
 * drag will behave like bottom to top, and a left to right drag will behave like right to left.
 * @param interactionSource Optional [MutableInteractionSource] that will passed on to
 * the internal [Modifier.draggable].
 */
fun <T> Modifier.anchoredDraggable2D(
    state: AnchoredDraggable2DState<T>,
    enabled: Boolean = true,
    reverseDirection: Boolean = false,
    interactionSource: MutableInteractionSource? = null,
): Modifier = this then AnchoredDraggable2DElement(
    state = state,
    enabled = enabled,
    interactionSource = interactionSource,
    reverseDirection = reverseDirection,
    startDragImmediately = state.isAnimationRunning,
)

private class AnchoredDraggable2DElement<T>(
    private val state: AnchoredDraggable2DState<T>,
    private val enabled: Boolean,
    private val reverseDirection: Boolean,
    private val interactionSource: MutableInteractionSource?,
    private val startDragImmediately: Boolean,
) : ModifierNodeElement<AnchoredDraggable2DNode<T>>() {
    override fun create() =
        AnchoredDraggable2DNode(
            state = state,
            enabled = enabled,
            reverseDirection = reverseDirection,
            interactionSource = interactionSource,
            startDragImmediately = startDragImmediately,
        )

    override fun update(node: AnchoredDraggable2DNode<T>) {
        node.update(
            state = state,
            enabled = enabled,
            reverseDirection = reverseDirection,
            interactionSource = interactionSource,
            startDragImmediately = startDragImmediately,
        )
    }

    override fun hashCode(): Int {
        var result = state.hashCode()
        result = 31 * result + enabled.hashCode()
        result = 31 * result + reverseDirection.hashCode()
        result = 31 * result + interactionSource.hashCode()
        result = 31 * result + startDragImmediately.hashCode()
        return result
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true

        if (other !is AnchoredDraggable2DElement<*>) return false

        if (state != other.state) return false
        if (enabled != other.enabled) return false
        if (reverseDirection != other.reverseDirection) return false
        if (interactionSource != other.interactionSource) return false
        if (startDragImmediately != other.startDragImmediately) return false

        return true
    }

    override fun InspectorInfo.inspectableProperties() {
        name = "anchoredDraggable"
        properties["state"] = state
        properties["enabled"] = enabled
        properties["reverseDirection"] = reverseDirection
        properties["interactionSource"] = interactionSource
        properties["startDragImmediately"] = startDragImmediately
    }
}

private class AnchoredDraggable2DNode<T>(
    private var state: AnchoredDraggable2DState<T>,
    enabled: Boolean,
    interactionSource: MutableInteractionSource?,
    private var startDragImmediately: Boolean,
    private var reverseDirection: Boolean,
) : DragGestureNode(
    canDrag = AlwaysDrag,
    enabled = enabled,
    interactionSource = interactionSource,
    orientationLock = null,
) {
    override suspend fun drag(forEachDelta: suspend ((dragDelta: DragDelta) -> Unit) -> Unit) {
        state.anchoredDrag {
            forEachDelta { dragDelta ->
                dragTo(state.newOffsetForDelta(dragDelta.delta.reverseIfNeeded()))
            }
        }
    }

    override fun onDragStarted(startedPosition: Offset) = Unit

    override fun onDragStopped(velocity: Velocity) {
        coroutineScope.launch {
            state.settle(velocity.reverseIfNeeded())
        }
    }

    override fun startDragImmediately(): Boolean = startDragImmediately

    fun update(
        state: AnchoredDraggable2DState<T>,
        enabled: Boolean,
        interactionSource: MutableInteractionSource?,
        startDragImmediately: Boolean,
        reverseDirection: Boolean,
    ) {
        var resetPointerInputHandling = false
        if (this.state != state) {
            this.state = state
            resetPointerInputHandling = true
        }
        if (this.reverseDirection != reverseDirection) {
            this.reverseDirection = reverseDirection
            resetPointerInputHandling = true
        }

        this.startDragImmediately = startDragImmediately

        update(
            canDrag = canDrag,
            enabled = enabled,
            interactionSource = interactionSource,
            orientationLock = null,
            shouldResetPointerInputHandling = resetPointerInputHandling,
        )
    }

    private fun Velocity.reverseIfNeeded() = if (reverseDirection) this * -1f else this * 1f

    private fun Offset.reverseIfNeeded() = if (reverseDirection) this * -1f else this * 1f
}

private val AlwaysDrag: (PointerInputChange) -> Boolean = { true }

/** A node that performs drag gesture recognition and event propagation. */
internal abstract class DragGestureNode(
    canDrag: (PointerInputChange) -> Boolean,
    enabled: Boolean,
    interactionSource: MutableInteractionSource?,
    private var orientationLock: Orientation?,
) : DelegatingNode(), PointerInputModifierNode, CompositionLocalConsumerModifierNode {

    protected var canDrag = canDrag
        private set

    protected var enabled = enabled
        private set

    protected var interactionSource = interactionSource
        private set

    // Use wrapper lambdas here to make sure that if these properties are updated while we suspend,
    // we point to the new reference when we invoke them. startDragImmediately is a lambda since we
    // need the most recent value passed to it from Scrollable.
    private var channel: Channel<DragEvent>? = null
    private var dragInteraction: DragInteraction.Start? = null
    private var isListeningForEvents = false

    /**
     * Responsible for the dragging behavior between the start and the end of the drag. It
     * continually invokes `forEachDelta` to process incoming events. In return, `forEachDelta`
     * calls `dragBy` method to process each individual delta.
     */
    abstract suspend fun drag(forEachDelta: suspend ((dragDelta: DragDelta) -> Unit) -> Unit)

    /**
     * Passes the action needed when a drag starts. This gives the ability to pass the desired
     * behavior from other nodes implementing AbstractDraggableNode
     */
    abstract fun onDragStarted(startedPosition: Offset)

    /**
     * Passes the action needed when a drag stops. This gives the ability to pass the desired
     * behavior from other nodes implementing AbstractDraggableNode
     */
    abstract fun onDragStopped(velocity: Velocity)

    /**
     * If touch slop recognition should be skipped. If this is true, this node will start
     * recognizing drag events immediately without waiting for touch slop.
     */
    abstract fun startDragImmediately(): Boolean

    private fun startListeningForEvents() {
        isListeningForEvents = true

        /**
         * To preserve the original behavior we had (before the Modifier.Node migration) we need to
         * scope the DragStopped and DragCancel methods to the node's coroutine scope instead of
         * using the one provided by the pointer input modifier, this is to ensure that even when
         * the pointer input scope is reset we will continue any coroutine scope scope that we
         * started from these methods while the pointer input scope was active.
         */
        coroutineScope.launch {
            while (isActive) {
                var event = channel?.receive()
                if (event !is DragStarted) continue
                processDragStart(event)
                @Suppress("SwallowedException")
                try {
                    drag { processDelta ->
                        while (event !is DragStopped && event !is DragCancelled) {
                            (event as? DragDelta)?.let(processDelta)
                            event = channel?.receive()
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

    private var pointerInputNode: SuspendingPointerInputModifierNode? = null

    override fun onDetach() {
        isListeningForEvents = false
        disposeInteractionSource()
    }

    override fun onPointerEvent(
        pointerEvent: PointerEvent,
        pass: PointerEventPass,
        bounds: IntSize,
    ) {
        if (enabled && pointerInputNode == null) {
            pointerInputNode = delegate(initializePointerInputNode())
        }
        pointerInputNode?.onPointerEvent(pointerEvent, pass, bounds)
    }

    private fun initializePointerInputNode(): SuspendingPointerInputModifierNode {
        return SuspendingPointerInputModifierNode {
            // re-create tracker when pointer input block restarts. This lazily creates the tracker
            // only when it is need.
            val velocityTracker = VelocityTracker()

            val onDragStart:
                (
                    down: PointerInputChange,
                    slopTriggerChange: PointerInputChange,
                    postSlopOffset: Offset,
                ) -> Unit =
                { down, slopTriggerChange, postSlopOffset ->
                    if (canDrag.invoke(down)) {
                        if (!isListeningForEvents) {
                            if (channel == null) {
                                channel = Channel(capacity = Channel.UNLIMITED)
                            }
                            startListeningForEvents()
                        }
                        velocityTracker.addPointerInputChange(down)
                        val dragStartedOffset = slopTriggerChange.position - postSlopOffset
                        // the drag start event offset is the down event + touch slop value
                        // or in this case the event that triggered the touch slop minus
                        // the post slop offset
                        channel?.trySend(DragStarted(dragStartedOffset))
                    }
                }

            val onDragEnd: (change: PointerInputChange) -> Unit = { upEvent ->
                velocityTracker.addPointerInputChange(upEvent)
                val maximumVelocity = currentValueOf(LocalViewConfiguration).maximumFlingVelocity
                val velocity =
                    velocityTracker.calculateVelocity(Velocity(maximumVelocity, maximumVelocity))
                velocityTracker.resetTracking()
                channel?.trySend(DragStopped(velocity.toValidVelocity()))
            }

            val onDragCancel: () -> Unit = { channel?.trySend(DragCancelled) }

            val shouldAwaitTouchSlop: () -> Boolean = { !startDragImmediately() }

            val onDrag: (change: PointerInputChange, dragAmount: Offset) -> Unit =
                { change, delta ->
                    velocityTracker.addPointerInputChange(change)
                    channel?.trySend(DragDelta(delta))
                }

            coroutineScope {
                try {
                    detectDragGestures(
                        orientationLock = orientationLock,
                        onDragStart = onDragStart,
                        onDragEnd = onDragEnd,
                        onDragCancel = onDragCancel,
                        shouldAwaitTouchSlop = shouldAwaitTouchSlop,
                        onDrag = onDrag,
                    )
                } catch (cancellation: CancellationException) {
                    channel?.trySend(DragCancelled)
                    if (!isActive) throw cancellation
                }
            }
        }
    }

    override fun onCancelPointerInput() {
        pointerInputNode?.onCancelPointerInput()
    }

    private suspend fun processDragStart(event: DragStarted) {
        dragInteraction?.let { oldInteraction ->
            interactionSource?.emit(DragInteraction.Cancel(oldInteraction))
        }
        val interaction = DragInteraction.Start()
        interactionSource?.emit(interaction)
        dragInteraction = interaction
        onDragStarted(event.startPoint)
    }

    private suspend fun processDragStop(event: DragStopped) {
        dragInteraction?.let { interaction ->
            interactionSource?.emit(DragInteraction.Stop(interaction))
            dragInteraction = null
        }
        onDragStopped(event.velocity)
    }

    private suspend fun processDragCancel() {
        dragInteraction?.let { interaction ->
            interactionSource?.emit(DragInteraction.Cancel(interaction))
            dragInteraction = null
        }
        onDragStopped(Velocity.Zero)
    }

    fun disposeInteractionSource() {
        dragInteraction?.let { interaction ->
            interactionSource?.tryEmit(DragInteraction.Cancel(interaction))
            dragInteraction = null
        }
    }

    fun update(
        canDrag: (PointerInputChange) -> Boolean = this.canDrag,
        enabled: Boolean = this.enabled,
        interactionSource: MutableInteractionSource? = this.interactionSource,
        orientationLock: Orientation? = this.orientationLock,
        shouldResetPointerInputHandling: Boolean = false,
    ) {
        var resetPointerInputHandling = shouldResetPointerInputHandling

        this.canDrag = canDrag
        if (this.enabled != enabled) {
            this.enabled = enabled
            if (!enabled) {
                disposeInteractionSource()
                pointerInputNode?.let { undelegate(it) }
                pointerInputNode = null
            }
            resetPointerInputHandling = true
        }
        if (this.interactionSource != interactionSource) {
            disposeInteractionSource()
            this.interactionSource = interactionSource
        }

        if (this.orientationLock != orientationLock) {
            this.orientationLock = orientationLock
            resetPointerInputHandling = true
        }

        if (resetPointerInputHandling) {
            pointerInputNode?.resetPointerInputHandler()
        }
    }
}

@Suppress("LongParameterList")
internal suspend fun PointerInputScope.detectDragGestures(
    onDragStart:
    (
        down: PointerInputChange,
        slopTriggerChange: PointerInputChange,
        overSlopOffset: Offset,
    ) -> Unit,
    onDragEnd: (change: PointerInputChange) -> Unit,
    onDragCancel: () -> Unit,
    shouldAwaitTouchSlop: () -> Boolean,
    orientationLock: Orientation?,
    onDrag: (change: PointerInputChange, dragAmount: Offset) -> Unit,
) {
    var overSlop: Offset

    awaitEachGesture {
        val initialDown = awaitFirstDown(requireUnconsumed = false, pass = PointerEventPass.Initial)
        val awaitTouchSlop = shouldAwaitTouchSlop()

        if (!awaitTouchSlop) {
            initialDown.consume()
        }
        val down = awaitFirstDown(requireUnconsumed = false)
        var drag: PointerInputChange?
        overSlop = Offset.Zero

        if (awaitTouchSlop) {
            do {
                drag =
                    awaitPointerSlopOrCancellation(
                        down.id,
                        down.type,
                        orientation = orientationLock,
                    ) { change, over ->
                        change.consume()
                        overSlop = over
                    }
            } while (drag != null && !drag.isConsumed)
        } else {
            drag = initialDown
        }

        if (drag != null) {
            onDragStart.invoke(down, drag, overSlop)
            onDrag(drag, overSlop)
            val upEvent =
                drag(
                    pointerId = drag.id,
                    onDrag = {
                        onDrag(it, it.positionChange())
                        it.consume()
                    },
                    orientation = orientationLock,
                    motionConsumed = { it.isConsumed },
                )
            if (upEvent == null) {
                onDragCancel()
            } else {
                onDragEnd(upEvent)
            }
        }
    }
}

/**
 * Continues to read drag events until all pointers are up or the drag event is canceled. The
 * initial pointer to use for driving the drag is [pointerId]. [onDrag] is called whenever the
 * pointer moves. The up event is returned at the end of the drag gesture.
 *
 * @param pointerId The pointer where that is driving the gesture.
 * @param onDrag Callback for every new drag event.
 * @param motionConsumed If the PointerInputChange should be considered as consumed.
 * @return The last pointer input event change when gesture ended with all pointers up and null when
 *   the gesture was canceled.
 */
@Suppress("ReturnCount")
internal suspend inline fun AwaitPointerEventScope.drag(
    pointerId: PointerId,
    onDrag: (PointerInputChange) -> Unit,
    orientation: Orientation?,
    motionConsumed: (PointerInputChange) -> Boolean,
): PointerInputChange? {
    if (currentEvent.isPointerUp(pointerId)) {
        return null // The pointer has already been lifted, so the gesture is canceled
    }
    var pointer = pointerId
    while (true) {
        val change =
            awaitDragOrUp(pointer) {
                val positionChange = it.positionChangeIgnoreConsumed()
                val motionChange =
                    if (orientation == null) {
                        positionChange.getDistance()
                    } else {
                        if (orientation == Orientation.Vertical) {
                            positionChange.y
                        } else {
                            positionChange.x
                        }
                    }
                motionChange != 0.0f
            } ?: return null

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
 * Continues to read drag events until all pointers are up or the drag event is canceled. The
 * initial pointer to use for driving the drag is [pointerId]. [onDrag] is called whenever the
 * pointer moves. The up event is returned at the end of the drag gesture.
 *
 * @param pointerId The pointer where that is driving the gesture.
 * @param onDrag Callback for every new drag event.
 * @param motionConsumed If the PointerInputChange should be considered as consumed.
 * @return The last pointer input event change when gesture ended with all pointers up and null when
 *   the gesture was canceled.
 */
@Suppress("ReturnCount")
internal suspend inline fun AwaitPointerEventScope.drag(
    pointerId: PointerId,
    onDrag: (PointerInputChange) -> Unit,
    motionConsumed: (PointerInputChange) -> Boolean,
): PointerInputChange? {
    if (currentEvent.isPointerUp(pointerId)) {
        return null // The pointer has already been lifted, so the gesture is canceled
    }
    var pointer = pointerId
    while (true) {
        val change =
            awaitDragOrUp(pointer) {
                val positionChange = it.positionChangeIgnoreConsumed()
                val motionChange = positionChange.getDistance()
                motionChange != 0.0f
            } ?: return null

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
@Suppress("ReturnCount")
private suspend inline fun AwaitPointerEventScope.awaitDragOrUp(
    pointerId: PointerId,
    hasDragged: (PointerInputChange) -> Boolean,
): PointerInputChange? {
    var pointer = pointerId
    while (true) {
        val event = awaitPointerEvent()
        val dragEvent = event.changes.fastFirstOrNull { it.id == pointer } ?: return null
        if (dragEvent.changedToUpIgnoreConsumed()) {
            val otherDown = event.changes.fastFirstOrNull { it.pressed }
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

private fun Velocity.toValidVelocity() =
    Velocity(if (this.x.isNaN()) 0f else this.x, if (this.y.isNaN()) 0f else this.y)

internal sealed class DragEvent {
    class DragStarted(val startPoint: Offset) : DragEvent()
    class DragStopped(val velocity: Velocity) : DragEvent()
    data object DragCancelled : DragEvent()
    class DragDelta(val delta: Offset) : DragEvent()
}

/**
 * Scope used for suspending anchored drag blocks. Allows to set [AnchoredDraggable2DState.offset] to
 * a new value.
 *
 * @see [AnchoredDraggable2DState.anchoredDrag] to learn how to start the anchored drag and get the
 * access to this scope.
 */
interface AnchoredDrag2DScope {
    /**
     * Assign a new value for an offset value for [AnchoredDraggable2DState].
     *
     * @param newOffset new value for [AnchoredDraggable2DState.offset].
     * @param lastKnownVelocity last known velocity (if known)
     */
    fun dragTo(
        newOffset: Offset,
        lastKnownVelocity: Velocity = Velocity.Zero,
    )
}

/**
 * State of the [anchoredDraggable] modifier.
 * Use the constructor overload with anchors if the anchors are defined in composition, or update
 * the anchors using [updateAnchors].
 *
 * This contains necessary information about any ongoing drag or animation and provides methods
 * to change the state either immediately or by starting an animation.
 *
 * @param initialValue The initial value of the state.
 * @param animationSpec The default animation that will be used to animate to a new state.
 * @param confirmValueChange Optional callback invoked to confirm or veto a pending state change.
 */
@Stable
class AnchoredDraggable2DState<T>(
    initialValue: T,
    val animationSpec: AnimationSpec<Offset>,
    internal val confirmValueChange: (newValue: T) -> Boolean = { true },
) {

    /**
     * Construct an [AnchoredDraggable2DState] instance with anchors.
     *
     * @param initialValue The initial value of the state.
     * @param anchors The anchors of the state. Use [updateAnchors] to update the anchors later.
     * @param animationSpec The default animation that will be used to animate to a new state.
     * @param confirmValueChange Optional callback invoked to confirm or veto a pending state
     * change.
     */
    constructor(
        initialValue: T,
        anchors: DraggableAnchors2D<T>,
        animationSpec: AnimationSpec<Offset>,
        confirmValueChange: (newValue: T) -> Boolean = { true },
    ) : this(
        initialValue,
        animationSpec,
        confirmValueChange,
    ) {
        this.anchors = anchors
        trySnapTo(initialValue)
    }

    private val dragMutex = MutatorMutex()

    @OptIn(ExperimentalFoundationApi::class)
    internal val draggableState = object : Draggable2DState {

        private val dragScope = object : Drag2DScope {
            override fun dragBy(pixels: Offset) {
                with(anchoredDragScope) {
                    dragTo(newOffsetForDelta(pixels))
                }
            }
        }

        override suspend fun drag(
            dragPriority: MutatePriority,
            block: suspend Drag2DScope.() -> Unit,
        ) {
            this@AnchoredDraggable2DState.anchoredDrag(dragPriority) {
                with(dragScope) { block() }
            }
        }

        override fun dispatchRawDelta(delta: Offset) {
            this@AnchoredDraggable2DState.dispatchRawDelta(delta)
        }
    }

    /**
     * The current value of the [AnchoredDraggable2DState].
     */
    var currentValue: T by mutableStateOf(initialValue)
        private set

    /**
     * The target value. This is the closest value to the current offset, taking into account
     * positional thresholds. If no interactions like animations or drags are in progress, this
     * will be the current value.
     */
    val targetValue: T by derivedStateOf {
        dragTarget ?: run {
            val currentOffset = offset
            if (currentOffset.isSpecified) {
                computeTarget(currentOffset, currentValue, velocity = Velocity.Zero)
            } else {
                currentValue
            }
        }
    }

    /**
     * The closest value in the swipe direction from the current offset, not considering thresholds.
     * If an [anchoredDrag] is in progress, this will be the target of that anchoredDrag (if
     * specified).
     */
    internal val closestValue: T by derivedStateOf {
        dragTarget ?: run {
            val currentOffset = offset
            if (currentOffset.isSpecified) {
                computeTargetWithoutThresholds(currentOffset, currentValue)
            } else {
                currentValue
            }
        }
    }

    /**
     * The current offset, or [Offset.Unspecified] if it has not been initialized yet.
     *
     * The offset will be initialized when the anchors are first set through [updateAnchors].
     *
     * Strongly consider using [requireOffset] which will throw if the offset is read before it is
     * initialized. This helps catch issues early in your workflow.
     */
    var offset: Offset by mutableStateOf(Offset.Unspecified)
        private set

    /**
     * Require the current offset.
     *
     * @see offset
     *
     * @throws IllegalStateException If the offset has not been initialized yet
     */
    fun requireOffset(): Offset {
        check(offset.isSpecified) {
            "The offset was read before being initialized. Did you access the offset in a phase " +
                "before layout, like effects or composition?"
        }
        return offset
    }

    /**
     * Whether an animation is currently in progress.
     */
    val isAnimationRunning: Boolean get() = dragTarget != null

    /**
     * The velocity of the last known animation. Gets reset to 0f when an animation completes
     * successfully, but does not get reset when an animation gets interrupted.
     * You can use this value to provide smooth reconciliation behavior when re-targeting an
     * animation.
     */
    var lastVelocity: Velocity by mutableStateOf(Velocity.Zero)
        private set

    private var dragTarget: T? by mutableStateOf(null)

    var anchors: DraggableAnchors2D<T> by mutableStateOf(emptyDraggableAnchors())
        private set

    /**
     * Update the anchors. If there is no ongoing [anchoredDrag] operation, snap to the [newTarget],
     * otherwise restart the ongoing [anchoredDrag] operation (e.g. an animation) with the new
     * anchors.
     *
     * <b>If your anchors depend on the size of the layout, updateAnchors should be called in the
     * layout (placement) phase, e.g. through Modifier.onSizeChanged.</b> This ensures that the
     * state is set up within the same frame.
     * For static anchors, or anchors with different data dependencies, [updateAnchors] is safe to
     * be called from side effects or layout.
     *
     * @param newAnchors The new anchors.
     * @param newTarget The new target, by default the closest anchor or the current target if there
     * are no anchors.
     */
    fun updateAnchors(
        newAnchors: DraggableAnchors2D<T>,
        newTarget: T = if (offset.isSpecified) {
            newAnchors.closestAnchor(offset) ?: targetValue
        } else {
            targetValue
        },
    ) {
        if (anchors != newAnchors) {
            anchors = newAnchors
            // Attempt to snap. If nobody is holding the lock, we can immediately update the offset.
            // If anybody is holding the lock, we send a signal to restart the ongoing work with the
            // updated anchors.
            val snapSuccessful = trySnapTo(newTarget)
            if (!snapSuccessful) {
                dragTarget = newTarget
            }
        }
    }

    /**
     * Find the closest anchor and settle at it with an animation.
     */
    suspend fun settle(velocity: Velocity) {
        val previousValue = this.currentValue
        val targetValue = computeTarget(
            offset = requireOffset(),
            currentValue = previousValue,
            velocity = velocity,
        )
        if (confirmValueChange(targetValue)) {
            animateTo(targetValue, velocity)
        } else {
            // If the user vetoed the state change, rollback to the previous state.
            animateTo(previousValue, velocity)
        }
    }

    private fun computeTarget(
        offset: Offset,
        currentValue: T,
        velocity: Velocity,
    ): T {
        val currentAnchors = anchors
        val targetOffset = exponentialDecay<Offset>(
            frictionMultiplier = 5f,
        ).calculateTargetValue(
            typeConverter = Offset.VectorConverter,
            initialValue = offset,
            initialVelocity = Offset(velocity.x, velocity.y),
        )
        return currentAnchors.closestAnchor(targetOffset) ?: currentValue
    }

    private fun computeTargetWithoutThresholds(
        offset: Offset,
        currentValue: T,
    ): T {
        val currentAnchors = anchors
        val currentAnchor = currentAnchors.positionOf(currentValue)
        return if (currentAnchor == offset || currentAnchor.isUnspecified) {
            currentValue
        } else {
            currentAnchors.closestAnchor(offset) ?: currentValue
        }
    }

    private val anchoredDragScope: AnchoredDrag2DScope = object : AnchoredDrag2DScope {
        override fun dragTo(newOffset: Offset, lastKnownVelocity: Velocity) {
            offset = newOffset
            lastVelocity = lastKnownVelocity
        }
    }

    /**
     * Call this function to take control of drag logic and perform anchored drag with the latest
     * anchors.
     *
     * All actions that change the [offset] of this [AnchoredDraggable2DState] must be performed
     * within an [anchoredDrag] block (even if they don't call any other methods on this object)
     * in order to guarantee that mutual exclusion is enforced.
     *
     * If [anchoredDrag] is called from elsewhere with the [dragPriority] higher or equal to ongoing
     * drag, the ongoing drag will be cancelled.
     *
     * <b>If the [anchors] change while the [block] is being executed, it will be cancelled and
     * re-executed with the latest anchors and target.</b> This allows you to target the correct
     * state.
     *
     * @param dragPriority of the drag operation
     * @param block perform anchored drag given the current anchor provided
     */
    suspend fun anchoredDrag(
        dragPriority: MutatePriority = MutatePriority.Default,
        block: suspend AnchoredDrag2DScope.(anchors: DraggableAnchors2D<T>) -> Unit,
    ) {
        try {
            dragMutex.mutate(dragPriority) {
                restartable(inputs = { anchors }) { latestAnchors ->
                    anchoredDragScope.block(latestAnchors)
                }
            }
        } finally {
            val closest = anchors.closestAnchor(offset)
            if (closest != null &&
                (offset - anchors.positionOf(closest)).getDistanceSquared() <= 0.5f &&
                confirmValueChange.invoke(closest)
            ) {
                currentValue = closest
            }
        }
    }

    /**
     * Call this function to take control of drag logic and perform anchored drag with the latest
     * anchors and target.
     *
     * All actions that change the [offset] of this [AnchoredDraggable2DState] must be performed
     * within an [anchoredDrag] block (even if they don't call any other methods on this object)
     * in order to guarantee that mutual exclusion is enforced.
     *
     * This overload allows the caller to hint the target value that this [anchoredDrag] is intended
     * to arrive to. This will set [AnchoredDraggable2DState.targetValue] to provided value so
     * consumers can reflect it in their UIs.
     *
     * <b>If the [anchors] or [AnchoredDraggable2DState.targetValue] change while the [block] is being
     * executed, it will be cancelled and re-executed with the latest anchors and target.</b> This
     * allows you to target the correct state.
     *
     * If [anchoredDrag] is called from elsewhere with the [dragPriority] higher or equal to ongoing
     * drag, the ongoing drag will be cancelled.
     *
     * @param targetValue hint the target value that this [anchoredDrag] is intended to arrive to
     * @param dragPriority of the drag operation
     * @param block perform anchored drag given the current anchor provided
     */
    suspend fun anchoredDrag(
        targetValue: T,
        dragPriority: MutatePriority = MutatePriority.Default,
        block: suspend AnchoredDrag2DScope.(anchors: DraggableAnchors2D<T>, targetValue: T) -> Unit,
    ) {
        if (anchors.hasPositionFor(targetValue)) {
            try {
                dragMutex.mutate(dragPriority) {
                    dragTarget = targetValue
                    restartable(
                        inputs = { anchors to this@AnchoredDraggable2DState.targetValue },
                    ) { (latestAnchors, latestTarget) ->
                        anchoredDragScope.block(latestAnchors, latestTarget)
                    }
                }
            } finally {
                dragTarget = null
                val closest = anchors.closestAnchor(offset)
                if (closest != null &&
                    (offset - anchors.positionOf(closest)).getDistanceSquared() <= 0.5f &&
                    confirmValueChange.invoke(closest)
                ) {
                    currentValue = closest
                }
            }
        } else {
            // Todo: b/283467401, revisit this behavior
            currentValue = targetValue
        }
    }

    internal fun newOffsetForDelta(delta: Offset) =
        (if (offset.isUnspecified) Offset.Zero else offset) + delta

    /**
     * Drag by the [delta], coerce it in the bounds and dispatch it to the [AnchoredDraggable2DState].
     *
     * @return The delta the consumed by the [AnchoredDraggable2DState]
     */
    fun dispatchRawDelta(delta: Offset): Offset {
        val newOffset = newOffsetForDelta(delta)
        val oldOffset = if (offset.isUnspecified) Offset.Zero else offset
        offset = newOffset
        return newOffset - oldOffset
    }

    /**
     * Attempt to snap synchronously. Snapping can happen synchronously when there is no other drag
     * transaction like a drag or an animation is progress. If there is another interaction in
     * progress, the suspending [snapTo] overload needs to be used.
     *
     * @return true if the synchronous snap was successful, or false if we couldn't snap synchronous
     */
    private fun trySnapTo(targetValue: T): Boolean = dragMutex.tryMutate {
        with(anchoredDragScope) {
            val targetOffset = anchors.positionOf(targetValue)
            if (targetOffset.isSpecified) {
                dragTo(targetOffset)
                dragTarget = null
            }
            currentValue = targetValue
        }
    }

    companion object {
        /**
         * The default [Saver] implementation for [AnchoredDraggable2DState].
         */
        fun <T : Any> Saver(
            animationSpec: AnimationSpec<Offset>,
            confirmValueChange: (T) -> Boolean = { true },
        ) = Saver<AnchoredDraggable2DState<T>, T>(
            save = { it.currentValue },
            restore = {
                AnchoredDraggable2DState(
                    initialValue = it,
                    animationSpec = animationSpec,
                    confirmValueChange = confirmValueChange,
                )
            },
        )
    }
}

/**
 * Snap to a [targetValue] without any animation.
 * If the [targetValue] is not in the set of anchors, the [AnchoredDraggable2DState.currentValue] will
 * be updated to the [targetValue] without updating the offset.
 *
 * @throws CancellationException if the interaction interrupted by another interaction like a
 * gesture interaction or another programmatic interaction like a [animateTo] or [snapTo] call.
 *
 * @param targetValue The target value of the animation
 */
suspend fun <T> AnchoredDraggable2DState<T>.snapTo(targetValue: T) {
    anchoredDrag(targetValue = targetValue) { anchors, latestTarget ->
        val targetOffset = anchors.positionOf(latestTarget)
        if (targetOffset.isSpecified) dragTo(targetOffset)
    }
}

/**
 * Animate to a [targetValue].
 * If the [targetValue] is not in the set of anchors, the [AnchoredDraggable2DState.currentValue] will
 * be updated to the [targetValue] without updating the offset.
 *
 * @throws CancellationException if the interaction interrupted by another interaction like a
 * gesture interaction or another programmatic interaction like a [animateTo] or [snapTo] call.
 *
 * @param targetValue The target value of the animation
 * @param velocity The velocity the animation should start with
 */
suspend fun <T> AnchoredDraggable2DState<T>.animateTo(
    targetValue: T,
    velocity: Velocity = this.lastVelocity,
) {
    anchoredDrag(targetValue = targetValue) { anchors, latestTarget ->
        val targetOffset = anchors.positionOf(latestTarget)
        if (targetOffset.isSpecified) {
            var prev = if (offset.isUnspecified) Offset.Zero else offset

            animate(
                typeConverter = Offset.VectorConverter,
                initialValue = prev,
                targetValue = targetOffset,
                initialVelocity = Offset(velocity.x, velocity.y),
                animationSpec = animationSpec,
            ) { value: Offset, velocity: Offset ->
                // Our onDrag coerces the value within the bounds, but an animation may
                // overshoot, for example a spring animation or an overshooting interpolator
                // We respect the user's intention and allow the overshoot, but still use
                // DraggableState's drag for its mutex.
                dragTo(value, Velocity(velocity.x, velocity.y))
                prev = value
            }
        }
    }
}

private class AnchoredDragFinishedSignal : CancellationException() {
    override fun fillInStackTrace(): Throwable {
        stackTrace = emptyArray()
        return this
    }
}

private suspend fun <I> restartable(inputs: () -> I, block: suspend (I) -> Unit) {
    try {
        coroutineScope {
            var previousDrag: Job? = null
            snapshotFlow(inputs)
                .collect { latestInputs ->
                    previousDrag?.apply {
                        cancel(AnchoredDragFinishedSignal())
                        join()
                    }
                    previousDrag = launch(start = CoroutineStart.UNDISPATCHED) {
                        block(latestInputs)
                        this@coroutineScope.cancel(AnchoredDragFinishedSignal())
                    }
                }
        }
    } catch (@Suppress("SwallowedException") anchoredDragFinished: AnchoredDragFinishedSignal) {
        // Ignored
    }
}

private fun <T> emptyDraggableAnchors() = MapDraggableAnchors2D<T>(emptyMap())

private class MapDraggableAnchors2D<T>(private val anchors: Map<T, Offset>) : DraggableAnchors2D<T> {

    override fun positionOf(anchor: T): Offset = anchors[anchor] ?: Offset.Unspecified
    override fun hasPositionFor(anchor: T) = anchors.containsKey(anchor)

    override fun closestAnchor(position: Offset): T? = anchors.minByOrNull {
        (position - it.value).getDistanceSquared()
    }?.key

    override val size: Int
        get() = anchors.size

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is MapDraggableAnchors2D<*>) return false

        return anchors == other.anchors
    }

    override fun hashCode() = 31 * anchors.hashCode()

    override fun toString() = "MapDraggableAnchors2D($anchors)"
}
