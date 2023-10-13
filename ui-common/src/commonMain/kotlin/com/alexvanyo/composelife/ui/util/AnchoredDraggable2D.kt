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

package com.alexvanyo.composelife.ui.util

import androidx.compose.animation.core.AnimationSpec
import androidx.compose.animation.core.VectorConverter
import androidx.compose.animation.core.animate
import androidx.compose.animation.core.calculateTargetValue
import androidx.compose.animation.core.exponentialDecay
import androidx.compose.foundation.MutatePriority
import androidx.compose.foundation.gestures.draggable
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
import androidx.compose.ui.unit.Velocity
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.CoroutineStart
import kotlinx.coroutines.Job
import kotlinx.coroutines.cancel
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.launch
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock
import java.util.concurrent.atomic.AtomicReference

/**
 * Structure that represents the anchors of a [AnchoredDraggable2DState].
 *
 * See the DraggableAnchors factory method to construct drag anchors using a default implementation.
 */
interface DraggableAnchors2D<T> {

    /**
     * Get the anchor position for an associated [value]
     *
     * @param value The value to look up
     *
     * @return The position of the anchor, or [Offset.Unspecified] if the anchor does not exist
     */
    fun positionOf(value: T): Offset

    /**
     * Whether there is an anchor position associated with the [value]
     *
     * @param value The value to look up
     *
     * @return true if there is an anchor for this value, false if there is no anchor for this value
     */
    fun hasAnchorFor(value: T): Boolean

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
) = draggable2D(
    state = state.draggableState,
    enabled = enabled,
    interactionSource = interactionSource,
    reverseDirection = reverseDirection,
    startDragImmediately = state.isAnimationRunning,
    onDragStopped = { velocity -> launch { state.settle(velocity) } },
)

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
        if (anchors.hasAnchorFor(targetValue)) {
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

    override fun positionOf(value: T): Offset = anchors[value] ?: Offset.Unspecified
    override fun hasAnchorFor(value: T) = anchors.containsKey(value)

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

/**
 * Used in place of the standard Job cancellation pathway to avoid reflective
 * javaClass.simpleName lookups to build the exception message and stack trace collection.
 * Remove if these are changed in kotlinx.coroutines.
 */
private class MutationInterruptedException : CancellationException("Mutation interrupted") {
    override fun fillInStackTrace(): Throwable {
        // Avoid null.clone() on Android <= 6.0 when accessing stackTrace
        stackTrace = emptyArray()
        return this
    }
}

/**
 * Mutual exclusion for UI state mutation over time.
 *
 * [mutate] permits interruptible state mutation over time using a standard [MutatePriority].
 * A [MutatorMutex] enforces that only a single writer can be active at a time for a particular
 * state resource. Instead of queueing callers that would acquire the lock like a traditional
 * [Mutex], new attempts to [mutate] the guarded state will either cancel the current mutator or
 * if the current mutator has a higher priority, the new caller will throw [CancellationException].
 *
 * [MutatorMutex] should be used for implementing hoisted state objects that many mutators may
 * want to manipulate over time such that those mutators can coordinate with one another. The
 * [MutatorMutex] instance should be hidden as an implementation detail. For example:
 *
 * @sample androidx.compose.foundation.samples.mutatorMutexStateObject
 */
@Stable
private class MutatorMutex {
    private class Mutator(val priority: MutatePriority, val job: Job) {
        fun canInterrupt(other: Mutator) = priority >= other.priority

        fun cancel() = job.cancel(MutationInterruptedException())
    }

    private val currentMutator = AtomicReference<Mutator?>(null)
    private val mutex = Mutex()

    private fun tryMutateOrCancel(mutator: Mutator) {
        while (true) {
            val oldMutator = currentMutator.get()
            if (oldMutator == null || mutator.canInterrupt(oldMutator)) {
                if (currentMutator.compareAndSet(oldMutator, mutator)) {
                    oldMutator?.cancel()
                    break
                }
            } else {
                throw CancellationException("Current mutation had a higher priority")
            }
        }
    }

    /**
     * Enforce that only a single caller may be active at a time.
     *
     * If [mutate] is called while another call to [mutate] or [mutateWith] is in progress, their
     * [priority] values are compared. If the new caller has a [priority] equal to or higher than
     * the call in progress, the call in progress will be cancelled, throwing
     * [CancellationException] and the new caller's [block] will be invoked. If the call in
     * progress had a higher [priority] than the new caller, the new caller will throw
     * [CancellationException] without invoking [block].
     *
     * @param priority the priority of this mutation; [MutatePriority.Default] by default. Higher
     * priority mutations will interrupt lower priority mutations.
     * @param block mutation code to run mutually exclusive with any other call to [mutate] or
     * [mutateWith].
     */
    suspend fun <R> mutate(
        priority: MutatePriority = MutatePriority.Default,
        block: suspend () -> R,
    ) = coroutineScope {
        val mutator = Mutator(priority, coroutineContext[Job]!!)

        tryMutateOrCancel(mutator)

        mutex.withLock {
            try {
                block()
            } finally {
                currentMutator.compareAndSet(mutator, null)
            }
        }
    }

    /**
     * Enforce that only a single caller may be active at a time.
     *
     * If [mutateWith] is called while another call to [mutate] or [mutateWith] is in progress,
     * their [priority] values are compared. If the new caller has a [priority] equal to or
     * higher than the call in progress, the call in progress will be cancelled, throwing
     * [CancellationException] and the new caller's [block] will be invoked. If the call in
     * progress had a higher [priority] than the new caller, the new caller will throw
     * [CancellationException] without invoking [block].
     *
     * This variant of [mutate] calls its [block] with a [receiver], removing the need to create
     * an additional capturing lambda to invoke it with a receiver object. This can be used to
     * expose a mutable scope to the provided [block] while leaving the rest of the state object
     * read-only. For example:
     *
     * @sample androidx.compose.foundation.samples.mutatorMutexStateObjectWithReceiver
     *
     * @param receiver the receiver `this` that [block] will be called with
     * @param priority the priority of this mutation; [MutatePriority.Default] by default. Higher
     * priority mutations will interrupt lower priority mutations.
     * @param block mutation code to run mutually exclusive with any other call to [mutate] or
     * [mutateWith].
     */
    suspend fun <T, R> mutateWith(
        receiver: T,
        priority: MutatePriority = MutatePriority.Default,
        block: suspend T.() -> R,
    ) = coroutineScope {
        val mutator = Mutator(priority, coroutineContext[Job]!!)

        tryMutateOrCancel(mutator)

        mutex.withLock {
            try {
                receiver.block()
            } finally {
                currentMutator.compareAndSet(mutator, null)
            }
        }
    }

    /**
     * Attempt to mutate synchronously if there is no other active caller.
     * If there is no other active caller, the [block] will be executed in a lock. If there is
     * another active caller, this method will return false, indicating that the active caller
     * needs to be cancelled through a [mutate] or [mutateWith] call with an equal or higher
     * mutation priority.
     *
     * Calls to [mutate] and [mutateWith] will suspend until execution of the [block] has finished.
     *
     * @param block mutation code to run mutually exclusive with any other call to [mutate],
     * [mutateWith] or [tryMutate].
     * @return true if the [block] was executed, false if there was another active caller and the
     * [block] was not executed.
     */
    inline fun tryMutate(block: () -> Unit): Boolean {
        val didLock = tryLock()
        if (didLock) {
            try {
                block()
            } finally {
                unlock()
            }
        }
        return didLock
    }

    @PublishedApi
    internal fun tryLock(): Boolean = mutex.tryLock()

    @PublishedApi
    internal fun unlock() {
        mutex.unlock()
    }
}
