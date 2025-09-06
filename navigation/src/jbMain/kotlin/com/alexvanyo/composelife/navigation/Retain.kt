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

package com.alexvanyo.composelife.navigation

import androidx.collection.MutableScatterMap
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.ControlledRetainScope
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.LocalRetainScope
import androidx.compose.runtime.NonRestartableComposable
import androidx.compose.runtime.RetainObserver
import androidx.compose.runtime.RetainScope
import androidx.compose.runtime.RetainStateProvider
import androidx.compose.runtime.ReusableContentHost
import androidx.compose.runtime.currentComposer
import androidx.compose.runtime.retain

/**
 * `RetainedContentHost` is used to install a [RetainScope] around a block of [content]. The
 * installed `RetainScope` is managed such that the scope will start to keep exited values with
 * [active] is false, and stop keeping exited values when [active] becomes true. See
 * [RetainScope.isKeepingExitedValues] for more information on this terminology.
 *
 * `RetainedContentHost` is designed as an out-of-the-box solution for managing content that's
 * controlled effectively by an if/else statement. The [content] provided to this lambda will render
 * when [active] is true, and be removed when [active] is false. If the content is hidden and then
 * shown again in this way, the installed RetainScope will restore all retained values from the last
 * time the content was shown.
 *
 * The managed RetainScope is _also_ retained. If this composable is removed while the parent scope
 * is keeping its exited values, this scope will be persisted so that it can be restored in the
 * future. If this composable is removed while its parent scope is not keeping its exited values,
 * the scope will be discarded and all its held values will be immediately retired.
 *
 * For this reason, when using this as a mechanism to retain values for content that is being shown
 * and hidden, this composable must be hoisted high enough so that it is not removed when the
 * content being retained is hidden.
 *
 * @param active Whether this host should compose its [content]. When this value is true, [content]
 *   will be rendered and the installed [RetainScope] will not keep exited values. When this value
 *   is false, [content] will stop being rendered and the installed [RetainScope] will collect and
 *   keep its exited values for future restoration.
 * @param content The content to render. Inside of this lambda, [LocalRetainScope] is set to the
 *   [RetainScope] managed by this composable.
 * @see retainControlledRetainScope
 */
@Composable
public fun RetainedContentHost(active: Boolean, content: @Composable () -> Unit) {
    val retainScope = retainControlledRetainScope()
    if (active) {
        CompositionLocalProvider(LocalRetainScope provides retainScope, content)

        // Match the isKeepingExitedValues state to the active parameter. This effect must come
        // AFTER the content to correctly capture values.
        val composer = currentComposer
        DisposableEffect(retainScope) {
            // Stop keeping exited values when we become active
            val cancellationHandle =
                composer.scheduleFrameEndCallback { retainScope.stopKeepingExitedValues() }

            onDispose {
                // Start keeping exited values when we deactivate
                cancellationHandle.cancel()
                retainScope.startKeepingExitedValues()
            }
        }
    }
}

/**
 * `RetainedContentHost` is used to install a [RetainScope] around a block of [content]. The
 * installed `RetainScope` is managed such that the scope will start to keep exited values with
 * [active] is false, and stop keeping exited values when [active] becomes true. See
 * [RetainScope.isKeepingExitedValues] for more information on this terminology.
 *
 * `RetainedContentHost` is designed as an out-of-the-box solution for managing content that's
 * controlled effectively by an if/else statement. The [content] provided to this lambda will render
 * when [active] is true, and be removed when [active] is false. If the content is hidden and then
 * shown again in this way, the installed RetainScope will restore all retained values from the last
 * time the content was shown.
 *
 * The managed RetainScope is _also_ retained. If this composable is removed while the parent scope
 * is keeping its exited values, this scope will be persisted so that it can be restored in the
 * future. If this composable is removed while its parent scope is not keeping its exited values,
 * the scope will be discarded and all its held values will be immediately retired.
 *
 * For this reason, when using this as a mechanism to retain values for content that is being shown
 * and hidden, this composable must be hoisted high enough so that it is not removed when the
 * content being retained is hidden.
 *
 * This host is "Reusable," matching the behavior of [ReusableContentHost]. When [active] becomes
 * `false`, remembered values are deleted, but the node tree is kept. When this composable later
 * becomes [active], the previous node instances are able to be reused.
 *
 * @param active Whether this host should compose its [content]. When this value is true, [content]
 *   will be rendered and the installed [RetainScope] will not keep exited values. When this value
 *   is false, [content] will stop being rendered and the installed [RetainScope] will collect and
 *   keep its exited values for future restoration.
 * @param content The content to render. Inside of this lambda, [LocalRetainScope] is set to the
 *   [RetainScope] managed by this composable.
 * @see ReusableContentHost
 * @see retainControlledRetainScope
 */
@Composable
public fun RetainedReusableContentHost(active: Boolean, content: @Composable () -> Unit) {
    val retainScope = retainControlledRetainScope()
    ReusableContentHost(active) {
        CompositionLocalProvider(LocalRetainScope provides retainScope, content)

        // Match the isKeepingExitedValues state to the active parameter. This effect must come
        // AFTER the content to correctly capture values.
        val composer = currentComposer
        DisposableEffect(retainScope) {
            // Stop keeping exited values when we become active
            val cancellationHandle =
                composer.scheduleFrameEndCallback { retainScope.stopKeepingExitedValues() }

            onDispose {
                // Start keeping exited values when we deactivate
                cancellationHandle.cancel()
                retainScope.startKeepingExitedValues()
            }
        }
    }
}

/**
 * Retains a [ControlledRetainScope] that is nested under the current [LocalRetainScope] and has no
 * other defined retention scenarios.
 *
 * A [ControlledRetainScope] created in this way will mirror the retention behavior of
 * [LocalRetainScope]. When the parent scope begins retaining its values, the returned scope will
 * receive a request to start retaining values as well. When the parent scope stops retaining
 * values, that request is cleared.
 *
 * This API is available as a building block for other retain scopes defined in composition. To
 * define your own retention scenario, call [ControlledRetainScope.startKeepingExitedValues] and
 * [ControlledRetainScope.stopKeepingExitedValues] on the returned scope as appropriate. You must
 * also install this scope in the composition hierarchy by providing it as the value of
 * [LocalRetainScope].
 *
 * @return A [ControlledRetainScope] nested under the [LocalRetainScope], ready to be installed in
 *   the composition hierarchy and be used to define a retention scenario.
 * @see RetainedContentHost
 */
@Composable
public fun retainControlledRetainScope(): ControlledRetainScope {
    val retainScope = retain { ControlledRetainScope() }

    RetainedEffect(retainScope) {
        onRetire {
            // The retainScope has stopped being retained. Dispose it.
            retainScope.setParentRetainStateProvider(RetainStateProvider.NeverKeepExitedValues)
            if (retainScope.isKeepingExitedValues) retainScope.stopKeepingExitedValues()
        }
    }

    val parentScope = LocalRetainScope.current
    DisposableEffect(parentScope) {
        retainScope.setParentRetainStateProvider(parentScope)
        onDispose {
            // Keep the parent's state until we get a new scope. This lets us continue
            // retaining when the composition hierarchy is destroyed and this parent is removed.
            retainScope.setParentRetainStateProvider(
                if (parentScope.isKeepingExitedValues) {
                    RetainStateProvider.AlwaysKeepExitedValues
                } else {
                    RetainStateProvider.NeverKeepExitedValues
                },
            )
        }
    }

    return retainScope
}

/**
 * Receiver scope for [RetainedEffect] that offers the [onRetire] clause that should be the last
 * statement in any call to [RetainedEffect].
 */
public class RetainedEffectScope {
    /**
     * Provide [onRetiredEffect] to the [DisposableEffect] to run when it leaves the composition or
     * its key changes.
     */
    public inline fun onRetire(crossinline onRetiredEffect: () -> Unit): RetainedEffectResult =
        object : RetainedEffectResult {
            override fun retire() {
                onRetiredEffect()
            }
        }
}

/**
 * The return type of a built [RetainedEffect]. This is created in the
 * [RetainedEffectScope.onRetire] clause and tracks the `onRetiredEffect` callback for internal
 * usage.
 */
public interface RetainedEffectResult {
    /**
     * Called when the [RetainedEffect] is retired from composition. This should call the
     * `onRetiredEffect` provided to [RetainedEffectScope.onRetire].
     */
    public fun retire()
}

private val InternalRetainedEffectScope = RetainedEffectScope()

private class RetainedEffectImpl(
    private val effect: RetainedEffectScope.() -> RetainedEffectResult,
) : RetainObserver {
    private var onRetire: RetainedEffectResult? = null

    override fun onRetained() {
        onRetire = InternalRetainedEffectScope.effect()
    }

    override fun onRetired() {
        onRetire?.retire()
        onRetire = null
    }

    override fun onEnteredComposition() {
        // Do nothing. The effect doesn't care about this callback event.
    }

    override fun onExitedComposition() {
        // Do nothing. The effect doesn't care about this callback event.
    }
}

private const val RetainedEffectNoParamError =
    "RetainedEffect must provide one or more 'key' parameters that define the identity of " +
        "the RetainedEffect and determine when its previous effect should be disposed and " +
        "a new effect started for the new key."

// This deprecated-error function shadows the varargs overload so that the varargs version
// is not used without key parameters.
@Composable
@NonRestartableComposable
@Suppress("DeprecatedCallableAddReplaceWith", "UNUSED_PARAMETER")
@Deprecated(RetainedEffectNoParamError, level = DeprecationLevel.ERROR)
public fun RetainedEffect(effect: RetainedEffectScope.() -> RetainedEffectResult): Unit =
    error(RetainedEffectNoParamError)

/**
 * A side effect of composition that must run for any new unique value of [key1] and must be
 * reversed or cleaned up if [key1] changes or if the [RetainedEffect] permanently leaves
 * composition.
 *
 * A [RetainedEffect] tracks the lifecycle of retained content. If the current [RetainScope] is
 * keeping values because its managed content is being transiently destroyed, the [RetainedEffect]
 * is kept alive. From this state, the [RetainedEffect] can either:
 * - Be retired because the [RetainScope] is destroyed without its content being restored
 * - Be retired if the [RetainScope]'s content re-enters the composition but does not include this
 *   [RetainedEffect] or invokes it with different keys
 * - Be restored to the recreated composition hierarchy. In this case, the [RetainedEffect] does not
 *   execute any callbacks.
 *
 * If a [RetainedEffect] is removed from the composition hierarchy when the [RetainScope] is not
 * keeping exited values, then the scope will immediately be retired and behave like a
 * [DisposableEffect]. Retirement has the same timing guarantees as [RetainObserver.onRetired].
 *
 * A [RetainedEffect]'s _key_ is a value that defines the identity of the [RetainedEffect]. If a
 * [RetainedEffect] is recomposed with different keys, a new effect will be created and the previous
 * effect will be retired. If the current RetainScope is not keeping exited values, the retirement
 * happens before the new effect is started. Otherwise, the prior instance of the effect will
 * continue to be retained for possible restoration until the scope stops keeping exited values.
 *
 * [RetainedEffect] may be used to initialize or subscribe to a key and reinitialize when a
 * different key is provided, performing cleanup for the old operation before initializing the new.
 * For example:
 *
 * @sample androidx.compose.runtime.samples.retainedEffectSample
 *
 * A [RetainedEffect] **must** include a [retire][RetainedEffectScope.onRetire] clause as the final
 * statement in its [effect] block. If your operation does not require disposal it might be a
 * [SideEffect] instead, or a [LaunchedEffect] if it launches a coroutine that should be managed by
 * the composition.
 *
 * There is guaranteed to be one call to [retire][RetainedEffectScope.onRetire] for every call to
 * [effect]. Both [effect] and [retire][RetainedEffectScope.onRetire] will always be run on the
 * composition's apply dispatcher and appliers are never run concurrent with themselves, one
 * another, applying changes to the composition tree, or running [RememberObserver] event callbacks.
 */
@Composable
@NonRestartableComposable
public fun RetainedEffect(key1: Any?, effect: RetainedEffectScope.() -> RetainedEffectResult) {
    retain(key1) { RetainedEffectImpl(effect) }
}

/**
 * A side effect of composition that must run for any new unique value of [key1] or [key2] and must
 * be reversed or cleaned up if [key1] or [key2] changes or if the [RetainedEffect] permanently
 * leaves composition.
 *
 * A [RetainedEffect] tracks the lifecycle of retained content. If the current [RetainScope] is
 * keeping values because its managed content is being transiently destroyed, the [RetainedEffect]
 * is kept alive. From this state, the [RetainedEffect] can either:
 * - Be retired because the [RetainScope] is destroyed without its content being restored
 * - Be retired if the [RetainScope]'s content re-enters the composition but does not include this
 *   [RetainedEffect] or invokes it with different keys
 * - Be restored to the recreated composition hierarchy. In this case, the [RetainedEffect] does not
 *   execute any callbacks.
 *
 * If a [RetainedEffect] is removed from the composition hierarchy when the [RetainScope] is not
 * keeping exited values, then the scope will immediately be retired and behave like a
 * [DisposableEffect]. Retirement has the same timing guarantees as [RetainObserver.onRetired].
 *
 * A [RetainedEffect]'s _key_ is a value that defines the identity of the [RetainedEffect]. If a
 * [RetainedEffect] is recomposed with different keys, a new effect will be created and the previous
 * effect will be retired. If the current RetainScope is not keeping exited values, the retirement
 * happens before the new effect is started. Otherwise, the prior instance of the effect will
 * continue to be retained for possible restoration until the scope stops keeping exited values.
 *
 * [RetainedEffect] may be used to initialize or subscribe to a key and reinitialize when a
 * different key is provided, performing cleanup for the old operation before initializing the new.
 * For example:
 *
 * @sample androidx.compose.runtime.samples.retainedEffectSample
 *
 * A [RetainedEffect] **must** include a [retire][RetainedEffectScope.onRetire] clause as the final
 * statement in its [effect] block. If your operation does not require disposal it might be a
 * [SideEffect] instead, or a [LaunchedEffect] if it launches a coroutine that should be managed by
 * the composition.
 *
 * There is guaranteed to be one call to [retire][RetainedEffectScope.onRetire] for every call to
 * [effect]. Both [effect] and [retire][RetainedEffectScope.onRetire] will always be run on the
 * composition's apply dispatcher and appliers are never run concurrent with themselves, one
 * another, applying changes to the composition tree, or running [RememberObserver] event callbacks.
 */
@Composable
@NonRestartableComposable
public fun RetainedEffect(
    key1: Any?,
    key2: Any?,
    effect: RetainedEffectScope.() -> RetainedEffectResult,
) {
    retain(key1, key2) { RetainedEffectImpl(effect) }
}

/**
 * A side effect of composition that must run for any new unique value of [key1], [key2], or [key3]
 * and must be reversed or cleaned up if [key1], [key2], or [key3] changes or if the
 * [RetainedEffect] permanently leaves composition.
 *
 * A [RetainedEffect] tracks the lifecycle of retained content. If the current [RetainScope] is
 * keeping values because its managed content is being transiently destroyed, the [RetainedEffect]
 * is kept alive. From this state, the [RetainedEffect] can either:
 * - Be retired because the [RetainScope] is destroyed without its content being restored
 * - Be retired if the [RetainScope]'s content re-enters the composition but does not include this
 *   [RetainedEffect] or invokes it with different keys
 * - Be restored to the recreated composition hierarchy. In this case, the [RetainedEffect] does not
 *   execute any callbacks.
 *
 * If a [RetainedEffect] is removed from the composition hierarchy when the [RetainScope] is not
 * keeping exited values, then the scope will immediately be retired and behave like a
 * [DisposableEffect]. Retirement has the same timing guarantees as [RetainObserver.onRetired].
 *
 * A [RetainedEffect]'s _key_ is a value that defines the identity of the [RetainedEffect]. If a
 * [RetainedEffect] is recomposed with different keys, a new effect will be created and the previous
 * effect will be retired. If the current RetainScope is not keeping exited values, the retirement
 * happens before the new effect is started. Otherwise, the prior instance of the effect will
 * continue to be retained for possible restoration until the scope stops keeping exited values.
 *
 * [RetainedEffect] may be used to initialize or subscribe to a key and reinitialize when a
 * different key is provided, performing cleanup for the old operation before initializing the new.
 * For example:
 *
 * @sample androidx.compose.runtime.samples.retainedEffectSample
 *
 * A [RetainedEffect] **must** include a [retire][RetainedEffectScope.onRetire] clause as the final
 * statement in its [effect] block. If your operation does not require disposal it might be a
 * [SideEffect] instead, or a [LaunchedEffect] if it launches a coroutine that should be managed by
 * the composition.
 *
 * There is guaranteed to be one call to [retire][RetainedEffectScope.onRetire] for every call to
 * [effect]. Both [effect] and [retire][RetainedEffectScope.onRetire] will always be run on the
 * composition's apply dispatcher and appliers are never run concurrent with themselves, one
 * another, applying changes to the composition tree, or running [RememberObserver] event callbacks.
 */
@Composable
@NonRestartableComposable
public fun RetainedEffect(
    key1: Any?,
    key2: Any?,
    key3: Any?,
    effect: RetainedEffectScope.() -> RetainedEffectResult,
) {
    retain(key1, key2, key3) { RetainedEffectImpl(effect) }
}

/**
 * A side effect of composition that must run for any new unique value of [keys] and must be
 * reversed or cleaned up if [keys] changes or if the [RetainedEffect] permanently leaves
 * composition.
 *
 * A [RetainedEffect] tracks the lifecycle of retained content. If the current [RetainScope] is
 * keeping values because its managed content is being transiently destroyed, the [RetainedEffect]
 * is kept alive. From this state, the [RetainedEffect] can either:
 * - Be retired because the [RetainScope] is destroyed without its content being restored
 * - Be retired if the [RetainScope]'s content re-enters the composition but does not include this
 *   [RetainedEffect] or invokes it with different keys
 * - Be restored to the recreated composition hierarchy. In this case, the [RetainedEffect] does not
 *   execute any callbacks.
 *
 * If a [RetainedEffect] is removed from the composition hierarchy when the [RetainScope] is not
 * keeping exited values, then the scope will immediately be retired and behave like a
 * [DisposableEffect]. Retirement has the same timing guarantees as [RetainObserver.onRetired].
 *
 * A [RetainedEffect]'s _key_ is a value that defines the identity of the [RetainedEffect]. If a
 * [RetainedEffect] is recomposed with different keys, a new effect will be created and the previous
 * effect will be retired. If the current RetainScope is not keeping exited values, the retirement
 * happens before the new effect is started. Otherwise, the prior instance of the effect will
 * continue to be retained for possible restoration until the scope stops keeping exited values.
 *
 * [RetainedEffect] may be used to initialize or subscribe to a key and reinitialize when a
 * different key is provided. For example:
 *
 * @sample androidx.compose.runtime.samples.retainedEffectSample
 *
 * A [RetainedEffect] **must** include a [retire][RetainedEffectScope.onRetire] clause as the final
 * statement in its [effect] block. If your operation does not require disposal it might be a
 * [SideEffect] instead, or a [LaunchedEffect] if it launches a coroutine that should be managed by
 * the composition.
 *
 * There is guaranteed to be one call to [retire][RetainedEffectScope.onRetire] for every call to
 * [effect]. Both [effect] and [retire][RetainedEffectScope.onRetire] will always be run on the
 * composition's apply dispatcher and appliers are never run concurrent with themselves, one
 * another, applying changes to the composition tree, or running [RememberObserver] event callbacks.
 */
@Composable
@NonRestartableComposable
public fun RetainedEffect(
    vararg keys: Any?,
    effect: RetainedEffectScope.() -> RetainedEffectResult,
) {
    retain(*keys) { RetainedEffectImpl(effect) }
}

/**
 * Returns a [retain] instance of a new [FanOutRetainScopeProvider]. The returned provider will be
 * parented to the [LocalRetainScope] at this point in the composition hierarchy. If the
 * [LocalRetainScope] is changed, the returned provider will be re-parented to the new new
 * [LocalRetainScope]. When this invocation leaves composition, it will continue retaining if its
 * parent scope was retaining.
 *
 * This method is intended to be used for managing retain state in composables that swap in and out
 * children arbitrarily.
 *
 * @param initialSize The initial size of the backing map created by the [FanOutRetainScopeProvider]
 */
@Composable
public fun <T> retainFanOutRetainScopeProvider(
    initialSize: Int = FanOutRetainScopeProvider.DEFAULT_CAPACITY,
): FanOutRetainScopeProvider<T> {
    val provider = retain { FanOutRetainScopeProvider<T>(initialSize) }
    val parentScope = LocalRetainScope.current
    DisposableEffect(parentScope) {
        provider.setParentRetainStateProvider(parentScope)
        onDispose {
            provider.setParentRetainStateProvider(
                parent =
                if (parentScope.isKeepingExitedValues) {
                    RetainStateProvider.AlwaysKeepExitedValues
                } else {
                    RetainStateProvider.NeverKeepExitedValues
                },
            )
        }
    }
    return provider
}

/**
 * A [FanOutRetainScopeProvider] creates and manages [RetainScope] instances for collections of
 * items. This is desirable for components that swap in and out children where each child should be
 * able to retain state when it becomes removed from the composition hierarchy.
 *
 * To use this class, call [getOrCreateRetainScopeForChild] to instantiate the [RetainScope] that
 * should be installed for a given child content block. When that child is being removed, call
 * [beginRetainChild] to start its retention cycle. After the child has been added back to the
 * composition, invoke [endRetainChild] to end the retention cycle.
 *
 * @param K the key type used to identify scopes created by this provider
 * @param initialSize The initial capacity of the backing map used to store the child
 *   [RetainScope]s. This is useful to specify if you know how many children you expect to be
 *   managing as it can prevent unnecessary resizes of the backing map.
 */
public class FanOutRetainScopeProvider<K>(initialSize: Int = DEFAULT_CAPACITY) {
    private val childScopes = MutableScatterMap<K, ControlledRetainScope>(initialSize)

    private var parentScope: RetainStateProvider = RetainStateProvider.NeverKeepExitedValues
    private var isParentKeepingExitedValues = false
    private val parentObserver =
        object : RetainStateProvider.RetainStateObserver {
            override fun onStartKeepingExitedValues() {
                setKeepExitedValues(true)
            }

            override fun onStopKeepingExitedValues() {
                setKeepExitedValues(false)
            }
        }

    /**
     * Starts retaining for a child with the given [key]. If a retain scope has not been created for
     * this key (because [getOrCreateRetainScopeForChild] was not called for the key or it has been
     * cleared with [clearChild] or [clearChildren]), then this function does nothing. Similarly, if
     * the retain scope for the given key is already retaining, this function will do nothing.
     *
     * This function must be called **before** any content for the associated child is removed from
     * the composition hierarchy.
     *
     * @param key The key of the child to begin retention for
     */
    public fun beginRetainChild(key: K) {
        val scope = childScopes[key] ?: return
        scope.startKeepingExitedValues()
    }

    /**
     * Ends retention for a child with the given [key] as previously started by [beginRetainChild].
     * If the underlying scope is not retaining because [beginRetainChild] has not been called, or
     * was called without first creating the scope via [getOrCreateRetainScopeForChild], this
     * function will do nothing.
     *
     * This function must be called **after** the completion of the frame in which the child content
     * is being restored to allow the restored child to re-consume all of its retained values. You
     * can use [Recomposer.scheduleFrameEndCallback] or [Composer.scheduleFrameEndCallback] to
     * insert a sufficient delay.
     *
     * @param key The key of the child to end retention for
     */
    public fun endRetainChild(key: K) {
        val scope = childScopes[key] ?: return
        scope.stopKeepingExitedValues()
    }

    /**
     * Installs child [content] that should be retained under the given [key]. [beginRetainChild]
     * and [endRetainChild] and automatically called based on the presence of this composable for
     * the [key].
     *
     * When removed, this composable begins retaining values in the [content] lambda under the given
     * [key]. When added back to the composition hierarchy, retention will be ended once the
     * composition completes. The keys used with this method should only be used once in a
     * composition per [FanOutRetainScopeProvider].
     *
     * This composable only attempts to manage the retention lifecycle for the [content] and [key]
     * pair. It will retain removed content indefinitely until [clearChild] or [clearChildren] is
     * invoked.
     *
     * @param key The child key associated with the given [content]. This key is used to identify
     *   the retention pool for objects [retained][retain] by the content composable.
     * @param content The composable content to compose with the [RetainScope] of the given [key]
     */
    @Suppress("ComposeUnstableReceiver")
    @Composable
    public fun ChildWithPresenceTracking(key: K, content: @Composable () -> Unit) {
        CompositionLocalProvider(LocalRetainScope provides getOrCreateRetainScopeForChild(key)) {
            content()
            PresenceIndicator(key)
        }
    }

    /**
     * Indicates the presence of [key] in the composition hierarchy. When this composable is added,
     * [beginRetainChild] is called for the [key]. When this composable is removed, [endRetainChild]
     * will be called at the completion of the frame.
     *
     * **This composable must be installed AFTER content using [key]'s [RetainScope] to order its
     * effects correctly.**
     */
    @Suppress("ComposeUnstableReceiver")
    @Composable
    private fun PresenceIndicator(key: K) {
        val composer = currentComposer
        DisposableEffect(key) {
            // This key is entering the composition. End retention when the frame completes.
            val endRetainHandle = composer.scheduleFrameEndCallback { endRetainChild(key) }
            onDispose {
                // This key is exiting the composition. Begin retaining now.
                endRetainHandle.cancel()
                beginRetainChild(key)
            }
        }
    }

    /**
     * Creates or returns a previously created [RetainScope] instance for the given [key]. The
     * returned [RetainScope] will be managed by this provider. It will begin retaining if the
     * parent retain scope starts retaining or if [beginRetainChild] is called with the same [key],
     * and it will stop retaining with the parent retain scope ends retaining and there is no
     * [beginRetainChild] call without a corresponding [endRetainChild] call for the specified
     * [key].
     *
     * The first time this function is called for a given [key], a new [RetainScope] is created for
     * the [key]. When this function is called for the same [key], it will return the same
     * [RetainScope] it originally returned. If a given [key]'s scope is [cleared][clearChild], then
     * a new one will be created for it the next time it is requested via this function.
     *
     * This function must be called before [beginRetainChild] or [endRetainChild] is called for
     * those two methods to have any effect on the retention state for the given [key].
     *
     * @param key The [key] to return an existing [RetainScope] instance for, if one exists, or to
     *   create a new instance for
     * @return A [RetainScope] instance suitable to be installed as the [LocalRetainScope] for the
     *   child content with the specified [key]
     */
    public fun getOrCreateRetainScopeForChild(key: K): RetainScope {
        return childScopes.getOrPut(key) {
            ControlledRetainScope().apply {
                if (isParentKeepingExitedValues) startKeepingExitedValues()
            }
        }
    }

    /**
     * When a [RetainStateProvider] is set as the parent of a [FanOutRetainScopeProvider], the
     * [FanOutRetainScopeProvider] will mirror the retention state of the parent. If the parent
     * stops retaining, all children that have started retaining via [beginRetainChild] will
     * continue being retained after the parent stops retaining.
     *
     * If this function is called twice, the new parent will replace the old parent. The new
     * parent's state is immediately applied to the child scopes.
     *
     * To clear a parent, call this function and pass in either
     * [RetainStateProvider.AlwaysKeepExitedValues] or [RetainStateProvider.NeverKeepExitedValues]
     * depending on whether you want this scope to keep exited values in the absence of a parent.
     */
    public fun setParentRetainStateProvider(parent: RetainStateProvider) {
        val oldParent = parentScope
        parentScope = parent

        parent.addRetainStateObserver(parentObserver)
        oldParent.removeRetainStateObserver(parentObserver)

        setKeepExitedValues(parent.isKeepingExitedValues)
    }

    /**
     * Removes the [RetainScope] for the child with the given [key] from this
     * [FanOutRetainScopeProvider]. If the key doesn't have an associated [RetainScope] yet (either
     * because it hasn't been created or has already been cleared), this function does nothing.
     *
     * If the scope being cleared is currently keeping exited values, it will stop as a result of
     * this call. To ensure consistent behavior, the child with the given [key] should **not** be in
     * the composition hierarchy when clearing its key, otherwise the child may attempt to store
     * data in an orphaned retain scope that will never begin retaining in the future.
     *
     * If [getOrCreateRetainScopeForChild] is called again for the given [key], a new [RetainScope]
     * will be created and returned.
     *
     * @param key The key of the child content whose [RetainScope] should be discarded
     */
    public fun clearChild(key: K) {
        childScopes.remove(key)?.let { clearScope(it) }
    }

    /**
     * Bulk removes all child scopes for which the [predicate] returns true. This function follows
     * the same clearing rules as [clearChild].
     *
     * @param predicate The predicate to evaluate on all child keys in the
     *   [FanOutRetainScopeProvider]. If the predicate returns `true` for a given key, it will be
     *   cleared. If the predicate returns `false` it will remain in the collection.
     * @see clearChild
     */
    public fun clearChildren(predicate: (key: K) -> Boolean) {
        childScopes.removeIf { key, scope -> predicate(key).also { if (it) clearScope(scope) } }
    }

    private fun clearScope(scope: ControlledRetainScope) {
        while (scope.isKeepingExitedValues) scope.stopKeepingExitedValues()
    }

    private fun setKeepExitedValues(shouldRetain: Boolean) {
        if (shouldRetain == isParentKeepingExitedValues) return
        isParentKeepingExitedValues = shouldRetain

        if (shouldRetain) {
            childScopes.forEachValue { scope -> scope.startKeepingExitedValues() }
        } else {
            childScopes.forEachValue { scope -> scope.stopKeepingExitedValues() }
        }
    }

    public companion object {
        public const val DEFAULT_CAPACITY: Int = 6
    }
}
