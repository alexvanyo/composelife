# session-value-key

A utility library defining a value wrapper that indicates the value is associated with a particular
session.

## Generalized UDF-compliant asynchronous state management in Compose

The simplest state management in Compose is synchronous updates to snapshot state:

```kotlin
@Preview
@Composable
fun Example1() {
    var count by remember { mutableStateOf(0) }

    Button(
        onClick = { count++ },
    ) {
        Text("Count: $count")
    }
}
```

With this code, when the button is clicked, the `mutableStateOf` state holder backing `count`
is updated synchronously and incremented.

Let's now hoist `count` to an outer `@Composable`, and pass down `count` and `setCount`:

```kotlin
@Preview
@Composable
fun Example2() {
    var count by remember { mutableStateOf(0) }
    
    CountButton(
        count = count,
        setCount = { count = it },
    )
}

@Composable
fun CountButton(
    count: Int,
    setCount: (Int) -> Unit,
    modifier: Modifier = Modifier,
) {
    Button(
        onClick = {
            setCount(count + 1)
        },
    ) {
        Text("Count: $count")
    }
}
```

`Example1` will act the same as `Example2` under most cases.
However, there is an important assumption in this usage that `onClick` is called _at most once_
before `CountButton` has a chance to recompose.

The reason why this assumption is important is that while the update to `count` may be synchronous,
composition itself doesn't happen instantly.

This can be revealed if we change the code slightly:

```kotlin
@Preview
@Composable
fun Example3() {
    var count by remember { mutableStateOf(0) }

    Button(
        onClick = {
            count++
            count++
        },
    ) {
        Text("Count: $count")
    }
}

@Preview
@Composable
fun Example4() {
    var count by remember { mutableStateOf(0) }
    
    CountButton(
        count = count,
        setCount = { count = it },
    )
}

@Composable
fun CountButton(
    count: Int,
    setCount: (Int) -> Unit,
    modifier: Modifier = Modifier,
) {
    Button(
        onClick = {
            setCount(count + 1)
            setCount(count + 1)
        },
    ) {
        Text("Count: $count")
    }
}
```

`Example3` and `Example4` will now behave very differently in all situations.
`Example3` will increment `count` by 2 when the button is clicked, whereas `Example4` will increment
`count` by only 1.
The reason for this difference is that the `CountButton` uses the `count` that is captured when
composing `CountButton`.
Composition doesn't magically happen instantly after calling the first `setCount`, updating the
captured `count`, and allow the new count to be used when calling the second `setCount`.
Instead, `setCount(count + 1)` twice in a row.

`Example3` hides its behavior due to the usage of the property delegate syntax for reading and
writing `count`.
The following `Example5` is equivalent to `Example3`, with the syntax sugar removed:

```kotlin
@Preview
@Composable
fun Example5() {
    val countState = remember { mutableStateOf(0) }

    Button(
        onClick = {
            countState.value = countState.value + 1
            countState.value = countState.value + 1
        },
    ) {
        Text("Count: ${countState.value}")
    }
}
```

With the synatax sugar removed, it is more clear why `Example5` does increment by 2.
The backing snapshot state holder is updated synchronously, re-queried, and then updated again.

With the syntax sugar removed, it's possible to change this slightly to get back to the behavior
we see in `Example4` where clicking the button will only increment `count` by 1:

```kotlin
@Preview
@Composable
fun Example6() {
    val countState = remember { mutableStateOf(0) }

    val count = countState.value
    
    Button(
        onClick = {
            countState.value = count + 1
            countState.value = count + 1
        },
    ) {
        Text("Count: $count")
    }
}
```

Now, even without calling into a different `@Composable`, we can see the behavior difference
caused by capturing a value of `count` in composition, and then referring to that captured value
upon the button being clicked.

Again, `count` won't magically reflect the backing snapshot state instantly in time for the second 
`countState.value` call.
The cached value is used instead.

Let's go back to the idea of "synchronicity", and a straightforward hoisting in `Example7` of a
value for a `Slider`:

```kotlin
@Preview
@Composable
fun Example7() {
    var value by remember { mutableStateOf(0f) }
    
    MySlider(
        value = value,
        onValueChange = { value = it },
    )
}

@Composable
fun MySlider(
    value: Float,
    onValueChange: (Float) -> Unit,
    modifier: Modifier = Modifier,
) {
    Slider(
        value = value,
        onValueChange = onValueChange,
        modifier = modifier,
    )
}
```

We've learned that `value` pass to `MySlider` doesn't happen instantaneously, but this still works
fine with `Slider` - it's still as synchronous as it needs to be from the perspective of
composition.

The state update isn't reflected immediately, but it will be reflected in the next composition.
And, a new composition will happen because `value` is backed by snapshot state and its value
is read in composition.

Let's now introduce some asynchronicity.
Instead of applying the value change immediately, let's delay updating the backing snapshot state
by just a bit:

```kotlin
@Preview
@Composable
fun Example7() {
    val updateChannel = Channel<Float>(Channel.CONFLATED)
    val value by produceState(0f) {
        updateChannel
            .receiveAsFlow()
            .collect {
                delay(50)
                value = it
            }
    }

    MySlider(
        value = value,
        onValueChange = { updateChannel.trySend(it) },
    )
}

@Composable
fun MySlider(
    value: Float,
    onValueChange: (Float) -> Unit,
    modifier: Modifier = Modifier,
) {
    Slider(
        value = value,
        onValueChange = onValueChange,
        modifier = modifier,
    )
}
```

If you run this on a device and interact with it, the problem should be apparent quickly:
It feels like the `Slider` is completely broken!
But, this approach satisfies unidirectional data flow.
We still have a single source of truth for what the value is as represented in the UI after hoisting
it.
So why is this not working well?

`Slider` expects that the `onValueChange` will synchronously update whichever state is ultimately
giving `value` to `Slider` in composition.
Per the principles of state hoisting, `Slider` doesn't care exactly where this is being kept.
It could be in a plain `mutableStateOf` state holder, it could be part of a `data class`, or
derived from some other calculation, if `onValueChange` also changes that calculation.

But `Slider` behaves strangely if this expectation isn't met.

The simplest solution is to keep state changes synchronous.
Common ways to introduce asynchronicity is to globally debounce inputs, or feed state through
`Flow`s or other observable streams that can't guarantee that an update will be reflected in the
next composition.

If this sounds familiar, `Slider` isn't unique in this regard.
`TextField` is another component that cares strongly about its state being updated synchronously,
even if hoisted.
This requirement is one of the reasons why the `TextField` state handling is being reworked
in `BasicTextField2`.

However, there are real cases where the state changes can't be synchronous.
If this `Slider` is a representation of a preference that is being saved to disk, disk access
is by nature synchronous.

This initially seems like an impossible task while preserving the principles of unidirectional
data flow: asynchronous state handling with a single source of truth will lead to buggy behavior,
but keeping a synchronous piece of state is resulting in a different source of truth of state
than the asynchronous data source.

This is a tricky problem, but it isn't an impossible one.
The important insight is that in these situations while we do have to have two sets of state, these
two sources of state represent tangibly different things.
We don't violate a single source of truth principle, because our sources of truth represent
different (but related) pieces of state.

Through careful handling of how these pieces of state interact, we can create a good experience
even when asynchronicity is involved.

Let's create a simple data source for state that is asynchronous:

```kotlin
interface ProbabilityInfo {
   val probabilityState: StateFlow<Float>
   
   fun updateProbability(value: Float)
}
```

And let's create a piece of UI with a `Slider` to modify this state:

```kotlin
@Composable
fun Example8(
    probabilityInfo: ProbabilityInfo
) {
    val probability by probabilityInfo.probabilityState.collectAsState()
 
    MySlider(
        value = probability,
        onValueChange = { probabilityInfo.updateProbability(it) }
    )
}

@Composable
fun MySlider(
    value: Float,
    onValueChange: (Float) -> Unit,
    modifier: Modifier = Modifier,
) {
    Slider(
        value = value,
        onValueChange = onValueChange,
        modifier = modifier,
    )
}
```

Similar to `Example7`, this may not work well in the general case since `probabilityState`
will be updating asynchronously from the `Slider`.

We can avoid this by creating a new, distinct source of truth for a local value of `Slider`.
I'm calling this a "local" editing session for the value, since the value in the UI may not
reflect the value on disk.

The simplest way to do this is with a confirm and cancel pair of buttons that will update the 
asynchronous state:

```kotlin
@Composable
fun Example8(
    probabilityInfo: ProbabilityInfo
) {
    val asyncProbability by probabilityInfo.probabilityState.collectAsState()
 
    val localProbability by rememberSaveable { mutableStateOf(asyncProbability) }
    
    Column {
        MySlider(
            value = localProbability,
            onValueChange = {
                localProbability = it
            }
        )

        Button(
            onClick = {
                localProbability = asyncProbability
            },
            enabled = asyncProbability != localProbability
        ) {
            Text("Cancel")
        }
        Button(
            onClick = {
                probabilityInfo.updateProbability(localProbability)
            },
            enabled = asyncProbability != localProbability
        ) {
            Text("Confirm")
        }
    }
}

@Composable
fun MySlider(
    value: Float,
    onValueChange: (Float) -> Unit,
    modifier: Modifier = Modifier,
) {
    Slider(
        value = value,
        onValueChange = onValueChange,
        modifier = modifier,
    )
}
```

This works alright, but has a few drawbacks:
- It doesn't show the current state on disk. If the probability on disk changes while this UI is
  visible, the user has no way to know.
- It requires an explicit user interaction to save the state although this might be desirable in some
  situations, if the change is important enough to warrant explicit confirmation.
- There isn't feedback when the change is confirmed, but before it is asynchronously updated.

An alternative would be to update the asynchronous state upon every change in the UI:

```kotlin
@Composable
fun Example9(
    probabilityInfo: ProbabilityInfo
) {
    val asyncProbability by probabilityInfo.probabilityState.collectAsState()
 
    val localProbability by rememberSaveable { mutableStateOf(asyncProbability) }
    
    MySlider(
        value = localProbability,
        onValueChange = {
            localProbability = it
            probabilityInfo.updateProbability(localProbability)
        }
    )
}

@Composable
fun MySlider(
    value: Float,
    onValueChange: (Float) -> Unit,
    modifier: Modifier = Modifier,
) {
    Slider(
        value = value,
        onValueChange = onValueChange,
        modifier = modifier,
    )
}
```

This also works alright, but still has drawbacks:
- It doesn't show the current state on disk either. If the probability on disk changes while this
  UI is visible, the user has no way to know.
- There isn't feedback when the change is confirmed, but before it is asynchronously updated.

Because the asynchronous state can lag behind when the state is set an arbitrarily long time, it is
hard to directly solve these issues without adding additional information.

The two pieces of additional information that we can use is a "session id" and a "value id",
both of which are bundled with the value into a `SessionValue`:

```kotlin
data class SessionValue<out T>(
    val sessionId: UUID,
    val valueId: UUID,
    val value: T,
)
```

The `sessionId` uniquely identifies the session that was used to update the value.
A session can be an ongoing set of updates, or a one-shot update with a UUID that won't be used
again.

The `valueId` uniquely identifies a specific update of `value` within a session.
This allows distinguishing between two updates that have the same `value`, but occurred at different
times, potentially with a different `value` update in-between.

Storing and using these ids allows distinguishing between situations like:
- Is this change a previous one the local session requested, but not necessarily the most recent
  one requested?
- Did a different local session update the value separately, and therefore the local session
  is invalidated?
- Did a different local session update the value separately, and therefore a "compare and set" to
  update the value should fail to update?
- Has the asynchronous source reported the most recently set value?

The general flow for updating this value is:

- The asynchronous value contains the current value, and the id for the previous session.
  For the initial value, a random UUID can be used to represent a one-shot "session" that
  initialized the value.
- UI that could update the session initializes itself to the asynchronous value, and prepares
  itself to update the value if the user starts changing the value.
- Once the user starts changing the value, the id for this local session becomes the current
  session.
- This will invalidate all sessions other than the local session, which will be able to
  synchronously update the local value while safely ignoring updates from the asynchronous state,
  because they are asynchronous reflections of the local session.

To achieve this gracefully in Compose code, we need one more tool: a way to "upgrade" a key from
the previous session, to the new local session.
We can achieve this with an `UpgradableSessionKey`:

```kotlin
/**
 * An upgradable key made of [UUID]s.
 *
 * A [UpgradableSessionKey] is equal to another [UpgradableSessionKey] if any of the [UUID]s used to
 * construct this [UpgradableSessionKey] match any of the [UUID]s used to construct the other
 * [UpgradableSessionKey].
 */
class UpgradableSessionKey {
    constructor(
        a: UUID,
    )
    constructor(
        a: UUID,
        b: UUID,
    )
}
```

This allows directly encoding our session logic into `remember` and `key` functions in Compose,
which rely on `equals` to decide whether to re-initialize state explicitly or implicitly.

Using both of these tools, we can update our `SessionValueProbabilityInfo` interface and both the
confirmation case, and the continuous case:

```kotlin
interface SessionValueProbabilityInfo {
   val probabilityState: StateFlow<SessionValue<Float>>

  /**
   * Updates the probability info in a compare-and-set manner.
   * 
   * The [oldSessionId] should be the previous session id currently stored for the probability
   * info, or `null`.
   * 
   * If [oldSessionId] is null, or the current session id matches [oldSessionId] or [newSessionId],
   * then the update will go through.
   *
   * If [oldSessionId] is non-null, and the current session id is different from [oldSessionId] and
   * [newSessionId], then the update will not go through.
   * 
   * If the update succeeds, then the value will be updated, and the session id will be set to
   * [newSessionId]. [oldSessionId] and [newSessionId] can be the same, for instance if the same
   * local session is updating the probability value repeatedly.
   */
  fun updateProbability(oldSessionId: UUID?, newSessionId: UUID, value: Float)
}
```

```kotlin
@Composable
fun Example10(
    probabilityInfo: ProbabilityInfo
) {
    val asyncProbabilitySessionValue by probabilityInfo.probabilityState.collectAsState()

    val oldSessionId = asyncProbabilitySessionValue.id
    val nextSessionId = remember(oldSessionId) { UUID.randomUUID() }
    val upgradableSessionKey = UpgradableSessionKey(oldSessionId, nextSessionId)
    val currentSessionId = remember(upgradableSessionKey) { nextSessionId }

    /**
     * The local source of truth for the probability.
     * This is initialized to the asynchronously-updated value, and is reset to the
     * asynchronously-updated value if the session changes to anything other than
     * [currentSessionId].
     */
    val localProbability by rememberSaveable(upgradableSessionKey) {
        mutableStateOf(asyncProbabilitySessionValue.value)
    }

    var mostRecentlyUpdatedValueId: UUID? by remember(currentSessionId) {
        mutableStateOf(null)
    }
  
    /**
     * Enable the buttons if we haven't updated the value yet and the local value is different,
     * or we have updated the value, we see the most recent update in the asynchronous state,
     * and the value is different than the local one.
     */
    val enableButtons =
        (mostRecentlyUpdatedValueId == null &&
            asyncProbabilitySessionValue.value != localProbability) ||
                (asyncProbabilitySessionValue.valueId == mostRecentlyUpdatedValueId &&
                      asyncProbabilitySessionValue.value != localProbability)
    
    Column {
        MySlider(
            value = localProbability,
            onValueChange = {
                localProbability = it
            }
        )

        Button(
            onClick = {
                localProbability = asyncProbabilitySessionValue.value
            },
            enabled = enableButtons
        ) {
            Text("Cancel")
        }
        Button(
            onClick = {
                val valueId = UUID.randomUUID()
                mostRecentlyUpdatedValueId = valueId
                probabilityInfo.updateProbability(
                  oldSessionId = oldSessionId,
                  newSessionId = currentSessionId,
                  valueId = valueId,
                  value = localProbability,
                )
            },
            enabled = enableButtons
        ) {
            Text("Confirm")
        }
    }
}

@Composable
fun MySlider(
    value: Float,
    onValueChange: (Float) -> Unit,
    modifier: Modifier = Modifier,
) {
    Slider(
        value = value,
        onValueChange = onValueChange,
        modifier = modifier,
    )
}
```

```kotlin
@Composable
fun Example11(
    probabilityInfo: ProbabilityInfo
) {
    val asyncProbabilitySessionValue by probabilityInfo.probabilityState.collectAsState()
  
    val oldSessionId = asyncProbabilitySessionValue.id
    val nextSessionId = remember(oldSessionId) { UUID.randomUUID() }
    val upgradableSessionKey = UpgradableSessionKey(oldSessionId, nextSessionId)
    val currentSessionId = remember(upgradableSessionKey) { nextSessionId }

    /**
     * The local source of truth for the probability.
     * This is initialized to the asynchronously-updated value, and is reset to the
     * asynchronously-updated value if the session changes to anything other than
     * [currentSessionId].
     */
    val localProbability by rememberSaveable(upgradableSessionKey) {
        mutableStateOf(asyncProbabilitySessionValue.value)
    }

    var mostRecentlyUpdatedValueId: UUID? by remember(currentSessionId) {
        mutableStateOf(null)
    }
  
    MySlider(
        value = localProbability,
        onValueChange = {
            localProbability = it
            val valueId = UUID.randomUUID()
            mostRecentlyUpdatedValueId = valueId
            probabilityInfo.updateProbability(
                oldSessionId = oldSessionId,
                newSessionId = currentSessionId,
                valueId = valueId,
                value = localProbability,
            )
        }
    )
}

@Composable
fun MySlider(
    value: Float,
    onValueChange: (Float) -> Unit,
    modifier: Modifier = Modifier,
) {
    Slider(
        value = value,
        onValueChange = onValueChange,
        modifier = modifier,
    )
}
```
