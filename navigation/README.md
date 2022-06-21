# navigation

A library implementing navigation in a stateful way.

A [`NavigationEntry`](src/main/kotlin/com/alexvanyo/composelife/navigation/NavigationEntry.kt) is
a specific instance of being at a particular destination that can be returned to, uniquely
identified by its `id`.

A [`NavigationState`](src/main/kotlin/com/alexvanyo/composelife/navigation/NavigationState.kt) is
a map of all `NavigationEntry`s that could be returned to in the future, and a pointer to the
current `NavigationEntry`. (Implication: the `entryMap` can never be empty, since there must
always be a current destination)

A [`NavigationHost`](src/main/kotlin/com/alexvanyo/composelife/navigation/NavigationHost.kt) only
needs a `NavigationState` to render a particular instance of navigation, with rendering and
and animations between different destinations based on the current `NavigationEntry`.
The `NavigationHost` retains state for all entries that are in the `entryMap`, and will remove
the state only when the entries are finally removed from the `entryMap`.

This setup keeps the `NavigationHost` unaware from the precise implementation of how the
`NavigationState` is modified and changed.

The main built-in method is via a backstack, with a
[`BackstackEntry`](src/main/kotlin/com/alexvanyo/composelife/navigation/BackstackEntry.kt) as an
implementation of `NavigationEntry` that exists in a `BackstackEntry`.
The backstack is kept as a linked list, with the `BackstackEntry` having a reference to the previous
`BackstackEntry`, if any. Each `BackstackEntry` also can contain a typed, arbitrary value, which
can be a state or state holder defining that destination.

Similarly, the
[`BackstackState`](src/main/kotlin/com/alexvanyo/composelife/navigation/BackstackState.kt) is an
implementation of `NavigationState` that describes a collection of all `BackstackEntry`s.
Importantly, the `BackstackState` must be saved to instance state in such a way that it is possible
to reconstructed the linked list of `BackstackEntry`s.

This setup allows (and guarantees) constructing a `BackstackEntry` and its value with the previous
entry, which allows hard references backwards in the stack, meaning that entries can directly call
methods, read state, and otherwise delegate work to previous `BackstackEntry`s.

Finally, a
[`MutableBackstackNavigationController`](src/main/kotlin/com/alexvanyo/composelife/navigation/MutableBackstackNavigationController.kt)
is a canonical implementation of a controller for a mutable `BackstackState`, where the map of
entries and pointer to the current entries can be modified by common `navigate`, `popBackstack`,
and similar utilities.
