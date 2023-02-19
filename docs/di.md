# Dependency Injection

This project uses a combination of [Hilt](https://dagger.dev/hilt/) and
[context receivers](https://github.com/Kotlin/KEEP/blob/master/proposals/context-receivers.md) to
implement dependency injection.

Hilt is used to create a dependency graph of singleton and `Activity`-scoped classes (data layer,
preferences, and algorithm configuration).

These dependencies are then provided to UI components via context receivers with the approach
outlined below.

## Context Receivers Step 0

The most basic approach to provide a `@Composable` method a dependency is directly passing it as
an argument:

```kotlin
@Composable
fun InnerComposable(
    random: Random,
) {
    // use Logger
}

@Composable
fun OuterComposable(
    random: Random,
) {
    InnerComposable(
        random = random,
    )
}
```

This is the most explicit form of providing a dependency, but starts to scale poorly
for the usage of dependency injection. In particular, providing a long-lived dependency to a
`@Composable` method deep in the call hierarchy requires passing that dependency through all
intermediate layers. This has the downside that all intermediate layers are aware of this
dependency, even if it doesn't use it directly. For example, adding a new required dependency
requires changing the call sites and declaration sites of all intermediate layers:

```kotlin
@Composable
fun InnerComposable(
    random: Random,
    clock: Clock,
) {
    // use random
}

@Composable
fun OuterComposable(
    random: Random,
    clock: Clock,
) {
    InnerComposable(
        random = random,
        clock = clock,
    )
}
```

## Context Receivers Step 1

[Context receivers](https://github.com/Kotlin/KEEP/blob/master/proposals/context-receivers.md) are
an experimental feature that allow an additional way to pass parameters to methods by adding
additional receivers to methods. These are also experimentally supported by `@Composable` methods.

For example, passing the `Random` from before as a context receiver can be done like the following.

```kotlin
context(Random)
@Composable
fun InnerComposable() {
    // use methods and properties in Random
}

context(Random)
@Composable
fun OuterComposable() {
    InnerComposable() // Random is passed as a context receiver
}
```

This is an improvement, in that dependencies are passed down more transparently, and don't impact
the intermediate call sites.

However, each additional dependency still requires changing the declaration site:


```kotlin
context(Random, Clock)
@Composable
fun InnerComposable() {
    // use methods and properties in Random and Clock
}

context(Random, Clock)
@Composable
fun OuterComposable() {
    InnerComposable() // Random and Clock are passed as context receivers
}
```

One addition issue is that `Random` and `Clock` are both implicit `this` targets throughout the
call hierarchy, meaning that all layers have properties and methods of each dependency polluting
the call space, potentially resulting in erroneous methods or introducing unclear usages of
dependencies.

## Context Receivers Step 2

We can make one refinement to this second issue first.

Instead of using the dependency directly as a context receiver, we can define a canonical `Provider`
interface for a dependency injected in this manner:

```kotlin
interface RandomProvider {
    val random: Random
}
```

We can then use that provider interface as the context receiver:

```kotlin
context(RandomProvider)
@Composable
fun InnerComposable() {
    random // from RandomProvider scope
}

context(RandomProvider)
@Composable
fun OuterComposable() {
    InnerComposable() // RandomProvider passed as context receiver
}
```

Each dependency would then have its own provider interface declared:

```kotlin
interface ClockProvider {
    val clock: Clock
}

context(RandomProvider, ClockProvider)
@Composable
fun InnerComposable() {
    random // from RandomProvider scope
    clock // from ClockProvider scope
}

context(RandomProvider, ClockProvider)
@Composable
fun OuterComposable() {
    InnerComposable() // RandomProvider and ClockProvider are passed as context receivers
}
```

Having a canonical provider interface for each dependency means that multiple components can
use the same interface type to request being injected with a particular dependency. Additionally,
using a provider interface specific to each dependency type (as opposed to using the Dagger
`Provider<T>` interface) keeps the naming to retrieve each dependency.

This avoids polluting the call-space too much, as only the dependencies themselves are available.
However, they are still available throughout the entire call stack, and the declaration of each
component in all layers has to change to inject a new dependency.

## Context Receivers Step 3

The next step is to collect these provider into a combined super-interface for each component. Due
to their similarities (and potential use with Hilt's `@EntryPoint`), I've termed these
"entry-point" interfaces for a component, and are the name of the component suffixed by
`EntryPoint`. Each component that is capable of being injected gets one of these entry point
interfaces:

```kotlin
interface InnerComposableEntryPoint : RandomProvider

context(InnerComposableEntryPoint)
@Composable
fun InnerComposable() {
    random // from inherited RandomProvider scope
}

interface OuterComposableEntryPoint : InnerComposableEntryPoint

context(OuterComposableEntryPoint)
@Composable
fun OuterComposable() {
    InnerComposable() // InnerComposableEntryPoint passed as context receiver
}
```

This does not change the call-site usage at all, since the entry-point component interfaces
extend from the provider interfaces (meaning that the same properties of the provider interfaces
are still in scope).

However, this does change the declaration site: Now, each component only declares a combination
of its direct dependencies and any subcomponents it may call. This localizes the requirement
of knowing about dependencies to a particular component, and breaks the requirement that every
intermediate component changes in some way due to a new dependency introduced:

```kotlin
interface InnerComposableEntryPoint : RandomProvider, ClockProvider

context(InnerComposableEntryPoint)
@Composable
fun InnerComposable() {
    random // from inherited RandomProvider scope
    clock // from inherited ClockProvider scope
}

interface OuterComposableEntryPoint : InnerComposableEntryPoint

context(OuterComposableEntryPoint)
@Composable
fun OuterComposable() {
    InnerComposable() // InnerComposableEntryPoint passed as context receiver
}
```

Dependencies are still available in scope throughout the entire call stack, if a subcomponent
is depending on it. This is unfortunate, but is more a problem of explict-ness and convention
instead of correctness. This should be fixable with a lint check of some sort, where each
component should only use dependencies that are from directly inherited interfaces, and not the
transitively inherited interfaces.

## Context Receivers Step 4

The final step is providing the actual implementations for the entry points.

The project here creates a distinction between two types of dependencies:
- Hilt-provided, `Activity`-scoped dependencies
- Local scoped dependencies defined by Compose

These two sets of dependencies are then provided by two different entry points for each component:

```kotlin
@EntryPoint
@InstallIn(ActivityComponent::class)
interface InnerComposableHiltEntryPoint : RandomProvider, ClockProvider

interface InnerComposableLocalEntryPoint : LoadedComposeLifePreferencesProvider

context(InnerComposableHiltEntryPoint, InnerComposableLocalEntryPoint)
@Composable
fun InnerComposable() {
    random // from inherited RandomProvider scope
    clock // from inherited ClockProvider scope
    preferences // from inherited LoadedComposeLifePreferencesProvider scope
}

@EntryPoint
@InstallIn(ActivityComponent::class)
interface OuterComposableHiltEntryPoint :
    InnerComposableHiltEntryPoint,
    ComposeLifePreferencesProvider

context(OuterComposableHiltEntryPoint)
@Composable
fun OuterComposable() {
    val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
    
    when (loadedPreferencesState) {
        is ResourceState.Failure -> {
            // Error screen
        }
        ResourceState.Loading -> {
            CircularProgressIndicator()
        }
        is ResourceState.Success -> {
            with(
                remember(loadedPreferencesState) {
                    object : InnerComposableLocalEntryPoint {
                        override val preferences = loadedPreferencesState
                    }
                }
            ) {
                // InnerComposableHiltEntryPoint passed as context receiver
                // InnerComposableLocalEntryPoint created in-scope
                InnerComposable()
            }
        }
    }
}
```

With the approach above, the scope of local entry points is governed by normal Compose state
mechanisms, where the entry points are created and remembered with snapshot state.

This allows, as in the example above, creating a type-safe subcomponent where loaded preferences
are available, with the loading state handled by a higher-level component.

The Hilt-provided entry points are true Hilt `@EntryPoint`s, installed in the `ActivityComponent`.
In production code, only the outermost `***HiltEntryPoint` is injected inside the `Activity`,
but in tests each individual component can be injected directly to test a component in isolation.

For `@Preview`s, each of these entry points can also be implemented directly with appropriate
fakes or mock values, as in `ui-app`'s
[`PreviewEntryPoint`](ui-app/src/androidMain/kotlin/com/alexvanyo/composelife/ui/app/entrypoints/PreviewEntryPoint.kt).
