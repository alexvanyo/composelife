# Dependency Injection

This project uses a combination of [kotlin-inject][kotlin_inject],
[kotlin-inject-anvil][kotlin_inject_anvil] and
[context parameters][context_parameters] to
implement dependency injection.

kotlin-inject and kotlin-inject-anvil are used to create a dependency graph of singleton and
`Activity`-scoped classes (data layer, preferences, and algorithm configuration).

These dependencies are then provided to UI components via context parameters with the approach
outlined below.

## Context Parameters Step 0

The most basic approach to provide a `@Composable` method a dependency is directly passing it as
an argument:

```kotlin
@Composable
fun InnerComposable(
    random: Random,
) {
    // use random
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

## Context Parameters Step 1

[Context parameters][context_parameters] are
an experimental feature that allow an additional way to pass parameters to methods by adding
additional context parameters to methods. These are also experimentally supported by
`@Composable` methods.

For example, passing the `Random` from before as a context parameter can be done like the following.

```kotlin
context(random: Random)
@Composable
fun InnerComposable() {
    // use methods and properties in Random
}

context(_: Random)
@Composable
fun OuterComposable() {
    InnerComposable() // Random is passed as a context parameter
}
```

This is an improvement, in that dependencies are passed down more transparently, and don't impact
the intermediate call sites.

However, each additional dependency still requires changing the declaration site:

```kotlin
context(random: Random, clock: Clock)
@Composable
fun InnerComposable() {
    // use methods and properties in Random and Clock
}

context(_: Random, _: Clock)
@Composable
fun OuterComposable() {
    InnerComposable() // Random and Clock are passed as context parameters
}
```

## Context Parameters Step 2

Instead of using the dependency directly as a context parameter, we can define a canonical `Provider`
interface for a dependency injected in this manner:

```kotlin
interface RandomProvider {
    val random: Random
}
```

We can then use that provider interface as the context parameter:

```kotlin
context(randomProvider: RandomProvider)
@Composable
fun InnerComposable() {
    randomProvider.random
}

context(_: RandomProvider)
@Composable
fun OuterComposable() {
    InnerComposable() // RandomProvider passed as context parameter
}
```

Each dependency would then have its own provider interface declared:

```kotlin
interface ClockProvider {
    val clock: Clock
}

context(randomProvider: RandomProvider, clockProvider: ClockProvider)
@Composable
fun InnerComposable() {
    randomProvider.random // from RandomProvider scope
    clockProvider.clock // from ClockProvider scope
}

context(_: RandomProvider, _: ClockProvider)
@Composable
fun OuterComposable() {
    InnerComposable() // RandomProvider and ClockProvider are passed as context parameters
}
```

Having a canonical provider interface for each dependency means that multiple components can
use the same interface type to request being injected with a particular dependency. Additionally,
using a provider interface specific to each dependency type (as opposed to using the Dagger
`Provider<T>` interface) keeps the naming to retrieve each dependency.

However, the declaration of each component in all layers has to change to inject a new dependency.

## Context Parameters Step 3

The next step is to collect these provider into a combined super-interface for each component.
I've termed these "entry-point" interfaces for a component, and are the name of the component
suffixed by `EntryPoint`. Each component that is capable of being injected gets one of these entry
point interfaces:

```kotlin
interface InnerComposableEntryPoint : RandomProvider

context(entryPoint: InnerComposableEntryPoint)
@Composable
fun InnerComposable() {
    entryPoint.random // from inherited RandomProvider scope
}

interface OuterComposableEntryPoint : InnerComposableEntryPoint

context(_: OuterComposableEntryPoint)
@Composable
fun OuterComposable() {
    InnerComposable() // InnerComposableEntryPoint passed as context parameter
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

context(entryPoint: InnerComposableEntryPoint)
@Composable
fun InnerComposable() {
    entryPoint.random // from inherited RandomProvider scope
    entryPoint.clock // from inherited ClockProvider scope
}

interface OuterComposableEntryPoint : InnerComposableEntryPoint

context(_: OuterComposableEntryPoint)
@Composable
fun OuterComposable() {
    InnerComposable() // InnerComposableEntryPoint passed as context parameter
}
```

Dependencies are still available in scope throughout the entire call stack, if a subcomponent
is depending on it. This is unfortunate, but is more a problem of explict-ness and convention
instead of correctness. This should be fixable with a lint check of some sort, where each
component should only use dependencies that are from directly inherited interfaces, and not the
transitively inherited interfaces.

## Context Parameters Step 4

The final step is providing the actual implementations for the entry points.

The project here creates a distinction between two types of dependencies:
- Injected, `Activity`-scoped dependencies
- Local scoped dependencies defined by Compose

These two sets of dependencies are then provided by two different entry points for each component:

```kotlin
interface InnerComposableInjectEntryPoint : RandomProvider, ClockProvider

interface InnerComposableLocalEntryPoint : LoadedComposeLifePreferencesProvider

context(injectEntryPoint: InnerComposableInjectEntryPoint, localEntryPoint: InnerComposableLocalEntryPoint)
@Composable
fun InnerComposable() {
    injectEntryPoint.random // from inherited RandomProvider scope
    injectEntryPoint.clock // from inherited ClockProvider scope
    localEntryPoint.preferences // from inherited LoadedComposeLifePreferencesProvider scope
}

interface OuterComposableInjectEntryPoint :
    InnerComposableInjectEntryPoint,
    ComposeLifePreferencesProvider

context(injectEntryPoint: OuterComposableInjectEntryPoint)
@Composable
fun OuterComposable() {
    val loadedPreferencesState = injectEntryPoint.composeLifePreferences.loadedPreferencesState
    
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
                // InnerComposableInjectEntryPoint passed as context parameter
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

For `@Preview`s, each of these entry points can also be implemented directly with appropriate
fakes or mock values, as in `ui-app`'s
[`PreviewEntryPoint`][preview_entry_point].

[//]: # (website links)

[context_parameters]: https://github.com/Kotlin/KEEP/blob/master/proposals/context-parameters.md
[kotlin_inject]: https://github.com/evant/kotlin-inject
[kotlin_inject_anvil]: https://github.com/amzn/kotlin-inject-anvil

[//]: # (relative links)

[preview_entry_point]: ../ui-app/src/androidMain/kotlin/com/alexvanyo/composelife/ui/app/entrypoints/PreviewEntryPoint.kt
