# Dependency Injection

This project uses a combination of [Metro][metro] and
[context parameters][context_parameters] to
implement dependency injection.

Metro is used to create dependency graphs for various scoped components.

These dependencies are then provided to UI components via context parameters with the approach
outlined below.

## Context Parameters Step 0

The most basic approach to provide a `@Composable` method a dependency is directly passing it as
an argument:

```kotlin
@Composable
fun InnerComposable(
    random: Random,
    modifier: Modifier = Modifier,
) {
    // use random
}

@Composable
fun OuterComposable(
    random: Random,
    modifier: Modifier = Modifier,
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
    modifier: Modifier = Modifier,
) {
    // use random
}

@Composable
fun OuterComposable(
    random: Random,
    clock: Clock,
    modifier: Modifier = Modifier,
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
fun InnerComposable(modifier: Modifier = Modifier) {
    // use methods and properties in Random and Clock
}

context(_: Random, _: Clock)
@Composable
fun OuterComposable(modifier: Modifier = Modifier) {
    InnerComposable() // Random and Clock are passed as context parameters
}
```

## Context Parameters Step 2

Instead of expecting callers to have the dependency directly available as a context parameter,
we can define an injectable `Ctx` class that contains each dependency, along with helper methods
to extract these dependencies:

```kotlin
// region templated-ctx
@Inject
class InnerComposableCtx internal constructor(
    private val random: Random,
    private val clock: Clock,
) {
    @Composable
    operator fun invoke(
        modifier: Modifier = Modifier,
    ) = lambda(random, clock, modifier)

    companion object {
        private val lambda:
            @Composable context(Random, Clock) (
                modifier: Modifier,
            ) -> Unit =
            { modifier ->
                InnerComposable(modifier)
            }
    }
}

context(ctx: InnerComposableCtx)
@Composable
fun InnerComposable(modifier: Modifier = Modifier) =
    ctx(modifier)
// endregion templated-ctx

context(random: Random, clock: Clock)
@Composable
private fun InnerComposable(modifier: Modifier = Modifier) {
    // use methods and properties in Random and Clock
}
```

We can then use that context class as the context parameter in the `OuterComposable` to call the
`InnerComposable`, without having knowledge of what dependencies `InnerComposable` needs:

```kotlin
context(_: InnerComposableCtx)
@Composable
fun OuterComposable() {
    InnerComposable() // InnerComposableCtx passed as context parameter
}
```

We can also nest these `Ctx` classes, by injecting the inner component `Ctx` in an outer component
`Ctx` in a similar way:

```kotlin
// region templated-ctx
@Inject
class OuterComposableCtx internal constructor(
    private val innerComposableCtx: InnerComposableCtx,
) {
    @Composable
    operator fun invoke(
        modifier: Modifier = Modifier,
    ) = lambda(random, clock, modifier)

    companion object {
        private val lambda:
            @Composable context(InnerComposableCtx) (
                modifier: Modifier,
            ) -> Unit =
            { modifier ->
                OuterComposable(modifier)
            }
    }
}

context(ctx: OuterComposableCtx)
@Composable
fun OuterComposable(modifier: Modifier = Modifier) =
    ctx(modifier)
// endregion templated-ctx

context(_: InnerComposableCtx)
@Composable
private fun OuterComposable(modifier: Modifier = Modifier) {
    InnerComposable() // InnerComposableCtx passed as context parameter
}
```

By nesting these `Ctx` classes, adding an additional dependency only changes a single `Ctx`
location. Additionally, since the dependencies are internal to the `Ctx` objects, they don't "leak".
Outer functions can't see what the inner functions depend on.

The approach also takes a more opinionated stance on how top-level functions are injected:
instead of allowing for _instances of a function_ to be directly injected, _instances of a
function's context_ are injected instead.

This preserves the composition of functions, and works nicely with how Compose's lifecycle of
function calls doesn't map 1:1 with the lifecycle of an injected object.

## Context Parameters Step 3

The regions in the snippets above are theoretically generatable, as the context objects are derived
from the signature of the implementation functions in an assisted injection manner.
Currently however, Metro doesn't support injecting context parameters, and KSP doesn't support
reading context parameters, so in this project this templated regions are explicitly written out.

## Injecting with graphs

With the approach above, the scope of local context object can be governed by normal Compose state
mechanisms, where the dependency graphs are created and remembered with snapshot state.

For `@Preview`s, each of these context object can also be created directly with an appropriate
dependency graph as in `ui-app-screenshot-tests`'s [`PreviewCtx`][preview_ctx].

[//]: # (website links)

[context_parameters]: https://github.com/Kotlin/KEEP/blob/master/proposals/context-parameters.md
[metro]: https://github.com/ZacSweers/metro

[//]: # (relative links)

[preview_ctx]: ../ui-app-screenshot-tests/src/androidMain/kotlin/com/alexvanyo/composelife/ui/app/ctxs/PreviewCtx.kt
