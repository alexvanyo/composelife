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
we can define an injectable context class that encapsulates each dependency, along with an `invoke`
operator:

```kotlin
@Inject
class InnerComposable(
    private val random: Random,
    private val clock: Clock,
) {
    @Composable
    operator fun invoke(
        modifier: Modifier = Modifier,
    ) {
        // use random, clock, and modifier
    }
}

context(ctx: InnerComposable)
@Composable
fun InnerComposable(modifier: Modifier = Modifier) =
    ctx(modifier)
```

We can then use that context class as the context parameter in the `OuterComposable` to call
`InnerComposable`, without having knowledge of what dependencies `InnerComposable` needs:

```kotlin
context(_: InnerComposable)
@Composable
fun OuterComposable() {
    InnerComposable() // InnerComposable passed as context parameter
}
```

By nesting these context classes, adding an additional dependency only changes a single
location. Additionally, since the dependencies are internal to the context objects, they don't "leak".
Outer functions can't see what the inner functions depend on.

The approach also takes an opinionated stance on how top-level functions are injected:
instead of allowing for _instances of a function_ to be directly injected, _instances of a
function's context_ are injected instead.

This preserves the composition of functions, and works nicely with how Compose's lifecycle of
function calls doesn't map 1:1 with the lifecycle of an injected object.

## Context Parameters Step 3: Automating with Metro and `di-compiler`

Manually writing the context classes and context function overloads above introduces substantial boilerplate.
This project automates the entire pattern using [Metro][metro] and a custom Kotlin compiler plugin,
[`di-compiler`][di_compiler].

Instead of writing the wrapper class and context functions by hand, top-level functions are annotated with
both `@InjectContext` and `@Inject`, marking any caller-supplied arguments with `@Assisted`:

```kotlin
@InjectContext
@Inject
@Composable
fun InnerComposable(
    random: Random,
    clock: Clock,
    @Assisted modifier: Modifier = Modifier,
) {
    // use random, clock, and modifier
}
```

Behind the scenes:
1. **Metro** generates an injectable class named `InnerComposable`. It receives `random` and `clock` from
   the Metro dependency graph, and provides `operator fun invoke(@Assisted modifier: Modifier = Modifier)`.
2. **`di-compiler`** (via Kotlin FIR and IR extensions) automatically generates the matching top-level context
   function:
   ```kotlin
   context(ctx: InnerComposable)
   @Composable
   fun InnerComposable(modifier: Modifier = Modifier) {
       ctx(modifier)
   }
   ```
   The plugin automatically generates overloads for assisted parameters with default values, preserves annotations
   from the original function (such as `@Composable`), and generates the IR body delegating directly to `ctx.invoke(...)`.

When composing components, the outer function simply declares dependencies on the generated context classes
as context parameters:

```kotlin
@InjectContext
@Inject
@Composable
context(_: InnerComposable)
fun OuterComposable(
    @Assisted modifier: Modifier = Modifier,
) {
    InnerComposable(modifier)
}
```

While demonstrated here with `@Composable` functions, the `@InjectContext` compiler plugin is completely general
and works with any top-level function that benefits from context-parameter-based dependency injection.

## Injecting with graphs

With the approach above, the scope of local context object can be governed by normal Compose state
mechanisms, where the dependency graphs are created and remembered with snapshot state.

For `@Preview`s, each of these context object can also be created directly with an appropriate
dependency graph as in `ui-app-screenshot-tests`'s [`PreviewCtx`][preview_ctx].

[//]: # (website links)

[context_parameters]: https://github.com/Kotlin/KEEP/blob/master/proposals/context-parameters.md
[metro]: https://github.com/ZacSweers/metro

[//]: # (relative links)

[di_compiler]: ../di-compiler/README.md
[preview_ctx]: ../ui-app-screenshot-tests/src/androidMain/kotlin/com/alexvanyo/composelife/ui/app/ctxs/PreviewCtx.kt
