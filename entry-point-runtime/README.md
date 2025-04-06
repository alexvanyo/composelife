# entry-point-runtime

A module defining an [`EntryPoint`](src/commonMain/kotlin/com/alexvanyo/composelife/entrypoint/EntryPoint.kt)
annotation for generating entry point implementations for dependency injection as an extension of
`kotlin-inject-anvil`, along with other utilities for retrieving entry points.

The associated required symbol processor is in
[entry-point-symbol-processor](../entry-point-symbol-processor).

## Usage

Entry points are interfaces whose properties are things that can be injected in a given scope.

Annotating such an interface with `@EntryPoint(MyScope::class)` will generate a concrete bound
implementation of the entry point, where all of the properties of the interface or its inherited
super-interfaces are bound via simple constructor injection.

For example,

```kotlin
interface MyInheritedInterface {
    val myInheritedDependency: MyInheritedDependency
}

@EntryPoint(AppScope::class)
interface MyEntryPoint : MyInheritedInterface {
    val myDependency: MyDependency
}
```

will generate

```kotlin
@Inject
@ContributesBinding(AppScope::class)
class MyEntryPointImpl(
    override val myDependency: MyDependency,
    override val myInheritedDependency: MyInheritedDependency // from MyInheritedInterface
) : MyEntryPoint
```

In addition, entry point accessors will be generated that allow retrieving an entry point from
the component for the given scope, that must implement `EntryPointProvider`.

```kotlin
@ContributesTo(AppScope::class)
interface MyEntryPointImplBindingComponent {
    @Provides
    @IntoMap
    @OptIn(InternalEntryPointProviderApi::class)
    fun providesMyEntryPointIntoEntryPointMap(
        entryPointCreator: () -> MyEntryPoint
    ): Pair<KClass<*>, ScopedEntryPoint<AppScope, *>> =
        MyEntryPoint::class to ScopedEntryPoint(entryPointCreator)
}

@OptIn(InternalEntryPointProviderApi::class)
inline fun <reified T : MyEntryPoint> EntryPointProvider<AppScope>.getEntryPoint(
    unused: KClass<T> = T::class
): MyEntryPoint = entryPoints.getValue(MyEntryPoint::class).entryPointCreator() as MyEntryPoint
```

This allows retrieving the entry point from the component safely using
`applicationComponent.getEntryPoint<MyEntryPoint>()`.
