# Module: updatable

This module provides a mechanism for creating updatable values by defining a simple `Updatable` interface for components that can perform ongoing, long-running work.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- It defines the `Updatable` interface:
  ```kotlin
  interface Updatable {
      suspend fun update(): Nothing
  }
  ```
- Any component that needs to run continuously in the background (e.g., database drivers, state sync, cache cleaners, or simulation loops) implements this interface.
- Because `update()` returns `Nothing`, the implementation is expected to run indefinitely (usually via a loop or collecting flow changes) until the coroutine scope in which it is launched is cancelled.

## Normal Usage

1. **Implement `Updatable`**:
   Implement the interface in your service or repository:
   ```kotlin
   class MyFeatureSync(
       private val repository: MyRepository,
   ) : Updatable {
       override suspend fun update(): Nothing {
           repository.flowOfUpdates.collect { update ->
               // Perform ongoing background updates
           }
       }
   }
   ```

2. **Bind into the DI Graph**:
   Bind the implementation to the dependency injection graph (using `metro`) contributing it to the set of updatables:
   - **`appUpdatables`**: For background work tied to the application's process lifecycle.
   - **`uiUpdatables`**: For background work tied to the UI/Activity lifecycle.

3. **Execution**:
   The application framework automatically launches and runs all bound `Updatable` instances concurrently in their respective lifecycle scope.
