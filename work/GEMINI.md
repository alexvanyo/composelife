# Module: work

This module provides an abstraction over Android's WorkManager.

## Purpose & Architecture

- This is an Android-only library module.
- It likely provides an injectable interface for scheduling and managing background work using `androidx.work.WorkManager`.
- This allows for decoupling components from the static `WorkManager` instance, making them easier to test.
- It might also define specific `Worker` implementations for background tasks used in the app.

## Key Dependencies

- `androidx.work:work-runtime-ktx`: The core WorkManager library.
- `:inject-scopes`: For dependency injection.
