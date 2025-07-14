# Module: work-test

This module provides test implementations and helpers for the `:work` module.

## Purpose & Architecture

- This is an Android-only library module.
- It provides test helpers for `androidx.work.WorkManager`, allowing for synchronous and deterministic testing of background `Worker`s.
- It enables testing of the application's background processing logic without needing to run it on a real device or emulator.

## Key Dependencies

- `:work`: The module being tested.
- `androidx.work:work-testing`: The testing library for WorkManager.
- `:dispatchers-test`: To provide test dispatchers for coroutine-based workers.
