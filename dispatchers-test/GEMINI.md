# Module: dispatchers-test

This is a Kotlin Multiplatform library module that provides test implementations for the `:dispatchers` module.

## Purpose & Architecture

- This module contains a test implementation of the `ComposeLifeDispatchers` interface, which is useful for writing
  deterministic tests involving coroutines.
- It uses `kotlinx-coroutines-test` to provide a `TestDispatcher` that can control the execution of coroutines in
  tests.

## Usage

- When writing tests that involve components using `ComposeLifeDispatchers`, inject the test dispatcher from this
  module to control timing and ensure your tests are not flaky.
