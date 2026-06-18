# Module: inject-test

This is a Kotlin Multiplatform library module that provides test implementations for the dependency injection
framework.

## Purpose & Architecture

- This module contains test components and modules for the `kotlin-inject` and `kotlin-inject-anvil` dependency injection
  framework.
- It allows for writing tests that can provide fake implementations of dependencies, which is essential for
  isolating components under test.

## Usage

- When writing tests that require a dependency injection graph, use the test components and modules from this module
  to create a test-specific graph with the necessary test doubles.
