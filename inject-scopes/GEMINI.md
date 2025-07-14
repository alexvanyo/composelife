# Module: inject-scopes

This is a Kotlin Multiplatform library module that defines the dependency injection scopes for the application.

## Purpose & Architecture

- This module contains the annotations and components that define the different dependency injection scopes used
  throughout the application, such as `@ApplicationScope`, `@ActivityScope`, etc.
- It uses `kotlin-inject` and `kotlin-inject-anvil` to create a hierarchical dependency injection graph.

## Usage

- When creating a new component that needs to be injected, annotate it with the appropriate scope annotation from
  this module.
- This module is a core part of the application's dependency injection setup and is used in almost every other
  module.
