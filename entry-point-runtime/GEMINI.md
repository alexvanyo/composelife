# Module: entry-point-runtime

This is a Kotlin Multiplatform library module that defines the runtime components for a custom entry point system,
as described in [README.md](README.md).

## Purpose & Architecture

- This module contains the runtime annotations and interfaces needed for defining entry points in the application.
- It is part of a custom dependency injection setup, working with `kotlin-inject` and `kotlin-inject-anvil`.
- The `entry-point-symbol-processor` module is the `ksp` annotation processor that generates code based on the
  annotations in this module.

## Usage

- Annotate classes or interfaces with the entry point annotations defined in this module to have them processed by the
  accompanying symbol processor, which will generate the necessary boilerplate for dependency injection.
