# Module: entry-point-symbol-processor

This is a Kotlin Multiplatform library module that contains a KSP (Kotlin Symbol Processor) for the custom entry
point system as described in [entry-point-runtime/README.md](../entry-point-runtime/README.md).

## Purpose & Architecture

- This module is an annotation processor that generates code based on the entry point annotations defined in the
  `:entry-point-runtime` module.
- It uses KSP to inspect the source code for those annotations and generate the necessary boilerplate for the
  dependency injection framework.

## Usage

- This module is not used directly in the application code. Instead, it is applied as a KSP dependency in the
  `build.gradle.kts` files of modules that use the entry point system.
