# Module: parameterized-string

This module provides a utility for creating and using parameterized strings.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module that provides a data structure for representing a string with named placeholders, which can be formatted with a list of arguments.
- This is particularly useful for creating localizable strings where the order of placeholders might change between languages.
- It is built with Jetpack Compose in mind, and the `ParameterizedString` object is designed to be `rememberSaveable`, allowing it to be preserved across configuration changes.
- The module targets both Android and Desktop platforms.

## Usage

- Use `ParameterizedString` when you need to define a string with dynamic parts, especially for UI text that needs to be translated.

## Key Dependencies

- `org.jetbrains.compose.runtime`: For Jetpack Compose integration.
- `org.jetbrains.compose.runtime.saveable`: To allow the `ParameterizedString` to be saved and restored.
- `:serialization`: For custom serialization of the `ParameterizedString` object.
