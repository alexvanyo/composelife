# Module: serialization

This is a Kotlin Multiplatform library module that provides centralized utilities for serialization and state restoration.

## Purpose & Architecture

- It contains helper functions and custom serializers for saving and restoring complex objects, especially Jetpack Compose state, across process death or configuration changes.
- It integrates with Compose's `Saver` mechanism to provide robust state restoration for serializable objects.

## Usage

- When you need to make a custom object `rememberSaveable` in Jetpack Compose, use the `Saver` utilities provided here. This ensures that UI state is preserved correctly.
