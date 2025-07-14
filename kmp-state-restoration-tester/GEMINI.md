# Module: kmp-state-restoration-tester

This is a Kotlin Multiplatform library module that provides utilities for testing state restoration in a
platform-agnostic way.

## Purpose & Architecture

- This module contains helpers and test utilities for verifying that state is correctly saved and restored across
  process death or other configuration changes.
- It is built on top of Jetpack Compose's `runtime-saveable` and Circuit's `retained` artifacts.

## Usage

- When writing tests for components that use `rememberSaveable` or other state restoration mechanisms, use the
  utilities in this module to simulate state being saved and restored, and to assert that the state is restored
  correctly.
