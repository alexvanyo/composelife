# Module: do-not-keep-process

This is a Kotlin Multiplatform library module that helps simulate process death during development.

## Purpose & Architecture

- This module provides functionality to manually kill the process when backgrounded if this debug
  feature is enabled. This is useful for testing an app's ability to handle process death and state
  restoration.

## Usage

- This module is primarily a developer tool.
