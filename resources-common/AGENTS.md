# Module: resources-common

This module contains common Android resources shared across all Android targets.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module that holds the base set of resources for the entire project.
- It is intended for resources that are used across all form factors, including mobile and Wear OS.
- This module should only contain truly global assets, such as common strings, colors, or icons.

## Usage

- Other resource modules (like `:resources-app` and `:resources-wear`) depend on this module to access the common resources.
- Place resources here only if they are needed on all form factors. For form-factor-specific resources, use the more specialized resource modules.
