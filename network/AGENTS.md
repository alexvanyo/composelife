# Module: network

This is a Kotlin Multiplatform library module responsible for all networking operations.

## Purpose & Architecture

- This module uses the **Ktor** client library to make HTTP requests.
- It provides a pre-configured `HttpClient` instance that is shared across the application.
- The configuration likely includes things like logging, content negotiation (e.g., for JSON), and setting up the OkHttp engine.
- It defines repository interfaces for any remote data sources.

## Usage

- When you need to make a network request, you should use the `HttpClient` provided by this module.
- This ensures all requests use the same configuration and middleware.
- The actual repository implementations that use this client are in the `:data` module.
