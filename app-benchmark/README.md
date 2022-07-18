# app-benchmark

A test module which runs performance benchmarks for [app](../app).

This is a separate module to facilitate only running benchmarks when specifically
enabled, by setting the Gradle property `com.alexvanyo.composelife.runBenchmarks` to
`true`. This setting exists since benchmarks can only be run on real devices.
