![CI](https://github.com/alexvanyo/composelife/actions/workflows/ci.yml/badge.svg)
[![codecov](https://codecov.io/gh/alexvanyo/composelife/branch/main/graph/badge.svg?token=z7yP8Z8xqC)](https://codecov.io/gh/alexvanyo/composelife)

# composelife

**This is not an official Google product**

composelife is a work-in-progress [Game of Life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life) simulator Android app.

This project is a personal sandbox of sorts, experimenting with the latest libraries and tools. These include:

- Written in [Kotlin](https://kotlinlang.org/)
- UI written in [Jetpack Compose](https://developer.android.com/jetpack/compose)
- Dependency injection using [Hilt](https://dagger.dev/hilt/)
- Fully functional CI system with Github Actions with:
  - JVM tests
  - [Robolectric](http://robolectric.org/) tests
  - Integration tests (minification with the help of [Keeper](https://slackhq.github.io/keeper/))
  - Linting, with android/lint and [detekt](https://detekt.dev/)
  - Code coverage with Jacoco (reporting done with [Codecov](https://about.codecov.io/)
  - Automatic dependency updates with [Renovate](https://docs.renovatebot.com/)

## Setup

Download the latest (canary) version of Android Studio.

Clone the project, and build! (no API keys or other setup necessary)

## License

```
Copyright 2022 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
```
