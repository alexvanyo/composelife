![CI][ci_badge]
[![codecov][codecov_badge]][codecov_project]

![Icon][icon]

# ComposeLife

**This is not an official Google product**

ComposeLife is a
work-in-progress [Game of Life][wikipedia_gameoflife] simulator
multiplatform app.

This project is a personal sandbox of sorts, experimenting with the latest libraries and tools.
These include:

- Written in [Kotlin][kotlin]
- UI written in [Jetpack Compose][jetpack_compose]
  - Mobile Android app and desktop app for exploring Game of Life patterns.
  - Watchface for Wear OS with configuration
  - Custom [adaptive navigation library][navigation]
- [Dependency injection][dependency-injection] using [kotlin-inject][kotlin_inject] and [context receivers][context_receivers]
- [AGSL][agsl], [OpenGL](https://developer.android.com/develop/ui/views/graphics/opengl/about-opengl) and [SKSL][sksl] rendering
- Fully functional CI system with GitHub Actions with:
    - Comprehensive automated tests
      - Hierarchical KMP tests shared across platforms
      - Shared [Robolectric][robolectric] and instrumentation tests
      - Minified instrumentation tests with the help of [Keeper][keeper], memory leak checking with [LeakCanary][leakcanary])
      - Screenshot tests with [Roborazzi][roborazzi] with automatic updates on CI
      - Code coverage with [JaCoCo][jacoco] (reporting done with [Codecov][codecov])
    - Linting, with android/lint and [detekt][detekt] with automatic updates on CI
    - Automatic dependency updates with [Renovate][renovate]
    - Automatic [baseline profile][baseline_profiles] generation

## Setup

Requirements:
- Android Studio Meerkat 2024.3.1
- JDK 21+

Clone the project, and build! (no API keys or other setup necessary)

## Runnable Modules

[app][app] contains the mobile app simulator for running, editing, and exploring Game of Life
patterns.

[desktop-app][desktop-app] contains the desktop app simulator for running, editing, and exploring Game of Life
patterns.

[wear][wear] contains a Game of Life watchface, with a stable pattern displaying the time with a
surrounding random soup potentially destroying it while the watchface is active.

![Round Watchface][watchface]

## License

```
Copyright 2022 The Android Open Source Project

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

[//]: # (website links)

[agsl]: https://developer.android.com/develop/ui/views/graphics/agsl
[baseline_profiles]: https://developer.android.com/topic/performance/baselineprofiles
[ci_badge]: https://github.com/alexvanyo/composelife/actions/workflows/ci.yml/badge.svg
[codecov]: https://about.codecov.io/
[codecov_badge]: https://codecov.io/gh/alexvanyo/composelife/branch/main/graph/badge.svg?token=z7yP8Z8xqC
[codecov_project]: https://codecov.io/gh/alexvanyo/composelife
[context_receivers]: https://github.com/Kotlin/KEEP/blob/master/proposals/context-receivers.md
[detekt]: https://detekt.dev/
[icon]: app/src/androidMain/ic_launcher-playstore.png
[jacoco]: https://github.com/jacoco/jacoco
[jetpack_compose]: https://developer.android.com/jetpack/compose
[keeper]: https://slackhq.github.io/keeper/
[kotlin]: https://kotlinlang.org/
[kotlin_inject]: https://github.com/evant/kotlin-inject
[leakcanary]: https://square.github.io/leakcanary/
[opengl]: https://developer.android.com/develop/ui/views/graphics/opengl/about-opengl
[renovate]: https://docs.renovatebot.com/
[robolectric]: https://robolectric.org/
[roborazzi]: https://github.com/takahirom/roborazzi/
[sksl]: https://skia.org/docs/user/sksl/
[wikipedia_gameoflife]: https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life

[//]: # (relative links)

[app]: app
[desktop-app]: desktop-app
[dependency-injection]: docs/di.md
[icon]: app/src/androidMain/ic_launcher-playstore.png
[navigation]: docs/navigation.md
[watchface]: resources-wear/src/androidMain/res/drawable-nodpi/watchface_round.png
[wear]: wear
