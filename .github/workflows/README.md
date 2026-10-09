# GitHub Actions CI Architecture & Resource Management Strategy

This document details the CI resource management, CPU reservation, and Gradle task sequencing strategy used across GitHub Actions workflows in ComposeLife.

---

## 1. Context & Motivation

GitHub Actions standard Linux runners (`ubuntu-latest`) provide:
- **4 vCPUs**
- **16 GB RAM**

ComposeLife is a large Kotlin Multiplatform project comprising ~50 modules targeting Android, JVM Desktop, Wasm, and Linux native, with extensive verification tasks:
- Robolectric-based screenshot tests using Roborazzi with native graphics rendering
- Formal verification theorem proving using Lean 4 (`lake build`)
- Android Lint AST/PSI semantic model extraction
- Detekt static analysis
- Karma + Headless Chromium browser tests for Wasm
- Multi-target Kotlin compilation

### Historical Failure Modes

When executing `./gradlew check` naively in parallel, two severe issues occurred that caused jobs to stall, freeze, and time out:

1. **CPU Starvation (Lost Heartbeats)**:
   Under full compilation load, parallel JVM GC threads, Kotlin daemon workers, Clang, Lean 4 (`lake`), and Chromium saturated all 4 CPU cores at 100%. The GitHub Actions runner daemon (`Runner.Worker` / `Runner.Listener`), which executes in user space on the runner VM, was starved of CPU time. When the runner failed to deliver heartbeat pings to GitHub's orchestrator, GitHub marked the runner as unresponsive and terminated the job with a timeout.

2. **Memory Overcommitment & Swap Thrashing**:
   If Android Lint, Roborazzi screenshot tests, and Chromium ran concurrently while the Gradle and Kotlin daemons held memory, peak memory requirements exceeded the 16 GB physical RAM. On Linux, this triggers aggressive `kswapd` page reclamation and disk I/O thrashing against the virtual disk swap. Disk I/O latencies soared, processes spent nearly 100% of CPU time waiting in `iowait` / memory reclaim, and the entire container became unresponsive before eventually being terminated or killed by the Linux OOM killer.

---

## 2. CPU Reservation Strategy: Leaving 1 Core Free

To guarantee that the host OS and the GitHub Actions runner daemon never suffer CPU starvation, we reserve **1 CPU core at all times**.

### Mechanism: `.github/actions/reserve-cpu-core`

1. **Dynamic Core Calculation**:
   The action queries `nproc` (e.g. 4 cores) and calculates `0-$((N - 2))` (e.g. `0-2`).
2. **CPU Affinity via `taskset`**:
   Linux provides hardware-level CPU affinity masking via `sched_setaffinity` / `taskset`. Restricting a process to cores `0-2` guarantees that the Linux kernel scheduler will **never** schedule any thread or child process of that process on Core 3.
3. **Automatic Inheritance via `BASH_ENV`**:
   GitHub Actions spawns a separate non-interactive bash shell for each workflow step. Non-interactive bash automatically executes the file pointed to by the `BASH_ENV` environment variable upon startup.
   The action writes an initialization script to `$RUNNER_TEMP/reserve-cpu-core.sh` and exports `BASH_ENV=$RUNNER_TEMP/reserve-cpu-core.sh` to `$GITHUB_ENV`.
   Consequently, every subsequent step in the job (and all subprocesses they spawn—including `./gradlew`, the Gradle daemon, the Kotlin daemon, Lake, Clang, and Chromium) automatically executes under affinity mask `0-2`.
4. **Host / Runner Immunity**:
   The GitHub Actions runner service (`Runner.Worker`) was started prior to the job and is not part of this process tree. It retains full access to Core 3, which remains free from build contention. The runner can always deliver heartbeats on schedule.

---

## 3. Gradle Task Sequencing Strategy

To prevent memory demand from exceeding the 16 GB physical RAM envelope, tasks are sequenced at two complementary levels:

### Level 1: Build Logic Concurrency Limiting (`HeavyTaskLimitingBuildService`)

Gradle executes tasks in parallel across decoupled projects by default (`org.gradle.parallel=true`).
To constrain resource-heavy tasks, we use Gradle's `BuildService` API:

- **Service**: `HeavyTaskLimitingBuildService` (`build-logic/convention/src/main/kotlin/com/alexvanyo/composelife/buildlogic/HeavyTaskLimitingBuildService.kt`).
- **Configuration**: In `.github/ci-gradle.properties`, `com.alexvanyo.composelife.maxConcurrentHeavyTasks=1`.
- **Enforcement**: Any task calling `usesService(heavyTaskLimitingBuildService)` acquires an exclusive lease. At most **1 heavy task** is allowed to run concurrently across the *entire multi-project build*, regardless of how many modules or workers are available.
- **Covered Tasks**:
  - Android Lint tasks (`AndroidLintAnalysisTask`, `LintModelWriterTask`, `AndroidLintGlobalTask`)
  - Detekt static analysis tasks (`Detekt`)
  - Test tasks (`AbstractTestTask`, `Test`, `KotlinNativeTest`)
  - Kotlin JS/Wasm browser test tasks (`KotlinJsTest`)
  - Lean 4 verification tasks (`verifyLean`, `cacheLean`)
  - R8 minification tasks (`R8Task`)
  - Binaryen executable optimization (`BinaryenExec`)

### Level 2: Task Ordering via `mustRunAfter`

In `build-logic`, ordering rules are established:
- Lint tasks run after Detekt: `mustRunAfter(tasks.withType(Detekt::class.java))`
- Test tasks run after Detekt and Lint: `mustRunAfter(tasks.withType(Detekt::class.java))`, `mustRunAfter(tasks.withType(AndroidLintAnalysisTask::class.java))`

> **Important**: `mustRunAfter` enforces relative ordering **only when both tasks are already scheduled** in the task graph (such as during `check`). Running `./gradlew lint` alone will **not** trigger `detekt`.

### Level 3: Workflow Phasing in `ci.yml`

In `.github/workflows/ci.yml`, the monolithic `./gradlew check` invocation is separated into discrete verification steps:

1. **Static Analysis & Formal Proofs**: `detekt`, `verifyLean`, `dependencyGuard`, `checkSortDependencies`
2. **Auto-commit fixes** (if static analysis failed on PR)
3. **Android Lint**: `lintDebug`
4. **Unit Tests & Roborazzi Screenshot Tests**: `testDebugUnitTest`, `desktopTest`, `linuxX64Test`
5. **Auto-commit screenshots** (if screenshot tests failed on PR)
6. **Wasm Browser Tests**: `wasmJsTest`
7. **Final Check Verification**: `check` (catches any remaining checks; largely UP-TO-DATE)

**Benefit**: Running discrete Gradle invocations flushes and terminates forked worker processes (Robolectric JVMs, Karma, and Chromium) between phases, returning their heap and off-heap memory to the OS before the next phase begins.

---

## 4. Memory Sizing & Tuning Reference

Defined in `.github/ci-gradle.properties`:

| Process | Setting | Memory Cap | Rationale |
|---|---|---|---|
| **Gradle Daemon** | `org.gradle.jvmargs` | `-Xmx6g -Xms2g` | 6 GB heap + ~1.5 GB metaspace/overhead = ~7.5 GB max. Matches local `gradle.properties`. |
| **Kotlin Daemon** | `kotlin.daemon.jvmargs` | `-Xmx3g -Xms2g` | 3 GB heap + ~0.5 GB overhead = ~3.5 GB max. |
| **Test Workers** | `maxHeapSize` | `2g` | Forked Robolectric JVM runs with 2 GB heap; only 1 worker runs at a time due to `maxConcurrentHeavyTasks=1`. |
| **GC Threads** | `jvmargs` | `-XX:ParallelGCThreads=3 -XX:ConcGCThreads=1` | Limits JVM garbage collection threads to the 3 available cores. |
| **Gradle Workers** | `org.gradle.workers.max` | `2` | Leaves 1 core for daemons and scheduler, avoiding CPU thrashing on cores 0–2. |

### Memory Budget Breakdown

$$
\begin{align*}
\text{Gradle Daemon (heap + native)} &\approx 7.5\text{ GB} \\
\text{Kotlin Daemon (heap + native)} &\approx 3.5\text{ GB} \\
\text{Active Heavy Task (Test / Lint / Chromium)} &\approx 3.0\text{ GB} \\
\hline
\textbf{Total Peak Memory} &\approx \mathbf{14.0\text{ GB}} \quad (< 16.0\text{ GB Physical RAM})
\end{align*}
$$

This leaves ~2.0 GB headroom for the OS kernel, page tables, system utilities, and runner daemon, avoiding any swap thrashing.

---

## 5. Maintenance Guide

### When adding a new memory-intensive task:
1. Ensure the task registers with `heavyTaskLimitingBuildService`:
   ```kotlin
   tasks.withType(MyHeavyTask::class.java).configureEach {
       usesService(heavyTaskLimitingBuildService)
   }
   ```
2. If it belongs in a particular execution sequence, apply `mustRunAfter` relative to preceding tasks.

### When updating runner hardware:
If GitHub Actions updates standard runners to higher core counts (e.g., 8 cores) or more RAM:
- `.github/actions/reserve-cpu-core` automatically scales (`0-$((N - 2))`).
- You can increase `org.gradle.workers.max` in `.github/ci-gradle.properties` accordingly.
