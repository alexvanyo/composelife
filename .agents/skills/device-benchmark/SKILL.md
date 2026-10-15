---
name: device-benchmark
description: >-
  Guides running Android microbenchmarks on attached physical or rooted devices.
  Covers locking CPU/GPU clocks, disabling JIT compilation, running benchmarks via Gradle
  or direct instrumentation, parsing metrics into Markdown tables, and resetting device state.
---

# Device Benchmark Skill

Use this skill when running Android microbenchmarks (such as `:algorithm-benchmark`) on an attached physical or rooted Android device.

Microbenchmarking on Android requires stable device conditions to ensure reproducible results and avoid thermal throttling noise. This skill utilizes helper scripts (`lockClocks.sh`, `disableJit.sh`, `resetDevice.sh`) and a metric parser (`parse_benchmark_results.py`).

---

## 🧰 Scripts Reference

The skill includes the following scripts under `.agents/skills/device-benchmark/scripts/`:

| Script | Purpose |
| :--- | :--- |
| `lockClocks.sh` | Locks CPU and GPU clocks to fixed, sustainable frequencies to eliminate frequency scaling and thermal throttle jitter. |
| `disableJit.sh` | Sets `dalvik.vm.extra-opts="-Xusejit:false"`, restarts runtime, and waits for boot completion. Eliminates JIT compilation variance. |
| `resetDevice.sh` | Restores default animation scales and reboots device to clear clock locks and re-enable JIT. |
| `parse_benchmark_results.py` | Parses logcat files or JSON output and generates a clean Markdown summary table with median/min/max times and allocation counts. |

---

## 🏃 Step-by-Step Workflow

### Step 1: Verify Device & Acquire Root

Ensure `adb` is available on `PATH` (e.g. `/home/xela/Android/Sdk/platform-tools/adb`) and verify device connectivity:

```bash
adb devices
adb root
adb shell id  # Verify uid=0(root)
```

### Step 2: Lock Clocks and Disable JIT

Run the helper scripts on the device:

1. **Lock Clocks**:
   ```bash
   .agents/skills/device-benchmark/scripts/lockClocks.sh
   ```
   *Verification:*
   ```bash
   adb shell "cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_cur_freq"
   ```

2. **Disable JIT (Optional / Recommended for deterministic AOT benchmarks)**:
   ```bash
   .agents/skills/device-benchmark/scripts/disableJit.sh
   ```
   *Verification:*
   ```bash
   adb shell getprop dalvik.vm.extra-opts  # Should return -Xusejit:false
   ```
   > [!NOTE]
   > Disabling JIT restarts the Android framework. If CPU clocks unlocked during restart, rerun `lockClocks.sh` to ensure frequencies remain locked.

---

### Step 3: Run the Benchmarks

There are two methods to execute the benchmarks:

#### Method A: Gradle Connected Test (Standard)

```bash
./gradlew :algorithm-benchmark:connectedStagingAndroidTest \
    -Pandroid.testInstrumentationRunnerArguments.class=com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithmBenchmarks
```

Results and logcat outputs will be placed in:
`algorithm-benchmark/build/outputs/androidTest-results/connected/staging/<DeviceName>/`

#### Method B: Direct Instrumentation via ADB (Resilient for Long Runs)

If running very long benchmark suites or working over USB connections prone to socket timeouts:

1. **Build and install the staging and test APKs**:
   ```bash
   ./gradlew :algorithm-benchmark:packageStaging :algorithm-benchmark:packageStagingAndroidTest
   adb install -r -t algorithm-benchmark/build/outputs/apk/staging/algorithm-benchmark-staging.apk
   adb install -r -t algorithm-benchmark/build/outputs/apk/androidTest/staging/algorithm-benchmark-staging-androidTest.apk
   ```

2. **Run instrumentation directly**:
   ```bash
   adb shell am instrument -w -r \
       -e class com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithmBenchmarks \
       -e androidx.benchmark.suppressErrors EMULATOR,UNLOCKED,NOT-AOT-COMPILED \
       com.alexvanyo.composelife.algorithm.benchmark.test/androidx.benchmark.junit4.AndroidBenchmarkRunner
   ```

---

### Step 4: Extract and Format Results

Use `parse_benchmark_results.py` to extract metrics into a Markdown table:

1. **From Gradle connected test results**:
   ```bash
   .agents/skills/device-benchmark/scripts/parse_benchmark_results.py \
       algorithm-benchmark/build/outputs/androidTest-results/connected/staging/*/logcat-*.txt
   ```

2. **From device logcat or piped output**:
   ```bash
   adb logcat -d -s Benchmark:I | .agents/skills/device-benchmark/scripts/parse_benchmark_results.py
   ```

3. **From JSON reports**:
   ```bash
   .agents/skills/device-benchmark/scripts/parse_benchmark_results.py path/to/benchmarkData.json
   ```

---

### Step 5: Reset Device

Once benchmarking is complete, restore the device to its normal state:

```bash
.agents/skills/device-benchmark/scripts/resetDevice.sh
# or simply:
adb reboot
```
