---
name: improve-code-coverage
description: |
  Helps increment code coverage in this Kotlin Multiplatform project.
  Guides the agent to ask the user for the number of areas to improve, establish a baseline report,
  plan the improvements, write Kotlin unit tests following all Detekt/formatting style rules,
  and commit them (including using git fixup).
---

# Skill: Improve Code Coverage

This skill guides you through the process of systematically and incrementally improving code coverage in the **ComposeLife** project by adding realistic unit tests.

## Step-by-Step Workflow

### 1. Ask for Target Count
At the start of the task, ask the user:
> "How many low-coverage areas would you like to improve?"
Get the number $N$ from the user.

### 2. Generate and Parse Baseline Coverage
1. Ensure a fresh coverage report is built by running:
   ```bash
   ./gradlew jacocoDebugUnitTestCoverageReport
   ```
2. Parse the Jacoco XML report by running the helper script:
   ```bash
   python3 .agents/skills/improve-code-coverage/scripts/parse_jacoco.py
   ```
   This will output a sorted list of classes by missed instructions to `build/jacoco_report.txt`.

### 3. Create the Plan
1. Select the top $N$ classes from the report that fit these criteria:
   - Very low existing coverage.
   - More likely to be user-visible behavior (e.g. settings, geometric extension functions, state management).
   - Core algorithms or serialization code.
2. Formulate an ordered list of these $N$ areas.
3. Draft a plan similar to `test_coverage_plan.md` listing the baseline coverage and the targeted test files.
4. Present this plan to the user for approval.

### 4. Implement Improvements Incrementally (1:1)
For each area in the plan, perform the following steps:

#### A. Find Missed Lines
Run the line lookup script to identify the exact lines and branches that are not covered:
```bash
python3 .agents/skills/improve-code-coverage/scripts/find_missed_lines.py <SourceFileName.kt>
```

#### B. Write Realistic Unit Tests
1. Locate the corresponding test directory (e.g., `jbTest`, `commonTest`, `jvmTest` under the same module).
2. Write unit tests targeting the missed functions/lines.
3. **CRITICAL:** Adhere strictly to the project style rules enforced by Detekt to prevent CI compilation failures:
   - **Trailing Commas:** Add trailing commas to all multi-line function calls, parameter lists, and declarations (e.g., lists of arguments or elements).
   - **Line Length:** Ensure no line of code exceeds **120 characters**. Assign long expressions to local variables if they would wrap awkwardly.
   - **Import Ordering:** Keep all imports sorted lexicographically, with no empty lines between them. Group `kotlin.*`, `kotlinx.*`, `okio.*` correctly, and put `kotlin.*` imports at the end of the imports block.
   - **Function and Class Sizes:** Avoid test methods longer than **60 lines** (Detekt `LongMethod`). Avoid test classes with too many functions (or apply `@Suppress("TooManyFunctions")` to the class declaration).
   - **Unit Testing Framework:** Use `kotlin.test` APIs (`assertEquals`, `assertTrue`, `assertFalse`, `assertNotEquals<Any?>`, etc.) rather than JUnit.

#### C. Run the Module Tests
1. Run the target-specific host tests rather than generic long-running tasks. For example, for the `navigation` module:
   ```bash
   ./gradlew :navigation:testAndroidHostTest
   ```
2. Verify that all tests pass. If compiling or test failures occur, fix them.

#### D. Regenerate Coverage and Verify
1. Run the report task:
   ```bash
   ./gradlew jacocoDebugUnitTestCoverageReport
   ```
2. Parse the report and verify that instruction and branch coverage improved for the target class.

#### E. Commit and Fixup
1. Create a git commit with a message specifying:
   - The area/class improved.
   - The coverage improvement metrics (X% from Y%, and missed branches reduced to A from B).
   - What behavior wasn't previously covered.
2. If minor formatting fixes or code style changes are needed after feedback or check failures, stage the fixes and commit them with `--fixup` targeting the original commit, like:
   ```bash
   git commit --fixup <commit-hash>
   ```

### 5. Final Verification
After all $N$ areas are implemented, run:
```bash
./gradlew check
```
Verify that all CI checks, tests, and Detekt inspections pass successfully.
