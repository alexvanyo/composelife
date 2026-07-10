---
name: guided-pr-fixup
description: >-
  Performs a guided fixup of a given GitHub PR. Checks out the PR branch, retrieves CI status and review comments,
  reruns flaky CI checks, resolves code/compilation/test/lint failures locally, addresses review comments, verifies
  locally using gradlew check, and presents changes to the user for approval before pushing or responding.
---

# Guided PR Fixup Skill

Use this skill when the user requests to fix, update, or troubleshoot a currently open GitHub Pull Request (PR) in this repository. The goal is to get the PR passing on CI and address all code review comments with supervision from the user.

---

## ⚠️ Important Rules & Constraints

1. **NO Unapproved Pushing**: Do **NOT** run `git push` or push code to GitHub unless the user gives explicit written approval in the chat.
2. **NO Unapproved Comments**: Do **NOT** post any replies, reactions, or submit review responses directly to the PR comments on GitHub unless explicitly approved by the user.
3. **Kotlin Formatting Rules**: All Kotlin edits must adhere to the style guide in [AGENTS.md](file:///home/xela/Projects/composelife/AGENTS.md) (120-char line limit, trailing commas on multi-line lists, and Apache 2.0 headers on any new files).

---

## 🏃 Step-by-Step Workflow

### Step 1: Checkout the PR Branch
Ask the user for the PR number or URL if not already provided. Checkout the PR branch locally:
```bash
gh pr checkout <pr-number>
```

### Step 2: Fetch and Parse PR Status
Run the parsed status check helper script to see current CI check rollup and review comments:
```bash
gh pr view <pr-number> --json statusCheckRollup,reviews | .agents/skills/guided-pr-fixup/scripts/parse_pr_status.py
```

### Step 3: Address CI Check Failures
Review the list of checks under `=== CI CHECK ROLLUP ===`.
1. **If checks are still running** (`IN_PROGRESS` or `QUEUED`), inform the user and ask if they want to wait.
2. **If a check failed**:
   - Extract the `Run ID` from the output or the `detailsUrl`.
   - View the logs of the failed jobs using:
     ```bash
     gh run view <run-id> --log-failed
     ```
   - **Flaky or Timeout Failure**: If the failure is transient (e.g. download timeouts, network flakes, gradle daemon issues), rerun the failed jobs:
     ```bash
     gh run rerun <run-id> --failed
     ```
   - **Code or Test Failure**: If it is a compilation error, test failure, or lint error:
     1. Locate the file and line number.
     2. Reproduce the failure locally by running the relevant gradle task, for example:
        * All checks: `./gradlew check`
        * Detekt/Formatting: `./gradlew detekt`
        * Run a specific test: `./gradlew :<module>:test --tests "<class_name>"`
     3. Make the necessary code modifications locally to fix the compilation or logic error.

### Step 4: Address Review Comments
Review the list of comments under `=== REVIEW COMMENTS ===`.
1. For each active comment, find the file and line number.
2. Make code edits in the local workspace to resolve the reviewer's feedback.
3. Keep a checklist of which comments have been addressed. Do **NOT** reply on GitHub yet.

### Step 5: Local Validation
Ensure everything is fully passing before asking for approval. Run:
```bash
./gradlew check
```
If this fails, continue fixing errors locally until it passes.

### Step 6: Present Changes and Seek Approval
Once the branch is fully corrected and passes local validation:
1. Provide the user with a clear summary in chat:
   - A list of the CI failures that were fixed.
   - A list of the review comments that were addressed.
   - A summary of the local verification status.
2. Ask the user for explicit approval:
   * *"Would you like me to push these changes to GitHub now?"*
   * *"Would you like me to resolve or reply to the PR review comments?"*

---

## 🛠️ Helper Commands

* **Checking Run Log**:
  ```bash
  gh run view <run-id> --log
  ```
* **Checking Current Branch Status**:
  ```bash
  git status
  ```
* **Git Commit**:
  Commit changes locally with a descriptive message. Use `git commit --amend` or fixups if appropriate for the repository's workflow, or simply commit normally.
