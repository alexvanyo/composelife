/-
 * Copyright 2026 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 -/

import SessionValue.Basic
import SessionValue.StateMachine

namespace SessionValue

/--
An emitted update pair: `(expected, newValue)` for compare-and-set upstream storage.
-/
abbrev Update (α : Type u) := SessionValue α × SessionValue α

/--
Determines if an update in the queue is stale with respect to the current local session IDs.
An update is stale if its expected session ID neither matches `localSessionId` nor `preLocalSessionId`.
-/
def isStaleUpdate (localId preLocalId : Uuid) (u : Update α) : Bool :=
  u.1.sessionId != localId && u.1.sessionId != preLocalId

/--
Removes stale updates from the front of the queue, modeling the `while` loop in
`rememberAsyncSessionValueHolder`:
```kotlin
while (firstUpdate != null &&
       firstUpdate.first.sessionId != localSessionId &&
       firstUpdate.first.sessionId != preLocalSessionId) {
    updateList.removeFirst()
}
```
-/
def dropStalePrefix (localId preLocalId : Uuid) : List (Update α) → List (Update α)
  | [] => []
  | u :: rest =>
    if isStaleUpdate localId preLocalId u then
      dropStalePrefix localId preLocalId rest
    else
      u :: rest

/--
Theorem: Once `dropStalePrefix` produces a non-empty list, the head update is guaranteed
not to be stale (its expected session matches either `localSessionId` or `preLocalSessionId`).
-/
theorem dropStalePrefix_head_valid (localId preLocalId : Uuid) (q : List (Update α)) :
    ∀ u rest, dropStalePrefix localId preLocalId q = u :: rest →
    isStaleUpdate localId preLocalId u = false := by
  induction q with
  | nil =>
    intro u rest h
    contradiction
  | cons head tail ih =>
    intro u rest h
    dsimp [dropStalePrefix] at h
    split at h
    · exact ih u rest h
    · injection h with h_head h_tail
      rw [← h_head]
      rename_i h_not_stale
      exact Bool.not_eq_true _ ▸ h_not_stale

/--
Predicate: A list of updates forms a chained sequence where each subsequent update's
`expected` value matches the preceding update's `newValue`.
-/
def CASChained : List (Update α) → Prop
  | [] => True
  | [_] => True
  | (_, n1) :: (e2, n2) :: rest =>
    n1 = e2 ∧ CASChained ((e2, n2) :: rest)

/--
Batches a non-empty list of chained updates into a single atomic update:
`expected` is the base requirement of the first update, and `newValue` is the target
of the final update.
-/
def batchUpdate (q : List (Update α)) (h : q ≠ []) : Update α :=
  ((q.head h).1, (q.getLast h).2)

/--
Upstream Compare-And-Set (CAS) semantics as documented in README:
An update succeeds if the expected session matches the current upstream session.
-/
def casApply (current : SessionValue α) (expected newValue : SessionValue α) :
    Option (SessionValue α) :=
  if current.sessionId == expected.sessionId then
    some newValue
  else
    none

/--
Applies a list of updates sequentially using CAS.
-/
def casApplyAll (current : SessionValue α) : List (Update α) → Option (SessionValue α)
  | [] => some current
  | (e, n) :: rest =>
    match casApply current e n with
    | some next => casApplyAll next rest
    | none => none

/--
Theorem: If an update is a single step, the batched update is identical to the single update.
-/
theorem batch_single (e n : SessionValue α) (h : [(e, n)] ≠ []) :
    batchUpdate [(e, n)] h = (e, n) := by
  rfl

/--
Theorem: For any chained pair of updates `[(e1, n1), (n1, n2)]` where upstream session
matches `e1.sessionId` and `n1.sessionId = e1.sessionId`, the batched update `(e1, n2)`
yields the exact same CAS result as sequential evaluation.
-/
theorem batch_two_step_cas_equivalence (current e1 n1 n2 : SessionValue α)
    (_h_chain : n1.sessionId = e1.sessionId)
    (h_curr : (current.sessionId == e1.sessionId) = true) :
    casApplyAll current [(e1, n1), (n1, n2)] = casApply current e1 n2 := by
  dsimp [casApplyAll, casApply]
  rw [h_curr]
  dsimp
  have h_next : (n1.sessionId == n1.sessionId) = true := by
    exact beq_self_eq_true n1.sessionId
  rw [h_next]
  rfl

end SessionValue
