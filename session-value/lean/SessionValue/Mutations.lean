/-
 * Copyright 2024 The Android Open Source Project
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
import SessionValue.Properties

namespace SessionValue

/-!
# Negative Verification & Mutation Proofs for `session-value`

This file proves that mutated / buggy implementations of `SessionValueHolder`
fail the formal theorems, demonstrating that the verified properties are tight
and actively catch real regression bugs.
-/

/--
Mutant 1: Buggy Echo Handling.
An implementation that blindly clears the local session on any upstream change,
failing to recognize echoes of its own local updates.
-/
def mutantEchoStep (st : State α) (newUpstream : SessionValue α) (freshId : Uuid) : State α :=
  { st with
    upstreamSessionIdBeforeLocalSession := newUpstream.sessionId,
    upstreamSessionValue := newUpstream,
    localSessionId := freshId,
    localSessionValue := none }

theorem mutant1_violates_echo_preservation (st : State α) (lv : SessionValue α)
    (newUpstream : SessionValue α) (freshId : Uuid)
    (h_active : st.localSessionValue = some lv)
    (_h_echo : newUpstream.sessionId = lv.sessionId) :
    (mutantEchoStep st newUpstream freshId).localSessionValue ≠ st.localSessionValue := by
  dsimp [mutantEchoStep]
  rw [h_active]
  intro h_contra
  contradiction

/--
Mutant 2: Buggy Conflict Handling.
An implementation that ignores conflicting upstream updates and fails to clear
its local editing session when another session commits upstream.
-/
def mutantConflictStep (st : State α) (newUpstream : SessionValue α) : State α :=
  { st with upstreamSessionValue := newUpstream }

theorem mutant2_violates_conflict_invalidation (st : State α) (lv : SessionValue α)
    (newUpstream : SessionValue α)
    (h_active : st.localSessionValue = some lv)
    (_h_conflict : newUpstream.sessionId ≠ lv.sessionId) :
    (mutantConflictStep st newUpstream).localSessionValue ≠ none := by
  dsimp [mutantConflictStep]
  rw [h_active]
  intro h_contra
  contradiction

/--
Mutant 4: Pre-5e57f71 State Restoration Bug.
Prior to commit 5e57f71ebffbc04b9db2d55b3571292b09a83d56, `SessionValueHolderImpl.Saver`
failed to persist `upstreamSessionValue`.
When restored from saved instance state, `upstreamSessionValue` was initialized
directly to the *new* incoming upstream value rather than the *persisted* baseline.
-/
def restorePre5e57f71 (savedLocalId : Uuid) (savedLocalVal : Option (SessionValue α))
    (newUpstream : SessionValue α) : State α := {
  upstreamSessionIdBeforeLocalSession := newUpstream.sessionId,
  upstreamSessionValue := newUpstream,
  localSessionId := savedLocalId,
  localSessionValue := savedLocalVal
}

/--
Theorem: Under the pre-5e57f71 restoration model, calling `stepSetValueFromUpstream`
fails to invalidate the local editing session even when an external session intervened
(`newUpstream.sessionId ≠ lv.sessionId`), directly reproducing the bug fixed in 5e57f71.
-/
theorem mutant4_reproduces_pre_5e57f71_bug
    (savedLocalId : Uuid) (lv : SessionValue α) (newUpstream : SessionValue α) (freshId : Uuid)
    (_h_foreign : newUpstream.sessionId ≠ lv.sessionId) :
    let restored := restorePre5e57f71 savedLocalId (some lv) newUpstream
    let synced := stepSetValueFromUpstream restored newUpstream freshId
    synced.localSessionValue = some lv := by
  dsimp [restorePre5e57f71, stepSetValueFromUpstream]
  have h_not_changed :
    (newUpstream.sessionId != newUpstream.sessionId ||
     newUpstream.valueId != newUpstream.valueId) = false := by
    simp only [bne_self_eq_false]
    rfl
  rw [h_not_changed]
  rfl

end SessionValue
