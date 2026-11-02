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
import SessionValueDefs

namespace SessionValue

/-!
# Mutation proofs for `session-value`

Each mutant below is a plausible buggy variant of the session-value logic. For each one, we prove
that it violates the property that the corresponding master theorem in `SessionValueTheorems.lean`
proves for the real implementation, so the master theorems would catch the bug.
-/

private def uid (n : UInt64) : Uuid := ⟨n, 0⟩

/--
Mutant 1: Buggy Echo Handling.
An implementation that clears the local session on any upstream change, failing to recognize
echoes of its own local updates.
-/
def mutantEchoStep (st : State α) (newUpstream : SessionValue α) (freshId : Uuid) : State α :=
  { st with
    upstreamSessionIdBeforeLocalSession := newUpstream.sessionId,
    upstreamSessionValue := newUpstream,
    localSessionId := freshId,
    localSessionValue := none }

/--
Mutant 1 violates Theorem 6a (`upstream_echo_keeps_active`): an echo of the local session drops it.
-/
theorem mutant1_violates_echo_preservation :
    ¬ ∀ (st : State Nat) (lv newUpstream : SessionValue Nat) (freshId : Uuid),
      st.localSessionValue = some lv → newUpstream.sessionId = lv.sessionId →
      (mutantEchoStep st newUpstream freshId).localSessionValue = some lv := by
  intro h
  have := h ⟨uid 1, ⟨uid 1, uid 10, 0⟩, uid 2, some ⟨uid 2, uid 11, 1⟩⟩ ⟨uid 2, uid 11, 1⟩
    ⟨uid 2, uid 11, 1⟩ (uid 3) rfl rfl
  simp [mutantEchoStep] at this

/--
Mutant 2: Buggy Conflict Handling.
An implementation that ignores conflicting upstream updates and fails to clear its local editing
session when another session commits upstream.
-/
def mutantConflictStep (st : State α) (newUpstream : SessionValue α) : State α :=
  { st with upstreamSessionValue := newUpstream }

/--
Mutant 2 violates Theorem 7 (`upstream_conflict_invalidates`): a foreign upstream change leaves
the local session active.
-/
theorem mutant2_violates_conflict_invalidation :
    ¬ ∀ (st : State Nat) (lv newUpstream : SessionValue Nat),
      st.localSessionValue = some lv → newUpstream.sessionId ≠ lv.sessionId →
      (mutantConflictStep st newUpstream).localSessionValue = none := by
  intro h
  have := h ⟨uid 1, ⟨uid 1, uid 10, 0⟩, uid 2, some ⟨uid 2, uid 11, 1⟩⟩ ⟨uid 2, uid 11, 1⟩
    ⟨uid 1, uid 12, 5⟩ rfl (by decide)
  simp [mutantConflictStep] at this

/--
Mutant 3: Pre-5e57f71 State Restoration Bug.
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
Mutant 3 violates Theorem 7 (`upstream_conflict_invalidates`): under the pre-5e57f71 restoration,
`stepSetValueFromUpstream` keeps the local editing session even though a foreign session
(`newUpstream.sessionId ≠ lv.sessionId`) wrote upstream, reproducing the bug fixed in 5e57f71.
-/
theorem mutant3_reproduces_pre_5e57f71_bug
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

/--
Mutant 4: Stale-Update Pruning by `expected`.
The pruning rule `rememberAsyncSessionValueHolder` used before it was fixed: keep a queued update
when its `expected` session is the local or the pre-local session.
-/
def pruneByExpectedSession (info : LocalSessionInfo) (q : List (Update α)) : List (Update α) :=
  q.dropWhile (fun u =>
    u.1.sessionId != info.localSessionId && u.1.sessionId != info.preLocalSessionId)

/-- Session `uid 1` wrote the upstream value; the holder's next local session id is `uid 2`. -/
private def raceBase : SessionValue Nat := ⟨uid 1, uid 10, 0⟩

/-- Session `uid 1` writes upstream again, invalidating local session `uid 2`. -/
private def raceForeign : SessionValue Nat := ⟨uid 1, uid 12, 5⟩

/-- The user edits (session `uid 2`), the update is still queued when `raceForeign` arrives. -/
private def raceEdit1 := stepSetValue (initialState raceBase (uid 2)) 1 (uid 11)

/-- The user edits again in the new local session `uid 3` before the queue is flushed. -/
private def raceEdit2 :=
  stepSetValue (stepSetValueFromUpstream raceEdit1.1 raceForeign (uid 3)) 2 (uid 13)

/--
Mutant 4 violates Theorem 10b (`pruneStaleUpdates_exact`) and Theorem 10c (`async_batch_sound`) in
a reachable state. When the session that invalidated the local session is the same session that
the local session started from, pruning by `expected` keeps the invalidated session's first update.
The batched update then fails its compare-and-set against the new upstream value, so the user's
next edit is lost, while the pruning by `pruneStaleUpdates` sends it successfully.
-/
theorem mutant4_prune_by_expected_loses_update :
    AsyncReachable raceEdit2.1 [raceEdit1.2, raceEdit2.2] ∧
    pruneByExpectedSession raceEdit2.1.info [raceEdit1.2, raceEdit2.2] =
      [raceEdit1.2, raceEdit2.2] ∧
    raceEdit1.2.2.sessionId ≠ raceEdit2.1.info.localSessionId ∧
    casApply raceForeign raceEdit1.2.1 raceEdit2.2.2 = none ∧
    pruneStaleUpdates raceEdit2.1.info [raceEdit1.2, raceEdit2.2] = [raceEdit2.2] ∧
    casApply raceForeign raceEdit2.2.1 raceEdit2.2.2 = some raceEdit2.2.2 := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide⟩
  exact AsyncReachable.setValue 2 (uid 13)
    (AsyncReachable.upstream raceForeign (uid 3) (by decide) (by decide)
      (AsyncReachable.setValue 1 (uid 11) (AsyncReachable.init raceBase (uid 2) (by decide))))

end SessionValue
