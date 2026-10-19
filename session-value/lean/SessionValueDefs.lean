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
The core inductive invariant of `SessionValueHolder`:
1. When inactive, `upstreamSessionIdBeforeLocalSession` strictly equals `upstreamSessionValue.sessionId`.
2. When inactive, `localSessionId` is fresh with respect to `upstreamSessionValue.sessionId`.
3. When active, `localSessionValue` is tagged with `localSessionId`.
-/
structure ValidState (st : State α) : Prop where
  inactive_sound : st.localSessionValue = none →
    st.upstreamSessionIdBeforeLocalSession = st.upstreamSessionValue.sessionId
  inactive_fresh : st.localSessionValue = none →
    st.localSessionId ≠ st.upstreamSessionValue.sessionId
  active_sound : ∀ lv, st.localSessionValue = some lv →
    lv.sessionId = st.localSessionId

/--
An update pair `(expected, newValue)` that `setValue` hands to upstream for a compare-and-set (CAS).
-/
abbrev Update (α : Type u) := SessionValue α × SessionValue α

/--
A list of updates is chained when each update's `expected` value is the preceding update's `newValue`.
-/
def CASChained : List (Update α) → Prop
  | [] => True
  | [_] => True
  | (_, n1) :: (e2, n2) :: rest =>
    n1 = e2 ∧ CASChained ((e2, n2) :: rest)

/--
Batches a non-empty list of chained updates into a single update: `expected` is the requirement of
the first update, and `newValue` is the target of the last update.
-/
def batchUpdate (q : List (Update α)) (h : q ≠ []) : Update α :=
  ((q.head h).1, (q.getLast h).2)

/--
Upstream compare-and-set: the update succeeds when the upstream accepts `expected` as matching its
current value. Upstreams compare differently: `DefaultComposeLifePreferences` uses full equality
(`fullMatch`), while `CellShapeConfigUiState` compares only the ids (`idMatch`).
-/
def casApplyWith (accepts : SessionValue α → SessionValue α → Bool)
    (current expected newValue : SessionValue α) : Option (SessionValue α) :=
  if accepts current expected then
    some newValue
  else
    none

/--
Applies a list of updates one after another using compare-and-set.
-/
def casApplyAllWith (accepts : SessionValue α → SessionValue α → Bool) (current : SessionValue α) :
    List (Update α) → Option (SessionValue α)
  | [] => some current
  | (e, n) :: rest =>
    match casApplyWith accepts current e n with
    | some next => casApplyAllWith accepts next rest
    | none => none

/--
Compare-and-set acceptance by full equality, as in `DefaultComposeLifePreferences`.
-/
def fullMatch [DecidableEq α] (current expected : SessionValue α) : Bool :=
  decide (current = expected)

/--
Compare-and-set acceptance by session and value id, as in `CellShapeConfigUiState`.
-/
def idMatch (current expected : SessionValue α) : Bool :=
  current.sessionId == expected.sessionId && current.valueId == expected.valueId

/--
Compare-and-set by full equality.
-/
abbrev casApply [DecidableEq α] (current expected newValue : SessionValue α) : Option (SessionValue α) :=
  casApplyWith fullMatch current expected newValue

/--
Sequential compare-and-set by full equality.
-/
abbrev casApplyAll [DecidableEq α] (current : SessionValue α) (q : List (Update α)) :
    Option (SessionValue α) :=
  casApplyAllWith fullMatch current q

/--
The stale-update pruning in `rememberAsyncSessionValueHolder`: queued updates are dropped from the
front until the first one written by the current local session.
-/
def pruneStaleUpdates (info : LocalSessionInfo) (q : List (Update α)) : List (Update α) :=
  q.dropWhile (fun u => !info.isCurrentSessionUpdate u.2)

/--
The updates of the current local session in the async queue: each was written by the current local
session, they are chained, and the last one writes the value that the holder currently shows.
-/
structure SessionQueue (st : State α) (cur : List (Update α)) : Prop where
  tagged : ∀ u ∈ cur, u.2.sessionId = st.localSessionId
  chained : CASChained cur
  last_shown : ∀ u ∈ cur.getLast?, u.2 = st.sessionValue

/--
Invariant of the update queue of `rememberAsyncSessionValueHolder`: the queue is a block of stale
updates, written by earlier local sessions, followed by the updates of the current local session.
-/
def QueueInv (st : State α) (q : List (Update α)) : Prop :=
  ∃ stale cur, q = stale ++ cur ∧
    (∀ u ∈ stale, u.2.sessionId ≠ st.localSessionId) ∧
    SessionQueue st cur

/--
The holder states and update queues of `rememberAsyncSessionValueHolder` reachable by any
interleaving of local edits, upstream changes and flushes.

- `setValue` appends the update emitted by `stepSetValue` to the queue.
- An upstream change draws a fresh local session id, as `Uuid.random()` does: it differs from the
  new upstream session and from every session that wrote a queued update.
- A flush sends the batch of the pruned queue and empties the queue. The Kotlin effect prunes when
  the local session changes, before its next flush, and clears the whole list when it flushes.
-/
inductive AsyncReachable : State α → List (Update α) → Prop
  | init (u0 : SessionValue α) (localId : Uuid) (h_fresh : localId ≠ u0.sessionId) :
    AsyncReachable (initialState u0 localId) []
  | setValue {st : State α} {q : List (Update α)} (v : α) (vid : Uuid) :
    AsyncReachable st q →
    AsyncReachable (stepSetValue st v vid).1 (q ++ [(stepSetValue st v vid).2])
  | upstream {st : State α} {q : List (Update α)} (newUpstream : SessionValue α) (freshId : Uuid)
    (h_fresh : freshId ≠ newUpstream.sessionId) (h_unused : ∀ u ∈ q, u.2.sessionId ≠ freshId) :
    AsyncReachable st q →
    AsyncReachable (stepSetValueFromUpstream st newUpstream freshId) q
  | flush {st : State α} {q : List (Update α)} :
    AsyncReachable st q → AsyncReachable st []

/--
Lifts a function `f : α → β` to a transformation on `State α`.
Models the state representation of `MappedSessionValueHolder`.
-/
def State.map (f : α → β) (st : State α) : State β := {
  upstreamSessionIdBeforeLocalSession := st.upstreamSessionIdBeforeLocalSession,
  upstreamSessionValue := st.upstreamSessionValue.map f,
  localSessionId := st.localSessionId,
  localSessionValue := st.localSessionValue.map (fun sv => sv.map f)
}

end SessionValue
