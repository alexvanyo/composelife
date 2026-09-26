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

/-- `SessionValue.map` with identity is the identity. -/
@[simp]
theorem SessionValue.map_id (sv : SessionValue α) : sv.map id = sv := by
  cases sv
  rfl

/-- `SessionValue.map` is functorial under function composition. -/
@[simp]
theorem SessionValue.map_comp (f : α → β) (g : β → γ) (sv : SessionValue α) :
    (sv.map f).map g = sv.map (g ∘ f) := by
  cases sv
  rfl

/--
Lifts a function `f : α → β` to a transformation on `State α`.
Models the state representation of `MappedSessionValueHolder`.
-/
def State.map (f : α → β) (st : State α) : State β := {
  upstreamSessionIdBeforeLocalSession := st.upstreamSessionIdBeforeLocalSession,
  upstreamSessionValue := st.upstreamSessionValue.map f,
  localSessionId := st.localSessionId,
  localSessionValue := st.localSessionValue.map (SessionValue.map f)
}

/--
The exposed `sessionValue` of a mapped state is the mapped `sessionValue` of the base state.
-/
theorem State.map_sessionValue (f : α → β) (st : State α) :
    (st.map f).sessionValue = st.sessionValue.map f := by
  cases st with
  | mk uBefore uVal locId locVal =>
    dsimp [State.map, State.sessionValue]
    cases locVal with
    | none => rfl
    | some lv => rfl

/--
`LocalSessionInfo` is invariant under `map`: transforming the payload value
does not alter session lifecycle status or session IDs.
-/
theorem State.map_info (f : α → β) (st : State α) :
    (st.map f).info = st.info := by
  cases st with
  | mk uBefore uVal locId locVal =>
    dsimp [State.map, State.info, SessionValue.map]
    cases locVal with
    | none => rfl
    | some lv => rfl

/--
Round-trip fidelity of `MappedSessionValueHolder`:
If `transformTo (transformFrom b) = b`, then setting `b` via `transformFrom`
and observing through `transformTo` faithfully yields `b`.
-/
theorem mapped_setValue_roundtrip (st : State α) (transformTo : α → β) (transformFrom : β → α)
    (h_retract : ∀ b, transformTo (transformFrom b) = b) (b : β) (vid : Uuid) :
    let (st', _) := stepSetValue st (transformFrom b) vid
    (st'.map transformTo).sessionValue.value = b := by
  dsimp [stepSetValue, State.map, State.sessionValue, SessionValue.map]
  exact h_retract b

end SessionValue
