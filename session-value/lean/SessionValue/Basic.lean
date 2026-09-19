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

namespace SessionValue

/-- Abstract representation of a UUID with decidable equality. -/
def Uuid := Nat
deriving DecidableEq, Repr, Inhabited

instance (n : Nat) : OfNat Uuid n := ⟨n⟩

/--
An object representing a specific session for `value`.
This `value` is from the given `sessionId`, and has the associated `valueId`.
-/
structure SessionValue (α : Type u) where
  sessionId : Uuid
  valueId : Uuid
  value : α
deriving DecidableEq, Repr, Inhabited

/--
Converts a `SessionValue` of type `α` to a `SessionValue` of type `β` using `f`.
This preserves `sessionId` and `valueId`.
-/
def SessionValue.map (f : α → β) (sv : SessionValue α) : SessionValue β :=
  { sessionId := sv.sessionId, valueId := sv.valueId, value := f sv.value }

/--
Information about a local session in a `SessionValueHolder`.
-/
inductive LocalSessionInfo where
  /--
  The local session is active, meaning that the session value is running ahead of the upstream value.
  -/
  | active (currentLocalSessionId : Uuid)
           (isUpstreamSessionValueUpToDate : Bool)
           (previousUpstreamSessionId : Uuid) : LocalSessionInfo
  /--
  The local session is inactive, meaning that the session value is just matching the upstream value.
  -/
  | inactive (currentUpstreamSessionId : Uuid)
             (nextLocalSessionId : Uuid) : LocalSessionInfo
deriving DecidableEq, Repr, Inhabited

/--
The local session id that will remain constant when upgrading from
`LocalSessionInfo.inactive` to `LocalSessionInfo.active`.
-/
def LocalSessionInfo.localSessionId : LocalSessionInfo → Uuid
  | .active currentLocalSessionId _ _ => currentLocalSessionId
  | .inactive _ nextLocalSessionId => nextLocalSessionId

/--
The previous upstream session id that will remain constant when upgrading from
`LocalSessionInfo.inactive` to `LocalSessionInfo.active`.
-/
def LocalSessionInfo.preLocalSessionId : LocalSessionInfo → Uuid
  | .active _ _ previousUpstreamSessionId => previousUpstreamSessionId
  | .inactive currentUpstreamSessionId _ => currentUpstreamSessionId

/--
Returns `true` if the `LocalSessionInfo` is `LocalSessionInfo.active`, and `false` if `inactive`.
-/
def LocalSessionInfo.isLocalSessionActive : LocalSessionInfo → Bool
  | .active .. => true
  | .inactive .. => false

end SessionValue
