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

import Lean.Compiler.Kotlin
open Lean.Compiler.Kotlin

namespace SessionValue

/--
A 128-bit UUID representation matching RFC 4122 / RFC 9562 and Kotlin's `kotlin.uuid.Uuid`.
Represented as two 64-bit unsigned integers: `mostSignificantBits` and `leastSignificantBits`.
-/
@[extern "kotlin:kotlin.uuid.Uuid"]
structure Uuid where
  mostSignificantBits : UInt64
  leastSignificantBits : UInt64
deriving DecidableEq, Repr, Inhabited

attribute [kotlin_expr "({0} == {1})"] instDecidableEqUuid

/--
An object representing a specific session for `value`.
This `value` is from the given `sessionId`, and has the associated `valueId`.
-/
@[kotlin_class "data class SessionValue"]
structure SessionValue (α : Type u) where
  sessionId : Uuid
  valueId : Uuid
  value : α
deriving DecidableEq, Repr, Inhabited

/--
Converts a `SessionValue` of type `α` to a `SessionValue` of type `β` using `f`.
This preserves `sessionId` and `valueId`.
-/
@[kotlin_member "SessionValue" "public" "map"]
def SessionValue.map (sv : SessionValue α) (f : α → β) : SessionValue β :=
  { sessionId := sv.sessionId, valueId := sv.valueId, value := f sv.value }

/--
Information about a local session in a `SessionValueHolder`.
-/
@[kotlin_class "data sealed interface LocalSessionInfo"]
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
@[export session_value_local_session_id, kotlin_member "LocalSessionInfo" "public extension val" "localSessionId"]
def LocalSessionInfo.localSessionId : LocalSessionInfo → Uuid
  | .active currentLocalSessionId _ _ => currentLocalSessionId
  | .inactive _ nextLocalSessionId => nextLocalSessionId

/--
The previous upstream session id that will remain constant when upgrading from
`LocalSessionInfo.inactive` to `LocalSessionInfo.active`.
-/
@[export session_value_pre_local_session_id, kotlin_member "LocalSessionInfo" "public extension val" "preLocalSessionId"]
def LocalSessionInfo.preLocalSessionId : LocalSessionInfo → Uuid
  | .active _ _ previousUpstreamSessionId => previousUpstreamSessionId
  | .inactive currentUpstreamSessionId _ => currentUpstreamSessionId

/--
Returns `true` if the `LocalSessionInfo` is `LocalSessionInfo.active`, and `false` if `inactive`.
-/
@[export session_value_is_local_session_active,
  kotlin_member "LocalSessionInfo" "public extension" "isLocalSessionActive",
  kotlin_contract "returns(true) implies (this@isLocalSessionActive is LocalSessionInfo.Active)"
                  "returns(false) implies (this@isLocalSessionActive is LocalSessionInfo.Inactive)"]
def LocalSessionInfo.isLocalSessionActive : LocalSessionInfo → Bool
  | .active .. => true
  | .inactive .. => false

@[kotlin_file]
def basicFileSpec : FileSpec := {
  imports := #[
    "import kotlinx.serialization.Serializable",
    "import kotlin.uuid.Uuid"
  ]
  items := #[
    .cls {
      name := "SessionValue"
      header := "@Serializable\ndata class SessionValue<out T>(val sessionId: Uuid, val valueId: Uuid, val value: T)"
      body := #[
        .verbatim "companion object {}",
        .members
      ]
    },
    .topLevel
  ]
}

end SessionValue
