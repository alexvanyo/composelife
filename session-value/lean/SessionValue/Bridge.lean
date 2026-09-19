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

structure StateSnapshot where
  exposedSessionId : Nat
  exposedValueId : Nat
  exposedValue : String
  isLocalSessionActive : Bool
  localSessionId : Nat
  preLocalSessionId : Nat
  isUpstreamUpToDate : Bool
  lastExpectedSessionId : Nat
  lastExpectedValueId : Nat

def makeSnapshot (st : State String) (lastExp : SessionValue String) : StateSnapshot :=
  let exp := st.sessionValue
  let info := st.info
  let isUpToDate :=
    match info with
    | .active _ upToDate _ => upToDate
    | .inactive .. => false
  {
    exposedSessionId := exp.sessionId,
    exposedValueId := exp.valueId,
    exposedValue := exp.value,
    isLocalSessionActive := info.isLocalSessionActive,
    localSessionId := info.localSessionId,
    preLocalSessionId := info.preLocalSessionId,
    isUpstreamUpToDate := isUpToDate,
    lastExpectedSessionId := lastExp.sessionId,
    lastExpectedValueId := lastExp.valueId
  }

@[export session_value_initial_state]
def oracleInit (uSess : Nat) (uVal : Nat) (uValStr : String) (locId : Nat) :
    State String × SessionValue String :=
  let u0 : SessionValue String := { sessionId := uSess, valueId := uVal, value := uValStr }
  let st := initialState u0 locId
  (st, st.sessionValue)

@[export session_value_step_set_value]
def oracleStepSetValue (st : State String) (valStr : String) (valId : Nat) :
    State String × SessionValue String :=
  let (nextSt, (exp, _)) := stepSetValue st valStr valId
  (nextSt, exp)

@[export session_value_step_set_upstream]
def oracleStepSetUpstream (st : State String) (uSess : Nat) (uVal : Nat) (uValStr : String) (freshId : Nat) :
    State String × SessionValue String :=
  let newUpstream : SessionValue String := { sessionId := uSess, valueId := uVal, value := uValStr }
  let nextSt := stepSetValueFromUpstream st newUpstream freshId
  (nextSt, nextSt.sessionValue)

@[export session_value_make_snapshot]
def oracleMakeSnapshot (st : State String) (lastExp : SessionValue String) : StateSnapshot :=
  makeSnapshot st lastExp

end SessionValue
