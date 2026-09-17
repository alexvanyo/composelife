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
import Lean.Data.Json

open SessionValue
open Lean

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
deriving ToJson

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

def reply (snap : StateSnapshot) : IO Unit := do
  IO.println (toJson snap).compress
  (← IO.getStdout).flush

partial def runLoop (stdin : IO.FS.Stream) (st : State String) (lastExp : SessionValue String) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    return ()
  let trimmed := line.trimAscii.toString
  if trimmed == "EXIT" || trimmed.isEmpty then
    return ()
  let parts := trimmed.splitOn " "
  match parts with
  | ["INIT", uSessStr, uValStr, valStr, locIdStr] =>
    let uSess := uSessStr.toNat?.getD 0
    let uVal := uValStr.toNat?.getD 0
    let locId := locIdStr.toNat?.getD 0
    let u0 : SessionValue String := { sessionId := uSess, valueId := uVal, value := valStr }
    let nextSt := initialState u0 locId
    let nextExp := nextSt.sessionValue
    reply (makeSnapshot nextSt nextExp)
    runLoop stdin nextSt nextExp
  | ["SET_VALUE", valStr, valIdStr] =>
    let valId := valIdStr.toNat?.getD 0
    let (nextSt, (exp, _)) := stepSetValue st valStr valId
    reply (makeSnapshot nextSt exp)
    runLoop stdin nextSt exp
  | ["SET_UPSTREAM", uSessStr, uValStr, valStr, freshIdStr] =>
    let uSess := uSessStr.toNat?.getD 0
    let uVal := uValStr.toNat?.getD 0
    let freshId := freshIdStr.toNat?.getD 0
    let newUpstream : SessionValue String := { sessionId := uSess, valueId := uVal, value := valStr }
    let nextSt := stepSetValueFromUpstream st newUpstream freshId
    let nextExp := nextSt.sessionValue
    reply (makeSnapshot nextSt nextExp)
    runLoop stdin nextSt nextExp
  | _ =>
    IO.eprintln s!"Unknown command: {trimmed}"
    runLoop stdin st lastExp

def main : IO Unit := do
  let stdin ← IO.getStdin
  let dummy : SessionValue String := { sessionId := 0, valueId := 0, value := "" }
  let initSt := initialState dummy 0
  runLoop stdin initSt dummy
