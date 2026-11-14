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

import Lean
import Std.Tactic.BVDecide
import JvmSemantics
import JvmBytecode

namespace Geometry.JvmVerification

open Geometry.JvmBytecode

theorem absFloat_closed0_equiv :
    runJvm 5 f_Geometry_absFloat___closed__0_prog (initJvmState []) =
      some (.f64 0.0) := by
  rfl

theorem absFloat_equiv (x : Float) :
    runJvm 15 f_Geometry_absFloat_prog (initJvmState [(0, .f64 x)]) =
      some (.f64 (Geometry.absFloat x)) := by
  change some (JvmVal.f64 _) = some (JvmVal.f64 _)
  congr 2
  dsimp [JvmVal.asI32, JvmVal.asF64, setLocal, initJvmState, List.foldl, Geometry.absFloat]
  by_cases hlt : x < 0.0
  · simp [hlt]
  · by_cases heq : (x == 0.0) = true <;> simp [hlt, heq]

theorem absInt_equiv (x : Int32) :
    runJvm 15 f_Geometry_absInt_prog (initJvmState [(0, .i32 x.toUInt32)]) =
      some (.i32 (Geometry.absInt x)) := by
  rfl

end Geometry.JvmVerification

open Lean in
private def isJvmBvCheckAxiom (env : Environment) (a : Name) : Bool :=
  let named := match a with
    | .str (.str (.str _ "_native") "bv_decide") _ => true
    | _ => false
  named && match env.find? a with
    | some (.axiomInfo info) =>
      info.type.isAppOfArity ``Eq 3 &&
        (info.type.getArg! 1).isAppOf `Std.Tactic.BVDecide.Reflect.verifyBVExpr &&
        (info.type.getArg! 2).isConstOf ``Bool.true
    | _ => false

open Lean Elab Command in
elab "#audit_jvm_equiv_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut provenProgs : NameSet := {}
  for (n, ci) in env.constants.toList do
    unless `Geometry.JvmVerification |>.isPrefixOf n do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    count := count + 1
    for c in ci.type.getUsedConstants do
      if `Geometry.JvmBytecode |>.isPrefixOf c then
        provenProgs := provenProgs.insert c
    let axioms ← liftCoreM <| Lean.collectAxioms n
    let bad := axioms.filter (fun a => !allowed.contains a && !isJvmBvCheckAxiom env a)
    unless bad.isEmpty do
      logError m!"JVM equivalence theorem {n} depends on non-standard axioms: {bad.toList}"
  if count == 0 then
    logError "no JVM equivalence theorems found"
  for (n, ci) in env.constants.toList do
    unless `Geometry.JvmBytecode |>.isPrefixOf n do continue
    unless ci matches .defnInfo _ do continue
    if n.isInternal then continue
    if n.toString.endsWith "_prog" && !provenProgs.contains n then
      logError m!"lifted JVM program {n} has no equivalence theorem in Geometry.JvmVerification"

#audit_jvm_equiv_axioms
