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
import JvmBytecode
import proofs.JvmEquiv.Infra
import proofs.JvmEquiv.Batch1
import proofs.JvmEquiv.Batch2
import proofs.JvmEquiv.FlatInfra
import proofs.JvmEquiv.SubBatch23
import proofs.JvmEquiv.Batch3a
import proofs.JvmEquiv.Batch3b
import proofs.JvmEquiv.Family1
import proofs.JvmEquiv.Family1Bitwise
import proofs.JvmEquiv.Family2
import proofs.JvmEquiv.Family2b
import proofs.JvmEquiv.HeapInfra
import proofs.JvmEquiv.SharedStep
import proofs.JvmEquiv.StepExt
import proofs.JvmEquiv.Family3
import proofs.JvmEquiv.Family3b
import proofs.JvmEquiv.Family3c
import proofs.JvmEquiv.Family4
import proofs.JvmEquiv.Family5a
import proofs.JvmEquiv.Family5b
import proofs.JvmEquiv.Family5c
import proofs.JvmEquiv.Family5d
import proofs.JvmEquiv.Family6a
import proofs.JvmEquiv.Family6b
import proofs.JvmEquiv.Family6c
import proofs.JvmEquiv.Family6d

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
    unless `Algorithm.JvmVerification |>.isPrefixOf n do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    count := count + 1
    for c in ci.type.getUsedConstants do
      if `Algorithm.JvmBytecode |>.isPrefixOf c then
        provenProgs := provenProgs.insert c
    let axioms ← liftCoreM <| Lean.collectAxioms n
    let bad := axioms.filter (fun a => !allowed.contains a && !isJvmBvCheckAxiom env a)
    unless bad.isEmpty do
      logError m!"JVM equivalence theorem {n} depends on non-standard axioms: {bad.toList}"
  if count == 0 then
    logError "no JVM equivalence theorems found"
  for (n, ci) in env.constants.toList do
    unless `Algorithm.JvmBytecode |>.isPrefixOf n do continue
    unless ci matches .defnInfo _ do continue
    if n.isInternal then continue
    if n.toString.endsWith "_prog" && !provenProgs.contains n then
      logError m!"lifted JVM program {n} has no equivalence theorem in Algorithm.JvmVerification"

#audit_jvm_equiv_axioms
