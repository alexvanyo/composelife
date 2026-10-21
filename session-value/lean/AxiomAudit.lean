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
import SessionValueTheorems
import proofs.Mutations

/-!
# Axiom audit

Fails the build if any master theorem or mutation proof depends on an axiom other than `propext`,
`Classical.choice`, `Quot.sound` and the axioms `bv_check` adds. This catches `sorry`, custom axioms and
`native_decide`.

`bv_check` (like `bv_decide`) adds an axiom `<declaration>._native.bv_decide.ax_<n>` stating
`verifyBVExpr <goal> <certificate> = true`, that the compiled LRAT checker accepts its certificate; these are
allowed. Lean sources may not declare axioms themselves (`checkLeanBvCheck` rejects them), so only the tactic
can add one.
-/

open Lean in
/-- Whether `a` is an axiom added by `bv_check` or `bv_decide` to trust the compiled LRAT checker. -/
def isBvCheckAxiom (env : Environment) (a : Name) : Bool :=
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
/-- Checks the axioms of every theorem declared in the master theorem and mutation modules. -/
elab "#audit_master_theorem_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let some modIdx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[modIdx.toNat]!
    unless mod == `SessionValueTheorems || mod.toString.endsWith "Mutations" do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    count := count + 1
    let axioms ← liftCoreM <| Lean.collectAxioms n
    let bad := axioms.filter (fun a => !allowed.contains a && !isBvCheckAxiom env a)
    unless bad.isEmpty do
      logError m!"master theorem {n} depends on non-standard axioms: {bad.toList}"
  if count == 0 then
    logError "no master theorems found"

#audit_master_theorem_axioms
