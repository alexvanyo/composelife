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

namespace Jvm

open Lean in
/-- Whether `a` is an axiom added by `bv_check` or `bv_decide` to trust the compiled LRAT checker. -/
def isJvmBvCheckAxiom (env : Environment) (a : Name) : Bool :=
  let named := match a with
    | .str (.str (.str _ "_native") "bv_decide") _ => true
    | _ => false
  named && match env.find? a with
    | some (.axiomInfo info) =>
      info.type.isAppOfArity ``Eq 3 &&
        (info.type.getArg! 1).isAppOfArity `Std.Tactic.BVDecide.Reflect.verifyBVExpr 2 &&
        (info.type.getArg! 2).isConstOf ``Bool.true
    | _ => false

open Lean in
private def isJvmExecConst (c : Name) : Bool :=
  let s : String := toString c
  s.endsWith "runJvm" || s.endsWith "runJvmRes" ||
    s.endsWith "runJvmFast" || s.endsWith "runJvmResFast" || s.endsWith "runJvmValFast"

open Lean in
def isNonTrivialTheoremType (ty : Expr) : Bool := Id.run do
  let mut cur := ty
  while cur.isForall do
    cur := cur.bindingBody!
  if cur.isConstOf ``True then
    return false
  if cur.isAppOfArity ``Eq 3 && cur.getArg! 1 == cur.getArg! 2 then
    return false
  return true

open Lean in
private def executesProg (ty : Expr) (progName : Name) : Bool :=
  (ty.find? fun e =>
    e.isApp &&
    (match e.getAppFn.constName? with
    | some fn => isJvmExecConst fn
    | none => false) &&
    e.getAppArgs.any (fun arg => (arg.find? (·.isConstOf progName)).isSome)).isSome

def referencesJvmExec (consts : Array Lean.Name) : Bool :=
  consts.any isJvmExecConst

open Lean Elab Command in
/-- Audits all JVM equivalence theorems in `verifNs` and ensures every `_prog` in `bytecodeNs` is covered. -/
elab "#audit_jvm_equiv_axioms" verifNs:ident bytecodeNs:ident : command => do
  let env ← getEnv
  let verifPrefix := verifNs.getId
  let bytecodePrefix := bytecodeNs.getId
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut provenProgs : NameSet := {}
  let mut bytecodeProgs := 0
  for (n, ci) in env.constants.toList do
    unless verifPrefix.isPrefixOf n do continue
    if n.isInternal then continue
    if ci matches .axiomInfo _ then
      logError m!"verification namespace {verifPrefix} must not declare custom axiom {n}"
      continue
    unless ci matches .thmInfo _ do continue
    count := count + 1
    let used := ci.type.getUsedConstants
    if referencesJvmExec used && isNonTrivialTheoremType ci.type then
      for c in used do
        if bytecodePrefix.isPrefixOf c && executesProg ci.type c then
          provenProgs := provenProgs.insert c
    let axioms ← liftCoreM <| Lean.collectAxioms n
    let bad := axioms.filter (fun a => !allowed.contains a && !isJvmBvCheckAxiom env a)
    unless bad.isEmpty do
      logError m!"JVM equivalence theorem {n} depends on non-standard axioms: {bad.toList}"
  if count == 0 then
    logError "no JVM equivalence theorems found"
  for (n, ci) in env.constants.toList do
    unless bytecodePrefix.isPrefixOf n do continue
    unless ci matches .defnInfo _ do continue
    if n.isInternal then continue
    if n.toString.endsWith "_prog" then
      bytecodeProgs := bytecodeProgs + 1
      unless provenProgs.contains n do
        logError m!"lifted JVM program {n} has no JVM execution equivalence theorem in {verifPrefix}"
  if bytecodeProgs == 0 then
    logError m!"no lifted *_prog definitions found in {bytecodePrefix}"

open Lean Elab Command in
/-- Shared checker for axiom hygiene across module master theorems and mutation proofs. -/
def checkMasterTheoremAxioms (isMaster : Name → Bool) : CommandElabM Unit := do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let some modIdx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[modIdx.toNat]!
    unless isMaster mod || mod.toString.endsWith "Mutations" do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    count := count + 1
    let axioms ← liftCoreM <| Lean.collectAxioms n
    let bad := axioms.filter (fun a => !allowed.contains a && !isJvmBvCheckAxiom env a)
    unless bad.isEmpty do
      logError m!"master theorem {n} depends on non-standard axioms: {bad.toList}"
  if count == 0 then
    logError "no master theorems found"

open Lean Elab Command in
/-- Shared checker for `X` / `X_Impl` master theorem naming conventions. -/
def checkMasterTheoremNames (isMaster isProof : Name → Bool) : CommandElabM Unit := do
  let env ← getEnv
  let moduleOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)
  let mut masters : NameSet := {}
  for (n, ci) in env.constants.toList do
    let some mod := moduleOf n | continue
    unless isMaster mod do continue
    let .thmInfo info := ci | continue
    if n.isInternal then continue
    masters := masters.insert n
    let .str _ last := n | continue
    for suffix in ["_Impl", "_spec", "_thm"] do
      if last.endsWith suffix then
        logError m!"master theorem {n} ends in `{suffix}`: name it for what it states"
    let impl := n.appendAfter "_Impl"
    let mut body := info.value
    while body.isLambda do body := body.bindingBody!
    unless body.getAppFn.isConstOf impl && body.getAppArgs.all (·.isBVar) do
      logError m!"master theorem {n} must be `{impl}` applied to its parameters"
  for (n, ci) in env.constants.toList do
    unless ci matches .thmInfo _ do continue
    let .str pre last := n | continue
    unless last.endsWith "_Impl" do continue
    let some mod := moduleOf n | continue
    unless isProof mod do continue
    unless masters.contains (.str pre (last.dropEnd 5).toString) do
      logError m!"{n} is not the proof of a master theorem `{(last.dropEnd 5).toString}`"

end Jvm
