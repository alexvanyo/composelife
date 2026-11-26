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

import Jvm.Audit
import GeometryTheorems
import proofs.Mutations

/-!
# Axiom audit

Fails the build if any master theorem or mutation proof depends on an axiom other than `propext`,
`Classical.choice`, `Quot.sound` and the axioms `bv_check` adds. This catches `sorry`, custom axioms and
`native_decide`.
-/

open Lean Elab Command in
/-- Checks the axioms of every theorem declared in the master theorem and mutation modules. -/
elab "#audit_master_theorem_axioms" : command =>
  Jvm.checkMasterTheoremAxioms (· == `GeometryTheorems)

#audit_master_theorem_axioms

open Lean Elab Command in
/-- Checks the `X` / `X_Impl` naming pattern for `GeometryTheorems`. -/
elab "#audit_master_theorem_names" : command =>
  Jvm.checkMasterTheoremNames
    (· == `GeometryTheorems)
    (fun mod => mod.getRoot == `proofs || mod == `GeometryProofs)

#audit_master_theorem_names
