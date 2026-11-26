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

import Jvm.Proofs

/-!
# Fast and reference JVM runners agree on programs without `i2l`

`Jvm.runJvmRes_of_runJvmResFast` only transports successful runs. Equivalence theorems that also characterize
trapping runs (`none`) need the full equality, which holds for every program that never fuses `i2l; lconst; land`.
-/

namespace UiCommon.KotlinJvmVerification

open Jvm

/-- `false` exactly on `i2l`, the only instruction the fast runner fuses with its successors. -/
def notI2l : JvmInstr → Bool
  | .i2l => false
  | _ => true

theorem i2l_not_mem_of_all {prog : List JvmInstr} (h : prog.all notI2l = true) : JvmInstr.i2l ∉ prog := by
  intro hm
  have := List.all_eq_true.mp h _ hm
  simp [notI2l] at this

section
variable {Ext Heap : Type} (hooks : JvmHooks Ext Heap)

theorem dispatchBranch_eq_evalBranchTarget' {α : Type}
    (pc : Nat) (instr : JvmInstr) (stack : List (JvmVal Ext))
    (onTaken : Nat → List (JvmVal Ext) → Option α)
    (onFallthrough : List (JvmVal Ext) → Option α) :
    dispatchBranch hooks pc instr stack onTaken onFallthrough =
      match evalBranchTarget hooks pc instr stack with
      | some (true, target, s) => onTaken target s
      | some (false, _, s) => onFallthrough s
      | none => none := by
  cases instr <;> simp [dispatchBranch, evalBranchTarget] <;>
    rcases stack with _ | ⟨v0, s0⟩ <;> try rfl
  all_goals first
  | ((split <;> rfl); done)
  | ((cases h0 : hooks.isZero? v0 <;> simp [h0] <;> try (split <;> rfl)); done)
  | ((cases h0 : v0.asI32? <;> simp [h0] <;> try (split <;> rfl)); done)
  | (rcases s0 with _ | ⟨v1, s⟩ <;> try dsimp <;> first
    | rfl
    | ((cases h1 : v1.asI32? with
        | none => simp
        | some _ => cases h0 : v0.asI32? with
          | none => simp
          | some _ => simp; split <;> rfl); done)
    | ((cases h1 : JvmVal.refEq? hooks.beqRefExt v1 v0 <;> simp <;> try (split <;> rfl)); done))

theorem evalBranchTarget_false_pc'
    {pc : Nat} {instr : JvmInstr} {stack : List (JvmVal Ext)} {nextPc : Nat} {s' : List (JvmVal Ext)}
    (hev : evalBranchTarget hooks pc instr stack = some (false, nextPc, s')) :
    nextPc = pc + 1 := by
  cases instr <;> simp [evalBranchTarget, dispatchBranch] at hev
  all_goals
    rcases stack with _ | ⟨v0, _ | ⟨v1, s⟩⟩ <;> simp at hev
    all_goals
      try (cases h0 : hooks.isZero? v0 <;> simp [h0] at hev)
      try (cases h0 : v0.asI32? <;> simp [h0] at hev)
      try (cases h1 : v1.asI32? <;> simp [h1] at hev)
      try (cases h1 : JvmVal.refEq? hooks.beqRefExt v1 v0 <;> simp [h1] at hev)
      all_goals (try split at hev) <;> simp_all

theorem runJvmRes_branch_of_evalBranchTarget'
    {fuel : Nat} {prog : List JvmInstr} {st : JvmState Ext Heap} {instr : JvmInstr}
    (hget : prog[st.pc]? = some instr) (hbr : isBranchInstr instr = true) :
    runJvmRes hooks (fuel + 1) prog st =
      match evalBranchTarget hooks st.pc instr st.stack with
      | some (_, nextPc, s') => runJvmRes hooks fuel prog { st with pc := nextPc, stack := s' }
      | none => none := by
  cases instr <;> simp [isBranchInstr] at hbr <;>
    simp [runJvmRes, hget, evalBranchTarget, dispatchBranch]
  · rcases st.stack with _ | ⟨v, s⟩
    · rfl
    · cases hev : hooks.isZero? v with | none => simp [hev] | some b => cases b <;> simp [hev]
  · rcases st.stack with _ | ⟨v, s⟩
    · rfl
    · cases hev : hooks.isZero? v with | none => simp [hev] | some b => cases b <;> simp [hev]
  · rcases st.stack with _ | ⟨v, s⟩
    · rfl
    · cases hv : v.asI32? with | none => simp [hv] | some iv => by_cases h : iv.toBitVec.slt 0#32 <;> simp [hv, h]
  · rcases st.stack with _ | ⟨v, s⟩
    · rfl
    · cases hv : v.asI32? with | none => simp [hv] | some iv => by_cases h : iv.toBitVec.sle 0#32 <;> simp [hv, h]
  · rcases st.stack with _ | ⟨v, s⟩
    · rfl
    · cases hv : v.asI32? with | none => simp [hv] | some iv => by_cases h : (0#32).slt iv.toBitVec <;> simp [hv, h]
  · rcases st.stack with _ | ⟨v, s⟩
    · rfl
    · cases hv : v.asI32? with | none => simp [hv] | some iv => by_cases h : (0#32).sle iv.toBitVec <;> simp [hv, h]
  · rcases st.stack with _ | ⟨v, s⟩
    · rfl
    · by_cases h : v.isNull <;> simp [h]
  · rcases st.stack with _ | ⟨v, s⟩
    · rfl
    · by_cases h : v.isNull <;> simp [h]
  · rcases st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> try rfl
    cases ha : a.asI32? <;> cases hb : b.asI32? <;> simp [ha, hb]
    split <;> rfl
  · rcases st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> try rfl
    cases ha : a.asI32? <;> cases hb : b.asI32? <;> simp [ha, hb]
    split <;> rfl
  · rcases st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> try rfl
    cases ha : a.asI32? <;> cases hb : b.asI32? <;> simp [ha, hb]
    split <;> rfl
  · rcases st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> try rfl
    cases ha : a.asI32? <;> cases hb : b.asI32? <;> simp [ha, hb]
    split <;> rfl
  · rcases st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> try rfl
    cases ha : a.asI32? <;> cases hb : b.asI32? <;> simp [ha, hb]
    split <;> rfl
  · rcases st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> try rfl
    cases ha : a.asI32? <;> cases hb : b.asI32? <;> simp [ha, hb]
    split <;> rfl
  · rcases st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> try rfl
    cases hc : JvmVal.refEq? hooks.beqRefExt a b with | none => simp [hc] | some c => cases c <;> simp [hc]
  · rcases st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩ <;> try rfl
    cases hc : JvmVal.refEq? hooks.beqRefExt a b with | none => simp [hc] | some c => cases c <;> simp [hc]
  · unfold stepInstr; rfl
  · rcases st.stack with _ | ⟨k, s⟩
    · rfl
    · cases hk : k.asI32? <;> simp [hk]
  · rcases st.stack with _ | ⟨k, s⟩
    · rfl
    · cases hk : k.asI32? <;> simp [hk]

/-- On a program without `i2l`, the fast runner computes exactly the reference `runJvmRes`, including traps. -/
theorem runJvmResFast_eq_runJvmRes (prog : List JvmInstr) (hno : JvmInstr.i2l ∉ prog) :
    ∀ fuel pc (st : JvmState Ext Heap), st.pc = pc →
      runJvmResFast hooks fuel prog pc (prog.drop pc) st = runJvmRes hooks fuel prog st := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ f ih =>
    intro pc st hpc
    have hst : { st with pc := pc } = st := by cases st; cases hpc; rfl
    cases hdrop : prog.drop pc with
    | nil =>
      have hg : prog[st.pc]? = none := by
        rw [hpc]
        exact List.getElem?_eq_none (List.drop_eq_nil_iff.mp hdrop)
      simp [runJvmResFast, runJvmRes, hg]
    | cons instr rest =>
      have hg : prog[st.pc]? = some instr := by
        have h := (List.getElem?_drop (xs := prog) (i := pc) (j := 0))
        rw [hdrop] at h; simp at h; rw [hpc, ← h]
      have hrest : rest = prog.drop (pc + 1) := by
        rw [← List.drop_drop, hdrop]; rfl
      have hmem : instr ∈ prog := List.mem_of_getElem? hg
      have hni : instr ≠ .i2l := fun h => hno (h ▸ hmem)
      by_cases hbr : isBranchInstr instr = true
      · rw [runJvmRes_branch_of_evalBranchTarget' hooks hg hbr]
        have hfast : runJvmResFast hooks (f + 1) prog pc (instr :: rest) st =
            dispatchBranch hooks pc instr st.stack
              (fun target s => runJvmResFast hooks f prog target (prog.drop target)
                { st with pc := target, stack := s })
              (fun s => runJvmResFast hooks f prog (pc + 1) rest { st with pc := pc + 1, stack := s }) := by
          cases instr <;> simp [isBranchInstr] at hbr <;> simp [runJvmResFast, isBranchInstr]
        rw [hfast, dispatchBranch_eq_evalBranchTarget', hpc]
        cases hev : evalBranchTarget hooks pc instr st.stack with
        | none => rfl
        | some x =>
          rcases x with ⟨taken, nextPc, s'⟩
          cases taken
          · have hpc' := evalBranchTarget_false_pc' hooks hev
            subst hpc'
            simp only []
            rw [hrest]
            exact ih (pc + 1) _ rfl
          · exact ih nextPc _ rfl
      · have hbrF : isBranchInstr instr = false := Bool.eq_false_iff.mpr hbr
        rw [runJvmResFast_step_nonbranch hooks f prog pc instr rest st hbrF (fun h => hni h.1),
          runJvmRes_nonbranch hooks f prog st instr hg hbrF, hst]
        cases hs : stepInstr hooks instr st with
        | inl o =>
          cases o with
          | none => rfl
          | some st' =>
            simp only []
            split
            · next hpc' => rw [hrest]; exact ih (pc + 1) st' hpc'
            · exact ih st'.pc st' rfl
        | inr o => cases o <;> rfl

theorem runJvmRes_eq_runJvmResFast0 (prog : List JvmInstr) (hno : prog.all notI2l = true)
    (fuel : Nat) (st : JvmState Ext Heap) (hpc : st.pc = 0) :
    runJvmRes hooks fuel prog st = runJvmResFast hooks fuel prog 0 prog st := by
  rw [← runJvmResFast_eq_runJvmRes hooks prog (i2l_not_mem_of_all hno) fuel 0 st hpc, List.drop_zero]

end

end UiCommon.KotlinJvmVerification
