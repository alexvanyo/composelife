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

import Jvm.Semantics

namespace Jvm

theorem signExtend_and_mask (x : UInt32) :
    ({ toBitVec := BitVec.signExtend 64 x.toBitVec } : UInt64) &&& 4294967295 = x.toUInt64 := by
  apply UInt64.toBitVec_inj.mp
  change (BitVec.signExtend 64 x.toBitVec &&& 4294967295#64) = BitVec.setWidth 64 x.toBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth]
  by_cases hi : i < 64
  · rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
    by_cases h : i < 32
    · have ht : (4294967295 % 2 ^ 64).testBit i = true := by
        have : 4294967295 % 2 ^ 64 = 2 ^ 32 - 1 := rfl
        rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true h
      simp [hi, h, ht]
    · have ht : (4294967295 % 2 ^ 64).testBit i = false := by
        have : 4294967295 % 2 ^ 64 = 2 ^ 32 - 1 := rfl
        rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_false h
      have hx : x.toBitVec.getLsbD i = false := by
        simp only [BitVec.getLsbD]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.toBitVec.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [hi, h, ht, hx]
  · simp [hi]

theorem coerceInI32_of_le (v lo hi : UInt32) (h1 : lo.toNat ≤ v.toNat) (h2 : v.toNat ≤ hi.toNat)
    (h3 : hi.toNat < 2 ^ 31) : coerceInI32 v lo hi = v := by
  dsimp [coerceInI32]
  have hlt1 : v.toBitVec.slt lo.toBitVec = false := by
    rw [BitVec.slt_eq_ult]
    have hm1 : v.toBitVec.msb = false := by rw [BitVec.msb_eq_toNat]; simp; omega
    have hm2 : lo.toBitVec.msb = false := by rw [BitVec.msb_eq_toNat]; simp; omega
    simp [hm1, hm2, BitVec.ult]; omega
  have hlt2 : hi.toBitVec.slt v.toBitVec = false := by
    rw [BitVec.slt_eq_ult]
    have hm1 : v.toBitVec.msb = false := by rw [BitVec.msb_eq_toNat]; simp; omega
    have hm2 : hi.toBitVec.msb = false := by rw [BitVec.msb_eq_toNat]; simp; omega
    simp [hm1, hm2, BitVec.ult]; omega
  simp [hlt1, hlt2]

@[simp] theorem compareUnsigned_slt' (a b : UInt32) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32 = decide (a < b) := by
  by_cases h1 : a == b <;> by_cases h2 : a < b <;> simp [h1, h2]
  have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; exact Nat.lt_irrefl _ h2

@[simp] theorem compareUnsigned_sle' (a b : UInt32) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.sle 0#32 = decide (a ≤ b) := by
  by_cases h1 : a == b <;> by_cases h2 : a < b <;> simp [h1, h2]
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; exact Nat.le_refl _
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; exact Nat.le_refl _
  · exact Nat.le_of_lt h2
  · have hne : a ≠ b := fun h => h1 (beq_iff_eq.mpr h)
    have hne' : a.toBitVec.toNat ≠ b.toBitVec.toNat :=
      fun h => hne (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))
    change ¬ (a.toBitVec.toNat < b.toBitVec.toNat) at h2
    change b.toBitVec.toNat < a.toBitVec.toNat
    omega

def isBranchInstr : JvmInstr → Bool
  | .ifeq _ | .ifne _ | .iflt _ | .ifle _ | .ifgt _ | .ifge _
  | .ifnull _ | .ifnonnull _ | .if_icmpeq _ | .if_icmpne _ | .if_icmplt _
  | .if_icmpge _ | .if_icmpgt _ | .if_icmple _ | .if_acmpeq _ | .if_acmpne _
  | .tableswitch _ _ _ | .lookupswitch _ _ | .goto _ => true
  | _ => false

theorem runJvm_nonbranch {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState Ext Heap) (instr : JvmInstr)
    (hget : prog[st.pc]? = some instr) (hnbr : isBranchInstr instr = false) :
    runJvm hooks (fuel + 1) prog st =
      match stepInstr hooks instr st with
      | .inl (some st') => runJvm hooks fuel prog st'
      | .inl none => none
      | .inr res => res := by
  cases instr <;> simp [isBranchInstr] at hnbr <;> simp [runJvm, hget] <;> rfl

def stepListAt {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (pc : Nat) (instrs : List JvmInstr) (st : JvmState Ext Heap) : Option (JvmVal Ext) :=
  match instrs with
  | [] => none
  | instr :: rest =>
    if isBranchInstr instr then none
    else match stepInstr hooks instr { st with pc := pc } with
    | .inl (some st') => if st'.pc = pc + 1 then stepListAt hooks (pc + 1) rest st' else none
    | .inl none => none
    | .inr res => res

theorem runJvm_of_stepListAt {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (prog instrs : List JvmInstr)
    (fuel : Nat) (st : JvmState Ext Heap) (v : JvmVal Ext)
    (hdrop : prog.drop st.pc = instrs) (hfuel : instrs.length ≤ fuel)
    (hstep : stepListAt hooks st.pc instrs st = some v) :
    runJvm hooks fuel prog st = some v := by
  induction instrs generalizing fuel st with
  | nil => simp [stepListAt] at hstep
  | cons instr rest ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel' =>
      have hget : prog[st.pc]? = some instr := by
        have h0 : (prog.drop st.pc)[0]? = prog[st.pc]? := by simp [List.getElem?_drop]
        rw [hdrop] at h0; simpa using h0.symm
      simp only [stepListAt] at hstep
      split at hstep
      · simp at hstep
      · next hnbr =>
        have hbr : isBranchInstr instr = false := Bool.eq_false_iff.mpr hnbr
        rw [runJvm_nonbranch hooks fuel' prog st instr hget hbr]
        have hst : { st with pc := st.pc } = st := rfl
        rw [hst] at hstep
        cases hs : stepInstr hooks instr st with
        | inl opt =>
          cases opt with
          | none => simp [hs] at hstep
          | some st' =>
            simp only [hs] at hstep
            split at hstep
            · next hpc =>
              apply ih fuel' st'
              · rw [hpc, List.drop_add_one_eq_tail_drop, hdrop]; rfl
              · simp at hfuel; omega
              · rw [hpc]; exact hstep
            · simp at hstep
        | inr res => simpa [hs] using hstep

def stepListAtClean {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (pc : Nat) (instrs : List JvmInstr) (st : JvmState Ext Heap) : Option (JvmVal Ext) :=
  match instrs with
  | .i2l :: .lconst 4294967295 :: .land :: rest =>
    match st.stack with
    | .i32 x :: s => stepListAtClean hooks (pc + 3) rest { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
    | _ => none
  | [] => none
  | instr :: rest =>
    if isBranchInstr instr then none
    else match stepInstr hooks instr { st with pc := pc } with
    | .inl (some st') => if st'.pc = pc + 1 then stepListAtClean hooks (pc + 1) rest st' else none
    | .inl none => none
    | .inr res => res

theorem stepListAt_of_clean {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (pc : Nat) (instrs : List JvmInstr) (st : JvmState Ext Heap) (v : JvmVal Ext)
    (h : stepListAtClean hooks pc instrs st = some v) :
    stepListAt hooks pc instrs st = some v := by
  induction pc, instrs, st using stepListAtClean.induct (hooks := hooks) with
  | case1 pc st rest x s hstk ih =>
    simp [stepListAtClean, hstk] at h
    simp [stepListAt, isBranchInstr, stepInstr, hstk, JvmVal.asI32, JvmVal.asI64, signExtend_and_mask]
    exact ih h
  | case2 pc st rest hno =>
    simp [stepListAtClean] at h
  | case3 pc st => simp [stepListAtClean] at h
  | case4 pc st instr rest hno hbr =>
    simp [stepListAtClean, hbr] at h
  | case5 pc st instr rest hno hbr st' hstep hpc ih =>
    simp [stepListAtClean, hbr, hstep, hpc] at h
    simp [stepListAt, hbr, hstep, hpc]
    exact ih h
  | case6 pc st instr rest hno hbr st' hstep hpc =>
    simp [stepListAtClean, hbr, hstep, hpc] at h
  | case7 pc st instr rest hno hbr hstep =>
    simp [stepListAtClean, hbr, hstep] at h
  | case8 pc st instr rest hno hbr res hstep =>
    simp [stepListAtClean, hbr, hstep] at h
    simp [stepListAt, hbr, hstep, h]

theorem runJvm_of_stepListAtClean {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (prog instrs : List JvmInstr)
    (fuel : Nat) (st : JvmState Ext Heap) (v : JvmVal Ext)
    (hdrop : prog.drop st.pc = instrs) (hfuel : instrs.length ≤ fuel)
    (hstep : stepListAtClean hooks st.pc instrs st = some v) :
    runJvm hooks fuel prog st = some v :=
  runJvm_of_stepListAt hooks prog instrs fuel st v hdrop hfuel
    (stepListAt_of_clean hooks st.pc instrs st v hstep)

theorem runJvmRes_nonbranch {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState Ext Heap) (instr : JvmInstr)
    (hget : prog[st.pc]? = some instr) (hnbr : isBranchInstr instr = false) :
    runJvmRes hooks (fuel + 1) prog st =
      match stepInstr hooks instr st with
      | .inl (some st') => runJvmRes hooks fuel prog st'
      | .inl none => none
      | .inr (some res) => some (res, st)
      | .inr none => none := by
  cases instr <;> simp [isBranchInstr] at hnbr <;> simp [runJvmRes, hget] <;> rfl

def runJvmResFast {Ext Heap : Type} (hooks : JvmHooks Ext Heap) :
    Nat → List JvmInstr → Nat → List JvmInstr → JvmState Ext Heap → Option (JvmVal Ext × JvmState Ext Heap)
  | 0, _, _, _, _ => none
  | f1 + 1, prog, pc, instrs, st =>
    match instrs with
    | [] => none
    | instr :: rest =>
      match instr with
      | .i2l =>
        match rest with
        | .lconst 4294967295 :: .land :: rest' =>
          match f1 with
          | 0 => none
          | f2 + 1 =>
            match f2 with
            | 0 => none
            | f3 + 1 =>
              match st.stack with
              | .i32 x :: s =>
                runJvmResFast hooks f3 prog (pc + 3) rest' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              | _ => none
        | _ =>
          match stepInstr hooks instr { st with pc := pc } with
          | .inl (some st') =>
            if st'.pc = pc + 1 then runJvmResFast hooks f1 prog (pc + 1) rest st'
            else runJvmResFast hooks f1 prog st'.pc (prog.drop st'.pc) st'
          | .inl none => none
          | .inr (some v) => some (v, { st with pc := pc })
          | .inr none => none
      | .goto target =>
        runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target }
      | .ifeq target =>
        match st.stack with
        | v :: s =>
          if hooks.isZero v then runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifne target =>
        match st.stack with
        | v :: s =>
          if !hooks.isZero v then runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .iflt target =>
        match st.stack with
        | v :: s =>
          if v.asI32.toBitVec.slt 0#32 then runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifle target =>
        match st.stack with
        | v :: s =>
          if v.asI32.toBitVec.sle 0#32 then runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifgt target =>
        match st.stack with
        | v :: s =>
          if (0#32).slt v.asI32.toBitVec then runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifge target =>
        match st.stack with
        | v :: s =>
          if (0#32).sle v.asI32.toBitVec then runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifnull target =>
        match st.stack with
        | v :: s =>
          if v.isNull then runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifnonnull target =>
        match st.stack with
        | v :: s =>
          if !v.isNull then runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmpeq target =>
        match st.stack with
        | b :: a :: s =>
          if a.asI32 == b.asI32 then runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmpne target =>
        match st.stack with
        | b :: a :: s =>
          if !(a.asI32 == b.asI32) then runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmplt target =>
        match st.stack with
        | b :: a :: s =>
          if a.asI32.toBitVec.slt b.asI32.toBitVec then
            runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmpge target =>
        match st.stack with
        | b :: a :: s =>
          if b.asI32.toBitVec.sle a.asI32.toBitVec then
            runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmpgt target =>
        match st.stack with
        | b :: a :: s =>
          if b.asI32.toBitVec.slt a.asI32.toBitVec then
            runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmple target =>
        match st.stack with
        | b :: a :: s =>
          if a.asI32.toBitVec.sle b.asI32.toBitVec then
            runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_acmpeq target =>
        match st.stack with
        | b :: a :: s =>
          if JvmVal.refEq hooks.beqExt a b then
            runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_acmpne target =>
        match st.stack with
        | b :: a :: s =>
          if !JvmVal.refEq hooks.beqExt a b then
            runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .tableswitch low targets defaultTarget =>
        match st.stack with
        | key :: s =>
          let target := tableswitchTarget key.asI32 low targets defaultTarget
          runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
        | _ => none
      | .lookupswitch cases defaultTarget =>
        match st.stack with
        | key :: s =>
          let target := lookupswitchTarget key.asI32 cases defaultTarget
          runJvmResFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
        | _ => none
      | _ =>
        match stepInstr hooks instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then
            runJvmResFast hooks f1 prog (pc + 1) rest st'
          else
            runJvmResFast hooks f1 prog st'.pc (prog.drop st'.pc) st'
        | .inl none => none
        | .inr (some v) => some (v, { st with pc := pc })
        | .inr none => none

def runJvmFast {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState Ext Heap) :
    Option (JvmVal Ext) :=
  (runJvmResFast hooks fuel prog pc instrs st).map Prod.fst

theorem runJvm_eq_runJvmRes {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (hite : ∀ c t e, hooks.iteVal c t e = if c then t else e)
    (hiteZ : ∀ v t e, hooks.iteZero v t e = if hooks.isZero v then t else e)
    (hiteNZ : ∀ v t e, hooks.iteNonZero v t e = if !hooks.isZero v then t else e)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState Ext Heap) :
    runJvm hooks fuel prog st = (runJvmRes hooks fuel prog st).map Prod.fst := by
  induction fuel generalizing st with
  | zero => rfl
  | succ f ih =>
    cases h : prog[st.pc]? with
    | none => simp [runJvm, runJvmRes, h]
    | some instr =>
      cases hbr : isBranchInstr instr with
      | false =>
        rw [runJvm_nonbranch hooks _ _ _ instr h hbr, runJvmRes_nonbranch hooks _ _ _ instr h hbr]
        cases stepInstr hooks instr st with
        | inl opt => cases opt with | none => rfl | some st' => simp only [ih]
        | inr r => cases r <;> rfl
      | true =>
        cases instr with
        | goto target =>
          simp only [runJvm, runJvmRes, h]
          cases stepInstr hooks (.goto target) st with
          | inl opt => cases opt with | none => rfl | some st' => simp only [ih]
          | inr r => cases r <;> rfl
        | ifeq _ =>
          simp only [runJvm, runJvmRes, h]
          rcases st.stack with _ | ⟨v, s⟩
          · rfl
          · simp only [hiteZ, ih]; split <;> rfl
        | ifne _ =>
          simp only [runJvm, runJvmRes, h]
          rcases st.stack with _ | ⟨v, s⟩
          · rfl
          · simp only [hiteNZ, ih]; split <;> rfl
        | iflt _ | ifle _ | ifgt _ | ifge _ =>
          simp only [runJvm, runJvmRes, h]
          rcases st.stack with _ | ⟨v, s⟩
          · rfl
          · simp only [hite, ih]; split <;> rfl
        | ifnull _ | ifnonnull _ =>
          simp only [runJvm, runJvmRes, h]
          rcases st.stack with _ | ⟨v, s⟩
          · rfl
          · simp only [ih]; split <;> rfl
        | if_icmpeq _ | if_icmpne _ | if_icmplt _ | if_icmpge _ | if_icmpgt _ | if_icmple _ =>
          simp only [runJvm, runJvmRes, h]
          rcases st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩
          · rfl
          · rfl
          · simp only [hite, ih]; split <;> rfl
        | if_acmpeq _ | if_acmpne _ =>
          simp only [runJvm, runJvmRes, h]
          rcases st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩
          · rfl
          · rfl
          · simp only [ih]; split <;> rfl
        | tableswitch _ _ _ | lookupswitch _ _ =>
          simp only [runJvm, runJvmRes, h]
          rcases st.stack with _ | ⟨key, s⟩
          · rfl
          · simp only [ih]
        | _ => simp [isBranchInstr] at hbr

theorem runJvmRes_of_runJvmResFast {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr)
    (st : JvmState Ext Heap) (res : JvmVal Ext × JvmState Ext Heap)
    (hpc : st.pc = pc) (hdrop : prog.drop pc = instrs)
    (hfast : runJvmResFast hooks fuel prog pc instrs st = some res) :
    runJvmRes hooks fuel prog st = some res := by
  refine Nat.strongRecOn (motive := fun f => ∀ pc instrs st,
      st.pc = pc → prog.drop pc = instrs → runJvmResFast hooks f prog pc instrs st = some res →
      runJvmRes hooks f prog st = some res) fuel (fun fuel ih pc instrs st hpc hdrop hfast => ?_) pc instrs st hpc hdrop hfast
  · cases fuel with
    | zero => simp [runJvmResFast] at hfast
    | succ f1 =>
      have hg0 : ∀ i rest', instrs = i :: rest' → prog[st.pc]? = some i := by
        intro i rest' heq
        have hg : (prog.drop pc)[0]? = prog[pc]? := by simp [List.getElem?_drop]
        rw [hpc, ← hg, hdrop, heq]; rfl
      have hg1 : ∀ i0 i1 rest', instrs = i0 :: i1 :: rest' → prog[st.pc + 1]? = some i1 := by
        intro i0 i1 rest' heq
        have hg : (prog.drop pc)[1]? = prog[pc + 1]? := by simp [List.getElem?_drop]
        rw [hpc, ← hg, hdrop, heq]; rfl
      have hg2 : ∀ i0 i1 i2 rest', instrs = i0 :: i1 :: i2 :: rest' → prog[st.pc + 2]? = some i2 := by
        intro i0 i1 i2 rest' heq
        have hg : (prog.drop pc)[2]? = prog[pc + 2]? := by simp [List.getElem?_drop]
        rw [hpc, ← hg, hdrop, heq]; rfl
      rcases instrs with _ | ⟨instr, rest⟩
      · simp [runJvmResFast] at hfast
      · have step_catchall (hnbr : isBranchInstr instr = false)
            (hf : (match stepInstr hooks instr { st with pc := pc } with
              | .inl (some st') =>
                if st'.pc = pc + 1 then runJvmResFast hooks f1 prog (pc + 1) rest st'
                else runJvmResFast hooks f1 prog st'.pc (prog.drop st'.pc) st'
              | .inl none => none
              | .inr (some v) => some (v, { st with pc := pc })
              | .inr none => none) = some res) :
            runJvmRes hooks (f1 + 1) prog st = some res := by
          have h0 := hg0 instr rest rfl
          have hst : { st with pc := pc } = st := by cases st; cases hpc; rfl
          rw [runJvmRes_nonbranch hooks f1 prog st instr h0 hnbr]
          rw [hst] at hf
          cases hs : stepInstr hooks instr st with
          | inl opt =>
            cases opt with
            | none => simp [hs] at hf
            | some st' =>
              simp only [hs] at hf ⊢
              split at hf
              · next hpc' => exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest st' hpc' (by rw [← List.drop_drop, hdrop]; rfl) hf
              · exact ih f1 (Nat.lt_succ_self f1) st'.pc (prog.drop st'.pc) st' rfl rfl hf
          | inr r =>
            cases r with
            | none => simp [hs] at hf
            | some v =>
              simp only [hs] at hf ⊢
              exact hf
        cases instr with
        | i2l =>
          rcases rest with _ | ⟨i1, rest1⟩
          · exact step_catchall rfl (by simpa [runJvmResFast] using hfast)
          · cases i1 with
            | lconst v =>
              by_cases hv : v = 4294967295
              · subst hv
                rcases rest1 with _ | ⟨i2, rest2⟩
                · exact step_catchall rfl (by simpa [runJvmResFast] using hfast)
                · cases i2 with
                  | land =>
                    cases f1 with
                    | zero => simp [runJvmResFast] at hfast
                    | succ f2 =>
                      cases f2 with
                      | zero => simp [runJvmResFast] at hfast
                      | succ f3 =>
                        rcases hstk : st.stack with _ | ⟨hd, s⟩
                        · simp [runJvmResFast, hstk] at hfast
                        · cases hd with
                          | i32 x =>
                            have h0 := hg0 .i2l _ rfl
                            have h1 := hg1 .i2l (.lconst 4294967295) _ rfl
                            have h2 := hg2 .i2l (.lconst 4294967295) .land _ rfl
                            rw [runJvmRes_nonbranch hooks _ prog st .i2l h0 rfl]
                            simp only [stepInstr, hstk, JvmVal.asI32]
                            rw [runJvmRes_nonbranch hooks _ prog _ (.lconst 4294967295) (by simpa [Nat.add_assoc] using h1) rfl]
                            simp only [stepInstr]
                            rw [runJvmRes_nonbranch hooks _ prog _ .land (by simpa [Nat.add_assoc] using h2) rfl]
                            simp only [stepInstr, JvmVal.asI64, signExtend_and_mask, hpc]
                            rw [runJvmResFast] at hfast
                            simp only [hstk] at hfast
                            exact ih f3 (by omega) (pc + 3) rest2 { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s } rfl
                              (by rw [← List.drop_drop, hdrop]; rfl) hfast
                          | _ => simp [runJvmResFast, hstk] at hfast
                  | _ => exact step_catchall rfl (by simpa [runJvmResFast] using hfast)
              · exact step_catchall rfl (by
                  cases rest1 <;> simp [runJvmResFast, hv] at hfast ⊢ <;> exact hfast)
            | _ => exact step_catchall rfl (by simpa [runJvmResFast] using hfast)
        | goto target =>
          have h0 := hg0 _ _ rfl
          unfold runJvmRes; rw [h0]; dsimp only
          rw [runJvmResFast] at hfast
          exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
        | ifeq target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨v, s⟩
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : hooks.isZero v = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | ifne target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨v, s⟩
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : (!hooks.isZero v) = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | iflt target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨v, s⟩
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : v.asI32.toBitVec.slt 0#32 = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | ifle target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨v, s⟩
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : v.asI32.toBitVec.sle 0#32 = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | ifgt target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨v, s⟩
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : (0#32).slt v.asI32.toBitVec = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | ifge target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨v, s⟩
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : (0#32).sle v.asI32.toBitVec = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | ifnull target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨v, s⟩
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : v.isNull = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | ifnonnull target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨v, s⟩
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : (!v.isNull) = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | if_icmpeq target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩
          · simp [runJvmResFast, hstk] at hfast
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : (a.asI32 == b.asI32) = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | if_icmpne target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩
          · simp [runJvmResFast, hstk] at hfast
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : (!(a.asI32 == b.asI32)) = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | if_icmplt target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩
          · simp [runJvmResFast, hstk] at hfast
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : a.asI32.toBitVec.slt b.asI32.toBitVec = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | if_icmpge target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩
          · simp [runJvmResFast, hstk] at hfast
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : b.asI32.toBitVec.sle a.asI32.toBitVec = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | if_icmpgt target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩
          · simp [runJvmResFast, hstk] at hfast
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : b.asI32.toBitVec.slt a.asI32.toBitVec = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | if_icmple target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩
          · simp [runJvmResFast, hstk] at hfast
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : a.asI32.toBitVec.sle b.asI32.toBitVec = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | if_acmpeq target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩
          · simp [runJvmResFast, hstk] at hfast
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : JvmVal.refEq hooks.beqExt a b = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | if_acmpne target =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩
          · simp [runJvmResFast, hstk] at hfast
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk, hpc]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            by_cases hcmp : (!JvmVal.refEq hooks.beqExt a b) = true
            · simp only [hcmp, ite_true] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) target (prog.drop target) _ rfl rfl hfast
            · simp only [hcmp] at hfast ⊢
              exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl (by rw [← List.drop_drop, hdrop]; rfl) hfast
        | tableswitch low targets defaultTarget =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨key, s⟩
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            exact ih f1 (Nat.lt_succ_self f1) _ (prog.drop _) _ rfl rfl hfast
        | lookupswitch cases defaultTarget =>
          have h0 := hg0 _ _ rfl
          rcases hstk : st.stack with _ | ⟨key, s⟩
          · simp [runJvmResFast, hstk] at hfast
          · unfold runJvmRes; rw [h0]; simp only [hstk]
            rw [runJvmResFast] at hfast; simp only [hstk] at hfast
            exact ih f1 (Nat.lt_succ_self f1) _ (prog.drop _) _ rfl rfl hfast
        | _ => exact step_catchall rfl (by simpa [runJvmResFast] using hfast)

theorem runJvm_of_runJvmFast {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (hite : ∀ c t e, hooks.iteVal c t e = if c then t else e)
    (hiteZ : ∀ v t e, hooks.iteZero v t e = if hooks.isZero v then t else e)
    (hiteNZ : ∀ v t e, hooks.iteNonZero v t e = if !hooks.isZero v then t else e)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState Ext Heap) (v : JvmVal Ext)
    (hfast : runJvmFast hooks fuel prog st.pc (prog.drop st.pc) st = some v) :
    runJvm hooks fuel prog st = some v := by
  simp only [runJvmFast, Option.map_eq_some_iff] at hfast
  rcases hfast with ⟨⟨res, st'⟩, hres, rfl⟩
  rw [runJvm_eq_runJvmRes hooks hite hiteZ hiteNZ,
    runJvmRes_of_runJvmResFast hooks fuel prog st.pc (prog.drop st.pc) st (res, st') rfl rfl hres]
  rfl

def runJvmValFast {Ext Heap : Type} (hooks : JvmHooks Ext Heap) :
    Nat → List JvmInstr → Nat → List JvmInstr → JvmState Ext Heap → Option (JvmVal Ext)
  | 0, _, _, _, _ => none
  | f1 + 1, prog, pc, instrs, st =>
    match instrs with
    | [] => none
    | instr :: rest =>
      match instr with
      | .i2l =>
        match rest with
        | .lconst 4294967295 :: .land :: rest' =>
          match f1 with
          | 0 => none
          | f2 + 1 =>
            match f2 with
            | 0 => none
            | f3 + 1 =>
              match st.stack with
              | .i32 x :: s =>
                runJvmValFast hooks f3 prog (pc + 3) rest' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              | _ => none
        | _ =>
          match stepInstr hooks instr { st with pc := pc } with
          | .inl (some st') =>
            if st'.pc = pc + 1 then runJvmValFast hooks f1 prog (pc + 1) rest st'
            else runJvmValFast hooks f1 prog st'.pc (prog.drop st'.pc) st'
          | .inl none => none
          | .inr (some v) => some v
          | .inr none => none
      | .goto target =>
        runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target }
      | .ifeq target =>
        match st.stack with
        | v :: s =>
          if hooks.isZero v then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifne target =>
        match st.stack with
        | v :: s =>
          if !hooks.isZero v then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .iflt target =>
        match st.stack with
        | v :: s =>
          if v.asI32.toBitVec.slt 0#32 then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifle target =>
        match st.stack with
        | v :: s =>
          if v.asI32.toBitVec.sle 0#32 then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifgt target =>
        match st.stack with
        | v :: s =>
          if (0#32).slt v.asI32.toBitVec then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifge target =>
        match st.stack with
        | v :: s =>
          if (0#32).sle v.asI32.toBitVec then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifnull target =>
        match st.stack with
        | v :: s =>
          if v.isNull then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifnonnull target =>
        match st.stack with
        | v :: s =>
          if !v.isNull then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmpeq target =>
        match st.stack with
        | b :: a :: s =>
          if a.asI32 == b.asI32 then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmpne target =>
        match st.stack with
        | b :: a :: s =>
          if !(a.asI32 == b.asI32) then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmplt target =>
        match st.stack with
        | b :: a :: s =>
          if a.asI32.toBitVec.slt b.asI32.toBitVec then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmpge target =>
        match st.stack with
        | b :: a :: s =>
          if b.asI32.toBitVec.sle a.asI32.toBitVec then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmpgt target =>
        match st.stack with
        | b :: a :: s =>
          if b.asI32.toBitVec.slt a.asI32.toBitVec then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmple target =>
        match st.stack with
        | b :: a :: s =>
          if a.asI32.toBitVec.sle b.asI32.toBitVec then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_acmpeq target =>
        match st.stack with
        | b :: a :: s =>
          if JvmVal.refEq hooks.beqExt a b then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_acmpne target =>
        match st.stack with
        | b :: a :: s =>
          if !JvmVal.refEq hooks.beqExt a b then runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast hooks f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .tableswitch low targets defaultTarget =>
        match st.stack with
        | key :: s =>
          let target := tableswitchTarget key.asI32 low targets defaultTarget
          runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
        | _ => none
      | .lookupswitch cases defaultTarget =>
        match st.stack with
        | key :: s =>
          let target := lookupswitchTarget key.asI32 cases defaultTarget
          runJvmValFast hooks f1 prog target (prog.drop target) { st with pc := target, stack := s }
        | _ => none
      | _ =>
        match stepInstr hooks instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then runJvmValFast hooks f1 prog (pc + 1) rest st'
          else runJvmValFast hooks f1 prog st'.pc (prog.drop st'.pc) st'
        | .inl none => none
        | .inr (some v) => some v
        | .inr none => none

private theorem runJvmFast_eq_runJvmValFast {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr)
    (st : JvmState Ext Heap) :
    runJvmFast hooks fuel prog pc instrs st = runJvmValFast hooks fuel prog pc instrs st := by
  induction fuel, prog, pc, instrs, st using runJvmValFast.induct (hooks := hooks) with
  | case1 => rfl
  | _ =>
    all_goals simp_all [runJvmFast, runJvmResFast, runJvmValFast]
    all_goals first | assumption | (split <;> simp_all)

theorem runJvm_of_runJvmValFast {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (hite : ∀ c t e, hooks.iteVal c t e = if c then t else e)
    (hiteZ : ∀ v t e, hooks.iteZero v t e = if hooks.isZero v then t else e)
    (hiteNZ : ∀ v t e, hooks.iteNonZero v t e = if !hooks.isZero v then t else e)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState Ext Heap) (v : JvmVal Ext)
    (hfast : runJvmValFast hooks fuel prog st.pc (prog.drop st.pc) st = some v) :
    runJvm hooks fuel prog st = some v :=
  runJvm_of_runJvmFast hooks hite hiteZ hiteNZ fuel prog st v
    (by rw [runJvmFast_eq_runJvmValFast]; exact hfast)

theorem runJvm_of_runJvmValFast0 {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (hite : ∀ c t e, hooks.iteVal c t e = if c then t else e)
    (hiteZ : ∀ v t e, hooks.iteZero v t e = if hooks.isZero v then t else e)
    (hiteNZ : ∀ v t e, hooks.iteNonZero v t e = if !hooks.isZero v then t else e)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState Ext Heap) (v : JvmVal Ext)
    (hpc : st.pc = 0)
    (hfast : runJvmValFast hooks fuel prog 0 prog st = some v) :
    runJvm hooks fuel prog st = some v := by
  apply runJvm_of_runJvmValFast hooks hite hiteZ hiteNZ
  rwa [hpc, List.drop_zero]

theorem runJvmRes_of_runJvmResFast0 {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState Ext Heap)
    (res : JvmVal Ext × JvmState Ext Heap) (hpc : st.pc = 0)
    (hfast : runJvmResFast hooks fuel prog 0 prog st = some res) :
    runJvmRes hooks fuel prog st = some res := by
  apply runJvmRes_of_runJvmResFast hooks fuel prog st.pc (prog.drop st.pc) st res rfl rfl
  rwa [hpc, List.drop_zero]

theorem runJvmRes_map_of_runJvmResFast0 {Ext Heap α : Type} (hooks : JvmHooks Ext Heap)
    (f : JvmVal Ext × JvmState Ext Heap → α)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState Ext Heap) (y : α)
    (hpc : st.pc = 0)
    (hfast : (runJvmResFast hooks fuel prog 0 prog st).map f = some y) :
    (runJvmRes hooks fuel prog st).map f = some y := by
  cases h : runJvmResFast hooks fuel prog 0 prog st with
  | none => simp [h] at hfast
  | some p =>
    simp only [h, Option.map_some, Option.some.injEq] at hfast
    have h1 := runJvmRes_of_runJvmResFast0 hooks fuel prog st p hpc h
    simp [h1, hfast]

def stepBlock {Ext Heap : Type} (hooks : JvmHooks Ext Heap) :
    Nat → List JvmInstr → JvmState Ext Heap → Sum (Nat × JvmState Ext Heap) (Option (JvmVal Ext))
  | pc, .i2l :: .lconst 4294967295 :: .land :: rest, st =>
    match st.stack with
    | .i32 x :: s =>
      match stepBlock hooks (pc + 3) rest { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s } with
      | .inl (c, st') => .inl (c + 3, st')
      | .inr res => .inr res
    | _ => .inr none
  | _, [], _ => .inr none
  | pc, instr :: rest, st =>
    if isBranchInstr instr then .inl (0, { st with pc := pc })
    else match stepInstr hooks instr { st with pc := pc } with
    | .inl (some st') =>
      if st'.pc = pc + 1 then
        match stepBlock hooks (pc + 1) rest st' with
        | .inl (c, st'') => .inl (c + 1, st'')
        | .inr res => .inr res
      else .inl (1, st')
    | .inl none => .inr none
    | .inr res => .inr res

private theorem runJvmValFast_eq_drop_pc {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState Ext Heap) (hbr : isBranchInstr instr = true) :
    runJvmValFast hooks fuel prog pc (instr :: rest) { st with pc := pc } =
      runJvmValFast hooks fuel prog pc (instr :: rest) st := by
  cases fuel with
  | zero => rfl
  | succ f1 =>
    cases instr <;> simp_all [isBranchInstr, runJvmValFast]

theorem runJvmValFast_step_nonbranch {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (f1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState Ext Heap) (hbr : isBranchInstr instr = false)
    (hno : ¬(instr = .i2l ∧ ∃ rest', rest = .lconst 4294967295 :: .land :: rest')) :
    runJvmValFast hooks (f1 + 1) prog pc (instr :: rest) st =
      match stepInstr hooks instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then runJvmValFast hooks f1 prog (pc + 1) rest st'
        else runJvmValFast hooks f1 prog st'.pc (prog.drop st'.pc) st'
      | .inl none => none
      | .inr (some v) => some v
      | .inr none => none := by
  cases instr with
  | i2l =>
    cases rest with
    | nil => rfl
    | cons a r1 =>
      cases a <;> try rfl
      case lconst v =>
        by_cases hv : v = 4294967295
        · subst hv
          cases r1 with
          | nil => rfl
          | cons b r2 =>
            cases b <;> try rfl
            exfalso; exact hno ⟨rfl, r2, rfl⟩
        · simp [runJvmValFast, hv]
  | _ => simp_all [runJvmValFast, isBranchInstr]

private theorem stepBlock_cons_ne {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (pc : Nat) (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState Ext Heap)
    (hno : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r')) :
    stepBlock hooks pc (instr :: rest) st =
      if isBranchInstr instr then .inl (0, { st with pc := pc })
      else match stepInstr hooks instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then
          match stepBlock hooks (pc + 1) rest st' with
          | .inl (c, st'') => .inl (c + 1, st'')
          | .inr res => .inr res
        else .inl (1, st')
      | .inl none => .inr none
      | .inr res => .inr res := by
  cases instr with
  | i2l =>
    cases rest with
    | nil => rfl
    | cons a r1 =>
      cases a <;> try rfl
      case lconst v =>
        by_cases hv : v = 4294967295
        · subst hv
          cases r1 with
          | nil => rfl
          | cons b r2 =>
            cases b <;> try rfl
            exfalso; exact hno ⟨rfl, r2, rfl⟩
        · simp [stepBlock, hv]
  | _ => rfl

private theorem runJvmValFast_stepBlock_aux {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (n : Nat) (fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState Ext Heap) (hlen : instrs.length ≤ n)
    (hdrop : prog.drop pc = instrs) (hfuel : instrs.length ≤ fuel) :
    runJvmValFast hooks fuel prog pc instrs st =
      match stepBlock hooks pc instrs st with
      | .inl (c', st') => runJvmValFast hooks (fuel - c') prog st'.pc (prog.drop st'.pc) st'
      | .inr res => res := by
  induction n generalizing fuel pc instrs st with
  | zero =>
    have hnil : instrs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hnil; cases fuel <;> simp [runJvmValFast, stepBlock]
  | succ n ih =>
    cases instrs with
    | nil => cases fuel <;> simp [runJvmValFast, stepBlock]
    | cons instr rest =>
      by_cases hpat : ∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r'
      · rcases hpat with ⟨r', rfl, rfl⟩
        have ⟨f3, hf3⟩ : ∃ f3, fuel = f3 + 3 :=
          ⟨fuel - 3, (Nat.sub_add_cancel (by simp at hfuel; omega)).symm⟩
        subst hf3
        simp only [stepBlock]
        cases hstk : st.stack with
        | nil => simp [runJvmValFast, hstk]
        | cons v s =>
          cases v with
          | i32 x =>
            have hstep : runJvmValFast hooks (f3 + 3) prog pc
                (.i2l :: .lconst 4294967295 :: .land :: r') st =
                runJvmValFast hooks f3 prog (pc + 3) r'
                  { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s } := by
              simp [runJvmValFast, hstk]
            rw [hstep]
            have hih := ih f3 (pc + 3) r' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              (by simp at hlen; omega) (by rw [← List.drop_drop, hdrop]; rfl) (by simp at hfuel; omega)
            rw [hih]
            cases hsb : stepBlock hooks (pc + 3) r' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s } with
            | inl p => rcases p with ⟨c, st'⟩; simp [hsb, Nat.add_sub_add_right]
            | inr res => simp [hsb]
          | _ => simp [runJvmValFast, hstk]
      · have hno : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r') := by
          rintro ⟨rfl, r', rfl⟩; exact hpat ⟨r', rfl, rfl⟩
        rw [stepBlock_cons_ne hooks pc instr rest st hno]
        by_cases hbr : isBranchInstr instr = true
        · simp only [hbr, ite_true, Nat.sub_zero, hdrop]
          exact (runJvmValFast_eq_drop_pc hooks fuel prog pc instr rest st hbr).symm
        · have hbrf : isBranchInstr instr = false := Bool.eq_false_iff.mpr hbr
          have ⟨f1, hf1⟩ : ∃ f1, fuel = f1 + 1 :=
            ⟨fuel - 1, (Nat.sub_add_cancel (by simp at hfuel; omega)).symm⟩
          subst hf1
          simp only [hbrf, Bool.false_eq_true, ite_false]
          rw [runJvmValFast_step_nonbranch hooks f1 prog pc instr rest st hbrf hno]
          cases hst : stepInstr hooks instr { st with pc := pc } with
          | inl o =>
            cases o with
            | none => rfl
            | some st' =>
              by_cases hpc : st'.pc = pc + 1
              · simp only [hpc, ite_true]
                have hih := ih f1 (pc + 1) rest st' (by simp at hlen; omega)
                  (by rw [← List.drop_drop, hdrop]; rfl) (by simp at hfuel; omega)
                rw [hih]
                cases stepBlock hooks (pc + 1) rest st' with
                | inl p => rcases p with ⟨c, st''⟩; simp [Nat.add_sub_add_right]
                | inr res => rfl
              · simp [hpc]
          | inr res =>
            cases res <;> rfl

def afterBlock {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (step : Sum (Nat × JvmState Ext Heap) (Option (JvmVal Ext))) (fuel : Nat) (prog : List JvmInstr) :
    Option (JvmVal Ext) :=
  match step with
  | .inl (c', st') => runJvmValFast hooks (fuel - c') prog st'.pc (prog.drop st'.pc) st'
  | .inr res => res

theorem runJvmValFast_stepBlock {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr)
    (st : JvmState Ext Heap) (hdrop : prog.drop pc = instrs) (hfuel : instrs.length ≤ fuel) :
    runJvmValFast hooks fuel prog pc instrs st =
      match stepBlock hooks pc instrs st with
      | .inl (c', st') => runJvmValFast hooks (fuel - c') prog st'.pc (prog.drop st'.pc) st'
      | .inr res => res :=
  runJvmValFast_stepBlock_aux hooks instrs.length fuel prog pc instrs st (Nat.le_refl _) hdrop hfuel

theorem runJvmValFast_stepBlock0 {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState Ext Heap)
    (hfuel : prog.length ≤ fuel) :
    runJvmValFast hooks fuel prog 0 prog st =
      match stepBlock hooks 0 prog st with
      | .inl (c', st') => runJvmValFast hooks (fuel - c') prog st'.pc (prog.drop st'.pc) st'
      | .inr res => res :=
  runJvmValFast_stepBlock hooks fuel prog 0 prog st (by simp) hfuel

theorem runJvmValFast_stepBlock_after {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr)
    (st : JvmState Ext Heap) (hdrop : prog.drop pc = instrs) (hfuel : instrs.length ≤ fuel) :
    runJvmValFast hooks fuel prog pc instrs st = afterBlock hooks (stepBlock hooks pc instrs st) fuel prog := by
  rw [runJvmValFast_stepBlock hooks fuel prog pc instrs st hdrop hfuel]; rfl

theorem runJvmValFast_stepBlock0_after {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState Ext Heap)
    (hfuel : prog.length ≤ fuel) :
    runJvmValFast hooks fuel prog 0 prog st = afterBlock hooks (stepBlock hooks 0 prog st) fuel prog :=
  runJvmValFast_stepBlock_after hooks fuel prog 0 prog st (by simp) hfuel

def evalBranchInstr {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (st : JvmState Ext Heap) : Option (JvmVal Ext) :=
  match instr with
  | .ifeq target =>
    match st.stack with
    | v :: s =>
      if hooks.isZero v then runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifne target =>
    match st.stack with
    | v :: s =>
      if !hooks.isZero v then runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .iflt target =>
    match st.stack with
    | v :: s =>
      if v.asI32.toBitVec.slt 0#32 then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifle target =>
    match st.stack with
    | v :: s =>
      if v.asI32.toBitVec.sle 0#32 then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifgt target =>
    match st.stack with
    | v :: s =>
      if (0#32).slt v.asI32.toBitVec then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifge target =>
    match st.stack with
    | v :: s =>
      if (0#32).sle v.asI32.toBitVec then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifnull target =>
    match st.stack with
    | v :: s =>
      if v.isNull then runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifnonnull target =>
    match st.stack with
    | v :: s =>
      if !v.isNull then runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpeq target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32 == b.asI32 then runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpne target =>
    match st.stack with
    | b :: a :: s =>
      if !(a.asI32 == b.asI32) then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmplt target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32.toBitVec.slt b.asI32.toBitVec then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpge target =>
    match st.stack with
    | b :: a :: s =>
      if b.asI32.toBitVec.sle a.asI32.toBitVec then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpgt target =>
    match st.stack with
    | b :: a :: s =>
      if b.asI32.toBitVec.slt a.asI32.toBitVec then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmple target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32.toBitVec.sle b.asI32.toBitVec then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_acmpeq target =>
    match st.stack with
    | b :: a :: s =>
      if JvmVal.refEq hooks.beqExt a b then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_acmpne target =>
    match st.stack with
    | b :: a :: s =>
      if !JvmVal.refEq hooks.beqExt a b then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .tableswitch low targets defaultTarget =>
    match st.stack with
    | key :: s =>
      let target := tableswitchTarget key.asI32 low targets defaultTarget
      runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
    | _ => none
  | .lookupswitch cases defaultTarget =>
    match st.stack with
    | key :: s =>
      let target := lookupswitchTarget key.asI32 cases defaultTarget
      runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
    | _ => none
  | .goto target => runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target }
  | _ => none

theorem runJvmValFast_at_branch {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    {fuel : Nat} (hf : 0 < fuel) {prog : List JvmInstr} {pc : Nat}
    {st : JvmState Ext Heap} (hbr : isBranchInstr ((prog.drop pc).headD .nop) = true) :
    runJvmValFast hooks fuel prog pc (prog.drop pc) st =
      evalBranchInstr hooks (fuel - 1) prog pc ((prog.drop pc).headD .nop) st := by
  obtain ⟨f1, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hf)
  simp only [Nat.succ_sub_one]
  cases hdrop : prog.drop pc with
  | nil => simp [hdrop, isBranchInstr] at hbr
  | cons instr rest =>
    have hrest : rest = prog.drop (pc + 1) := by
      have h1 : (instr :: rest).drop 1 = rest := rfl
      rw [← h1, ← hdrop, List.drop_drop, Nat.add_comm]
    rw [hdrop] at hbr
    simp only [List.headD] at hbr ⊢
    cases instr <;> first
      | (simp only [isBranchInstr] at hbr; contradiction)
      | simp [runJvmValFast, evalBranchInstr, hrest]
      | (simp only [runJvmValFast, evalBranchInstr, stepInstr]; split <;> simp_all [hrest])

inductive BlockChunkRes (Ext Heap : Type) where
  | cont (fuel' : Nat) (pc' : Nat) (instrs' : List JvmInstr) (st' : JvmState Ext Heap)
  | jump (fuel' : Nat) (st' : JvmState Ext Heap)
  | done (res : Option (JvmVal Ext))

def stepBlockChunk {Ext Heap : Type} (hooks : JvmHooks Ext Heap) :
    Nat → Nat → Nat → List JvmInstr → JvmState Ext Heap → BlockChunkRes Ext Heap
  | _, 0, _, _, _ => .done none
  | 0, f1 + 1, pc, instrs, st => .cont (f1 + 1) pc instrs st
  | m + 1, f1 + 1, pc, instrs, st =>
    match instrs with
    | [] => .done none
    | instr :: rest =>
      if isBranchInstr instr then .cont (f1 + 1) pc (instr :: rest) st
      else match instr with
      | .i2l =>
        match rest with
        | .lconst 4294967295 :: .land :: rest' =>
          match f1 with
          | 0 => .done none
          | f2 + 1 =>
            match f2 with
            | 0 => .done none
            | f3 + 1 =>
              match st.stack with
              | .i32 x :: s =>
                stepBlockChunk hooks m f3 (pc + 3) rest' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              | _ => .done none
        | _ =>
          match stepInstr hooks instr { st with pc := pc } with
          | .inl (some st') =>
            if st'.pc = pc + 1 then stepBlockChunk hooks m f1 (pc + 1) rest st'
            else .jump f1 st'
          | .inl none => .done none
          | .inr res => .done res
      | _ =>
        match stepInstr hooks instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then stepBlockChunk hooks m f1 (pc + 1) rest st'
          else .jump f1 st'
        | .inl none => .done none
        | .inr res => .done res

def afterBlockChunk {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (r : BlockChunkRes Ext Heap) (prog : List JvmInstr) : Option (JvmVal Ext) :=
  match r with
  | .cont f' pc' instrs' st' => runJvmValFast hooks f' prog pc' instrs' st'
  | .jump f' st' => runJvmValFast hooks f' prog st'.pc (prog.drop st'.pc) st'
  | .done res => res

private theorem stepBlockChunk_cons_ne {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (m f1 pc : Nat) (instr : JvmInstr) (rest : List JvmInstr)
    (st : JvmState Ext Heap) (hno : ¬∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r') :
    stepBlockChunk hooks (m + 1) (f1 + 1) pc (instr :: rest) st =
      if isBranchInstr instr then .cont (f1 + 1) pc (instr :: rest) st
      else match stepInstr hooks instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then stepBlockChunk hooks m f1 (pc + 1) rest st'
        else .jump f1 st'
      | .inl none => .done none
      | .inr res => .done res := by
  cases instr with
  | i2l =>
    cases rest with
    | nil => rfl
    | cons a r1 =>
      cases a <;> try rfl
      case lconst v =>
        by_cases hv : v = 4294967295
        · subst hv
          cases r1 with
          | nil => rfl
          | cons b r2 =>
            cases b <;> try rfl
            exfalso; exact hno ⟨r2, rfl, rfl⟩
        · simp [stepBlockChunk, hv]
  | _ => rfl

private theorem runJvmValFast_stepBlockChunk_aux {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (m : Nat) (fuel : Nat) (prog : List JvmInstr)
    (pc : Nat) (instrs : List JvmInstr) (st : JvmState Ext Heap) :
    runJvmValFast hooks fuel prog pc instrs st =
      afterBlockChunk hooks (stepBlockChunk hooks m fuel pc instrs st) prog := by
  induction m generalizing fuel pc instrs st with
  | zero => cases fuel <;> rfl
  | succ m ih =>
    cases fuel with
    | zero => rfl
    | succ f1 =>
      cases instrs with
      | nil => rfl
      | cons instr rest =>
        by_cases hpat : ∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r'
        · rcases hpat with ⟨r', rfl, rfl⟩
          cases f1 with
          | zero => rfl
          | succ f2 =>
            cases f2 with
            | zero => rfl
            | succ f3 =>
              simp only [runJvmValFast, stepBlockChunk, isBranchInstr, Bool.false_eq_true, ↓reduceIte]
              cases st.stack with
              | nil => rfl
              | cons hd tl => cases hd with | i32 x => exact ih f3 (pc + 3) r' _ | _ => rfl
        · by_cases hbr : isBranchInstr instr = true
          · rw [stepBlockChunk_cons_ne hooks m f1 pc instr rest st hpat]
            simp only [hbr, ↓reduceIte, afterBlockChunk]
          · have hbrf : isBranchInstr instr = false := Bool.eq_false_iff.mpr hbr
            have hno' : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r') :=
              fun ⟨h1, r', h2⟩ => hpat ⟨r', h1, h2⟩
            rw [stepBlockChunk_cons_ne hooks m f1 pc instr rest st hpat,
              runJvmValFast_step_nonbranch hooks f1 prog pc instr rest st hbrf hno']
            simp only [hbrf, Bool.false_eq_true, ↓reduceIte]
            cases hst : stepInstr hooks instr { st with pc := pc } with
            | inl o =>
              cases o with
              | none => rfl
              | some st' =>
                by_cases hpc : st'.pc = pc + 1
                · simp only [hpc, ↓reduceIte]; exact ih f1 (pc + 1) rest st'
                · simp only [hpc, ↓reduceIte, afterBlockChunk]
            | inr res => cases res <;> rfl

theorem runJvmValFast_stepBlockChunk {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState Ext Heap) :
    runJvmValFast hooks fuel prog pc instrs st =
      afterBlockChunk hooks (stepBlockChunk hooks maxSteps fuel pc instrs st) prog :=
  runJvmValFast_stepBlockChunk_aux hooks maxSteps fuel prog pc instrs st

def evalBranchInstrCons {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState Ext Heap) : Option (JvmVal Ext) :=
  match instr with
  | .ifeq target =>
    match st.stack with
    | v :: s =>
      if hooks.isZero v then runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifne target =>
    match st.stack with
    | v :: s =>
      if !hooks.isZero v then runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .iflt target =>
    match st.stack with
    | v :: s =>
      if v.asI32.toBitVec.slt 0#32 then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifle target =>
    match st.stack with
    | v :: s =>
      if v.asI32.toBitVec.sle 0#32 then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifgt target =>
    match st.stack with
    | v :: s =>
      if (0#32).slt v.asI32.toBitVec then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifge target =>
    match st.stack with
    | v :: s =>
      if (0#32).sle v.asI32.toBitVec then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifnull target =>
    match st.stack with
    | v :: s =>
      if v.isNull then runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifnonnull target =>
    match st.stack with
    | v :: s =>
      if !v.isNull then runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpeq target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32 == b.asI32 then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpne target =>
    match st.stack with
    | b :: a :: s =>
      if !(a.asI32 == b.asI32) then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmplt target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32.toBitVec.slt b.asI32.toBitVec then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpge target =>
    match st.stack with
    | b :: a :: s =>
      if b.asI32.toBitVec.sle a.asI32.toBitVec then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpgt target =>
    match st.stack with
    | b :: a :: s =>
      if b.asI32.toBitVec.slt a.asI32.toBitVec then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmple target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32.toBitVec.sle b.asI32.toBitVec then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_acmpeq target =>
    match st.stack with
    | b :: a :: s =>
      if JvmVal.refEq hooks.beqExt a b then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_acmpne target =>
    match st.stack with
    | b :: a :: s =>
      if !JvmVal.refEq hooks.beqExt a b then
        runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .tableswitch low targets defaultTarget =>
    match st.stack with
    | key :: s =>
      let target := tableswitchTarget key.asI32 low targets defaultTarget
      runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
    | _ => none
  | .lookupswitch cases defaultTarget =>
    match st.stack with
    | key :: s =>
      let target := lookupswitchTarget key.asI32 cases defaultTarget
      runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
    | _ => none
  | .goto target => runJvmValFast hooks fuel1 prog target (prog.drop target) { st with pc := target }
  | _ => none

theorem runJvmValFast_at_branch_cons {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState Ext Heap) (hbr : isBranchInstr instr = true) :
    runJvmValFast hooks (f1 + 1) prog pc (instr :: rest) st =
      evalBranchInstrCons hooks f1 prog pc instr rest st := by
  cases instr <;> first
    | (simp only [isBranchInstr] at hbr; contradiction)
    | rfl
    | (simp only [runJvmValFast, evalBranchInstrCons, stepInstr]; split <;> rfl)

inductive BlockResChunkRes (Ext Heap : Type) where
  | cont (fuel' : Nat) (pc' : Nat) (instrs' : List JvmInstr) (st' : JvmState Ext Heap)
  | jump (fuel' : Nat) (st' : JvmState Ext Heap)
  | done (res : Option (JvmVal Ext × JvmState Ext Heap))

def stepResBlockChunk {Ext Heap : Type} (hooks : JvmHooks Ext Heap) :
    Nat → Nat → Nat → List JvmInstr → JvmState Ext Heap → BlockResChunkRes Ext Heap
  | _, 0, _, _, _ => .done none
  | 0, f1 + 1, pc, instrs, st => .cont (f1 + 1) pc instrs st
  | m + 1, f1 + 1, pc, instrs, st =>
    match instrs with
    | [] => .done none
    | instr :: rest =>
      if isBranchInstr instr then .cont (f1 + 1) pc (instr :: rest) st
      else match instr with
      | .i2l =>
        match rest with
        | .lconst 4294967295 :: .land :: rest' =>
          match f1 with
          | 0 => .done none
          | f2 + 1 =>
            match f2 with
            | 0 => .done none
            | f3 + 1 =>
              match st.stack with
              | .i32 x :: s =>
                stepResBlockChunk hooks m f3 (pc + 3) rest' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              | _ => .done none
        | _ =>
          match stepInstr hooks instr { st with pc := pc } with
          | .inl (some st') =>
            if st'.pc = pc + 1 then stepResBlockChunk hooks m f1 (pc + 1) rest st'
            else .jump f1 st'
          | .inl none => .done none
          | .inr (some v) => .done (some (v, { st with pc := pc }))
          | .inr none => .done none
      | _ =>
        match stepInstr hooks instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then stepResBlockChunk hooks m f1 (pc + 1) rest st'
          else .jump f1 st'
        | .inl none => .done none
        | .inr (some v) => .done (some (v, { st with pc := pc }))
        | .inr none => .done none

def afterResBlockChunk {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (r : BlockResChunkRes Ext Heap) (prog : List JvmInstr) : Option (JvmVal Ext × JvmState Ext Heap) :=
  match r with
  | .cont f' pc' instrs' st' => runJvmResFast hooks f' prog pc' instrs' st'
  | .jump f' st' => runJvmResFast hooks f' prog st'.pc (prog.drop st'.pc) st'
  | .done res => res

private theorem stepResBlockChunk_cons_ne {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (m f1 pc : Nat) (instr : JvmInstr) (rest : List JvmInstr)
    (st : JvmState Ext Heap) (hno : ¬∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r') :
    stepResBlockChunk hooks (m + 1) (f1 + 1) pc (instr :: rest) st =
      if isBranchInstr instr then .cont (f1 + 1) pc (instr :: rest) st
      else match stepInstr hooks instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then stepResBlockChunk hooks m f1 (pc + 1) rest st'
        else .jump f1 st'
      | .inl none => .done none
      | .inr (some v) => .done (some (v, { st with pc := pc }))
      | .inr none => .done none := by
  cases instr with
  | i2l =>
    cases rest with
    | nil => rfl
    | cons a r1 =>
      cases a <;> try rfl
      case lconst v =>
        by_cases hv : v = 4294967295
        · subst hv
          cases r1 with
          | nil => rfl
          | cons b r2 =>
            cases b <;> try rfl
            exfalso; exact hno ⟨r2, rfl, rfl⟩
        · simp [stepResBlockChunk, hv]
  | _ => rfl

theorem runJvmResFast_step_nonbranch {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState Ext Heap) (hbr : isBranchInstr instr = false)
    (hno : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r')) :
    runJvmResFast hooks (f1 + 1) prog pc (instr :: rest) st =
      match stepInstr hooks instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then runJvmResFast hooks f1 prog (pc + 1) rest st'
        else runJvmResFast hooks f1 prog st'.pc (prog.drop st'.pc) st'
      | .inl none => none
      | .inr (some v) => some (v, { st with pc := pc })
      | .inr none => none := by
  cases instr with
  | i2l =>
    cases rest with
    | nil => rfl
    | cons a r1 =>
      cases a <;> try rfl
      case lconst v =>
        by_cases hv : v = 4294967295
        · subst hv
          cases r1 with
          | nil => rfl
          | cons b r2 =>
            cases b <;> try rfl
            exfalso; exact hno ⟨rfl, r2, rfl⟩
        · simp [runJvmResFast, hv]
  | _ => simp_all [runJvmResFast, isBranchInstr]

private theorem runJvmResFast_stepBlockChunk_aux {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (m : Nat) (fuel : Nat) (prog : List JvmInstr)
    (pc : Nat) (instrs : List JvmInstr) (st : JvmState Ext Heap) :
    runJvmResFast hooks fuel prog pc instrs st =
      afterResBlockChunk hooks (stepResBlockChunk hooks m fuel pc instrs st) prog := by
  induction m generalizing fuel pc instrs st with
  | zero => cases fuel <;> rfl
  | succ m ih =>
    cases fuel with
    | zero => rfl
    | succ f1 =>
      cases instrs with
      | nil => rfl
      | cons instr rest =>
        by_cases hpat : ∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r'
        · rcases hpat with ⟨r', rfl, rfl⟩
          cases f1 with
          | zero => rfl
          | succ f2 =>
            cases f2 with
            | zero => rfl
            | succ f3 =>
              simp only [runJvmResFast, stepResBlockChunk, isBranchInstr, Bool.false_eq_true, ↓reduceIte]
              cases st.stack with
              | nil => rfl
              | cons hd tl => cases hd with | i32 x => exact ih f3 (pc + 3) r' _ | _ => rfl
        · by_cases hbr : isBranchInstr instr = true
          · rw [stepResBlockChunk_cons_ne hooks m f1 pc instr rest st hpat]
            simp only [hbr, ↓reduceIte, afterResBlockChunk]
          · have hbrf : isBranchInstr instr = false := Bool.eq_false_iff.mpr hbr
            have hno' : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r') :=
              fun ⟨h1, r', h2⟩ => hpat ⟨r', h1, h2⟩
            rw [stepResBlockChunk_cons_ne hooks m f1 pc instr rest st hpat,
              runJvmResFast_step_nonbranch hooks f1 prog pc instr rest st hbrf hno']
            simp only [hbrf, Bool.false_eq_true, ↓reduceIte]
            cases hst : stepInstr hooks instr { st with pc := pc } with
            | inl o =>
              cases o with
              | none => rfl
              | some st' =>
                by_cases hpc : st'.pc = pc + 1
                · simp only [hpc, ↓reduceIte]; exact ih f1 (pc + 1) rest st'
                · simp only [hpc, ↓reduceIte, afterResBlockChunk]
            | inr res => cases res <;> rfl

theorem runJvmResFast_stepBlockChunk {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState Ext Heap) :
    runJvmResFast hooks fuel prog pc instrs st =
      afterResBlockChunk hooks (stepResBlockChunk hooks maxSteps fuel pc instrs st) prog :=
  runJvmResFast_stepBlockChunk_aux hooks maxSteps fuel prog pc instrs st

def evalResBranchInstrCons {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (fuel1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState Ext Heap) : Option (JvmVal Ext × JvmState Ext Heap) :=
  match instr with
  | .ifeq target =>
    match st.stack with
    | v :: s =>
      if hooks.isZero v then runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifne target =>
    match st.stack with
    | v :: s =>
      if !hooks.isZero v then runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .iflt target =>
    match st.stack with
    | v :: s =>
      if v.asI32.toBitVec.slt 0#32 then
        runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifle target =>
    match st.stack with
    | v :: s =>
      if v.asI32.toBitVec.sle 0#32 then
        runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifgt target =>
    match st.stack with
    | v :: s =>
      if (0#32).slt v.asI32.toBitVec then
        runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifge target =>
    match st.stack with
    | v :: s =>
      if (0#32).sle v.asI32.toBitVec then
        runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifnull target =>
    match st.stack with
    | v :: s =>
      if v.isNull then runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifnonnull target =>
    match st.stack with
    | v :: s =>
      if !v.isNull then runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpeq target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32 == b.asI32 then
        runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpne target =>
    match st.stack with
    | b :: a :: s =>
      if !(a.asI32 == b.asI32) then
        runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmplt target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32.toBitVec.slt b.asI32.toBitVec then
        runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpge target =>
    match st.stack with
    | b :: a :: s =>
      if b.asI32.toBitVec.sle a.asI32.toBitVec then
        runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpgt target =>
    match st.stack with
    | b :: a :: s =>
      if b.asI32.toBitVec.slt a.asI32.toBitVec then
        runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmple target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32.toBitVec.sle b.asI32.toBitVec then
        runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_acmpeq target =>
    match st.stack with
    | b :: a :: s =>
      if JvmVal.refEq hooks.beqExt a b then
        runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_acmpne target =>
    match st.stack with
    | b :: a :: s =>
      if !JvmVal.refEq hooks.beqExt a b then
        runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast hooks fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .tableswitch low targets defaultTarget =>
    match st.stack with
    | key :: s =>
      let target := tableswitchTarget key.asI32 low targets defaultTarget
      runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
    | _ => none
  | .lookupswitch cases defaultTarget =>
    match st.stack with
    | key :: s =>
      let target := lookupswitchTarget key.asI32 cases defaultTarget
      runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
    | _ => none
  | .goto target => runJvmResFast hooks fuel1 prog target (prog.drop target) { st with pc := target }
  | _ => none

theorem runJvmResFast_at_branch_cons {Ext Heap : Type} (hooks : JvmHooks Ext Heap)
    (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState Ext Heap) (hbr : isBranchInstr instr = true) :
    runJvmResFast hooks (f1 + 1) prog pc (instr :: rest) st =
      evalResBranchInstrCons hooks f1 prog pc instr rest st := by
  cases instr <;> first
    | (simp only [isBranchInstr] at hbr; contradiction)
    | rfl
    | (simp only [runJvmResFast, evalResBranchInstrCons, stepInstr]; split <;> rfl)

end Jvm
