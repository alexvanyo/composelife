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
import proofs.MacroCellEngineProofs

namespace Algorithm.JvmVerification

open Algorithm.JvmBytecode

theorem cellToLeafBit_equiv (x y : UInt32) :
    runJvm 60 f_Algorithm_cellToLeafBitUInt_prog (initJvmState [(0, .i32 x), (1, .i32 y)]) =
      some (.i32 (Algorithm.cellToLeafBitUInt x y)) := by rfl

theorem cellNodeHash_equiv (l qnw qne qsw qse : UInt32) :
    runJvm 70 f_Algorithm_cellNodeHash_prog
      (initJvmState [(0, .i32 l), (1, .i32 qnw), (2, .i32 qne), (3, .i32 qsw), (4, .i32 qse)]) =
      some (.i32 (Algorithm.cellNodeHash l qnw qne qsw qse)) := by rfl

theorem level4Hash_equiv (qnw qne qsw qse : UInt64) :
    runJvm 70 f_Algorithm_level4Hash_prog
      (initJvmState [(0, .i64 qnw), (2, .i64 qne), (4, .i64 qsw), (6, .i64 qse)]) =
      some (.i32 (Algorithm.level4Hash qnw qne qsw qse)) := by rfl

theorem centeredSubnodeLevel3_equiv (w : UInt64) :
    runJvm 90 f_Algorithm_centeredSubnodeLevel3BitsUInt_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (Algorithm.centeredSubnodeLevel3BitsUInt w)) := by rfl

theorem centeredHorizontalSubnodeLevel3_equiv (w e : UInt64) :
    runJvm 90 f_Algorithm_centeredHorizontalSubnodeLevel3BitsUInt_prog
      (initJvmState [(0, .i64 w), (2, .i64 e)]) =
      some (.i32 (Algorithm.centeredHorizontalSubnodeLevel3BitsUInt w e)) := by rfl

theorem centeredVerticalSubnodeLevel3_equiv (n s : UInt64) :
    runJvm 90 f_Algorithm_centeredVerticalSubnodeLevel3BitsUInt_prog
      (initJvmState [(0, .i64 n), (2, .i64 s)]) =
      some (.i32 (Algorithm.centeredVerticalSubnodeLevel3BitsUInt n s)) := by rfl

theorem centeredSubSubnodeLevel4_equiv (qnw qne qsw qse : UInt64) :
    runJvm 90 f_Algorithm_centeredSubSubnodeLevel4BitsUInt_prog
      (initJvmState [(0, .i64 qnw), (2, .i64 qne), (4, .i64 qsw), (6, .i64 qse)]) =
      some (.i32 (Algorithm.centeredSubSubnodeLevel4BitsUInt qnw qne qsw qse)) := by rfl

theorem centeredSubnodeLevel4_equiv (qnw qne qsw qse : UInt64) :
    runJvm 80 f_Algorithm_centeredSubnodeLevel4_prog
      (initJvmState [(0, .i64 qnw), (2, .i64 qne), (4, .i64 qsw), (6, .i64 qse)]) =
      some (.i64 (Algorithm.centeredSubnodeLevel4 qnw qne qsw qse)) := by
  change some (JvmVal.i64 _) = some (JvmVal.i64 _)
  congr 2
  dsimp [JvmVal.asI32, JvmVal.asI64, setLocal, initJvmState, List.foldl,
    Algorithm.centeredSubnodeLevel4]
  bv_check "lrat/JvmEquiv.Algorithm.JvmVerification.centeredSubnodeLevel4_equiv.lrat"

theorem centeredHorizontalSubnodeLevel4_equiv (qnw qne qsw qse : UInt64) :
    runJvm 80 f_Algorithm_centeredHorizontalSubnodeLevel4_prog
      (initJvmState [(0, .i64 qnw), (2, .i64 qne), (4, .i64 qsw), (6, .i64 qse)]) =
      some (.i64 (Algorithm.centeredHorizontalSubnodeLevel4 qnw qne qsw qse)) := by
  change some (JvmVal.i64 _) = some (JvmVal.i64 _)
  congr 2
  dsimp [JvmVal.asI32, JvmVal.asI64, setLocal, initJvmState, List.foldl,
    Algorithm.centeredHorizontalSubnodeLevel4, Algorithm.centeredSubnodeLevel4]
  bv_check "lrat/JvmEquiv.Algorithm.JvmVerification.centeredHorizontalSubnodeLevel4_equiv.lrat"

theorem centeredVerticalSubnodeLevel4_equiv (qnw qne qsw qse : UInt64) :
    runJvm 80 f_Algorithm_centeredVerticalSubnodeLevel4_prog
      (initJvmState [(0, .i64 qnw), (2, .i64 qne), (4, .i64 qsw), (6, .i64 qse)]) =
      some (.i64 (Algorithm.centeredVerticalSubnodeLevel4 qnw qne qsw qse)) := by
  change some (JvmVal.i64 _) = some (JvmVal.i64 _)
  congr 2
  dsimp [JvmVal.asI32, JvmVal.asI64, setLocal, initJvmState, List.foldl,
    Algorithm.centeredVerticalSubnodeLevel4, Algorithm.centeredSubnodeLevel4]
  bv_check "lrat/JvmEquiv.Algorithm.JvmVerification.centeredVerticalSubnodeLevel4_equiv.lrat"

theorem packLeafFrom4x4s_equiv (q0 q1 q2 q3 : UInt32) :
    runJvm 60 f_Algorithm_packLeafFrom4x4sUInt_prog
      (initJvmState [(0, .i32 q0), (1, .i32 q1), (2, .i32 q2), (3, .i32 q3)]) =
      some (.i64 (Algorithm.packLeafFrom4x4sUInt q0 q1 q2 q3)) := by
  change some (JvmVal.i64 _) = some (JvmVal.i64 _)
  congr 2
  dsimp [JvmVal.asI32, JvmVal.asI64, setLocal, initJvmState, List.foldl,
    Algorithm.packLeafFrom4x4sUInt]
  bv_check "lrat/JvmEquiv.Algorithm.JvmVerification.packLeafFrom4x4s_equiv.lrat"

theorem expandOffsetDelta_equiv (lvl : UInt32) (h1 : 1 ≤ lvl) (h2 : lvl ≤ 30) :
    runJvm 20 f_Algorithm_expandOffsetDeltaUInt_prog (initJvmState [(0, .i32 lvl)]) =
      some (.i32 (Algorithm.expandOffsetDeltaUInt lvl).toUInt32) := by
  change some (JvmVal.i32 _) = some (JvmVal.i32 _)
  congr 2
  dsimp [JvmVal.asI32, JvmVal.asI64, setLocal, initJvmState, List.foldl,
    Algorithm.expandOffsetDeltaUInt]
  bv_check "lrat/JvmEquiv.Algorithm.JvmVerification.expandOffsetDelta_equiv.lrat"

theorem stepOffsetDelta_equiv (lvl : UInt32) (h1 : 2 ≤ lvl) (h2 : lvl ≤ 30) :
    runJvm 20 f_Algorithm_stepOffsetDeltaUInt_prog (initJvmState [(0, .i32 lvl)]) =
      some (.i32 (Algorithm.stepOffsetDeltaUInt lvl).toUInt32) := by
  change some (JvmVal.i32 _) = some (JvmVal.i32 _)
  congr 2
  dsimp [JvmVal.asI32, JvmVal.asI64, setLocal, initJvmState, List.foldl,
    Algorithm.stepOffsetDeltaUInt]
  bv_check "lrat/JvmEquiv.Algorithm.JvmVerification.stepOffsetDelta_equiv.lrat"

theorem leafContains_equiv (leaf : UInt64) (x y : UInt32) :
    runJvm 25 f_Algorithm_leafContains_prog (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y)]) =
      some (.i32 (if Algorithm.leafContains leaf x y then 1 else 0)) := by
  change some (JvmVal.i32 _) = some (JvmVal.i32 _)
  congr 2
  dsimp [JvmVal.asI32, JvmVal.asI64, setLocal, initJvmState, List.foldl,
    Algorithm.leafContains, Algorithm.cellToLeafBitUInt]
  bv_check "lrat/JvmEquiv.Algorithm.JvmVerification.leafContains_equiv.lrat"

theorem leafWithCell_equiv (leaf : UInt64) (x y : UInt32) (isAlive : Bool) :
    runJvm 35 f_Algorithm_leafWithCell_prog
      (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y), (4, .i32 (if isAlive then 1 else 0))]) =
      some (.i64 (Algorithm.leafWithCell leaf x y isAlive)) := by
  change some (JvmVal.i64 _) = some (JvmVal.i64 _)
  congr 2
  dsimp [JvmVal.asI32, JvmVal.asI64, setLocal, initJvmState, List.foldl,
    Algorithm.leafWithCell, Algorithm.cellToLeafBitUInt]
  bv_check "lrat/JvmEquiv.Algorithm.JvmVerification.leafWithCell_equiv.lrat"

/-! ### Execution helpers -/

private theorem signExtend_and_mask (x : UInt32) :
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

private theorem coerceInI32_of_le (v lo hi : UInt32) (h1 : lo.toNat ≤ v.toNat) (h2 : v.toNat ≤ hi.toNat)
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

def isBranchInstr : JvmInstr → Bool
  | .ifeq _ | .ifne _ | .iflt _ | .ifle _ | .ifgt _ | .ifge _
  | .ifnull _ | .ifnonnull _ | .if_icmpeq _ | .if_icmpne _ | .if_icmplt _ | .goto _ => true
  | _ => false

theorem runJvm_nonbranch (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (instr : JvmInstr)
    (hget : prog[st.pc]? = some instr) (hnbr : isBranchInstr instr = false) :
    runJvm (fuel + 1) prog st =
      match stepInstr instr st with
      | .inl (some st') => runJvm fuel prog st'
      | .inl none => none
      | .inr res => res := by
  cases instr <;> simp [isBranchInstr] at hnbr <;> simp [runJvm, hget] <;> rfl

def stepListAt (pc : Nat) (instrs : List JvmInstr) (st : JvmState) : Option JvmVal :=
  match instrs with
  | [] => none
  | instr :: rest =>
    if isBranchInstr instr then none
    else match stepInstr instr { st with pc := pc } with
    | .inl (some st') => if st'.pc = pc + 1 then stepListAt (pc + 1) rest st' else none
    | .inl none => none
    | .inr res => res

theorem runJvm_of_stepListAt (prog instrs : List JvmInstr)
    (fuel : Nat) (st : JvmState) (v : JvmVal)
    (hdrop : prog.drop st.pc = instrs) (hfuel : instrs.length ≤ fuel)
    (hstep : stepListAt st.pc instrs st = some v) :
    runJvm fuel prog st = some v := by
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
        rw [runJvm_nonbranch fuel' prog st instr hget hbr]
        have hst : { st with pc := st.pc } = st := rfl
        rw [hst] at hstep
        cases hs : stepInstr instr st with
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

def stepListAtClean (pc : Nat) (instrs : List JvmInstr) (st : JvmState) : Option JvmVal :=
  match instrs with
  | .i2l :: .lconst 4294967295 :: .land :: rest =>
    match st.stack with
    | .i32 x :: s => stepListAtClean (pc + 3) rest { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
    | _ => none
  | [] => none
  | instr :: rest =>
    if isBranchInstr instr then none
    else match stepInstr instr { st with pc := pc } with
    | .inl (some st') => if st'.pc = pc + 1 then stepListAtClean (pc + 1) rest st' else none
    | .inl none => none
    | .inr res => res

theorem stepListAt_of_clean (pc : Nat) (instrs : List JvmInstr) (st : JvmState) (v : JvmVal)
    (h : stepListAtClean pc instrs st = some v) :
    stepListAt pc instrs st = some v := by
  induction pc, instrs, st using stepListAtClean.induct with
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

theorem runJvm_of_stepListAtClean (prog instrs : List JvmInstr)
    (fuel : Nat) (st : JvmState) (v : JvmVal)
    (hdrop : prog.drop st.pc = instrs) (hfuel : instrs.length ≤ fuel)
    (hstep : stepListAtClean st.pc instrs st = some v) :
    runJvm fuel prog st = some v :=
  runJvm_of_stepListAt prog instrs fuel st v hdrop hfuel (stepListAt_of_clean st.pc instrs st v hstep)

theorem runJvmRes_nonbranch (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (instr : JvmInstr)
    (hget : prog[st.pc]? = some instr) (hnbr : isBranchInstr instr = false) :
    runJvmRes (fuel + 1) prog st =
      match stepInstr instr st with
      | .inl (some st') => runJvmRes fuel prog st'
      | .inl none => none
      | .inr (some res) => some (res, st)
      | .inr none => none := by
  cases instr <;> simp [isBranchInstr] at hnbr <;> simp [runJvmRes, hget] <;> rfl

def runJvmResFast : Nat → List JvmInstr → Nat → List JvmInstr → JvmState → Option (JvmVal × JvmState)
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
                runJvmResFast f3 prog (pc + 3) rest' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              | _ => none
        | _ =>
          match stepInstr instr { st with pc := pc } with
          | .inl (some st') =>
            if st'.pc = pc + 1 then runJvmResFast f1 prog (pc + 1) rest st'
            else runJvmResFast f1 prog st'.pc (prog.drop st'.pc) st'
          | .inl none => none
          | .inr (some v) => some (v, { st with pc := pc })
          | .inr none => none
      | .goto target =>
        runJvmResFast f1 prog target (prog.drop target) { st with pc := target }
      | .ifeq target =>
        match st.stack with
        | v :: s =>
          if v.asI32 == 0 then runJvmResFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifne target =>
        match st.stack with
        | v :: s =>
          if !(v.asI32 == 0) then runJvmResFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .iflt target =>
        match st.stack with
        | v :: s =>
          if v.asI32.toBitVec.slt 0#32 then runJvmResFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifle target =>
        match st.stack with
        | v :: s =>
          if v.asI32.toBitVec.sle 0#32 then runJvmResFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifgt target =>
        match st.stack with
        | v :: s =>
          if (0#32).slt v.asI32.toBitVec then runJvmResFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifge target =>
        match st.stack with
        | v :: s =>
          if (0#32).sle v.asI32.toBitVec then runJvmResFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifnull target =>
        match st.stack with
        | v :: s =>
          if v.isNull then runJvmResFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifnonnull target =>
        match st.stack with
        | v :: s =>
          if !v.isNull then runJvmResFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmpeq target =>
        match st.stack with
        | b :: a :: s =>
          if a.asI32 == b.asI32 then runJvmResFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmpne target =>
        match st.stack with
        | b :: a :: s =>
          if !(a.asI32 == b.asI32) then runJvmResFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmplt target =>
        match st.stack with
        | b :: a :: s =>
          if a.asI32.toBitVec.slt b.asI32.toBitVec then runJvmResFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmResFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | _ =>
        match stepInstr instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then
            runJvmResFast f1 prog (pc + 1) rest st'
          else
            runJvmResFast f1 prog st'.pc (prog.drop st'.pc) st'
        | .inl none => none
        | .inr (some v) => some (v, { st with pc := pc })
        | .inr none => none

def runJvmFast (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState) : Option JvmVal :=
  (runJvmResFast fuel prog pc instrs st).map Prod.fst

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

@[simp] theorem JvmVal.ite_eq_if (c : Bool) (t e : Option JvmVal) :
    JvmVal.ite c t e = if c then t else e := by
  cases c <;> cases t with
  | none => simp [JvmVal.ite]
  | some v => cases v <;> cases e with | none => simp [JvmVal.ite] | some w => cases w <;> simp [JvmVal.ite]

theorem runJvm_eq_runJvmRes (fuel : Nat) (prog : List JvmInstr) (st : JvmState) :
    runJvm fuel prog st = (runJvmRes fuel prog st).map Prod.fst := by
  induction fuel generalizing st with
  | zero => rfl
  | succ f ih =>
    cases h : prog[st.pc]? with
    | none => simp [runJvm, runJvmRes, h]
    | some instr =>
      cases hbr : isBranchInstr instr with
      | false =>
        rw [runJvm_nonbranch _ _ _ instr h hbr, runJvmRes_nonbranch _ _ _ instr h hbr]
        cases stepInstr instr st with
        | inl opt => cases opt with | none => rfl | some st' => simp only [ih]
        | inr r => cases r <;> rfl
      | true =>
        cases instr with
        | goto target =>
          simp only [runJvm, runJvmRes, h]
          cases stepInstr (.goto target) st with
          | inl opt => cases opt with | none => rfl | some st' => simp only [ih]
          | inr r => cases r <;> rfl
        | ifeq _ | ifne _ | iflt _ | ifle _ | ifgt _ | ifge _ | ifnull _ | ifnonnull _ =>
          simp only [runJvm, runJvmRes, h]
          rcases st.stack with _ | ⟨v, s⟩
          · rfl
          · simp only [JvmVal.ite_eq_if]
            split <;> simp only [ih]
        | if_icmpeq _ | if_icmpne _ | if_icmplt _ =>
          simp only [runJvm, runJvmRes, h]
          rcases st.stack with _ | ⟨b, _ | ⟨a, s⟩⟩
          · rfl
          · rfl
          · simp only [JvmVal.ite_eq_if]
            split <;> simp only [ih]
        | _ => simp [isBranchInstr] at hbr

theorem runJvmRes_of_runJvmResFast (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr)
    (st : JvmState) (res : JvmVal × JvmState)
    (hpc : st.pc = pc) (hdrop : prog.drop pc = instrs)
    (hfast : runJvmResFast fuel prog pc instrs st = some res) :
    runJvmRes fuel prog st = some res := by
  refine Nat.strongRecOn (motive := fun f => ∀ pc instrs st,
      st.pc = pc → prog.drop pc = instrs → runJvmResFast f prog pc instrs st = some res →
      runJvmRes f prog st = some res) fuel (fun fuel ih pc instrs st hpc hdrop hfast => ?_) pc instrs st hpc hdrop hfast
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
            (hf : (match stepInstr instr { st with pc := pc } with
              | .inl (some st') =>
                if st'.pc = pc + 1 then runJvmResFast f1 prog (pc + 1) rest st'
                else runJvmResFast f1 prog st'.pc (prog.drop st'.pc) st'
              | .inl none => none
              | .inr (some v) => some (v, { st with pc := pc })
              | .inr none => none) = some res) :
            runJvmRes (f1 + 1) prog st = some res := by
          have h0 := hg0 instr rest rfl
          have hst : { st with pc := pc } = st := by cases st; cases hpc; rfl
          rw [runJvmRes_nonbranch f1 prog st instr h0 hnbr]
          rw [hst] at hf
          cases hs : stepInstr instr st with
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
                            rw [runJvmRes_nonbranch _ prog st .i2l h0 rfl]
                            simp only [stepInstr, hstk, JvmVal.asI32]
                            rw [runJvmRes_nonbranch _ prog _ (.lconst 4294967295) (by simpa [Nat.add_assoc] using h1) rfl]
                            simp only [stepInstr]
                            rw [runJvmRes_nonbranch _ prog _ .land (by simpa [Nat.add_assoc] using h2) rfl]
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
            by_cases hcmp : (v.asI32 == 0) = true
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
            by_cases hcmp : (!(v.asI32 == 0)) = true
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
        | _ => exact step_catchall rfl (by simpa [runJvmResFast] using hfast)

theorem runJvm_of_runJvmFast (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (v : JvmVal)
    (hfast : runJvmFast fuel prog st.pc (prog.drop st.pc) st = some v) :
    runJvm fuel prog st = some v := by
  simp only [runJvmFast, Option.map_eq_some_iff] at hfast
  rcases hfast with ⟨⟨res, st'⟩, hres, rfl⟩
  rw [runJvm_eq_runJvmRes, runJvmRes_of_runJvmResFast fuel prog st.pc (prog.drop st.pc) st (res, st') rfl rfl hres]
  rfl

def runJvmValFast : Nat → List JvmInstr → Nat → List JvmInstr → JvmState → Option JvmVal
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
                runJvmValFast f3 prog (pc + 3) rest' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              | _ => none
        | _ =>
          match stepInstr instr { st with pc := pc } with
          | .inl (some st') =>
            if st'.pc = pc + 1 then runJvmValFast f1 prog (pc + 1) rest st'
            else runJvmValFast f1 prog st'.pc (prog.drop st'.pc) st'
          | .inl none => none
          | .inr (some v) => some v
          | .inr none => none
      | .goto target =>
        runJvmValFast f1 prog target (prog.drop target) { st with pc := target }
      | .ifeq target =>
        match st.stack with
        | v :: s =>
          if v.asI32 == 0 then runJvmValFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifne target =>
        match st.stack with
        | v :: s =>
          if !(v.asI32 == 0) then runJvmValFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .iflt target =>
        match st.stack with
        | v :: s =>
          if v.asI32.toBitVec.slt 0#32 then runJvmValFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifle target =>
        match st.stack with
        | v :: s =>
          if v.asI32.toBitVec.sle 0#32 then runJvmValFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifgt target =>
        match st.stack with
        | v :: s =>
          if (0#32).slt v.asI32.toBitVec then runJvmValFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifge target =>
        match st.stack with
        | v :: s =>
          if (0#32).sle v.asI32.toBitVec then runJvmValFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifnull target =>
        match st.stack with
        | v :: s =>
          if v.isNull then runJvmValFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .ifnonnull target =>
        match st.stack with
        | v :: s =>
          if !v.isNull then runJvmValFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmpeq target =>
        match st.stack with
        | b :: a :: s =>
          if a.asI32 == b.asI32 then runJvmValFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmpne target =>
        match st.stack with
        | b :: a :: s =>
          if !(a.asI32 == b.asI32) then runJvmValFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | .if_icmplt target =>
        match st.stack with
        | b :: a :: s =>
          if a.asI32.toBitVec.slt b.asI32.toBitVec then runJvmValFast f1 prog target (prog.drop target) { st with pc := target, stack := s }
          else runJvmValFast f1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
        | _ => none
      | _ =>
        match stepInstr instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then runJvmValFast f1 prog (pc + 1) rest st'
          else runJvmValFast f1 prog st'.pc (prog.drop st'.pc) st'
        | .inl none => none
        | .inr (some v) => some v
        | .inr none => none

private theorem runJvmFast_eq_runJvmValFast (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr)
    (st : JvmState) :
    runJvmFast fuel prog pc instrs st = runJvmValFast fuel prog pc instrs st := by
  induction fuel, prog, pc, instrs, st using runJvmValFast.induct with
  | case1 => rfl
  | _ =>
    all_goals simp_all [runJvmFast, runJvmResFast, runJvmValFast]
    all_goals split <;> simp_all

theorem runJvm_of_runJvmValFast (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (v : JvmVal)
    (hfast : runJvmValFast fuel prog st.pc (prog.drop st.pc) st = some v) :
    runJvm fuel prog st = some v :=
  runJvm_of_runJvmFast fuel prog st v (by rw [runJvmFast_eq_runJvmValFast]; exact hfast)

theorem runJvm_of_runJvmValFast0 (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (v : JvmVal)
    (hpc : st.pc = 0)
    (hfast : runJvmValFast fuel prog 0 prog st = some v) :
    runJvm fuel prog st = some v := by
  apply runJvm_of_runJvmValFast
  rwa [hpc, List.drop_zero]

theorem runJvmRes_of_runJvmResFast0 (fuel : Nat) (prog : List JvmInstr) (st : JvmState)
    (res : JvmVal × JvmState) (hpc : st.pc = 0)
    (hfast : runJvmResFast fuel prog 0 prog st = some res) :
    runJvmRes fuel prog st = some res := by
  apply runJvmRes_of_runJvmResFast fuel prog st.pc (prog.drop st.pc) st res rfl rfl
  rwa [hpc, List.drop_zero]

theorem runJvmRes_map_of_runJvmResFast0 {α : Type} (f : JvmVal × JvmState → α)
    (fuel : Nat) (prog : List JvmInstr) (st : JvmState) (y : α)
    (hpc : st.pc = 0)
    (hfast : (runJvmResFast fuel prog 0 prog st).map f = some y) :
    (runJvmRes fuel prog st).map f = some y := by
  cases h : runJvmResFast fuel prog 0 prog st with
  | none => simp [h] at hfast
  | some p =>
    simp only [h, Option.map_some, Option.some.injEq] at hfast
    have h1 := runJvmRes_of_runJvmResFast0 fuel prog st p hpc h
    simp [h1, hfast]

def stepBlock : Nat → List JvmInstr → JvmState → Sum (Nat × JvmState) (Option JvmVal)
  | pc, .i2l :: .lconst 4294967295 :: .land :: rest, st =>
    match st.stack with
    | .i32 x :: s =>
      match stepBlock (pc + 3) rest { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s } with
      | .inl (c, st') => .inl (c + 3, st')
      | .inr res => .inr res
    | _ => .inr none
  | _, [], _ => .inr none
  | pc, instr :: rest, st =>
    if isBranchInstr instr then .inl (0, { st with pc := pc })
    else match stepInstr instr { st with pc := pc } with
    | .inl (some st') =>
      if st'.pc = pc + 1 then
        match stepBlock (pc + 1) rest st' with
        | .inl (c, st'') => .inl (c + 1, st'')
        | .inr res => .inr res
      else .inl (1, st')
    | .inl none => .inr none
    | .inr res => .inr res

private theorem runJvmValFast_eq_drop_pc (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = true) :
    runJvmValFast fuel prog pc (instr :: rest) { st with pc := pc } =
      runJvmValFast fuel prog pc (instr :: rest) st := by
  cases fuel with
  | zero => rfl
  | succ f1 =>
    cases instr <;> simp_all [isBranchInstr, runJvmValFast]

private theorem runJvmValFast_step_nonbranch (f1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = false)
    (hno : ¬(instr = .i2l ∧ ∃ rest', rest = .lconst 4294967295 :: .land :: rest')) :
    runJvmValFast (f1 + 1) prog pc (instr :: rest) st =
      match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then runJvmValFast f1 prog (pc + 1) rest st'
        else runJvmValFast f1 prog st'.pc (prog.drop st'.pc) st'
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

private theorem stepBlock_cons_ne (pc : Nat) (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState)
    (hno : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r')) :
    stepBlock pc (instr :: rest) st =
      if isBranchInstr instr then .inl (0, { st with pc := pc })
      else match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then
          match stepBlock (pc + 1) rest st' with
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

private theorem runJvmValFast_stepBlock_aux (n : Nat) (fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) (hlen : instrs.length ≤ n)
    (hdrop : prog.drop pc = instrs) (hfuel : instrs.length ≤ fuel) :
    runJvmValFast fuel prog pc instrs st =
      match stepBlock pc instrs st with
      | .inl (c', st') => runJvmValFast (fuel - c') prog st'.pc (prog.drop st'.pc) st'
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
            have hstep : runJvmValFast (f3 + 3) prog pc
                (.i2l :: .lconst 4294967295 :: .land :: r') st =
                runJvmValFast f3 prog (pc + 3) r'
                  { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s } := by
              simp [runJvmValFast, hstk]
            rw [hstep]
            have hih := ih f3 (pc + 3) r' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              (by simp at hlen; omega) (by rw [← List.drop_drop, hdrop]; rfl) (by simp at hfuel; omega)
            rw [hih]
            cases hsb : stepBlock (pc + 3) r' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s } with
            | inl p => rcases p with ⟨c, st'⟩; simp [hsb, Nat.add_sub_add_right]
            | inr res => simp [hsb]
          | _ => simp [runJvmValFast, hstk]
      · have hno : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r') := by
          rintro ⟨rfl, r', rfl⟩; exact hpat ⟨r', rfl, rfl⟩
        rw [stepBlock_cons_ne pc instr rest st hno]
        by_cases hbr : isBranchInstr instr = true
        · simp only [hbr, ite_true, Nat.sub_zero, hdrop]
          exact (runJvmValFast_eq_drop_pc fuel prog pc instr rest st hbr).symm
        · have hbrf : isBranchInstr instr = false := Bool.eq_false_iff.mpr hbr
          have ⟨f1, hf1⟩ : ∃ f1, fuel = f1 + 1 :=
            ⟨fuel - 1, (Nat.sub_add_cancel (by simp at hfuel; omega)).symm⟩
          subst hf1
          simp only [hbrf, Bool.false_eq_true, ite_false]
          rw [runJvmValFast_step_nonbranch f1 prog pc instr rest st hbrf hno]
          cases hst : stepInstr instr { st with pc := pc } with
          | inl o =>
            cases o with
            | none => rfl
            | some st' =>
              by_cases hpc : st'.pc = pc + 1
              · simp only [hpc, ite_true]
                have hih := ih f1 (pc + 1) rest st' (by simp at hlen; omega)
                  (by rw [← List.drop_drop, hdrop]; rfl) (by simp at hfuel; omega)
                rw [hih]
                cases stepBlock (pc + 1) rest st' with
                | inl p => rcases p with ⟨c, st''⟩; simp [Nat.add_sub_add_right]
                | inr res => rfl
              · simp [hpc]
          | inr res =>
            cases res <;> rfl

def afterBlock (step : Sum (Nat × JvmState) (Option JvmVal)) (fuel : Nat) (prog : List JvmInstr) :
    Option JvmVal :=
  match step with
  | .inl (c', st') => runJvmValFast (fuel - c') prog st'.pc (prog.drop st'.pc) st'
  | .inr res => res

theorem runJvmValFast_stepBlock (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr)
    (st : JvmState) (hdrop : prog.drop pc = instrs) (hfuel : instrs.length ≤ fuel) :
    runJvmValFast fuel prog pc instrs st =
      match stepBlock pc instrs st with
      | .inl (c', st') => runJvmValFast (fuel - c') prog st'.pc (prog.drop st'.pc) st'
      | .inr res => res :=
  runJvmValFast_stepBlock_aux instrs.length fuel prog pc instrs st (Nat.le_refl _) hdrop hfuel

theorem runJvmValFast_stepBlock0 (fuel : Nat) (prog : List JvmInstr) (st : JvmState)
    (hfuel : prog.length ≤ fuel) :
    runJvmValFast fuel prog 0 prog st =
      match stepBlock 0 prog st with
      | .inl (c', st') => runJvmValFast (fuel - c') prog st'.pc (prog.drop st'.pc) st'
      | .inr res => res :=
  runJvmValFast_stepBlock fuel prog 0 prog st (by simp) hfuel

theorem runJvmValFast_stepBlock_after (fuel : Nat) (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr)
    (st : JvmState) (hdrop : prog.drop pc = instrs) (hfuel : instrs.length ≤ fuel) :
    runJvmValFast fuel prog pc instrs st = afterBlock (stepBlock pc instrs st) fuel prog := by
  rw [runJvmValFast_stepBlock fuel prog pc instrs st hdrop hfuel]; rfl

theorem runJvmValFast_stepBlock0_after (fuel : Nat) (prog : List JvmInstr) (st : JvmState)
    (hfuel : prog.length ≤ fuel) :
    runJvmValFast fuel prog 0 prog st = afterBlock (stepBlock 0 prog st) fuel prog :=
  runJvmValFast_stepBlock_after fuel prog 0 prog st (by simp) hfuel

def evalBranchInstr (fuel1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (st : JvmState) : Option JvmVal :=
  match instr with
  | .ifeq target =>
    match st.stack with
    | v :: s =>
      if v.asI32 == 0 then runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifne target =>
    match st.stack with
    | v :: s =>
      if !(v.asI32 == 0) then runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .iflt target =>
    match st.stack with
    | v :: s =>
      if v.asI32.toBitVec.slt 0#32 then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifle target =>
    match st.stack with
    | v :: s =>
      if v.asI32.toBitVec.sle 0#32 then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifgt target =>
    match st.stack with
    | v :: s =>
      if (0#32).slt v.asI32.toBitVec then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifge target =>
    match st.stack with
    | v :: s =>
      if (0#32).sle v.asI32.toBitVec then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifnull target =>
    match st.stack with
    | v :: s =>
      if v.isNull then runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifnonnull target =>
    match st.stack with
    | v :: s =>
      if !v.isNull then runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpeq target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32 == b.asI32 then runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpne target =>
    match st.stack with
    | b :: a :: s =>
      if !(a.asI32 == b.asI32) then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmplt target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32.toBitVec.slt b.asI32.toBitVec then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) (prog.drop (pc + 1)) { st with pc := pc + 1, stack := s }
    | _ => none
  | .goto target => runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target }
  | _ => none

theorem runJvmValFast_at_branch {fuel : Nat} (hf : 0 < fuel) {prog : List JvmInstr} {pc : Nat}
    {st : JvmState} (hbr : isBranchInstr ((prog.drop pc).headD .nop) = true) :
    runJvmValFast fuel prog pc (prog.drop pc) st =
      evalBranchInstr (fuel - 1) prog pc ((prog.drop pc).headD .nop) st := by
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

inductive BlockChunkRes where
  | cont (fuel' : Nat) (pc' : Nat) (instrs' : List JvmInstr) (st' : JvmState)
  | jump (fuel' : Nat) (st' : JvmState)
  | done (res : Option JvmVal)

def stepBlockChunk : Nat → Nat → Nat → List JvmInstr → JvmState → BlockChunkRes
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
                stepBlockChunk m f3 (pc + 3) rest' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              | _ => .done none
        | _ =>
          match stepInstr instr { st with pc := pc } with
          | .inl (some st') =>
            if st'.pc = pc + 1 then stepBlockChunk m f1 (pc + 1) rest st'
            else .jump f1 st'
          | .inl none => .done none
          | .inr res => .done res
      | _ =>
        match stepInstr instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then stepBlockChunk m f1 (pc + 1) rest st'
          else .jump f1 st'
        | .inl none => .done none
        | .inr res => .done res

def afterBlockChunk (r : BlockChunkRes) (prog : List JvmInstr) : Option JvmVal :=
  match r with
  | .cont f' pc' instrs' st' => runJvmValFast f' prog pc' instrs' st'
  | .jump f' st' => runJvmValFast f' prog st'.pc (prog.drop st'.pc) st'
  | .done res => res

private theorem stepBlockChunk_cons_ne (m f1 pc : Nat) (instr : JvmInstr) (rest : List JvmInstr)
    (st : JvmState) (hno : ¬∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r') :
    stepBlockChunk (m + 1) (f1 + 1) pc (instr :: rest) st =
      if isBranchInstr instr then .cont (f1 + 1) pc (instr :: rest) st
      else match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then stepBlockChunk m f1 (pc + 1) rest st'
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

private theorem runJvmValFast_stepBlockChunk_aux (m : Nat) (fuel : Nat) (prog : List JvmInstr)
    (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    runJvmValFast fuel prog pc instrs st = afterBlockChunk (stepBlockChunk m fuel pc instrs st) prog := by
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
          · rw [stepBlockChunk_cons_ne m f1 pc instr rest st hpat]
            simp only [hbr, ↓reduceIte, afterBlockChunk]
          · have hbrf : isBranchInstr instr = false := Bool.eq_false_iff.mpr hbr
            have hno' : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r') :=
              fun ⟨h1, r', h2⟩ => hpat ⟨r', h1, h2⟩
            rw [stepBlockChunk_cons_ne m f1 pc instr rest st hpat,
              runJvmValFast_step_nonbranch f1 prog pc instr rest st hbrf hno']
            simp only [hbrf, Bool.false_eq_true, ↓reduceIte]
            cases hst : stepInstr instr { st with pc := pc } with
            | inl o =>
              cases o with
              | none => rfl
              | some st' =>
                by_cases hpc : st'.pc = pc + 1
                · simp only [hpc, ↓reduceIte]; exact ih f1 (pc + 1) rest st'
                · simp only [hpc, ↓reduceIte, afterBlockChunk]
            | inr res => cases res <;> rfl

theorem runJvmValFast_stepBlockChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmValFast fuel prog pc instrs st = afterBlockChunk (stepBlockChunk maxSteps fuel pc instrs st) prog :=
  runJvmValFast_stepBlockChunk_aux maxSteps fuel prog pc instrs st

def evalBranchInstrCons (fuel1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState) : Option JvmVal :=
  match instr with
  | .ifeq target =>
    match st.stack with
    | v :: s =>
      if v.asI32 == 0 then runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifne target =>
    match st.stack with
    | v :: s =>
      if !(v.asI32 == 0) then runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .iflt target =>
    match st.stack with
    | v :: s =>
      if v.asI32.toBitVec.slt 0#32 then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifle target =>
    match st.stack with
    | v :: s =>
      if v.asI32.toBitVec.sle 0#32 then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifgt target =>
    match st.stack with
    | v :: s =>
      if (0#32).slt v.asI32.toBitVec then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifge target =>
    match st.stack with
    | v :: s =>
      if (0#32).sle v.asI32.toBitVec then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifnull target =>
    match st.stack with
    | v :: s =>
      if v.isNull then runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifnonnull target =>
    match st.stack with
    | v :: s =>
      if !v.isNull then runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpeq target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32 == b.asI32 then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpne target =>
    match st.stack with
    | b :: a :: s =>
      if !(a.asI32 == b.asI32) then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmplt target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32.toBitVec.slt b.asI32.toBitVec then
        runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmValFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .goto target => runJvmValFast fuel1 prog target (prog.drop target) { st with pc := target }
  | _ => none

theorem runJvmValFast_at_branch_cons (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = true) :
    runJvmValFast (f1 + 1) prog pc (instr :: rest) st = evalBranchInstrCons f1 prog pc instr rest st := by
  cases instr <;> first
    | (simp only [isBranchInstr] at hbr; contradiction)
    | rfl
    | (simp only [runJvmValFast, evalBranchInstrCons, stepInstr]; split <;> rfl)

inductive BlockResChunkRes where
  | cont (fuel' : Nat) (pc' : Nat) (instrs' : List JvmInstr) (st' : JvmState)
  | jump (fuel' : Nat) (st' : JvmState)
  | done (res : Option (JvmVal × JvmState))

def stepResBlockChunk : Nat → Nat → Nat → List JvmInstr → JvmState → BlockResChunkRes
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
                stepResBlockChunk m f3 (pc + 3) rest' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              | _ => .done none
        | _ =>
          match stepInstr instr { st with pc := pc } with
          | .inl (some st') =>
            if st'.pc = pc + 1 then stepResBlockChunk m f1 (pc + 1) rest st'
            else .jump f1 st'
          | .inl none => .done none
          | .inr (some v) => .done (some (v, { st with pc := pc }))
          | .inr none => .done none
      | _ =>
        match stepInstr instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then stepResBlockChunk m f1 (pc + 1) rest st'
          else .jump f1 st'
        | .inl none => .done none
        | .inr (some v) => .done (some (v, { st with pc := pc }))
        | .inr none => .done none

def afterResBlockChunk (r : BlockResChunkRes) (prog : List JvmInstr) : Option (JvmVal × JvmState) :=
  match r with
  | .cont f' pc' instrs' st' => runJvmResFast f' prog pc' instrs' st'
  | .jump f' st' => runJvmResFast f' prog st'.pc (prog.drop st'.pc) st'
  | .done res => res

private theorem stepResBlockChunk_cons_ne (m f1 pc : Nat) (instr : JvmInstr) (rest : List JvmInstr)
    (st : JvmState) (hno : ¬∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r') :
    stepResBlockChunk (m + 1) (f1 + 1) pc (instr :: rest) st =
      if isBranchInstr instr then .cont (f1 + 1) pc (instr :: rest) st
      else match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then stepResBlockChunk m f1 (pc + 1) rest st'
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

private theorem runJvmResFast_step_nonbranch (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = false)
    (hno : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r')) :
    runJvmResFast (f1 + 1) prog pc (instr :: rest) st =
      match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then runJvmResFast f1 prog (pc + 1) rest st'
        else runJvmResFast f1 prog st'.pc (prog.drop st'.pc) st'
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

private theorem runJvmResFast_stepBlockChunk_aux (m : Nat) (fuel : Nat) (prog : List JvmInstr)
    (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    runJvmResFast fuel prog pc instrs st = afterResBlockChunk (stepResBlockChunk m fuel pc instrs st) prog := by
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
          · rw [stepResBlockChunk_cons_ne m f1 pc instr rest st hpat]
            simp only [hbr, ↓reduceIte, afterResBlockChunk]
          · have hbrf : isBranchInstr instr = false := Bool.eq_false_iff.mpr hbr
            have hno' : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r') :=
              fun ⟨h1, r', h2⟩ => hpat ⟨r', h1, h2⟩
            rw [stepResBlockChunk_cons_ne m f1 pc instr rest st hpat,
              runJvmResFast_step_nonbranch f1 prog pc instr rest st hbrf hno']
            simp only [hbrf, Bool.false_eq_true, ↓reduceIte]
            cases hst : stepInstr instr { st with pc := pc } with
            | inl o =>
              cases o with
              | none => rfl
              | some st' =>
                by_cases hpc : st'.pc = pc + 1
                · simp only [hpc, ↓reduceIte]; exact ih f1 (pc + 1) rest st'
                · simp only [hpc, ↓reduceIte, afterResBlockChunk]
            | inr res => cases res <;> rfl

theorem runJvmResFast_stepBlockChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmResFast fuel prog pc instrs st = afterResBlockChunk (stepResBlockChunk maxSteps fuel pc instrs st) prog :=
  runJvmResFast_stepBlockChunk_aux maxSteps fuel prog pc instrs st

def evalResBranchInstrCons (fuel1 : Nat) (prog : List JvmInstr) (pc : Nat) (instr : JvmInstr)
    (rest : List JvmInstr) (st : JvmState) : Option (JvmVal × JvmState) :=
  match instr with
  | .ifeq target =>
    match st.stack with
    | v :: s =>
      if v.asI32 == 0 then runJvmResFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifne target =>
    match st.stack with
    | v :: s =>
      if !(v.asI32 == 0) then runJvmResFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .iflt target =>
    match st.stack with
    | v :: s =>
      if v.asI32.toBitVec.slt 0#32 then
        runJvmResFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifle target =>
    match st.stack with
    | v :: s =>
      if v.asI32.toBitVec.sle 0#32 then
        runJvmResFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifgt target =>
    match st.stack with
    | v :: s =>
      if (0#32).slt v.asI32.toBitVec then
        runJvmResFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifge target =>
    match st.stack with
    | v :: s =>
      if (0#32).sle v.asI32.toBitVec then
        runJvmResFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifnull target =>
    match st.stack with
    | v :: s =>
      if v.isNull then runJvmResFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .ifnonnull target =>
    match st.stack with
    | v :: s =>
      if !v.isNull then runJvmResFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpeq target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32 == b.asI32 then
        runJvmResFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmpne target =>
    match st.stack with
    | b :: a :: s =>
      if !(a.asI32 == b.asI32) then
        runJvmResFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .if_icmplt target =>
    match st.stack with
    | b :: a :: s =>
      if a.asI32.toBitVec.slt b.asI32.toBitVec then
        runJvmResFast fuel1 prog target (prog.drop target) { st with pc := target, stack := s }
      else runJvmResFast fuel1 prog (pc + 1) rest { st with pc := pc + 1, stack := s }
    | _ => none
  | .goto target => runJvmResFast fuel1 prog target (prog.drop target) { st with pc := target }
  | _ => none

theorem runJvmResFast_at_branch_cons (f1 : Nat) (prog : List JvmInstr) (pc : Nat)
    (instr : JvmInstr) (rest : List JvmInstr) (st : JvmState) (hbr : isBranchInstr instr = true) :
    runJvmResFast (f1 + 1) prog pc (instr :: rest) st = evalResBranchInstrCons f1 prog pc instr rest st := by
  cases instr <;> first
    | (simp only [isBranchInstr] at hbr; contradiction)
    | rfl
    | (simp only [runJvmResFast, evalResBranchInstrCons, stepInstr]; split <;> rfl)

private partial def reduceStateProj (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let e := e.consumeMData
  if let .proj ``JvmState i s := e then
    let s' ← reduceStateProj s
    if s'.isAppOfArity ``JvmState.mk 6 then
      return ← reduceStateProj (s'.getArg! i)
    let sw ←
      if s'.isAppOf ``initJvmState then
        match ← Lean.Meta.unfoldDefinition? s' with
        | some u => Lean.Meta.whnfCore u
        | none => Lean.Meta.whnfCore s'
      else
        Lean.Meta.whnfCore s'
    if sw.isAppOfArity ``JvmState.mk 6 then
      return ← reduceStateProj (sw.getArg! i)
    return .proj ``JvmState i s'
  if let some n := e.getAppFn.constName? then
    if e.getAppNumArgs == 1 &&
       (n == ``JvmState.locals || n == ``JvmState.arenas ||
        n == ``JvmState.u64Arrays || n == ``JvmState.asciiArrays) then
      let i := if n == ``JvmState.locals then 2
        else if n == ``JvmState.arenas then 3
        else if n == ``JvmState.u64Arrays then 4
        else 5
      let s' ← reduceStateProj e.appArg!
      if s'.isAppOfArity ``JvmState.mk 6 then
        return ← reduceStateProj (s'.getArg! i)
      let sw ←
        if s'.isAppOf ``initJvmState then
          match ← Lean.Meta.unfoldDefinition? s' with
          | some u => Lean.Meta.whnfCore u
          | none => Lean.Meta.whnfCore s'
        else
          Lean.Meta.whnfCore s'
      if sw.isAppOfArity ``JvmState.mk 6 then
        return ← reduceStateProj (sw.getArg! i)
      return Lean.mkApp e.getAppFn s'
    if n == ``setLocal && e.getAppNumArgs == 3 then
      let args := e.getAppArgs
      return Lean.mkApp3 e.getAppFn (← reduceStateProj args[0]!) args[1]! args[2]!
  return e

private partial def normJvmExpr (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let e ← Lean.Meta.whnf e
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn.constName? with
  | some n =>
    if n == ``Sum.inl || n == ``Sum.inr || n == ``Prod.mk ||
       n == ``Option.some || n == ``List.cons ||
       n == ``BlockChunkRes.done || n == ``BlockResChunkRes.done then
      let args' ← args.mapM normJvmExpr
      return Lean.mkAppN fn args'
    else if n == ``BlockChunkRes.cont || n == ``BlockResChunkRes.cont then
      let f' ← normJvmExpr args[0]!
      let pc' ← normJvmExpr args[1]!
      let st' ← normJvmExpr args[3]!
      return Lean.mkAppN fn #[f', pc', args[2]!, st']
    else if n == ``BlockChunkRes.jump || n == ``BlockResChunkRes.jump then
      let f' ← normJvmExpr args[0]!
      let st' ← normJvmExpr args[1]!
      return Lean.mkAppN fn #[f', st']
    else if n == ``JvmState.mk then
      -- Normalize pc (0) and stack (1), and collapse JvmState field projections without expanding `setLocal`.
      let pc' ← normJvmExpr args[0]!
      let stk' ← normJvmExpr args[1]!
      let locs' ← reduceStateProj args[2]!
      let ar' ← reduceStateProj args[3]!
      let u64' ← reduceStateProj args[4]!
      let asc' ← reduceStateProj args[5]!
      return Lean.mkAppN fn #[pc', stk', locs', ar', u64', asc']
    else if n == ``Bool.rec then
      let args' ← args.mapM fun a => do
        let aw ← Lean.Meta.whnf a
        if aw.isLambda then
          Lean.Meta.lambdaTelescope aw fun xs body => do
            let body' ← normJvmExpr body
            Lean.Meta.mkLambdaFVars xs body'
        else return a
      return Lean.mkAppN fn args'
    else
      return e
  | none => return e

elab "jvm_whnf_blk" : conv => do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let lhs' ← normJvmExpr lhs
  Lean.Elab.Tactic.Conv.changeLhs lhs'

private partial def evalNatLit? (e : Lean.Expr) : Lean.MetaM (Option Nat) := do
  if e.hasFVar || e.hasLooseBVars then return none
  let e ← Lean.Meta.whnf e
  if let some n := e.rawNatLit? then return some n
  if e.isConstOf ``Nat.zero then return some 0
  if e.isAppOfArity ``Nat.succ 1 then
    return (← evalNatLit? e.appArg!).map (· + 1)
  return none

private def foldInitLocals (init slots : Lean.Expr) : Lean.Expr := Id.run do
  let mut acc := init
  let mut cur := slots
  while cur.isAppOfArity ``List.cons 3 do
    let hd := cur.getArg! 1
    let tl := cur.getArg! 2
    if hd.isAppOfArity ``Prod.mk 4 then
      acc := Lean.mkApp3 (Lean.mkConst ``setLocal) acc (hd.getArg! 2) (hd.getArg! 3)
      cur := tl
    else
      break
  return acc

private partial def normJvmLocalsExpr (e : Lean.Expr) : Lean.MetaM Lean.Expr :=
  Lean.Meta.transform e
    (pre := fun sub => do
      if sub.isAppOfArity ``List.cons 3 && (sub.getArg! 0).isConstOf ``JvmInstr then
        return .done sub
      else if sub.isAppOfArity ``List.nil 1 && (sub.getArg! 0).isConstOf ``JvmInstr then
        return .done sub
      else if sub.isAppOfArity ``setLocal 4 then
        let args := sub.getAppArgs
        if let (some nk, some nidx) := (← evalNatLit? args[1]!, ← evalNatLit? args[3]!) then
          if nidx == nk then
            return .visit args[2]!
          else
            return .visit (Lean.mkApp args[0]! args[3]!)
        return .continue
      else if sub.isAppOfArity ``List.foldl 6 then
        let args := sub.getAppArgs
        if Option.isSome (args[2]!.find? (·.isConstOf ``setLocal)) then
          if let some _ ← evalNatLit? args[5]! then
            if args[4]!.isAppOfArity ``List.cons 3 || args[4]!.isAppOfArity ``List.nil 1 then
              return .visit (Lean.mkApp (foldInitLocals args[3]! args[4]!) args[5]!)
        return .continue
      else if sub.isProj then
        let sub' ← reduceStateProj sub
        if sub' != sub then return .visit sub'
        return .continue
      else if sub.isAppOfArity ``JvmState.locals 1 || sub.isAppOfArity ``JvmState.arenas 1 ||
              sub.isAppOfArity ``JvmState.u64Arrays 1 || sub.isAppOfArity ``JvmState.asciiArrays 1 then
        let sub' ← reduceStateProj sub
        if sub' != sub then return .visit sub'
        return .continue
      else if sub.isApp && (sub.appFn!.isProj || sub.appFn!.isAppOfArity ``JvmState.locals 1) then
        let locs' ← reduceStateProj sub.appFn!
        if locs' != sub.appFn! then
          return .visit (Lean.mkApp locs' sub.appArg!)
        return .continue
      else if sub.isAppOfArity ``JvmState.locals 2 then
        let s := sub.appFn!.appArg!
        let idx := sub.appArg!
        if let some _ ← evalNatLit? idx then
          let sw ← Lean.Meta.whnf s
          if sw.isAppOfArity ``JvmState.mk 6 then
            let locs := sw.getArg! 2
            if locs.isAppOfArity ``List.foldl 5 then
              let folded := foldInitLocals (locs.getArg! 3) (locs.getArg! 4)
              return .visit (Lean.mkApp folded idx)
            else
              let next := Lean.mkApp locs idx
              if next != sub then return .visit next else return .continue
          else return .continue
        else return .continue
      else if sub.isApp && sub.appFn!.isLambda then
        let body := sub.appFn!.bindingBody!
        if !body.hasLooseBVars && !sub.appArg!.hasFVar && !sub.appArg!.hasLooseBVars then
          if let some _ ← evalNatLit? sub.appArg! then
            return .visit body
        return .continue
      else
        return .continue)
    (post := fun sub => do
      if sub.isAppOfArity ``JvmVal.asI32 1 then
        let a := sub.appArg!
        if a.isAppOfArity ``JvmVal.i32 1 then
          return .done a.appArg!
        else if a.isAppOfArity ``JvmVal.i64 1 then
          return .done (Lean.mkApp (Lean.mkConst ``UInt64.toUInt32) a.appArg!)
        return .done sub
      else if sub.isAppOfArity ``JvmVal.asI64 1 then
        let a := sub.appArg!
        if a.isAppOfArity ``JvmVal.i64 1 then
          return .done a.appArg!
        else if a.isAppOfArity ``JvmVal.i32 1 then
          return .done (Lean.mkApp (Lean.mkConst ``UInt32.toUInt64) a.appArg!)
        return .done sub
      else if sub.isAppOfArity ``JvmVal.isNull 1 then
        let a := sub.appArg!
        if a.isConstOf ``JvmVal.null then
          return .done (Lean.mkConst ``Bool.true)
        return .done sub
      else
        return .done sub)

elab "norm_jvm_locals" : conv => do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let lhs' ← normJvmLocalsExpr lhs
  Lean.Elab.Tactic.Conv.changeLhs lhs'

@[simp] theorem checkInstanceOf_level4_level4 (h : UInt32) (nw ne sw se : UInt64) :
    checkInstanceOf "com/alexvanyo/composelife/model/MacroCell$Level4Node"
      (.mc (.level4Node h nw ne sw se)) = true := rfl

@[simp] theorem checkInstanceOf_level4_cell (h : UInt32) (nw ne sw se : MacroCell) :
    checkInstanceOf "com/alexvanyo/composelife/model/MacroCell$Level4Node"
      (.mc (.cellNode h nw ne sw se)) = false := rfl

@[simp] theorem checkInstanceOf_cell_level4 (h : UInt32) (nw ne sw se : UInt64) :
    checkInstanceOf "com/alexvanyo/composelife/model/MacroCell$CellNode"
      (.mc (.level4Node h nw ne sw se)) = false := rfl

@[simp] theorem checkInstanceOf_cell_cell (h : UInt32) (nw ne sw se : MacroCell) :
    checkInstanceOf "com/alexvanyo/composelife/model/MacroCell$CellNode"
      (.mc (.cellNode h nw ne sw se)) = true := rfl

private theorem ui32_beq_0_0 : ((0 : UInt32) == 0) = true := rfl
private theorem ui32_beq_1_0 : ((1 : UInt32) == 0) = false := rfl

private partial def fastDropListEq (e : Lean.Expr) (n : Nat) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
  let ty := Lean.mkConst ``JvmInstr
  if n == 0 then
    let lhs := Lean.mkAppN (Lean.mkConst ``List.drop [Lean.Level.zero]) #[ty, Lean.toExpr 0, e]
    return (e, ← Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl e) (← Lean.Meta.mkEq lhs e))
  let mut cur := e
  let mut remaining := n
  let step := 40
  let mut accEq : Option Lean.Expr := none
  let mut dropped : Nat := 0
  while remaining > 0 do
    let k := min remaining step
    let curWhnf ← Lean.Meta.whnf cur
    let mut tail := curWhnf
    for _ in [:k] do
      let t ← Lean.Meta.whnf tail
      if t.isAppOfArity ``List.cons 3 then
        tail := t.getArg! 2
      else
        tail := t
        break
    let lhsStep := Lean.mkAppN (Lean.mkConst ``List.drop [Lean.Level.zero]) #[ty, Lean.toExpr k, curWhnf]
    let stepEq ← Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl tail) (← Lean.Meta.mkEq lhsStep tail)
    match accEq with
    | none =>
      let origLhs := Lean.mkAppN (Lean.mkConst ``List.drop [Lean.Level.zero]) #[ty, Lean.toExpr k, e]
      let eq0 ← Lean.Meta.mkExpectedTypeHint stepEq (← Lean.Meta.mkEq origLhs tail)
      accEq := some eq0
      cur := tail
      dropped := k
    | some prevEq =>
      let fnDropK := Lean.mkApp2 (Lean.mkConst ``List.drop [Lean.Level.zero]) ty (Lean.toExpr k)
      let ap ← Lean.Meta.mkCongrArg fnDropK prevEq
      let eqCurWhnf ← Lean.Meta.mkEqTrans ap stepEq
      let ddrop := Lean.mkAppN (Lean.mkConst ``List.drop_drop [Lean.Level.zero])
        #[ty, Lean.toExpr k, Lean.toExpr dropped, e]
      let symD ← Lean.Meta.mkEqSymm ddrop
      let ap1 ← Lean.Meta.mkEqTrans symD eqCurWhnf
      let newDropped := dropped + k
      let sumEq := Lean.mkAppN (Lean.mkConst ``List.drop [Lean.Level.zero]) #[ty, Lean.toExpr newDropped, e]
      let ap2 ← Lean.Meta.mkExpectedTypeHint ap1 (← Lean.Meta.mkEq sumEq tail)
      accEq := some ap2
      cur := tail
      dropped := newDropped
    remaining := remaining - k
  return (cur, accEq.get!)

private theorem option_map_ite {α β : Type} (f : α → β) (c : Prop) [Decidable c] (t e : Option α) :
    (if c then t else e).map f = if c then t.map f else e.map f := by
  split <;> rfl

private partial def normRunTail (b : Lean.Expr) : Lean.MetaM (Lean.Expr × Option Lean.Expr) := do
  if b.isAppOfArity ``Option.map 4 then
    let ma := b.getAppArgs
    let (inner', eqOpt) ← normRunTail ma[3]!
    let newB := Lean.mkAppN b.getAppFn #[ma[0]!, ma[1]!, ma[2]!, inner']
    match eqOpt with
    | none => return (newB, none)
    | some eqP =>
      let pf3 := Lean.mkAppN b.getAppFn #[ma[0]!, ma[1]!, ma[2]!]
      return (newB, some (← Lean.Meta.mkCongrArg pf3 eqP))
  else if b.isAppOfArity ``runJvmValFast 5 || b.isAppOfArity ``runJvmResFast 5 then
    let ba := b.getAppArgs
    let fuel' ← Lean.Meta.whnf ba[0]!
    let pc' ← Lean.Meta.whnf ba[2]!
    let st' ← normJvmExpr ba[4]!
    let mut instrs' := ba[3]!
    let mut instrsEq : Option Lean.Expr := none
    if instrs'.isAppOfArity ``List.drop 3 then
      let da := instrs'.getAppArgs
      if let some n ← evalNatLit? da[1]! then
        let (rhs, eqP) ← fastDropListEq da[2]! n
        instrs' := rhs
        instrsEq := some eqP
    let newB := Lean.mkAppN b.getAppFn #[fuel', ba[1]!, pc', instrs', st']
    match instrsEq with
    | none => return (newB, none)
    | some eqP =>
      let lam := Lean.mkLambda `x .default (← Lean.Meta.inferType ba[3]!)
        (Lean.mkAppN b.getAppFn #[fuel', ba[1]!, pc', Lean.Expr.bvar 0, st'])
      let fullEq ← Lean.Meta.mkCongrArg lam eqP
      let prefixB := Lean.mkAppN b.getAppFn #[fuel', ba[1]!, pc', ba[3]!, st']
      let defEq ← Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl b) (← Lean.Meta.mkEq b prefixB)
      return (newB, some (← Lean.Meta.mkEqTrans defEq fullEq))
  else return (b, none)

elab "jvm_whnf_run_args" : conv => do
  let e ← Lean.Elab.Tactic.Conv.getLhs
  let eTop := if e.isAppOfArity ``Option.map 4 then e else e
  if eTop.isAppOfArity ``Option.map 4 ||
     eTop.isAppOfArity ``runJvmValFast 5 || eTop.isAppOfArity ``runJvmResFast 5 then
    let (e', eqOpt) ← normRunTail eTop
    match eqOpt with
    | some eqP => Lean.Elab.Tactic.Conv.updateLhs e' eqP
    | none => Lean.Elab.Tactic.Conv.changeLhs e'
  else if e.isAppOfArity ``ite 5 then
    let args := e.getAppArgs
    let (t', teqOpt) ← normRunTail args[3]!
    let (f', feqOpt) ← normRunTail args[4]!
    let newE := Lean.mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, t', f']
    if teqOpt.isNone && feqOpt.isNone then
      Lean.Elab.Tactic.Conv.changeLhs newE
    else
      let teq ← match teqOpt with
        | some p => pure p
        | none => Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl t') (← Lean.Meta.mkEq args[3]! t')
      let feq ← match feqOpt with
        | some p => pure p
        | none => Lean.Meta.mkExpectedTypeHint (← Lean.Meta.mkEqRefl f') (← Lean.Meta.mkEq args[4]! f')
      let pf3 := Lean.mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!]
      let c1 ← Lean.Meta.mkCongrArg pf3 teq
      let c2 ← Lean.Meta.mkCongr c1 feq
      Lean.Elab.Tactic.Conv.updateLhs newE c2

private def unwrapRunLhs (e : Lean.Expr) : Lean.Expr × Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``Option.map 4 then
    ((e.getArg! 3).consumeMData, true)
  else
    (e, false)

private def isRunJvmAtNonBranch : Lean.Elab.Tactic.TacticM Bool := do
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let (inner, _) := unwrapRunLhs lhs
  if inner.isAppOfArity ``runJvmValFast 5 || inner.isAppOfArity ``runJvmResFast 5 then
    let instrs ← Lean.Meta.whnf (inner.getArg! 3)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr := instrs.getArg! 1
      let br ← Lean.Meta.whnf (Lean.mkApp (Lean.mkConst ``isBranchInstr) instr)
      return br.isConstOf ``Bool.false
  return false

private def isRunJvmAtForwardGoto : Lean.Elab.Tactic.TacticM Bool := do
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let (inner, _) := unwrapRunLhs lhs
  if inner.isAppOfArity ``runJvmValFast 5 || inner.isAppOfArity ``runJvmResFast 5 then
    let instrs ← Lean.Meta.whnf (inner.getArg! 3)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr ← Lean.Meta.whnf (instrs.getArg! 1)
      if instr.isAppOfArity ``JvmInstr.goto 1 then
        if let (some pcVal, some tgtVal) := (← evalNatLit? (inner.getArg! 2), ← evalNatLit? (instr.getArg! 0)) then
          return pcVal < tgtVal
  return false

private theorem afterBlockChunk_cont (f pc : Nat) (is : List JvmInstr) (st : JvmState) (prog : List JvmInstr) :
    afterBlockChunk (.cont f pc is st) prog = runJvmValFast f prog pc is st := rfl

private theorem afterBlockChunk_jump (f pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (prog : List JvmInstr) :
    afterBlockChunk (.jump f ⟨pc, stk, locs, ar, u64, asc⟩) prog =
      runJvmValFast f prog pc (prog.drop pc) ⟨pc, stk, locs, ar, u64, asc⟩ := rfl

private theorem afterBlockChunk_done (res : Option JvmVal) (prog : List JvmInstr) :
    afterBlockChunk (.done res) prog = res := rfl

private theorem afterResBlockChunk_cont (f pc : Nat) (is : List JvmInstr) (st : JvmState) (prog : List JvmInstr) :
    afterResBlockChunk (.cont f pc is st) prog = runJvmResFast f prog pc is st := rfl

private theorem afterResBlockChunk_jump (f pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (prog : List JvmInstr) :
    afterResBlockChunk (.jump f ⟨pc, stk, locs, ar, u64, asc⟩) prog =
      runJvmResFast f prog pc (prog.drop pc) ⟨pc, stk, locs, ar, u64, asc⟩ := rfl

private theorem afterResBlockChunk_done (res : Option (JvmVal × JvmState)) (prog : List JvmInstr) :
    afterResBlockChunk (.done res) prog = res := rfl

private theorem option_map_some' {α β : Type} (f : α → β) (x : α) :
    Option.map f (some x) = some (f x) := rfl

private theorem option_map_none' {α β : Type} (f : α → β) :
    Option.map f none = none := rfl

private theorem evalBranchInstrCons_ifeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifeq target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if v.asI32 == 0 then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalBranchInstrCons_ifne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifne target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if !(v.asI32 == 0) then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalBranchInstrCons_iflt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.iflt target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if v.asI32.toBitVec.slt 0#32 then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalBranchInstrCons_ifle (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifle target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if v.asI32.toBitVec.sle 0#32 then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalBranchInstrCons_ifgt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifgt target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if (0#32).slt v.asI32.toBitVec then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalBranchInstrCons_ifge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifge target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if (0#32).sle v.asI32.toBitVec then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalBranchInstrCons_ifnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifnull target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if v.isNull then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalBranchInstrCons_ifnonnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.ifnonnull target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if !v.isNull then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalBranchInstrCons_if_icmpeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.if_icmpeq target) rest ⟨pc0, b :: a :: s, locs, ar, u64, asc⟩ =
      if a.asI32 == b.asI32 then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalBranchInstrCons_if_icmpne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.if_icmpne target) rest ⟨pc0, b :: a :: s, locs, ar, u64, asc⟩ =
      if !(a.asI32 == b.asI32) then runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalBranchInstrCons_if_icmplt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.if_icmplt target) rest ⟨pc0, b :: a :: s, locs, ar, u64, asc⟩ =
      if a.asI32.toBitVec.slt b.asI32.toBitVec then
        runJvmValFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalBranchInstrCons_goto (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalBranchInstrCons f1 prog pc (.goto target) rest ⟨pc0, stk, locs, ar, u64, asc⟩ =
      runJvmValFast f1 prog target (prog.drop target) ⟨target, stk, locs, ar, u64, asc⟩ := rfl

private theorem evalResBranchInstrCons_ifeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifeq target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if v.asI32 == 0 then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalResBranchInstrCons_ifne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifne target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if !(v.asI32 == 0) then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalResBranchInstrCons_iflt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.iflt target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if v.asI32.toBitVec.slt 0#32 then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalResBranchInstrCons_ifle (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifle target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if v.asI32.toBitVec.sle 0#32 then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalResBranchInstrCons_ifgt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifgt target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if (0#32).slt v.asI32.toBitVec then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalResBranchInstrCons_ifge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifge target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if (0#32).sle v.asI32.toBitVec then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalResBranchInstrCons_ifnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifnull target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if v.isNull then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalResBranchInstrCons_ifnonnull (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (v : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.ifnonnull target) rest ⟨pc0, v :: s, locs, ar, u64, asc⟩ =
      if !v.isNull then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalResBranchInstrCons_if_icmpeq (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.if_icmpeq target) rest ⟨pc0, b :: a :: s, locs, ar, u64, asc⟩ =
      if a.asI32 == b.asI32 then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalResBranchInstrCons_if_icmpne (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.if_icmpne target) rest ⟨pc0, b :: a :: s, locs, ar, u64, asc⟩ =
      if !(a.asI32 == b.asI32) then runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalResBranchInstrCons_if_icmplt (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : JvmVal) (s : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.if_icmplt target) rest ⟨pc0, b :: a :: s, locs, ar, u64, asc⟩ =
      if a.asI32.toBitVec.slt b.asI32.toBitVec then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, ar, u64, asc⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, ar, u64, asc⟩ := rfl

private theorem evalResBranchInstrCons_goto (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.goto target) rest ⟨pc0, stk, locs, ar, u64, asc⟩ =
      runJvmResFast f1 prog target (prog.drop target) ⟨target, stk, locs, ar, u64, asc⟩ := rfl

private def rwEvalBranchByInstr (isRes : Bool) (instr : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  let some n := instr.consumeMData.getAppFn.constName? | return ()
  let thm : Option Lean.Name :=
    if !isRes then
      if n == ``JvmInstr.ifeq then some ``evalBranchInstrCons_ifeq
      else if n == ``JvmInstr.ifne then some ``evalBranchInstrCons_ifne
      else if n == ``JvmInstr.iflt then some ``evalBranchInstrCons_iflt
      else if n == ``JvmInstr.ifle then some ``evalBranchInstrCons_ifle
      else if n == ``JvmInstr.ifgt then some ``evalBranchInstrCons_ifgt
      else if n == ``JvmInstr.ifge then some ``evalBranchInstrCons_ifge
      else if n == ``JvmInstr.ifnull then some ``evalBranchInstrCons_ifnull
      else if n == ``JvmInstr.ifnonnull then some ``evalBranchInstrCons_ifnonnull
      else if n == ``JvmInstr.if_icmpeq then some ``evalBranchInstrCons_if_icmpeq
      else if n == ``JvmInstr.if_icmpne then some ``evalBranchInstrCons_if_icmpne
      else if n == ``JvmInstr.if_icmplt then some ``evalBranchInstrCons_if_icmplt
      else if n == ``JvmInstr.goto then some ``evalBranchInstrCons_goto
      else none
    else
      if n == ``JvmInstr.ifeq then some ``evalResBranchInstrCons_ifeq
      else if n == ``JvmInstr.ifne then some ``evalResBranchInstrCons_ifne
      else if n == ``JvmInstr.iflt then some ``evalResBranchInstrCons_iflt
      else if n == ``JvmInstr.ifle then some ``evalResBranchInstrCons_ifle
      else if n == ``JvmInstr.ifgt then some ``evalResBranchInstrCons_ifgt
      else if n == ``JvmInstr.ifge then some ``evalResBranchInstrCons_ifge
      else if n == ``JvmInstr.ifnull then some ``evalResBranchInstrCons_ifnull
      else if n == ``JvmInstr.ifnonnull then some ``evalResBranchInstrCons_ifnonnull
      else if n == ``JvmInstr.if_icmpeq then some ``evalResBranchInstrCons_if_icmpeq
      else if n == ``JvmInstr.if_icmpne then some ``evalResBranchInstrCons_if_icmpne
      else if n == ``JvmInstr.if_icmplt then some ``evalResBranchInstrCons_if_icmplt
      else if n == ``JvmInstr.goto then some ``evalResBranchInstrCons_goto
      else none
  if let some tn := thm then
    let id := Lean.mkIdent tn
    Lean.Elab.Tactic.evalTactic (← `(tactic| try rw [$id:ident]))

private def rwOptionMapResult : Lean.Elab.Tactic.TacticM Unit := do
  let tgt ← Lean.Elab.Tactic.getMainTarget
  let some (_, lhs, _) := tgt.consumeMData.eq? | return ()
  let lhs := lhs.consumeMData
  if lhs.isAppOfArity ``Option.map 4 then
    let arg := lhs.appArg!.consumeMData
    if arg.isAppOfArity ``Option.some 2 then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; rw [option_map_some'])))
    else if arg.isAppOfArity ``Option.none 1 then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; rw [option_map_none'])))

elab "jvm_step_one_chunk" : tactic => do
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let (inner, isMap) := unwrapRunLhs lhs
  let isRes := inner.isAppOfArity ``runJvmResFast 5
  if isRes then
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_stepBlockChunk 40]))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_stepBlockChunk 40]))
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    if isMap then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 2; arg 1; jvm_whnf_blk)))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 1; jvm_whnf_blk)))
    let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | return ()
    let (afterApp, _) := unwrapRunLhs lhs2
    let chunkRes := (afterApp.getArg! 0).consumeMData
    if let some cn := chunkRes.getAppFn.constName? then
      if !isRes then
        if cn == ``BlockChunkRes.cont then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_cont]))
        else if cn == ``BlockChunkRes.jump then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_jump]))
        else if cn == ``BlockChunkRes.done then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_done]))
      else
        if cn == ``BlockResChunkRes.cont then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_cont]))
        else if cn == ``BlockResChunkRes.jump then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_jump]))
        else if cn == ``BlockResChunkRes.done then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_done]))
          rwOptionMapResult
    if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals)))
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; jvm_whnf_run_args)))

private theorem ite_bool_eq_true_left {α : Type} {b : Bool} (h : b = true) (t e : α) :
    (if b = true then t else e) = t := by subst h; rfl

private theorem ite_bool_eq_true_right {α : Type} {b : Bool} (h : b = false) (t e : α) :
    (if b = true then t else e) = e := by subst h; rfl

elab "reduce_top_mc_ite" : tactic => Lean.Elab.Tactic.withMainContext do
  let tgt ← Lean.Elab.Tactic.getMainTarget
  let some (_, lhs, rhs) := tgt.eq? | return ()
  let lhs := lhs.consumeMData
  let (hasMap, mapFn, mapArgs, iteExpr) :=
    if lhs.isAppOfArity ``Option.map 4 then
      (true, lhs.getAppFn, lhs.getAppArgs, lhs.appArg!.consumeMData)
    else
      (false, lhs, #[], lhs)
  if !iteExpr.isAppOfArity ``ite 5 then return ()
  let args := iteExpr.getAppArgs
  let cond := args[1]!.consumeMData
  if !cond.isAppOfArity ``Eq 3 then return ()
  let b := cond.getArg! 1
  let eqTrue ← Lean.Meta.mkEq b (Lean.mkConst ``Bool.true)
  let eqFalse ← Lean.Meta.mkEq b (Lean.mkConst ``Bool.false)
  let saved ← Lean.Elab.Tactic.getGoals
  let g ← Lean.Elab.Tactic.getMainGoal
  let tryClose (goalTy : Lean.Expr) (thmName : Lean.Name) (branchExpr : Lean.Expr) :
      Lean.Elab.Tactic.TacticM Bool := do
    let mvar ← Lean.Meta.mkFreshExprMVar goalTy
    Lean.Elab.Tactic.setGoals [mvar.mvarId!]
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        simp only [checkInstanceOf_level4_level4, checkInstanceOf_level4_cell,
          checkInstanceOf_cell_level4, checkInstanceOf_cell_cell,
          ui32_beq_0_0, ui32_beq_1_0, eq_self_iff_true,
          Bool.not_true, Bool.not_false, Bool.false_eq_true, beq_self_eq_true, ite_true, ite_false]))
    catch _ =>
      Lean.Elab.Tactic.setGoals saved
      return false
    let rem ← Lean.Elab.Tactic.getUnsolvedGoals
    if rem.isEmpty then
      let pf ← Lean.instantiateMVars mvar
      let stepEq := Lean.mkAppN (Lean.mkConst thmName) #[args[0]!, b, pf, args[3]!, args[4]!]
      let fullEq ←
        if hasMap then
          let fn := Lean.mkApp3 mapFn mapArgs[0]! mapArgs[1]! mapArgs[2]!
          Lean.Meta.mkCongrArg fn stepEq
        else
          pure stepEq
      let newLhs :=
        if hasMap then
          Lean.mkAppN mapFn #[mapArgs[0]!, mapArgs[1]!, mapArgs[2]!, branchExpr]
        else branchExpr
      let newTgt ← Lean.Meta.mkEq newLhs rhs
      let newMvar ← Lean.Meta.mkFreshExprMVar newTgt
      g.assign (← Lean.Meta.mkEqTrans fullEq newMvar)
      Lean.Elab.Tactic.setGoals (newMvar.mvarId! :: saved.tail!)
      return true
    Lean.Elab.Tactic.setGoals saved
    return false
  if ← tryClose eqTrue ``ite_bool_eq_true_left args[3]! then return ()
  let _ ← tryClose eqFalse ``ite_bool_eq_true_right args[4]!

elab "jvm_step_nonbranch_chunks" : tactic => do
  for _ in [:40] do
    if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then break
    if ← isRunJvmAtNonBranch then
      Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_one_chunk))
    else if ← isRunJvmAtForwardGoto then
      let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      let some (_, lhs, _) := tgt.eq? | break
      let (inner, isMap) := unwrapRunLhs lhs
      let isRes := inner.isAppOfArity ``runJvmResFast 5
      if isRes then
        Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_at_branch_cons (hbr := rfl)]))
      else
        Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_at_branch_cons (hbr := rfl)]))
      if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
        if isMap then
          Lean.Elab.Tactic.evalTactic (← `(tactic| (
            (conv => lhs; arg 2; arg 1; whnf)
            (conv => lhs; arg 2; arg 3; whnf)
            (conv => lhs; arg 2; arg 4; whnf)
            (conv => lhs; arg 2; arg 6; jvm_whnf_blk))))
          let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
          let some (_, lhs2, _) := tgt2.eq? | break
          let (evalApp, _) := unwrapRunLhs lhs2
          rwEvalBranchByInstr isRes (evalApp.getArg! 3)
          if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
            Lean.Elab.Tactic.evalTactic (← `(tactic| (
              (conv => lhs; try rw [option_map_ite])
              (conv => lhs; norm_jvm_locals; jvm_whnf_run_args))))
        else
          Lean.Elab.Tactic.evalTactic (← `(tactic| (
            (conv => lhs; arg 1; whnf)
            (conv => lhs; arg 3; whnf)
            (conv => lhs; arg 4; whnf)
            (conv => lhs; arg 6; jvm_whnf_blk))))
          let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
          let some (_, lhs2, _) := tgt2.eq? | break
          rwEvalBranchByInstr isRes (lhs2.getArg! 3)
          if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
            Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)))
    else
      break

elab "jvm_step_branch_tail" : tactic => do
  if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then return ()
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let (inner, isMap) := unwrapRunLhs lhs
  let isRes := inner.isAppOfArity ``runJvmResFast 5
  let isVal := inner.isAppOfArity ``runJvmValFast 5
  if !isRes && !isVal then return ()
  try
    if isRes then
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_at_branch_cons (hbr := rfl)]))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_at_branch_cons (hbr := rfl)]))
  catch _ =>
    return ()
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    if isMap then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 2; arg 1; whnf)
        (conv => lhs; arg 2; arg 3; whnf)
        (conv => lhs; arg 2; arg 4; whnf)
        (conv => lhs; arg 2; arg 6; jvm_whnf_blk))))
      let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      let some (_, lhs2, _) := tgt2.eq? | return ()
      let (evalApp, _) := unwrapRunLhs lhs2
      rwEvalBranchByInstr isRes (evalApp.getArg! 3)
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 2; norm_jvm_locals)
        (conv => lhs; try rw [option_map_ite])
        reduce_top_mc_ite)))
      rwOptionMapResult
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; jvm_whnf_run_args)))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; arg 1; whnf)
        (conv => lhs; arg 3; whnf)
        (conv => lhs; arg 4; whnf)
        (conv => lhs; arg 6; jvm_whnf_blk))))
      let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      let some (_, lhs2, _) := tgt2.eq? | return ()
      rwEvalBranchByInstr isRes (lhs2.getArg! 3)
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; norm_jvm_locals)
        reduce_top_mc_ite
        (conv => lhs; jvm_whnf_run_args))))

elab "jvm_step_blk0" _prog:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_nonbranch_chunks))
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_branch_tail))

elab "jvm_step_blk" _prog:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_nonbranch_chunks))
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_branch_tail))

/-! ### Batch 1: Straight-line methods -/

theorem getNEXT_GEN_4X4_LUT_annotations_equiv :
    runJvmRes 5 getNEXT_GEN_4X4_LUT_annotations_prog (initJvmState []) = some (.unit, initJvmState []) := by rfl

theorem exportComputeNextGen4x4BitwiseUInt_equiv (w : UInt32) :
    runJvm 10 f_Algorithm_exportComputeNextGen4x4BitwiseUInt_prog (initJvmState [(0, .i32 w)]) =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt w)) := by rfl

theorem exportComputeLeafNextGen8x8BranchUInt_equiv (w : UInt64) :
    runJvm 10 f_Algorithm_exportComputeLeafNextGen8x8BranchUInt_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (Algorithm.computeLeafNextGen8x8BranchUInt w)) := by rfl

theorem flatHashLifeArena_setRemapL4_equiv (arena : Algorithm.FlatHashLifeArena) (idx val : UInt32) :
    runJvmRes 15 f_Algorithm_FlatHashLifeArena_setRemapL4_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 idx), (2, .i32 val)] [arena]) =
      some (.unit, { (initJvmState [(0, .arenaRef 0), (1, .i32 idx), (2, .i32 val)] [arena]) with
        pc := 10, arenas := [arena.setRemapL4 idx val],
        locals := setLocal (initJvmState [(0, .arenaRef 0), (1, .i32 idx), (2, .i32 val)] [arena]).locals 3 (.arenaU32Ref 0 .remapL4) }) := by rfl

theorem flatHashLifeArena_setRemapCell_equiv (arena : Algorithm.FlatHashLifeArena) (idx val : UInt32) :
    runJvmRes 15 f_Algorithm_FlatHashLifeArena_setRemapCell_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 idx), (2, .i32 val)] [arena]) =
      some (.unit, { (initJvmState [(0, .arenaRef 0), (1, .i32 idx), (2, .i32 val)] [arena]) with
        pc := 10, arenas := [arena.setRemapCell idx val],
        locals := setLocal (initJvmState [(0, .arenaRef 0), (1, .i32 idx), (2, .i32 val)] [arena]).locals 3 (.arenaU32Ref 0 .remapCell) }) := by rfl

theorem flatHashLifeArena_setCellStepRes_equiv (arena : Algorithm.FlatHashLifeArena) (idx val : UInt32) :
    runJvmRes 15 f_Algorithm_FlatHashLifeArena_setCellStepRes_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 idx), (2, .i32 val)] [arena]) =
      some (.unit, { (initJvmState [(0, .arenaRef 0), (1, .i32 idx), (2, .i32 val)] [arena]) with
        pc := 10, arenas := [arena.setCellStepRes idx val],
        locals := setLocal (initJvmState [(0, .arenaRef 0), (1, .i32 idx), (2, .i32 val)] [arena]).locals 3 (.arenaU32Ref 0 .cellStepRes) }) := by rfl

theorem flatHashLifeArena_setL4StepRes_equiv (arena : Algorithm.FlatHashLifeArena) (idx : UInt32) (val : UInt64) :
    runJvmRes 25 f_Algorithm_FlatHashLifeArena_setL4StepRes_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 idx), (2, .i64 val)] [arena]) =
      some (.unit, { (initJvmState [(0, .arenaRef 0), (1, .i32 idx), (2, .i64 val)] [arena]) with
        pc := 17, arenas := [arena.setL4StepRes idx val],
        locals := setLocal (setLocal (initJvmState [(0, .arenaRef 0), (1, .i32 idx), (2, .i64 val)] [arena]).locals 4 (.arenaU64Ref 0 .l4StepRes)) 5 (.arenaU8Ref 0 .l4HasRes) }) := by rfl

theorem flatHashLifeArena_setOverflow_equiv (arena : Algorithm.FlatHashLifeArena) :
    runJvmRes 15 f_Algorithm_FlatHashLifeArena_setOverflow_prog (initJvmState [(0, .arenaRef 0)] [arena]) =
      some (.unit, { (initJvmState [(0, .arenaRef 0)] [arena]) with pc := 6, arenas := [arena.setOverflow] }) := by rfl

theorem flatHashLifeArena_clearOverflow_equiv (arena : Algorithm.FlatHashLifeArena) :
    runJvmRes 15 f_Algorithm_FlatHashLifeArena_clearOverflow_prog (initJvmState [(0, .arenaRef 0)] [arena]) =
      some (.unit, { (initJvmState [(0, .arenaRef 0)] [arena]) with pc := 6, arenas := [arena.clearOverflow] }) := by rfl

theorem flatHashLifeArena_compactRootFrom_closed0_equiv :
    runJvm 15 f_Algorithm_FlatHashLifeArena_compactRootFrom___closed__0_prog (initJvmState []) =
      some (.pair (.boxedUInt 4294967295) (.boxedUByte 0)) := by rfl

theorem leafChunkKey_equiv (x0 y0 : Int64) (k : UInt32) :
    runJvm 45 f_Algorithm_leafChunkKey_prog
      (initJvmState [(0, .i64 x0.toUInt64), (2, .i64 y0.toUInt64), (4, .i32 k)]) =
      some (.i64 (Algorithm.leafChunkKey x0 y0 k)) := by
  apply runJvm_of_stepListAt f_Algorithm_leafChunkKey_prog f_Algorithm_leafChunkKey_prog 45 _ _ rfl
    (by change f_Algorithm_leafChunkKey_prog.length ≤ 45; decide)
  have heval : stepListAt 0 f_Algorithm_leafChunkKey_prog
      (initJvmState [(0, .i64 x0.toUInt64), (2, .i64 y0.toUInt64), (4, .i32 k)]) =
      some (.i64 (((x0.toUInt64 + (({ toBitVec := BitVec.signExtend 64 (k &&& 7).toBitVec } : UInt64) &&& 4294967295)) + 2147483648) <<< 32 +
        ((y0.toUInt64 + (({ toBitVec := BitVec.signExtend 64 (k >>> 3).toBitVec } : UInt64) &&& 4294967295)) + 2147483648))) := by rfl
  exact heval.trans (by rw [signExtend_and_mask, signExtend_and_mask]; rfl)

theorem cellCursorDone_equiv (fs : List Algorithm.CellFrame) :
    runJvm 10 f_Algorithm_cellCursorDone_prog (initJvmState [(0, .cellFrames fs)]) =
      some (.i32 (if Algorithm.cellCursorDone fs then 1 else 0)) := by rfl

theorem cellsToMacroCell_closed0_equiv :
    runJvm 10 f_Algorithm_cellsToMacroCell___closed__0_prog (initJvmState []) =
      some (.mc (Algorithm.emptyAtHeight 1)) := by rfl

theorem cellsToMacroCell_closed1_equiv :
    runJvm 15 f_Algorithm_cellsToMacroCell___closed__1_prog (initJvmState []) =
      some (.pair (.boxedULong 2147483648) (.mc (Algorithm.emptyAtHeight 1))) := by rfl

theorem cellsToMacroCell_closed2_equiv :
    runJvm 15 f_Algorithm_cellsToMacroCell___closed__2_prog (initJvmState []) =
      some (.pair (.boxedULong 2147483648) (.pair (.boxedULong 2147483648) (.mc (Algorithm.emptyAtHeight 1)))) := by rfl

theorem makeLevel4Node_equiv (nw ne sw se : UInt64) :
    runJvm 25 f_Algorithm_makeLevel4Node_prog
      (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)]) =
      some (.mc (Algorithm.makeLevel4Node nw ne sw se)) := by rfl

theorem makeCellNode_equiv (nw ne sw se : Algorithm.MacroCell) :
    runJvm 60 f_Algorithm_makeCellNode_prog
      (initJvmState [(0, .mc nw), (1, .mc ne), (2, .mc sw), (3, .mc se)]) =
      some (.mc (Algorithm.makeCellNode nw ne sw se)) := by rfl

theorem access_level4Hash_equiv (nw ne sw se : UInt64) :
    runJvm 15 access_f_Algorithm_level4Hash_prog
      (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)]) =
      some (.i32 (Algorithm.level4Hash nw ne sw se)) := by rfl

theorem access_cellNodeHash_equiv (l nw ne sw se : UInt32) :
    runJvm 15 access_f_Algorithm_cellNodeHash_prog
      (initJvmState [(0, .i32 l), (1, .i32 nw), (2, .i32 ne), (3, .i32 sw), (4, .i32 se)]) =
      some (.i32 (Algorithm.cellNodeHash l nw ne sw se)) := by rfl

theorem serializeLife105Block_equiv (cells : Array UInt64) (minX minY maxY : Int32) :
    runJvm 70 f_Algorithm_serializeLife105Block_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 minX.toUInt32), (2, .i32 minY.toUInt32), (3, .i32 maxY.toUInt32)] [] [cells]) =
      some (.strArr (Algorithm.serializeLife105Block cells minX minY maxY)) := by rfl

theorem serializeLife105_equiv (cells : Array UInt64) :
    runJvm 50 f_Algorithm_serializeLife105_prog
      (initJvmState [(0, .u64Ref 0)] [] [cells]) =
      some (.strArr (Algorithm.serializeLife105 cells)) := by rfl

private theorem u64buf_toArray_of_prog (prog : List JvmInstr)
    (hprog : prog = f_Algorithm_U64Buf_toArray_prog)
    (arr : Array UInt64) (h1 : 1 ≤ arr.size) (h2 : arr.size < 2 ^ 31)
    (h3 : arr[0]!.toUInt32.toNat + 1 ≤ arr.size) :
    runJvmRes 35 prog (initJvmState [(0, .u64Ref 0)] [] [arr]) =
      some (.u64Ref 1, { (initJvmState [(0, .u64Ref 0)] [] [arr]) with
        pc := 24, stack := [.u64Ref 1], u64Arrays := [arr, Algorithm.U64Buf.toArray arr] }) := by
  subst hprog
  have hs : arr.size.toUInt32.toNat = arr.size := Nat.mod_eq_of_lt (by omega)
  have hc1 : coerceInI32 1 0 arr.size.toUInt32 = 1 := by
    apply coerceInI32_of_le <;> simp [hs] <;> omega
  have h01 : (arr[0]!.toUInt32 + 1).toNat = arr[0]!.toUInt32.toNat + 1 := by
    rw [UInt32.toNat_add]; simp only [UInt32.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  have hc2 : coerceInI32 (arr[0]!.toUInt32 + 1) 1 arr.size.toUInt32 = arr[0]!.toUInt32 + 1 := by
    apply coerceInI32_of_le
    · rw [UInt32.toNat_one, h01]; omega
    · rw [h01, hs]; omega
    · rw [hs]; omega
  have heval : runJvmRes 35 f_Algorithm_U64Buf_toArray_prog (initJvmState [(0, .u64Ref 0)] [] [arr]) =
      some (.u64Ref 1, { (initJvmState [(0, .u64Ref 0)] [] [arr]) with
        pc := 24, stack := [.u64Ref 1],
        u64Arrays := [arr, arr.extract (coerceInI32 1 0 arr.size.toUInt32).toNat
          (coerceInI32 (arr[0]!.toUInt32 + 1) (coerceInI32 1 0 arr.size.toUInt32) arr.size.toUInt32).toNat] }) := by rfl
  rw [heval, hc1, hc2, UInt32.toNat_one]
  rfl

theorem u64Buf_toArray_equiv (arr : Array UInt64) (h1 : 1 ≤ arr.size) (h2 : arr.size < 2 ^ 31)
    (h3 : arr[0]!.toUInt32.toNat + 1 ≤ arr.size) :
    runJvmRes 35 f_Algorithm_U64Buf_toArray_prog (initJvmState [(0, .u64Ref 0)] [] [arr]) =
      some (.u64Ref 1, { (initJvmState [(0, .u64Ref 0)] [] [arr]) with
        pc := 24, stack := [.u64Ref 1], u64Arrays := [arr, Algorithm.U64Buf.toArray arr] }) :=
  u64buf_toArray_of_prog f_Algorithm_U64Buf_toArray_prog rfl arr h1 h2 h3

theorem u64Buf_toArray_1_equiv (arr : Array UInt64) (h1 : 1 ≤ arr.size) (h2 : arr.size < 2 ^ 31)
    (h3 : arr[0]!.toUInt32.toNat + 1 ≤ arr.size) :
    runJvmRes 35 f_Algorithm_U64Buf_toArray_1_prog (initJvmState [(0, .u64Ref 0)] [] [arr]) =
      some (.u64Ref 1, { (initJvmState [(0, .u64Ref 0)] [] [arr]) with
        pc := 24, stack := [.u64Ref 1], u64Arrays := [arr, Algorithm.U64Buf.toArray arr] }) :=
  u64buf_toArray_of_prog f_Algorithm_U64Buf_toArray_1_prog rfl arr h1 h2 h3

theorem u64Buf_toArray_2_equiv (arr : Array UInt64) (h1 : 1 ≤ arr.size) (h2 : arr.size < 2 ^ 31)
    (h3 : arr[0]!.toUInt32.toNat + 1 ≤ arr.size) :
    runJvmRes 35 f_Algorithm_U64Buf_toArray_2_prog (initJvmState [(0, .u64Ref 0)] [] [arr]) =
      some (.u64Ref 1, { (initJvmState [(0, .u64Ref 0)] [] [arr]) with
        pc := 24, stack := [.u64Ref 1], u64Arrays := [arr, Algorithm.U64Buf.toArray arr] }) :=
  u64buf_toArray_of_prog f_Algorithm_U64Buf_toArray_2_prog rfl arr h1 h2 h3

theorem u64Buf_toArray_3_equiv (arr : Array UInt64) (h1 : 1 ≤ arr.size) (h2 : arr.size < 2 ^ 31)
    (h3 : arr[0]!.toUInt32.toNat + 1 ≤ arr.size) :
    runJvmRes 35 f_Algorithm_U64Buf_toArray_3_prog (initJvmState [(0, .u64Ref 0)] [] [arr]) =
      some (.u64Ref 1, { (initJvmState [(0, .u64Ref 0)] [] [arr]) with
        pc := 24, stack := [.u64Ref 1], u64Arrays := [arr, Algorithm.U64Buf.toArray arr] }) :=
  u64buf_toArray_of_prog f_Algorithm_U64Buf_toArray_3_prog rfl arr h1 h2 h3

theorem noCells_equiv :
    runJvmRes 10 f_Algorithm_noCells_prog (initJvmState []) =
      some (.u64Ref 0, { (initJvmState []) with pc := 2, stack := [.u64Ref 0], u64Arrays := [Algorithm.noCells] }) := by rfl

theorem noCells_1_equiv :
    runJvmRes 10 f_Algorithm_noCells_1_prog (initJvmState []) =
      some (.u64Ref 0, { (initJvmState []) with pc := 2, stack := [.u64Ref 0], u64Arrays := [Algorithm.noCells] }) := by rfl

theorem noCells_2_equiv :
    runJvmRes 10 f_Algorithm_noCells_2_prog (initJvmState []) =
      some (.u64Ref 0, { (initJvmState []) with pc := 2, stack := [.u64Ref 0], u64Arrays := [Algorithm.noCells] }) := by rfl

theorem u64Buf_empty_equiv :
    runJvmRes 10 f_Algorithm_U64Buf_empty_prog (initJvmState []) =
      some (.u64Ref 0, { (initJvmState []) with pc := 2, stack := [.u64Ref 0], u64Arrays := [Algorithm.U64Buf.empty] }) := by rfl

theorem u64Buf_empty_1_equiv :
    runJvmRes 10 f_Algorithm_U64Buf_empty_1_prog (initJvmState []) =
      some (.u64Ref 0, { (initJvmState []) with pc := 2, stack := [.u64Ref 0], u64Arrays := [Algorithm.U64Buf.empty] }) := by rfl

theorem u64Buf_empty_2_equiv :
    runJvmRes 10 f_Algorithm_U64Buf_empty_2_prog (initJvmState []) =
      some (.u64Ref 0, { (initJvmState []) with pc := 2, stack := [.u64Ref 0], u64Arrays := [Algorithm.U64Buf.empty] }) := by rfl

theorem u64Buf_empty_3_equiv :
    runJvmRes 10 f_Algorithm_U64Buf_empty_3_prog (initJvmState []) =
      some (.u64Ref 0, { (initJvmState []) with pc := 2, stack := [.u64Ref 0], u64Arrays := [Algorithm.U64Buf.empty] }) := by rfl

theorem u64Buf_empty_4_equiv :
    runJvmRes 10 f_Algorithm_U64Buf_empty_4_prog (initJvmState []) =
      some (.u64Ref 0, { (initJvmState []) with pc := 2, stack := [.u64Ref 0], u64Arrays := [Algorithm.U64Buf.empty] }) := by rfl

theorem uint32ToInt32_equiv (x : UInt32) :
    runJvm 10 f_Algorithm_uint32ToInt32_prog (initJvmState [(0, .i32 x)]) =
      some (.i32 (Algorithm.uint32ToInt32 x).toUInt32) := by rfl

theorem uint32ToInt32_1_equiv (x : UInt32) :
    runJvm 10 f_Algorithm_uint32ToInt32_1_prog (initJvmState [(0, .i32 x)]) =
      some (.i32 (Algorithm.uint32ToInt32 x).toUInt32) := by rfl

theorem uint32ToInt32_2_equiv (x : UInt32) :
    runJvm 10 f_Algorithm_uint32ToInt32_2_prog (initJvmState [(0, .i32 x)]) =
      some (.i32 (Algorithm.uint32ToInt32 x).toUInt32) := by rfl

theorem serializeLife106_equiv (cells : Array UInt64) :
    runJvm 40 f_Algorithm_serializeLife106_prog (initJvmState [(0, .u64Ref 0)] [] [cells]) =
      some (.strArr (Algorithm.serializeLife106 cells)) := by rfl

theorem cellToLeafBit_1_equiv (x y : UInt32) :
    runJvm 60 f_Algorithm_cellToLeafBitUInt_1_prog (initJvmState [(0, .i32 x), (1, .i32 y)]) =
      some (.i32 (Algorithm.cellToLeafBitUInt x y)) := by
  exact cellToLeafBit_equiv x y

theorem cellNodeHash_1_equiv (l qnw qne qsw qse : UInt32) :
    runJvm 70 f_Algorithm_cellNodeHash_1_prog
      (initJvmState [(0, .i32 l), (1, .i32 qnw), (2, .i32 qne), (3, .i32 qsw), (4, .i32 qse)]) =
      some (.i32 (Algorithm.cellNodeHash l qnw qne qsw qse)) := by
  exact cellNodeHash_equiv l qnw qne qsw qse

theorem level4Hash_1_equiv (nw ne sw se : UInt64) :
    runJvm 75 f_Algorithm_level4Hash_1_prog
      (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)]) =
      some (.i32 (Algorithm.level4Hash nw ne sw se)) := by
  exact level4Hash_equiv nw ne sw se

theorem macroCell_level_equiv (m : Algorithm.MacroCell) :
    runJvm 15 f_Algorithm_MacroCell_level_prog (initJvmState [(0, .mc m)]) =
      some (.i32 m.level) := by rfl

theorem macroCell_cellHashCode_equiv (m : Algorithm.MacroCell) :
    runJvm 15 f_Algorithm_MacroCell_cellHashCode_prog (initJvmState [(0, .mc m)]) =
      some (.i32 m.cellHashCode) := by rfl

theorem makeLevel4Node_1_equiv (nw ne sw se : UInt64) :
    runJvm 25 f_Algorithm_makeLevel4Node_1_prog
      (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)]) =
      some (.mc (Algorithm.makeLevel4Node nw ne sw se)) := by rfl

theorem makeCellNode_1_equiv (nw ne sw se : Algorithm.MacroCell) :
    runJvm 70 f_Algorithm_makeCellNode_1_prog
      (initJvmState [(0, .mc nw), (1, .mc ne), (2, .mc sw), (3, .mc se)]) =
      some (.mc (Algorithm.makeCellNode nw ne sw se)) := by rfl

theorem macroCell_size_equiv (m : Algorithm.MacroCell) :
    runJvm 15 f_Algorithm_MacroCell_size_prog (initJvmState [(0, .mc m)]) =
      some (.i64 m.size) := by rfl

theorem macroCell_hashCode_equiv (m : Algorithm.MacroCell) :
    runJvm 15 f_Algorithm_MacroCell_hashCode_prog (initJvmState [(0, .mc m)]) =
      some (.i32 m.cellHashCode) := by rfl

theorem emptyLevel4_closed0_equiv :
    runJvm 15 f_Algorithm_emptyLevel4___closed__0_prog (initJvmState []) =
      some (.mc Algorithm.emptyLevel4) := by rfl

theorem emptyLevel4_equiv :
    runJvm 15 f_Algorithm_emptyLevel4_prog (initJvmState []) =
      some (.mc Algorithm.emptyLevel4) := by rfl

theorem centeredSubSubnodeFast_equiv (m : Algorithm.MacroCell) :
    runJvm 15 f_Algorithm_centeredSubSubnode_prog (initJvmState [(0, .mc m)]) =
      some (.mc (Algorithm.centeredSubSubnodeFast m)) := by rfl

theorem centeredSubSubnode_equiv (m : Algorithm.MacroCell) (d : Nat) (hm : Algorithm.WFd m d) (h5 : 5 ≤ d) :
    runJvm 15 f_Algorithm_centeredSubSubnode_prog (initJvmState [(0, .mc m)]) =
      some (.mc (Algorithm.centeredSubSubnode m)) := by
  rw [centeredSubSubnodeFast_equiv m, Algorithm.centeredSubSubnodeFast_eq_centeredSubSubnode_Impl hm h5]

theorem centeredSubSubnodeSizeFast_equiv (m : Algorithm.MacroCell) :
    runJvm 15 f_Algorithm_centeredSubSubnodeSize_prog (initJvmState [(0, .mc m)]) =
      some (.i64 (Algorithm.centeredSubSubnodeSizeFast m)) := by rfl

theorem centeredSubSubnodeSize_equiv (m : Algorithm.MacroCell) (d : Nat) (hm : Algorithm.WFd m d) (h5 : 5 ≤ d) :
    runJvm 15 f_Algorithm_centeredSubSubnodeSize_prog (initJvmState [(0, .mc m)]) =
      some (.i64 (Algorithm.centeredSubSubnodeSize m)) := by
  rw [centeredSubSubnodeSizeFast_equiv m, Algorithm.centeredSubSubnodeSizeFast_eq_centeredSubSubnodeSize_Impl hm h5]

theorem stepHashLifeStateWith_equiv (st : Algorithm.HashLifeStepState) (f : Algorithm.MacroCell → Algorithm.MacroCell) :
    runJvm 50 f_Algorithm_stepHashLifeStateWith_prog
      (initJvmState [(0, .hlState st), (1, .fnMcToMc f)]) =
      some (.hlState (Algorithm.stepHashLifeStateWith st f)) := by rfl

theorem computeGenerationStep_equiv (step : UInt32) (st : Algorithm.HashLifeStepState)
    (computedGenerations : UInt64) (macroKeep leafKeep : UInt32)
    (stepOneGen : Algorithm.HashLifeStepState → Algorithm.HashLifeStepState) :
    runJvm 45 f_Algorithm_computeGenerationStep_prog
      (initJvmState [(0, .i32 step), (1, .hlState st), (2, .i64 computedGenerations),
        (4, .i32 macroKeep), (5, .i32 leafKeep), (6, .fnHlToHl stepOneGen)]) =
      some (.stepBatch (Algorithm.computeGenerationStep step st computedGenerations macroKeep leafKeep stepOneGen)) := by
  change some (JvmVal.stepBatch _) = some (JvmVal.stepBatch _)
  congr 3
  dsimp [JvmVal.asI32, JvmVal.asI64, setLocal, initJvmState, List.foldl]
  rw [signExtend_and_mask]

theorem computeLevel4NextGen16x16UInt_equiv (nw ne sw se : UInt64) :
    runJvm 15 f_Algorithm_computeLevel4NextGen16x16UInt_prog
      (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)]) =
      some (.i64 (Algorithm.computeLevel4NextGen16x16UInt nw ne sw se)) := by rfl

theorem findLastLeafX_closed0_equiv :
    runJvm 10 f_Algorithm_findLastLeafX___closed__0_prog (initJvmState []) = some (.boxedUInt 0) := by rfl
theorem findLastLeafX_closed1_equiv :
    runJvm 10 f_Algorithm_findLastLeafX___closed__1_prog (initJvmState []) = some (.boxedUInt 1) := by rfl
theorem findLastLeafX_closed2_equiv :
    runJvm 10 f_Algorithm_findLastLeafX___closed__2_prog (initJvmState []) = some (.boxedUInt 2) := by rfl
theorem findLastLeafX_closed3_equiv :
    runJvm 10 f_Algorithm_findLastLeafX___closed__3_prog (initJvmState []) = some (.boxedUInt 3) := by rfl
theorem findLastLeafX_closed4_equiv :
    runJvm 10 f_Algorithm_findLastLeafX___closed__4_prog (initJvmState []) = some (.boxedUInt 4) := by rfl
theorem findLastLeafX_closed5_equiv :
    runJvm 10 f_Algorithm_findLastLeafX___closed__5_prog (initJvmState []) = some (.boxedUInt 5) := by rfl
theorem findLastLeafX_closed6_equiv :
    runJvm 10 f_Algorithm_findLastLeafX___closed__6_prog (initJvmState []) = some (.boxedUInt 6) := by rfl
theorem findLastLeafX_closed7_equiv :
    runJvm 10 f_Algorithm_findLastLeafX___closed__7_prog (initJvmState []) = some (.boxedUInt 7) := by rfl

theorem macrocellHeader_equiv :
    runJvm 10 f_Algorithm_macrocellHeader_prog (initJvmState []) = some (.str Algorithm.macrocellHeader) := by rfl

theorem emptyMacroCellUInt32_equiv (level : UInt32) :
    runJvm 20 f_Algorithm_emptyMacroCellUInt32_prog (initJvmState [(0, .i32 level)]) =
      some (.mc (Algorithm.emptyMacroCellUInt32 level)) := by rfl

theorem macrocellLeafChild_closed0_equiv :
    runJvm 10 f_Algorithm_macrocellLeafChild___closed__0_prog (initJvmState []) = some (.boxedULong 0) := by rfl

theorem serializePlaintextCells_equiv (cells : Array UInt64) :
    runJvm 45 f_Algorithm_serializePlaintextCells_prog (initJvmState [(0, .u64Ref 0)] [] [cells]) =
      some (.strArr (Algorithm.serializePlaintextCells cells)) := by rfl

theorem asciiStringLossy_equiv (bytes : ByteArray) (s e : UInt32) :
    runJvm 35 f_Algorithm_asciiStringLossy_prog
      (initJvmState [(0, .byteArr bytes), (1, .i32 s), (2, .i32 e)]) =
      some (.str (Algorithm.asciiStringLossy bytes s e)) := by rfl

theorem expandRuns_closed0_equiv :
    runJvm 15 f_Algorithm_expandRuns___closed__0_prog (initJvmState []) =
      some (.pair (.boxedUInt 0) (.boxedUInt 0)) := by rfl

theorem parseRLEData_closed0_equiv :
    runJvm 15 f_Algorithm_parseRLEData___closed__0_prog (initJvmState []) =
      some (.pair (.boxedUInt 0) (.boxedUInt 1)) := by rfl

theorem parseRLEComments_closed1_equiv :
    runJvm 15 f_Algorithm_parseRLEComments___closed__1_prog (initJvmState []) =
      some (.rleStatus (.invalidHeader "none")) := by rfl

theorem wrapRLEItems_closed0_equiv :
    runJvm 15 f_Algorithm_wrapRLEItems___closed__0_prog (initJvmState []) =
      some (.pair (.boxedUByte 0) (.boxedUInt 0)) := by rfl

theorem serializeRLE_closed0_equiv :
    runJvm 15 f_Algorithm_serializeRLE___closed__0_prog (initJvmState []) =
      some (.pair (.boxedUByte 33) (.boxedUInt 1)) := by rfl

theorem serializeRLECells_equiv (cells : Array UInt64) :
    runJvm 45 f_Algorithm_serializeRLECells_prog (initJvmState [(0, .u64Ref 0)] [] [cells]) =
      some (.strArr (Algorithm.serializeRLECells cells)) := by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem computeLevel4NextGen16x16WithUInt_spec0_equiv (nw ne sw se : UInt64) :
    runJvm 800 f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0_prog
      (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)]) =
      some (.i64 (Algorithm.computeLevel4NextGen16x16UInt nw ne sw se)) := by
  apply runJvm_of_stepListAtClean _ f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0_prog _ _ _ rfl (by decide)
  change stepListAtClean 0 f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0_prog
    (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)]) =
    some (.i64 (Algorithm.computeLevel4NextGen16x16UInt nw ne sw se))
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem computeLevel4NextGen16x16WithUInt_spec0_1_equiv (nw ne sw se : UInt64) :
    runJvm 800 f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0_1_prog
      (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)]) =
      some (.i64 (Algorithm.computeLevel4NextGen16x16UInt nw ne sw se)) := by
  apply runJvm_of_stepListAtClean _ f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0_1_prog _ _ _ rfl (by decide)
  change stepListAtClean 0 f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0_1_prog
    (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)]) =
    some (.i64 (Algorithm.computeLevel4NextGen16x16UInt nw ne sw se))
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem computeLevel4NextGen16x16WithUInt_equiv (nw ne sw se : UInt64) (fn : UInt64 → UInt32) :
    runJvm 800 f_Algorithm_computeLevel4NextGen16x16WithUInt_prog
      (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se), (8, .fnU64ToU32 fn)]) =
      some (.i64 (Algorithm.computeLevel4NextGen16x16WithUInt nw ne sw se fn)) := by
  apply runJvm_of_stepListAtClean _ f_Algorithm_computeLevel4NextGen16x16WithUInt_prog _ _ _ rfl (by decide)
  change stepListAtClean 0 f_Algorithm_computeLevel4NextGen16x16WithUInt_prog
    (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se), (8, .fnU64ToU32 fn)]) =
    some (.i64 (Algorithm.computeLevel4NextGen16x16WithUInt nw ne sw se fn))
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem stepLevel4NodeWith_spec0_equiv (nw ne sw se : UInt64) (fn : UInt64 → UInt32) :
    runJvm 800 f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_stepLevel4NodeWith_spec__0_prog
      (initJvmState [(0, .fnU64ToU32 fn), (1, .i64 nw), (3, .i64 ne), (5, .i64 sw), (7, .i64 se)]) =
      some (.i64 (Algorithm.computeLevel4NextGen16x16WithUInt nw ne sw se fn)) := by
  apply runJvm_of_stepListAtClean _ f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_stepLevel4NodeWith_spec__0_prog _ _ _ rfl (by decide)
  change stepListAtClean 0 f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_stepLevel4NodeWith_spec__0_prog
    (initJvmState [(0, .fnU64ToU32 fn), (1, .i64 nw), (3, .i64 ne), (5, .i64 sw), (7, .i64 se)]) =
    some (.i64 (Algorithm.computeLevel4NextGen16x16WithUInt nw ne sw se fn))
  rfl

/-! ### Batch 2: Forward-branching methods -/

@[simp] private theorem lcmp_bv_eq_zero (a b : UInt64) (hb : BitVec 64) :
    ((if a == b then (0 : UInt32) else if a.toBitVec.slt hb then 4294967295 else 1) == 0) = (a == b) := by
  by_cases h1 : a == b <;> by_cases h2 : a.toBitVec.slt hb <;> simp [h1, h2]

private theorem xor_allOnes_eq_not (x : UInt64) : x ^^^ 18446744073709551615 = ~~~x := by
  apply UInt64.toBitVec_inj.mp
  change (x.toBitVec ^^^ 18446744073709551615#64) = ~~~x.toBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_ofNat]
  by_cases hi : i < 64
  · have ht : Nat.testBit 18446744073709551615 i = true := by
      have h : (18446744073709551615 : Nat) = 2 ^ 64 - 1 := rfl
      rw [h, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hi
    simp [hi, ht]
  · simp [hi]

private theorem cellToLeafBitUInt_and_63 (x y : UInt32) :
    Algorithm.cellToLeafBitUInt x y &&& 63 = Algorithm.cellToLeafBitUInt x y := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [Algorithm.cellToLeafBitUInt, UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
    UInt32.toBitVec_ofNat, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ofNat]
  rcases Nat.lt_or_ge i 6 with hi | hi
  · have ht : Nat.testBit 63 i = true := by
      have h : (63 : Nat) = 2 ^ 6 - 1 := rfl
      rw [h, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hi
    have hi32 : i < 32 := by omega
    simp [hi32, ht]
  · have hf : Nat.testBit 63 i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hi))
    have hf1 : Nat.testBit 1 i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) hi))
    have hf1' : Nat.testBit 1 (i - 1) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (show 1 ≤ i - 1 by omega)))
    have hf2 : Nat.testBit 2 (i - 1) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (show 2 ≤ i - 1 by omega)))
    have hf2' : Nat.testBit 2 (i - 2) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (show 2 ≤ i - 2 by omega)))
    have hf4 : Nat.testBit 4 (i - 2) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (show 3 ≤ i - 2 by omega)))
    have hf4' : Nat.testBit 4 (i - 3) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (show 3 ≤ i - 3 by omega)))
    rcases Nat.lt_or_ge i 32 with h32 | h32
    · have ht1 : (1#32 : BitVec 32)[i - 1] = false := by
        rw [BitVec.getElem_eq_testBit_toNat]; simp [hf1']
      have ht2 : (2#32 : BitVec 32)[i - 1] = false := by
        rw [BitVec.getElem_eq_testBit_toNat]; simp [hf2]
      have ht2' : (2#32 : BitVec 32)[i - 2] = false := by
        rw [BitVec.getElem_eq_testBit_toNat]; simp [hf2']
      have ht4 : (4#32 : BitVec 32)[i - 2] = false := by
        rw [BitVec.getElem_eq_testBit_toNat]; simp [hf4]
      have ht4' : (4#32 : BitVec 32)[i - 3] = false := by
        rw [BitVec.getElem_eq_testBit_toNat]; simp [hf4']
      simp [hf, h32, hf1, ht1, ht2, ht2', ht4, ht4']
    · simp [show ¬(i < 32) by omega]

theorem computeLeafNextGen8x8BranchUInt_equiv (w : UInt64) :
    runJvm 15 f_Algorithm_computeLeafNextGen8x8BranchUInt_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (Algorithm.computeLeafNextGen8x8BranchUInt w)) := by
  apply runJvm_of_runJvmValFast0 15 _ _ _ rfl
  have heval : runJvmValFast 15 f_Algorithm_computeLeafNextGen8x8BranchUInt_prog 0
      f_Algorithm_computeLeafNextGen8x8BranchUInt_prog (initJvmState [(0, .i64 w)]) =
      (if ((if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0) = true then
        some (.i32 0) else some (.i32 (Algorithm.computeLeafNextGen8x8FastUInt w))) := rfl
  rw [heval, lcmp_bv_eq_zero]; unfold Algorithm.computeLeafNextGen8x8BranchUInt
  by_cases hw : w == 0 <;> simp [hw]

theorem computeLeafNextGen8x8BranchUInt_1_equiv (w : UInt64) :
    runJvm 15 f_Algorithm_computeLeafNextGen8x8BranchUInt_1_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (Algorithm.computeLeafNextGen8x8BranchUInt w)) := by
  apply runJvm_of_runJvmValFast0 15 _ _ _ rfl
  have heval : runJvmValFast 15 f_Algorithm_computeLeafNextGen8x8BranchUInt_1_prog 0
      f_Algorithm_computeLeafNextGen8x8BranchUInt_1_prog (initJvmState [(0, .i64 w)]) =
      (if ((if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0) = true then
        some (.i32 0) else some (.i32 (Algorithm.computeLeafNextGen8x8FastUInt w))) := rfl
  rw [heval, lcmp_bv_eq_zero]; unfold Algorithm.computeLeafNextGen8x8BranchUInt
  by_cases hw : w == 0 <;> simp [hw]

theorem computeLeafNextGen8x8BranchUInt_2_equiv (w : UInt64) :
    runJvm 15 f_Algorithm_computeLeafNextGen8x8BranchUInt_2_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (Algorithm.computeLeafNextGen8x8BranchUInt w)) := by
  apply runJvm_of_runJvmValFast0 15 _ _ _ rfl
  have heval : runJvmValFast 15 f_Algorithm_computeLeafNextGen8x8BranchUInt_2_prog 0
      f_Algorithm_computeLeafNextGen8x8BranchUInt_2_prog (initJvmState [(0, .i64 w)]) =
      (if ((if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0) = true then
        some (.i32 0) else some (.i32 (Algorithm.computeLeafNextGen8x8FastUInt w))) := rfl
  rw [heval, lcmp_bv_eq_zero]; unfold Algorithm.computeLeafNextGen8x8BranchUInt
  by_cases hw : w == 0 <;> simp [hw]

theorem leafContains_1_equiv (leaf : UInt64) (x y : UInt32) :
    runJvm 25 f_Algorithm_leafContains_1_prog (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y)]) =
      some (.i32 (if Algorithm.leafContains leaf x y then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 25 _ _ _ rfl
  have heval : runJvmValFast 25 f_Algorithm_leafContains_1_prog 0 f_Algorithm_leafContains_1_prog
      (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y)]) =
      (if !((if (leaf >>> (Algorithm.cellToLeafBitUInt x y &&& 63).toUInt64) &&& 1 == 1 then (0 : UInt32)
        else if ((leaf >>> (Algorithm.cellToLeafBitUInt x y &&& 63).toUInt64) &&& 1).toBitVec.slt 1#64 then 4294967295 else 1) == 0) then
        some (.i32 0) else some (.i32 1)) := rfl
  rw [heval, cellToLeafBitUInt_and_63, lcmp_bv_eq_zero]
  unfold Algorithm.leafContains
  by_cases h : (((leaf >>> (Algorithm.cellToLeafBitUInt x y).toUInt64) &&& 1) == 1) = true <;> simp [h]

theorem leafWithCell_1_equiv (leaf : UInt64) (x y : UInt32) (isAlive : Bool) :
    runJvm 35 f_Algorithm_leafWithCell_1_prog
      (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y), (4, .i32 (if isAlive then 1 else 0))]) =
      some (.i64 (Algorithm.leafWithCell leaf x y isAlive)) := by
  apply runJvm_of_runJvmValFast0 35 _ _ _ rfl
  unfold Algorithm.leafWithCell
  cases isAlive <;> dsimp
  · have heval : runJvmValFast 35 f_Algorithm_leafWithCell_1_prog 0 f_Algorithm_leafWithCell_1_prog
        (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y), (4, .i32 0)]) =
        some (.i64 (leaf &&& ((1 <<< (Algorithm.cellToLeafBitUInt x y &&& 63).toUInt64) ^^^ 18446744073709551615))) := rfl
    rw [heval, cellToLeafBitUInt_and_63, xor_allOnes_eq_not]
  · have heval : runJvmValFast 35 f_Algorithm_leafWithCell_1_prog 0 f_Algorithm_leafWithCell_1_prog
        (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y), (4, .i32 1)]) =
        some (.i64 (leaf ||| (1 <<< (Algorithm.cellToLeafBitUInt x y &&& 63).toUInt64))) := rfl
    rw [heval, cellToLeafBitUInt_and_63]

theorem leanUnboxULong_equiv (v : UInt64) :
    runJvm 25 leanUnboxULong_prog (initJvmState [(0, .boxedULong v)]) = some (.i64 v) := by rfl

theorem leanUnboxInt_equiv (v : UInt32) :
    runJvm 25 leanUnboxInt_prog (initJvmState [(0, .boxedInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxInt_1_equiv (v : UInt32) :
    runJvm 25 leanUnboxInt_1_prog (initJvmState [(0, .boxedInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxInt_2_equiv (v : UInt32) :
    runJvm 25 leanUnboxInt_2_prog (initJvmState [(0, .boxedInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxUInt_equiv (v : UInt32) :
    runJvm 25 leanUnboxUInt_prog (initJvmState [(0, .boxedUInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxUInt_1_equiv (v : UInt32) :
    runJvm 25 leanUnboxUInt_1_prog (initJvmState [(0, .boxedUInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxUInt_2_equiv (v : UInt32) :
    runJvm 25 leanUnboxUInt_2_prog (initJvmState [(0, .boxedUInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxUInt_3_equiv (v : UInt32) :
    runJvm 25 leanUnboxUInt_3_prog (initJvmState [(0, .boxedUInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxUInt_4_equiv (v : UInt32) :
    runJvm 25 leanUnboxUInt_4_prog (initJvmState [(0, .boxedUInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxUByte_equiv (v : UInt32) :
    runJvm 25 leanUnboxUByte_prog (initJvmState [(0, .boxedUByte v)]) = some (.i32 v) := by rfl

theorem macrocellSingleLeaf_lam0_equiv (w : UInt64) :
    runJvm 15 f_Algorithm_macrocellSingleLeaf___lam__0_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (if w == 0 then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 15 _ _ _ rfl
  have heval : runJvmValFast 15 f_Algorithm_macrocellSingleLeaf___lam__0_prog 0
      f_Algorithm_macrocellSingleLeaf___lam__0_prog (initJvmState [(0, .i64 w)]) =
      (if !((if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0) then
        some (.i32 0) else some (.i32 1)) := rfl
  rw [heval, lcmp_bv_eq_zero]
  by_cases hw : w == 0 <;> simp [hw]

theorem macrocellSingleLeaf_lam1_equiv (w : UInt64) :
    runJvm 15 f_Algorithm_macrocellSingleLeaf___lam__1_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (if w == 0 then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 15 _ _ _ rfl
  have heval : runJvmValFast 15 f_Algorithm_macrocellSingleLeaf___lam__1_prog 0
      f_Algorithm_macrocellSingleLeaf___lam__1_prog (initJvmState [(0, .i64 w)]) =
      (if !((if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0) then
        some (.i32 0) else some (.i32 1)) := rfl
  rw [heval, lcmp_bv_eq_zero]
  by_cases hw : w == 0 <;> simp [hw]

theorem macrocellSingleLeaf_lam2_equiv (w : UInt64) :
    runJvm 15 f_Algorithm_macrocellSingleLeaf___lam__2_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (if w == 0 then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 15 _ _ _ rfl
  have heval : runJvmValFast 15 f_Algorithm_macrocellSingleLeaf___lam__2_prog 0
      f_Algorithm_macrocellSingleLeaf___lam__2_prog (initJvmState [(0, .i64 w)]) =
      (if !((if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0) then
        some (.i32 0) else some (.i32 1)) := rfl
  rw [heval, lcmp_bv_eq_zero]
  by_cases hw : w == 0 <;> simp [hw]

theorem formatRLEItemLength_equiv (count : UInt32) :
    runJvm 20 f_Algorithm_formatRLEItemLength_prog (initJvmState [(0, .i32 count)]) =
      some (.i32 (Algorithm.formatRLEItemLength count)) := by
  apply runJvm_of_runJvmValFast0 20 _ _ _ rfl
  have heval : runJvmValFast 20 f_Algorithm_formatRLEItemLength_prog 0 f_Algorithm_formatRLEItemLength_prog
      (initJvmState [(0, .i32 count)]) =
      (if count == 1 then some (.i32 1) else some (.i32 (Algorithm.decimalLength count + 1))) := rfl
  rw [heval]; unfold Algorithm.formatRLEItemLength
  by_cases hc : count == 1 <;> simp [hc]

theorem decimalLength_equiv (n : UInt32) :
    runJvm 65 f_Algorithm_decimalLength_prog (initJvmState [(0, .i32 n)]) =
      some (.i32 (Algorithm.decimalLength n)) := by
  apply runJvm_of_runJvmValFast0 65 _ _ _ rfl
  unfold Algorithm.decimalLength
  jvm_step_blk0 f_Algorithm_decimalLength_prog; rw [compareUnsigned_slt']
  by_cases h1 : n < 10 <;> simp only [h1, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false]
  jvm_step_blk f_Algorithm_decimalLength_prog; rw [compareUnsigned_slt']
  by_cases h2 : n < 100 <;> simp only [h2, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false]
  jvm_step_blk f_Algorithm_decimalLength_prog; rw [compareUnsigned_slt']
  by_cases h3 : n < 1000 <;> simp only [h3, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false]
  jvm_step_blk f_Algorithm_decimalLength_prog; rw [compareUnsigned_slt']
  by_cases h4 : n < 10000 <;> simp only [h4, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false]
  jvm_step_blk f_Algorithm_decimalLength_prog; rw [compareUnsigned_slt']
  by_cases h5 : n < 100000 <;> simp only [h5, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false]
  jvm_step_blk f_Algorithm_decimalLength_prog; rw [compareUnsigned_slt']
  by_cases h6 : n < 1000000 <;> simp only [h6, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false]
  jvm_step_blk f_Algorithm_decimalLength_prog; rw [compareUnsigned_slt']
  by_cases h7 : n < 10000000 <;> simp only [h7, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false]
  jvm_step_blk f_Algorithm_decimalLength_prog; rw [compareUnsigned_slt']
  by_cases h8 : n < 100000000 <;> simp only [h8, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false]
  jvm_step_blk f_Algorithm_decimalLength_prog; rw [compareUnsigned_slt']
  by_cases h9 : n < 1000000000 <;> simp only [h9, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;> rfl

private def jvmBoxCellBox (b : Int32 × Int32 × Int32 × Int32) : JvmVal :=
  .pair (.boxedInt b.1.toUInt32)
    (.pair (.boxedInt b.2.1.toUInt32)
      (.pair (.boxedInt b.2.2.1.toUInt32) (.boxedInt b.2.2.2.toUInt32)))

theorem cellBox_equiv (cells : Array UInt64) :
    runJvm 60 f_Algorithm_cellBox_prog (initJvmState [(0, .u64Ref 0)] [] [cells]) =
      some (jvmBoxCellBox (Algorithm.cellBox cells)) := by
  apply runJvm_of_runJvmValFast0 60 _ _ _ rfl
  have heval : runJvmValFast 60 f_Algorithm_cellBox_prog 0 f_Algorithm_cellBox_prog
      (initJvmState [(0, .u64Ref 0)] [] [cells]) =
      (if cells.size.toUInt32 == 0 then some (jvmBoxCellBox (0, 0, 0, 0))
       else
         let k := cells[0]!
         let x := (k >>> 32).toUInt32.toInt32
         let y := k.toUInt32.toInt32
         some (jvmBoxCellBox (Algorithm.cellBounds cells 1 cells.size.toUInt32 x x y y))) := rfl
  rw [heval]; unfold Algorithm.cellBox Algorithm.cellKeyX Algorithm.cellKeyY
  by_cases h0 : cells.size.toUInt32 == 0 <;> simp [h0]

theorem cellBox_1_equiv (cells : Array UInt64) :
    runJvm 60 f_Algorithm_cellBox_1_prog (initJvmState [(0, .u64Ref 0)] [] [cells]) =
      some (jvmBoxCellBox (Algorithm.cellBox cells)) := by
  apply runJvm_of_runJvmValFast0 60 _ _ _ rfl
  have heval : runJvmValFast 60 f_Algorithm_cellBox_1_prog 0 f_Algorithm_cellBox_1_prog
      (initJvmState [(0, .u64Ref 0)] [] [cells]) =
      (if cells.size.toUInt32 == 0 then some (jvmBoxCellBox (0, 0, 0, 0))
       else
         let k := cells[0]!
         let x := (k >>> 32).toUInt32.toInt32
         let y := k.toUInt32.toInt32
         some (jvmBoxCellBox (Algorithm.cellBounds cells 1 cells.size.toUInt32 x x y y))) := rfl
  rw [heval]; unfold Algorithm.cellBox Algorithm.cellKeyX Algorithm.cellKeyY
  by_cases h0 : cells.size.toUInt32 == 0 <;> simp [h0]

theorem emptyAtHeight_equiv (h : UInt32) :
    runJvm 30 f_Algorithm_emptyAtHeight_prog (initJvmState [(0, .i32 h)]) =
      some (.mc (Algorithm.emptyAtHeight h)) := by
  apply runJvm_of_runJvmValFast0 30 _ _ _ rfl
  have heval : runJvmValFast 30 f_Algorithm_emptyAtHeight_prog 0 f_Algorithm_emptyAtHeight_prog
      (initJvmState [(0, .i32 h)]) =
      (if h == 0 then some (.mc Algorithm.emptyLevel4)
      else let e := Algorithm.emptyAtHeight (h - 1); some (.mc (Algorithm.makeCellNode e e e e))) := rfl
  rw [heval]
  by_cases hh : h = 0
  · subst hh; simp [Algorithm.emptyAtHeight]
  · have hb : (h == 0) = false := beq_false_of_ne hh
    simp only [hb, Bool.false_eq_true, ite_false]
    conv => rhs; rw [Algorithm.emptyAtHeight]
    simp [hh]

theorem serializePlaintext_equiv (cells : Array UInt64) (minX maxX minY maxY : Int32) :
    runJvm 70 f_Algorithm_serializePlaintext_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 minX.toUInt32), (2, .i32 maxX.toUInt32),
        (3, .i32 minY.toUInt32), (4, .i32 maxY.toUInt32)] [] [cells]) =
      some (.strArr (Algorithm.serializePlaintext cells minX maxX minY maxY)) := by
  apply runJvm_of_runJvmValFast0 70 _ _ _ rfl
  have heval : runJvmValFast 70 f_Algorithm_serializePlaintext_prog 0 f_Algorithm_serializePlaintext_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 minX.toUInt32), (2, .i32 maxX.toUInt32),
        (3, .i32 minY.toUInt32), (4, .i32 maxY.toUInt32)] [] [cells]) =
      (if cells.size.toUInt32 == 0 then some (.strArr #["."])
       else
         let w := maxX.toUInt32 - minX.toUInt32 + Int32.toUInt32 1
         let h := maxY.toUInt32 - minY.toUInt32 + Int32.toUInt32 1
         let g := Algorithm.fillGrid cells minX minY w h 79 (by decide) 0 cells.size.toUInt32
           (Algorithm.AsciiBytes.replicate (w * h) 46 (by decide))
         some (.strArr (Algorithm.gridRows g w h 0 Algorithm.GrowBuf.empty).toArray)) := rfl
  rw [heval]; unfold Algorithm.serializePlaintext
  by_cases h0 : cells.size.toUInt32 == 0
  · simp [h0]
  · simp [h0, Int32.toUInt32_add, Int32.toUInt32_sub]

theorem instBEqOption_findLastLeafRow_equiv (a b : Option UInt32) :
    runJvm 55 f_instBEqOption_beq___at___00Algorithm_findLastLeafRow_spec__0_prog
      (initJvmState [(0, match a with | some v => .boxedUInt v | none => .null),
        (1, match b with | some v => .boxedUInt v | none => .null)]) =
      some (.i32 (if a == b then 1 else 0)) := by
  cases a with
  | none => cases b <;> rfl
  | some va =>
    cases b with
    | none => rfl
    | some vb =>
      apply runJvm_of_runJvmValFast0 55 _ _ _ rfl
      have heval : runJvmValFast 55 f_instBEqOption_beq___at___00Algorithm_findLastLeafRow_spec__0_prog 0
          f_instBEqOption_beq___at___00Algorithm_findLastLeafRow_spec__0_prog
          (initJvmState [(0, .boxedUInt va), (1, .boxedUInt vb)]) =
          (if !(va == vb) then some (.i32 0) else some (.i32 1)) := rfl
      rw [heval]
      by_cases h : va == vb <;> simp [h]

theorem findLastLeafX_equiv (leaf : UInt64) (y : UInt32) :
    runJvm 85 f_Algorithm_findLastLeafX_prog (initJvmState [(0, .i64 leaf), (2, .i32 y)]) =
      some (match Algorithm.findLastLeafX leaf y with | some v => .boxedUInt v | none => .null) := by
  apply runJvm_of_runJvmValFast0 85 _ _ _ rfl
  have heval : runJvmValFast 85 f_Algorithm_findLastLeafX_prog 0 f_Algorithm_findLastLeafX_prog
      (initJvmState [(0, .i64 leaf), (2, .i32 y)]) =
      (if !(if Algorithm.leafContains leaf 7 y then (1 : UInt32) else 0) == 0 then some (.boxedUInt 7) else
      if !(if Algorithm.leafContains leaf 6 y then (1 : UInt32) else 0) == 0 then some (.boxedUInt 6) else
      if !(if Algorithm.leafContains leaf 5 y then (1 : UInt32) else 0) == 0 then some (.boxedUInt 5) else
      if !(if Algorithm.leafContains leaf 4 y then (1 : UInt32) else 0) == 0 then some (.boxedUInt 4) else
      if !(if Algorithm.leafContains leaf 3 y then (1 : UInt32) else 0) == 0 then some (.boxedUInt 3) else
      if !(if Algorithm.leafContains leaf 2 y then (1 : UInt32) else 0) == 0 then some (.boxedUInt 2) else
      if !(if Algorithm.leafContains leaf 1 y then (1 : UInt32) else 0) == 0 then some (.boxedUInt 1) else
      if !(if Algorithm.leafContains leaf 0 y then (1 : UInt32) else 0) == 0 then some (.boxedUInt 0) else
      some .null) := rfl
  rw [heval]; unfold Algorithm.findLastLeafX
  cases Algorithm.leafContains leaf 7 y <;> simp
  cases Algorithm.leafContains leaf 6 y <;> simp
  cases Algorithm.leafContains leaf 5 y <;> simp
  cases Algorithm.leafContains leaf 4 y <;> simp
  cases Algorithm.leafContains leaf 3 y <;> simp
  cases Algorithm.leafContains leaf 2 y <;> simp
  cases Algorithm.leafContains leaf 1 y <;> simp
  cases Algorithm.leafContains leaf 0 y <;> simp

attribute [local irreducible] checkInstanceOf

private theorem opt_ui32_some_beq_none (v : UInt32) : (some v == none) = false := rfl
private theorem opt_ui32_none_beq_none : ((none : Option UInt32) == none) = true := rfl
private theorem opt_ui32_some_bne_none (v : UInt32) : (some v != none) = true := rfl
private theorem opt_ui32_none_bne_none : ((none : Option UInt32) != none) = false := rfl

theorem findLastLeafRow_equiv (leaf : UInt64) :
    runJvm 110 f_Algorithm_findLastLeafRow_prog (initJvmState [(0, .i64 leaf)]) =
      some (match Algorithm.findLastLeafRow leaf with | some v => .boxedUInt v | none => .null) := by
  apply runJvm_of_runJvmValFast0 110 _ _ _ rfl
  unfold Algorithm.findLastLeafRow
  jvm_step_blk0 f_Algorithm_findLastLeafRow_prog
  cases h7 : Algorithm.findLastLeafX leaf 7 with
  | some v7 =>
    simp only [opt_ui32_some_beq_none, opt_ui32_some_bne_none, ui32_beq_0_0,
      Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
    rfl
  | none =>
    simp only [opt_ui32_none_beq_none, opt_ui32_none_bne_none, ui32_beq_1_0,
      Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
    jvm_step_blk f_Algorithm_findLastLeafRow_prog
    cases h6 : Algorithm.findLastLeafX leaf 6 with
    | some v6 =>
      simp only [opt_ui32_some_beq_none, opt_ui32_some_bne_none, ui32_beq_0_0,
        Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
      rfl
    | none =>
      simp only [opt_ui32_none_beq_none, opt_ui32_none_bne_none, ui32_beq_1_0,
        Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
      jvm_step_blk f_Algorithm_findLastLeafRow_prog
      cases h5 : Algorithm.findLastLeafX leaf 5 with
      | some v5 =>
        simp only [opt_ui32_some_beq_none, opt_ui32_some_bne_none, ui32_beq_0_0,
          Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
        rfl
      | none =>
        simp only [opt_ui32_none_beq_none, opt_ui32_none_bne_none, ui32_beq_1_0,
          Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
        jvm_step_blk f_Algorithm_findLastLeafRow_prog
        cases h4 : Algorithm.findLastLeafX leaf 4 with
        | some v4 =>
          simp only [opt_ui32_some_beq_none, opt_ui32_some_bne_none, ui32_beq_0_0,
            Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
          rfl
        | none =>
          simp only [opt_ui32_none_beq_none, opt_ui32_none_bne_none, ui32_beq_1_0,
            Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
          jvm_step_blk f_Algorithm_findLastLeafRow_prog
          cases h3 : Algorithm.findLastLeafX leaf 3 with
          | some v3 =>
            simp only [opt_ui32_some_beq_none, opt_ui32_some_bne_none, ui32_beq_0_0,
              Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
            rfl
          | none =>
            simp only [opt_ui32_none_beq_none, opt_ui32_none_bne_none, ui32_beq_1_0,
              Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
            jvm_step_blk f_Algorithm_findLastLeafRow_prog
            cases h2 : Algorithm.findLastLeafX leaf 2 with
            | some v2 =>
              simp only [opt_ui32_some_beq_none, opt_ui32_some_bne_none, ui32_beq_0_0,
                Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
              rfl
            | none =>
              simp only [opt_ui32_none_beq_none, opt_ui32_none_bne_none, ui32_beq_1_0,
                Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
              jvm_step_blk f_Algorithm_findLastLeafRow_prog
              cases h1 : Algorithm.findLastLeafX leaf 1 with
              | some v1 =>
                simp only [opt_ui32_some_beq_none, opt_ui32_some_bne_none, ui32_beq_0_0,
                  Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
                rfl
              | none =>
                simp only [opt_ui32_none_beq_none, opt_ui32_none_bne_none, ui32_beq_1_0,
                  Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
                jvm_step_blk f_Algorithm_findLastLeafRow_prog
                cases h0 : Algorithm.findLastLeafX leaf 0 with
                | some v0 =>
                  simp only [opt_ui32_some_beq_none, opt_ui32_some_bne_none, ui32_beq_0_0,
                    Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
                  rfl
                | none =>
                  simp only [opt_ui32_none_beq_none, opt_ui32_none_bne_none, ui32_beq_1_0,
                    Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
                  rfl

theorem dagWriter_addEntry_equiv (w : Algorithm.DagWriter) (m : Algorithm.MacroCell) (c1 c2 c3 c4 : UInt32) :
    runJvm 150 f_Algorithm_DagWriter_addEntry_prog
      (initJvmState [(0, .dagWriter w), (1, .mc m), (2, .i32 c1), (3, .i32 c2), (4, .i32 c3), (5, .i32 c4)]) =
      let r := w.addEntry m c1 c2 c3 c4
      some (.pair (.boxedUInt r.1) (.dagWriter r.2)) := by
  apply runJvm_of_runJvmValFast0 150 _ _ _ rfl
  rcases m with ⟨h, nw, ne, sw, se⟩ | ⟨h, nw, ne, sw, se⟩
  · jvm_step_blk0 f_Algorithm_DagWriter_addEntry_prog
    jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
    rw [lcmp_bv_eq_zero]
    by_cases hnw : nw = 0
    · simp only [hnw, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false]
      jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
      rw [lcmp_bv_eq_zero]
      by_cases hne : ne = 0
      · simp only [hne, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false]
        jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
        rw [lcmp_bv_eq_zero]
        by_cases hsw : sw = 0
        · simp only [hsw, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false]
          jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
          rw [lcmp_bv_eq_zero]
          by_cases hse : se = 0
          · simp only [hse, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false]
            jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
            simp [Algorithm.DagWriter.addEntry]
          · simp only [beq_eq_false_iff_ne.mpr hse, Bool.not_false, ite_true]
            jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
            simp [Algorithm.DagWriter.addEntry, hse]
        · simp only [beq_eq_false_iff_ne.mpr hsw, Bool.not_false, ite_true]
          jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
          simp [Algorithm.DagWriter.addEntry, hsw]
      · simp only [beq_eq_false_iff_ne.mpr hne, Bool.not_false, ite_true]
        jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
        simp [Algorithm.DagWriter.addEntry, hne]
    · simp only [beq_eq_false_iff_ne.mpr hnw, Bool.not_false, ite_true]
      jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
      simp [Algorithm.DagWriter.addEntry, hnw]
  · jvm_step_blk0 f_Algorithm_DagWriter_addEntry_prog
    jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
    jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
    by_cases h1 : c1 == 0
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
      by_cases h2 : c2 == 0
      · simp only [h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
        by_cases h3 : c3 == 0
        · simp only [h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
          by_cases h4 : c4 == 0
          · simp only [h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
            simp [Algorithm.DagWriter.addEntry, h1, h2, h3, h4]
          · simp only [h4, Bool.not_false, ↓reduceIte]
            jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
            simp [Algorithm.DagWriter.addEntry, h1, h2, h3, h4]
        · simp only [h3, Bool.not_false, ↓reduceIte]
          jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
          simp [Algorithm.DagWriter.addEntry, h1, h2, h3]
      · simp only [h2, Bool.not_false, ↓reduceIte]
        jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
        simp [Algorithm.DagWriter.addEntry, h1, h2]
    · simp only [h1, Bool.not_false, ↓reduceIte]
      jvm_step_blk f_Algorithm_DagWriter_addEntry_prog
      simp [Algorithm.DagWriter.addEntry, h1]

private theorem uint32_and_63_of_lt {i : UInt32} (hi : i < 64) : i &&& 63 = i := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_ofNat, BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
  rcases Nat.lt_or_ge k 6 with hk | hk
  · have ht : Nat.testBit 63 k = true := by
      have h : (63 : Nat) = 2 ^ 6 - 1 := rfl
      rw [h, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk
    have hk32 : k < 32 := by omega
    simp [hk32, ht]
  · have hlt : i.toNat < 64 := UInt32.lt_iff_toNat_lt.mp hi
    have hpow : 64 ≤ 2 ^ k := Nat.le_trans (by decide) (Nat.pow_le_pow_right (n := 2) (by decide) hk)
    have hf1 : Nat.testBit i.toNat k = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt hpow)
    have hbit : i.toBitVec.getLsbD k = false := by
      change i.toNat.testBit k = false; exact hf1
    simp [hbit]

private theorem uint32_shl_one (x : UInt32) : x <<< 1 = 2 * x := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  simp [UInt32.toBitVec_shiftLeft, UInt32.toBitVec_mul, BitVec.toNat_shiftLeft, BitVec.toNat_mul,
    Nat.shiftLeft_eq, Nat.mul_comm]

private theorem toUInt64_and_mask32 (x : UInt32) : x.toUInt64 &&& 4294967295 = x.toUInt64 := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_ofNat, BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
  rcases Nat.lt_or_ge k 32 with hk | hk
  · have ht : Nat.testBit 4294967295 k = true := by
      have h : (4294967295 : Nat) = 2 ^ 32 - 1 := rfl
      rw [h, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk
    have hk64 : k < 64 := by omega
    simp [hk64, ht]
  · have hlt : x.toBitVec.toNat < 2 ^ 32 := x.toBitVec.isLt
    have hpow : 2 ^ 32 ≤ 2 ^ k := Nat.pow_le_pow_right (n := 2) (by decide) hk
    have hf : Nat.testBit x.toBitVec.toNat k = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt hpow)
    have hbit : x.toBitVec.getLsbD k = false := by
      change x.toBitVec.toNat.testBit k = false; exact hf
    simp [hbit]

private theorem lcmp_bv_slt (a b : Int64) :
    (if a.toUInt64 == b.toUInt64 then (0 : UInt32)
      else if a.toUInt64.toBitVec.slt b.toUInt64.toBitVec then 4294967295 else 1).toBitVec.slt 0#32 =
      decide (a < b) := by
  change (if a.toUInt64 == b.toUInt64 then (0 : UInt32)
      else if a.toBitVec.slt b.toBitVec then 4294967295 else 1).toBitVec.slt 0#32 = decide (a < b)
  by_cases h1 : a.toUInt64 == b.toUInt64
  · have heq : a = b := by
      apply Int64.toBitVec_inj.mp
      exact congrArg UInt64.toBitVec (LawfulBEq.eq_of_beq h1)
    subst heq; simp [Int64.lt_irrefl]
  · by_cases h2 : a.toBitVec.slt b.toBitVec
    · have hlt : a < b := Int64.lt_iff_toBitVec_slt.mpr h2
      simp [h1, h2, hlt]
    · have hnlt : ¬(a < b) := fun h => h2 (Int64.lt_iff_toBitVec_slt.mp h)
      simp [h1, h2, hnlt]

private theorem lcmp_bv_sle (a b : Int64) :
    (if a.toUInt64 == b.toUInt64 then (0 : UInt32)
      else if a.toUInt64.toBitVec.slt b.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32 =
      decide (a ≤ b) := by
  change (if a.toUInt64 == b.toUInt64 then (0 : UInt32)
      else if a.toBitVec.slt b.toBitVec then 4294967295 else 1).toBitVec.sle 0#32 = decide (a ≤ b)
  by_cases h1 : a.toUInt64 == b.toUInt64
  · have heq : a = b := by
      apply Int64.toBitVec_inj.mp
      exact congrArg UInt64.toBitVec (LawfulBEq.eq_of_beq h1)
    subst heq; simp
  · by_cases h2 : a.toBitVec.slt b.toBitVec
    · have hle : a ≤ b := Int64.le_of_lt (Int64.lt_iff_toBitVec_slt.mpr h2)
      simp [h1, h2, hle]
    · have hne : a ≠ b := fun heq => h1 (by subst heq; simp)
      have hnle : ¬(a ≤ b) := by
        intro hle
        rcases Int64.lt_or_eq_of_le hle with hlt | rfl
        · exact h2 (Int64.lt_iff_toBitVec_slt.mp hlt)
        · exact hne rfl
      simp [h1, h2, hnle]

private def mkU64BufPushProg (cls : String) : List JvmInstr :=
  [.aload 0, .iconst 0, .invokestatic "kotlin/ULongArray" "get-s-VKNKU" "([JI)J", .l2i,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .iconst 1, .iadd,
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 3, .aload 0,
   .invokestatic "kotlin/ULongArray" "getSize-impl" "([J)I",
   .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 4, .iload 3, .iload 4,
   .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I", .iflt 45,
   .iload 4, .iconst 1, .ishl, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I",
   .invokestatic "kotlin/ULongArray" "constructor-impl" "(I)[J", .astore 5, .aload 0,
   .iload 4, .iconst 0, .aload 5, .invokestatic cls "f_Algorithm_copyU64-5j98i2w" "([JII[J)V",
   .aload 5, .iload 3, .lload 1, .invokestatic "kotlin/ULongArray" "set-k8EXiF4" "([JIJ)V",
   .aload 5, .iconst 0, .iload 3, .i2l, .lconst 4294967295, .land,
   .invokestatic "kotlin/ULong" "constructor-impl" "(J)J",
   .invokestatic "kotlin/ULongArray" "set-k8EXiF4" "([JIJ)V", .aload 5, .areturn,
   .aload 0, .iload 3, .lload 1, .invokestatic "kotlin/ULongArray" "set-k8EXiF4" "([JIJ)V",
   .aload 0, .iconst 0, .iload 3, .i2l, .lconst 4294967295, .land,
   .invokestatic "kotlin/ULong" "constructor-impl" "(J)J",
   .invokestatic "kotlin/ULongArray" "set-k8EXiF4" "([JIJ)V", .aload 0, .areturn]

macro "prove_u64Buf_push" prog:ident arr:ident x:ident : tactic =>
  `(tactic| (
    let st0 := initJvmState [(0, .u64Ref 0), (1, .i64 $x)] [] [$arr]
    let n := ($arr)[0]!.toUInt32 + 1
    let cap := ($arr).size.toUInt32
    let l3 := setLocal st0.locals 3 (.i32 n)
    let l4 := setLocal l3 4 (.i32 cap)
    let l5 := setLocal l4 5 (.u64Ref 1)
    have hcmp : (if n == cap then (0 : UInt32) else if n < cap then 4294967295 else 1).toBitVec.slt 0#32 =
        decide (n < cap) := compareUnsigned_slt' n cap
    have heval : runJvmResFast 65 $prog 0 $prog st0 =
        if (if n == cap then (0 : UInt32) else if n < cap then 4294967295 else 1).toBitVec.slt 0#32 then
          some (.u64Ref 0, {
            pc := 58
            stack := [.u64Ref 0]
            locals := l4
            u64Arrays := [(($arr).set! n.toNat $x).set! 0 n.toUInt64]
          })
        else
          let doubled := Array.replicate (cap <<< 1 + 1).toNat (0 : UInt64)
          let copied := Algorithm.copyU64 $arr cap 0 doubled
          some (.u64Ref 1, {
            pc := 44
            stack := [.u64Ref 1]
            locals := l5
            u64Arrays := [$arr, (copied.set! n.toNat $x).set! 0 n.toUInt64]
          }) := rfl
    rw [hcmp] at heval
    by_cases hlt : n < cap
    · simp only [hlt, decide_true, ite_true] at heval
      rw [runJvmRes_of_runJvmResFast 65 _ _ _ _ _ rfl rfl heval]
      simp [Algorithm.U64Buf.push, n, cap, hlt]
    · simp only [hlt, decide_false, ite_false] at heval
      rw [runJvmRes_of_runJvmResFast 65 _ _ _ _ _ rfl rfl heval]
      simp [Algorithm.U64Buf.push, n, cap, hlt, uint32_shl_one]))

theorem u64Buf_push_equiv (arr : Array UInt64) (x : UInt64) :
    (runJvmRes 65 f_Algorithm_U64Buf_push_prog (initJvmState [(0, .u64Ref 0), (1, .i64 x)] [] [arr])).map
      (fun p => (p.1, p.2.u64Arrays)) =
      some (if arr[0]!.toUInt32 + 1 < arr.size.toUInt32 then (.u64Ref 0, [Algorithm.U64Buf.push arr x])
            else (.u64Ref 1, [arr, Algorithm.U64Buf.push arr x])) := by
  prove_u64Buf_push f_Algorithm_U64Buf_push_prog arr x

theorem u64Buf_push_1_equiv (arr : Array UInt64) (x : UInt64) :
    (runJvmRes 65 f_Algorithm_U64Buf_push_1_prog (initJvmState [(0, .u64Ref 0), (1, .i64 x)] [] [arr])).map
      (fun p => (p.1, p.2.u64Arrays)) =
      some (if arr[0]!.toUInt32 + 1 < arr.size.toUInt32 then (.u64Ref 0, [Algorithm.U64Buf.push arr x])
            else (.u64Ref 1, [arr, Algorithm.U64Buf.push arr x])) := by
  prove_u64Buf_push f_Algorithm_U64Buf_push_1_prog arr x

theorem u64Buf_push_2_equiv (arr : Array UInt64) (x : UInt64) :
    (runJvmRes 65 f_Algorithm_U64Buf_push_2_prog (initJvmState [(0, .u64Ref 0), (1, .i64 x)] [] [arr])).map
      (fun p => (p.1, p.2.u64Arrays)) =
      some (if arr[0]!.toUInt32 + 1 < arr.size.toUInt32 then (.u64Ref 0, [Algorithm.U64Buf.push arr x])
            else (.u64Ref 1, [arr, Algorithm.U64Buf.push arr x])) := by
  prove_u64Buf_push f_Algorithm_U64Buf_push_2_prog arr x

theorem u64Buf_push_3_equiv (arr : Array UInt64) (x : UInt64) :
    (runJvmRes 65 f_Algorithm_U64Buf_push_3_prog (initJvmState [(0, .u64Ref 0), (1, .i64 x)] [] [arr])).map
      (fun p => (p.1, p.2.u64Arrays)) =
      some (if arr[0]!.toUInt32 + 1 < arr.size.toUInt32 then (.u64Ref 0, [Algorithm.U64Buf.push arr x])
            else (.u64Ref 1, [arr, Algorithm.U64Buf.push arr x])) := by
  prove_u64Buf_push f_Algorithm_U64Buf_push_3_prog arr x

theorem u64Buf_push_4_equiv (arr : Array UInt64) (x : UInt64) :
    (runJvmRes 65 f_Algorithm_U64Buf_push_4_prog (initJvmState [(0, .u64Ref 0), (1, .i64 x)] [] [arr])).map
      (fun p => (p.1, p.2.u64Arrays)) =
      some (if arr[0]!.toUInt32 + 1 < arr.size.toUInt32 then (.u64Ref 0, [Algorithm.U64Buf.push arr x])
            else (.u64Ref 1, [arr, Algorithm.U64Buf.push arr x])) := by
  prove_u64Buf_push f_Algorithm_U64Buf_push_4_prog arr x

theorem leafRowMask_equiv (leaf : UInt64) (x0 y0 l t r b : Int64) (i : UInt32) :
    runJvm 95 f_Algorithm_leafRowMask_prog
      (initJvmState [(0, .i64 leaf), (2, .i64 x0.toUInt64), (4, .i64 y0.toUInt64),
        (6, .i64 l.toUInt64), (8, .i64 t.toUInt64), (10, .i64 r.toUInt64), (12, .i64 b.toUInt64),
        (14, .i32 i)]) =
      some (.i64 (Algorithm.leafRowMask leaf x0 y0 l t r b i)) := by
  apply runJvm_of_runJvmValFast0 95 _ _ _ rfl
  jvm_step_blk0 f_Algorithm_leafRowMask_prog
  rw [compareUnsigned_slt']
  have h31 : ((3 : UInt32) &&& 31) = 3 := rfl
  by_cases hi : i < 64
  · simp only [hi, decide_true, ite_true]
    rw [Algorithm.leafRowMask]; simp only [hi, ↓reduceDIte]
    jvm_step_blk f_Algorithm_leafRowMask_prog
    cases hc : Algorithm.leafContains leaf (i &&& 7) (i >>> 3)
    · simp only [h31, hc, ui32_beq_0_0, ite_false, Bool.not_true, Bool.false_eq_true, Bool.false_and]
      jvm_step_blk f_Algorithm_leafRowMask_prog
      simp
    · simp only [h31, hc, ui32_beq_1_0, ite_true, Bool.not_false, Bool.true_and]
      jvm_step_blk f_Algorithm_leafRowMask_prog
      have hcx : x0.toUInt64 + (i &&& 7).toUInt64 = (x0 + (i &&& 7).toUInt64.toInt64).toUInt64 := by
        simp only [Int64.toUInt64_add]; rfl
      have hcy : y0.toUInt64 + (i >>> 3).toUInt64 = (y0 + (i >>> 3).toUInt64.toInt64).toUInt64 := by
        simp only [Int64.toUInt64_add]; rfl
      rw [hcx, lcmp_bv_sle]
      by_cases h1 : l ≤ x0 + (i &&& 7).toUInt64.toInt64
      · simp only [h1, decide_true, Bool.true_and, ite_true]
        jvm_step_blk f_Algorithm_leafRowMask_prog
        rw [lcmp_bv_slt]
        by_cases h2 : x0 + (i &&& 7).toUInt64.toInt64 < r
        · simp only [h2, decide_true, Bool.true_and, ite_true]
          jvm_step_blk f_Algorithm_leafRowMask_prog
          rw [hcy, lcmp_bv_sle]
          by_cases h3 : t ≤ y0 + (i >>> 3).toUInt64.toInt64
          · simp only [h3, decide_true, Bool.true_and, ite_true]
            jvm_step_blk f_Algorithm_leafRowMask_prog
            rw [lcmp_bv_slt]
            by_cases h4 : y0 + (i >>> 3).toUInt64.toInt64 < b
            · simp only [h4, decide_true, ite_true]
              jvm_step_blk f_Algorithm_leafRowMask_prog
              simp [uint32_and_63_of_lt hi]
            · simp only [h4, decide_false, Bool.false_eq_true, ite_false]
              jvm_step_blk f_Algorithm_leafRowMask_prog
              simp
          · simp only [h3, decide_false, Bool.false_eq_true, Bool.false_and, ite_false]
            jvm_step_blk f_Algorithm_leafRowMask_prog
            simp
        · simp only [h2, decide_false, Bool.false_eq_true, Bool.false_and, ite_false]
          jvm_step_blk f_Algorithm_leafRowMask_prog
          simp
      · simp only [h1, decide_false, Bool.false_eq_true, Bool.false_and, ite_false]
        jvm_step_blk f_Algorithm_leafRowMask_prog
        simp
  · simp only [hi, decide_false, Bool.false_eq_true, ite_false]
    jvm_step_blk f_Algorithm_leafRowMask_prog
    rw [Algorithm.leafRowMask]; simp [hi]

@[simp] theorem compareUnsigned64_slt' (a b : UInt64) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32 = decide (a < b) := by
  by_cases h1 : a == b <;> by_cases h2 : a < b <;> simp [h1, h2]
  have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; exact Nat.lt_irrefl _ h2

@[simp] theorem compareUnsigned64_sle' (a b : UInt64) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.sle 0#32 = decide (a ≤ b) := by
  by_cases h1 : a == b <;> by_cases h2 : a < b <;> simp [h1, h2]
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; exact Nat.le_refl _
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; exact Nat.le_refl _
  · exact Nat.le_of_lt h2
  · have hne : a ≠ b := fun h => h1 (beq_iff_eq.mpr h)
    have hne' : a.toBitVec.toNat ≠ b.toBitVec.toNat :=
      fun h => hne (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))
    change ¬ (a.toBitVec.toNat < b.toBitVec.toNat) at h2
    change b.toBitVec.toNat < a.toBitVec.toNat
    omega

@[simp] theorem compareUnsigned_sgt' (a b : UInt32) :
    (0#32).slt (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec = decide (b < a) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · have hne : a.toBitVec.toNat ≠ b.toBitVec.toNat :=
      fun h => h1 (beq_iff_eq.mpr (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))
    by_cases h2 : a < b
    · have hlt : a.toBitVec.toNat < b.toBitVec.toNat := h2
      have hn : ¬ (b < a) := show ¬ b.toBitVec.toNat < a.toBitVec.toNat by omega
      simp [h1, h2, hn]
    · have hn : ¬ a.toBitVec.toNat < b.toBitVec.toNat := h2
      have hgt : b < a := show b.toBitVec.toNat < a.toBitVec.toNat by omega
      simp [h1, h2, hgt]

@[simp] theorem compareUnsigned_sge' (a b : UInt32) :
    (0#32).sle (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec = decide (b ≤ a) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b
    · have hlt : a.toBitVec.toNat < b.toBitVec.toNat := h2
      have hn : ¬ (b ≤ a) := show ¬ b.toBitVec.toNat ≤ a.toBitVec.toNat by omega
      simp [h1, h2, hn]
    · have hn : ¬ a.toBitVec.toNat < b.toBitVec.toNat := h2
      have hle : b ≤ a := show b.toBitVec.toNat ≤ a.toBitVec.toNat by omega
      simp [h1, h2, hle]

@[simp] theorem compareUnsigned64_sgt' (a b : UInt64) :
    (0#32).slt (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec = decide (b < a) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · have hne : a.toBitVec.toNat ≠ b.toBitVec.toNat :=
      fun h => h1 (beq_iff_eq.mpr (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))
    by_cases h2 : a < b
    · have hlt : a.toBitVec.toNat < b.toBitVec.toNat := h2
      have hn : ¬ (b < a) := show ¬ b.toBitVec.toNat < a.toBitVec.toNat by omega
      simp [h1, h2, hn]
    · have hn : ¬ a.toBitVec.toNat < b.toBitVec.toNat := h2
      have hgt : b < a := show b.toBitVec.toNat < a.toBitVec.toNat by omega
      simp [h1, h2, hgt]

@[simp] theorem lcmp_bv_eq_zero' (a b : UInt64) :
    ((if a == b then (0 : UInt32) else if a.toBitVec.slt b.toBitVec = true then 4294967295 else 1) == 0) = (a == b) := by
  by_cases h1 : a == b <;> by_cases h2 : a.toBitVec.slt b.toBitVec = true <;> simp [h1, h2]

private theorem bv_max_sub_nlz (x : UInt32) (hx : x ≠ 0) :
    (if (UInt32.toBitVec 0).slt ((31 : UInt32) - nlz32 x).toBitVec = true then
      (31 : UInt32) - nlz32 x
    else 0) = x.log2 := by
  have hx0 : (x == 0) = false := beq_false_of_ne hx
  have hpos : x.toNat ≠ 0 :=
    fun h => hx (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))
  have hlt : x.toNat < 2 ^ 32 := x.toBitVec.isLt
  have hlog : x.log2.toNat < 32 := by
    change Nat.log2 x.toNat < 32
    exact (Nat.log2_lt hpos).mpr hlt
  have hnlz : (31 : UInt32) - nlz32 x = x.log2 := by
    simp only [nlz32, hx0, Bool.false_eq_true, ite_false]
    have h1 : x.log2.toBitVec.toNat ≤ 31 := Nat.le_of_lt_succ hlog
    apply UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq _)
    change ((31#32 - (31#32 - x.log2.toBitVec)).toNat) = x.log2.toBitVec.toNat
    have hle1 : x.log2.toBitVec ≤ 31#32 :=
      BitVec.le_def.mpr (show x.log2.toBitVec.toNat ≤ (31#32).toNat from by change x.log2.toBitVec.toNat ≤ 31; exact h1)
    have h31 : (31#32 - x.log2.toBitVec).toNat = 31 - x.log2.toBitVec.toNat := by
      rw [BitVec.toNat_sub_of_le hle1]; rfl
    have hle2 : 31#32 - x.log2.toBitVec ≤ 31#32 :=
      BitVec.le_def.mpr (by rw [h31]; change 31 - x.log2.toBitVec.toNat ≤ 31; omega)
    rw [BitVec.toNat_sub_of_le hle2]
    change 31 - (31#32 - x.log2.toBitVec).toNat = x.log2.toBitVec.toNat
    rw [h31]; omega
  rw [hnlz]
  split
  · rfl
  · rename_i hle
    have hlog0 : x.log2 = 0 := by
      rw [BitVec.slt_iff_toInt_lt] at hle
      change ¬ (0#32).toInt < x.log2.toBitVec.toInt at hle
      simp only [BitVec.toInt_zero] at hle
      have hto : x.log2.toBitVec.toInt = ↑x.log2.toBitVec.toNat := by
        rw [BitVec.toInt_eq_toNat_cond]
        split
        · rfl
        · have : x.log2.toBitVec.toNat < 32 := hlog
          omega
      rw [hto] at hle
      apply UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq _)
      change x.log2.toBitVec.toNat = 0
      omega
    exact hlog0.symm

/-! ### Sub-batch 2.2: MacroCell / HashLife FWD methods -/

private def findMcInstanceOfFVar? (e : Lean.Expr) : Option Lean.FVarId :=
  match e.find? (fun sub =>
    sub.isAppOfArity ``checkInstanceOf 2 &&
    (sub.getArg! 1).isAppOfArity ``JvmVal.mc 1 &&
    ((sub.getArg! 1).getArg! 0).isFVar) with
  | some sub => some ((sub.getArg! 1).getArg! 0).fvarId!
  | none => none

private def isUnbranchedRunLhs (e : Lean.Expr) : Bool :=
  let (inner, _) := unwrapRunLhs e
  inner.isAppOfArity ``runJvmValFast 5 || inner.isAppOfArity ``runJvmResFast 5

elab "split_next_mc_instanceof" : tactic => Lean.Elab.Tactic.withMainContext do
  let tgt ← Lean.Elab.Tactic.getMainTarget
  let some (_, lhs, _) := tgt.eq? | throwError "split_next_mc_instanceof: not an eq"
  let some fv := findMcInstanceOfFVar? lhs
    | throwError "split_next_mc_instanceof: no checkInstanceOf (.mc fvar)"
  Lean.Elab.Tactic.liftMetaTactic fun mvarId => do
    let subgoals ← mvarId.cases fv
    return subgoals.toList.map (·.mvarId)
  Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals reduce_top_mc_ite))

elab "step_mc_tree" prog:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_blk0 $prog))
  for _ in [:40] do
    let goals ← Lean.Elab.Tactic.getUnsolvedGoals
    if goals.isEmpty then break
    let mut madeProgress := false
    let mut nextGoals : List Lean.MVarId := []
    for g in goals do
      Lean.Elab.Tactic.setGoals [g]
      let tgt ← g.withContext Lean.Elab.Tactic.getMainTarget
      let (hasMc, isUnbranched) := match tgt.eq? with
        | some (_, lhs, _) => ((findMcInstanceOfFVar? lhs).isSome, isUnbranchedRunLhs lhs)
        | none => (false, false)
      if hasMc then
        Lean.Elab.Tactic.evalTactic (← `(tactic| split_next_mc_instanceof))
        Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals (try jvm_step_blk $prog)))
        madeProgress := true
      else if isUnbranched then
        Lean.Elab.Tactic.evalTactic (← `(tactic| try jvm_step_blk $prog))
        let post ← Lean.Elab.Tactic.getUnsolvedGoals
        if post != [g] then
          madeProgress := true
        else
          let tgt' ← g.withContext Lean.Elab.Tactic.getMainTarget
          if tgt' != tgt then madeProgress := true
      nextGoals := nextGoals ++ (← Lean.Elab.Tactic.getUnsolvedGoals)
    Lean.Elab.Tactic.setGoals nextGoals
    if !madeProgress then break

theorem needToExpand_equiv (m : Algorithm.MacroCell) (d : Nat) (hm : Algorithm.WFd m d) (hd : d < 2 ^ 32) :
    runJvm 45 f_Algorithm_needToExpand_prog (initJvmState [(0, .mc m)]) =
      some (.i32 (if Algorithm.needToExpand m then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 45 _ _ _ rfl
  jvm_step_blk0 f_Algorithm_needToExpand_prog
  rw [compareUnsigned_sle']
  unfold Algorithm.needToExpand
  by_cases h1 : m.level ≤ 4
  · simp only [h1, decide_true, Bool.true_or, ↓reduceIte]
    rfl
  · have hdf : decide False = false := rfl
    simp only [h1, hdf, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    jvm_step_blk f_Algorithm_needToExpand_prog
    rw [lcmp_bv_eq_zero']
    have hlev : m.level.toNat = d := Algorithm.WFd_level_toNat hm hd
    have hge4 : 4 ≤ d := Algorithm.WFd_ge_four hm
    have h5 : 5 ≤ d := by
      have : ¬ m.level.toNat ≤ 4 := fun h => h1 h
      omega
    rw [Algorithm.centeredSubSubnodeSizeFast_eq_centeredSubSubnodeSize_Impl hm h5]
    by_cases h2 : Algorithm.centeredSubSubnodeSize m = m.size
    · simp only [h2, beq_self_eq_true, bne_iff_ne, ne_eq, not_true_eq_false, ↓reduceIte]
      rfl
    · simp only [h2, beq_iff_eq, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte]
      rfl

theorem minimumMacroCellLevel_equiv (span : UInt32) :
    runJvm 40 f_Algorithm_minimumMacroCellLevel_prog (initJvmState [(0, .i32 span)]) =
      some (.i32 (Algorithm.minimumMacroCellLevel span)) := by
  apply runJvm_of_runJvmValFast0 40 _ _ _ rfl
  jvm_step_blk0 f_Algorithm_minimumMacroCellLevel_prog
  rw [compareUnsigned_sle']
  unfold Algorithm.minimumMacroCellLevel
  by_cases h1 : span ≤ 16
  · simp only [h1, decide_true, ↓reduceIte]
    rfl
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
    jvm_step_blk f_Algorithm_minimumMacroCellLevel_prog
    have hx : span - 1 ≠ 0 := by
      intro h0
      have hs : span = 1 := by
        calc span = (span - 1) + 1 := by rw [UInt32.sub_add_cancel]
          _ = 0 + 1 := by rw [h0]
          _ = 1 := rfl
      exact h1 (by subst hs; exact of_decide_eq_true rfl)
    rw [bv_max_sub_nlz (span - 1) hx, compareUnsigned_slt']
    by_cases h2 : (span - 1).log2 + 1 < 4
    · simp only [h2, decide_true, ↓reduceIte]
      rfl
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte]
      rfl

theorem stepLevel4Node_equiv (m : Algorithm.MacroCell) :
    runJvm 45 f_Algorithm_stepLevel4Node_prog (initJvmState [(0, .mc m)]) =
      some (.i64 (Algorithm.stepLevel4Node m)) := by
  apply runJvm_of_runJvmValFast0 45 _ _ _ rfl
  step_mc_tree f_Algorithm_stepLevel4Node_prog
  all_goals simp [Algorithm.stepLevel4Node]

theorem stepLevel4NodeWith_equiv (m : Algorithm.MacroCell) (computeLeaf : UInt64 → UInt32) :
    runJvm 45 f_Algorithm_stepLevel4NodeWith_prog
      (initJvmState [(0, .mc m), (1, .fnU64ToU32 computeLeaf)]) =
      some (.i64 (Algorithm.stepLevel4NodeWith m computeLeaf)) := by
  apply runJvm_of_runJvmValFast0 45 _ _ _ rfl
  step_mc_tree f_Algorithm_stepLevel4NodeWith_prog
  all_goals simp [Algorithm.stepLevel4NodeWith]

theorem importsAsEmpty_equiv (m : Algorithm.MacroCell) :
    runJvm 55 f_Algorithm_importsAsEmpty_prog (initJvmState [(0, .mc m)]) =
      some (.i32 (if Algorithm.importsAsEmpty m then 1 else 0)) := by
  rcases m with ⟨h, nw, ne, sw, se⟩ | ⟨h, nw, ne, sw, se⟩
  · apply runJvm_of_runJvmValFast0 55 _ _ _ rfl
    jvm_step_blk0 f_Algorithm_importsAsEmpty_prog; rfl
  · apply runJvm_of_runJvmValFast0 55 _ _ _ rfl
    step_mc_tree f_Algorithm_importsAsEmpty_prog
    rw [lcmp_bv_eq_zero']
    simp only [Algorithm.importsAsEmpty]
    by_cases h0 : (Algorithm.MacroCell.cellNode h nw ne sw se).size == 0
    · simp only [h0, ↓reduceIte, Bool.true_and]
      jvm_step_blk f_Algorithm_importsAsEmpty_prog
      rw [compareUnsigned_sgt']
      by_cases h31 : 31 < (Algorithm.MacroCell.cellNode h nw ne sw se).level
      · have hle : ¬ (Algorithm.MacroCell.cellNode h nw ne sw se).level ≤ 31 := by
          intro hle
          have hlt : 31 < (Algorithm.MacroCell.cellNode h nw ne sw se).level.toNat := h31
          have hle' : (Algorithm.MacroCell.cellNode h nw ne sw se).level.toNat ≤ 31 := hle
          omega
        simp only [h31, decide_true, hle, decide_false, Bool.false_eq_true, ↓reduceIte]; rfl
      · have hle : (Algorithm.MacroCell.cellNode h nw ne sw se).level ≤ 31 :=
          UInt32.not_lt.mp h31
        simp only [h31, decide_false, Bool.false_eq_true, hle, decide_true, ↓reduceIte]; rfl
    · simp only [h0, Bool.false_eq_true, Bool.false_and, ↓reduceIte]; rfl

theorem importNeedsChildren_equiv (m : Algorithm.MacroCell) :
    runJvm 55 f_Algorithm_importNeedsChildren_prog (initJvmState [(0, .mc m)]) =
      some (.i32 (if Algorithm.importNeedsChildren m then 1 else 0)) := by
  rcases m with ⟨h, nw, ne, sw, se⟩ | ⟨h, nw, ne, sw, se⟩
  · apply runJvm_of_runJvmValFast0 55 _ _ _ rfl
    jvm_step_blk0 f_Algorithm_importNeedsChildren_prog; rfl
  · apply runJvm_of_runJvmValFast0 55 _ _ _ rfl
    step_mc_tree f_Algorithm_importNeedsChildren_prog
    simp only [Algorithm.importNeedsChildren]
    by_cases he : Algorithm.importsAsEmpty (Algorithm.MacroCell.cellNode h nw ne sw se) = true
    · simp only [he, Bool.not_true, Bool.false_and, ui32_beq_1_0, Bool.false_eq_true, ↓reduceIte]
      rfl
    · have hef : Algorithm.importsAsEmpty (Algorithm.MacroCell.cellNode h nw ne sw se) = false :=
        Bool.eq_false_iff.mpr he
      simp only [hef, Bool.not_true, Bool.not_false, Bool.true_and, ui32_beq_0_0, Bool.false_eq_true, ↓reduceIte]
      jvm_step_blk f_Algorithm_importNeedsChildren_prog
      rw [compareUnsigned_sgt']
      by_cases h60 : 60 < (Algorithm.MacroCell.cellNode h nw ne sw se).level
      · have hle : ¬ (Algorithm.MacroCell.cellNode h nw ne sw se).level ≤ 60 := by
          intro hle
          have hlt : 60 < (Algorithm.MacroCell.cellNode h nw ne sw se).level.toNat := h60
          have hle' : (Algorithm.MacroCell.cellNode h nw ne sw se).level.toNat ≤ 60 := hle
          omega
        simp only [h60, decide_true, hle, decide_false, Bool.false_eq_true, ↓reduceIte]; rfl
      · have hle : (Algorithm.MacroCell.cellNode h nw ne sw se).level ≤ 60 :=
          UInt32.not_lt.mp h60
        simp only [h60, decide_false, Bool.false_eq_true, hle, decide_true, ↓reduceIte]; rfl

theorem computePruneThresholds_equiv (computedGenerations : UInt64)
    (generationsToCacheInMacroCellMaps generationsToCacheInLeafNodeMap : UInt32) :
    runJvm 65 f_Algorithm_computePruneThresholds_prog
      (initJvmState [(0, .i64 computedGenerations), (2, .i32 generationsToCacheInMacroCellMaps),
        (3, .i32 generationsToCacheInLeafNodeMap)]) =
      some (.pruneThresh (Algorithm.computePruneThresholds computedGenerations
        generationsToCacheInMacroCellMaps generationsToCacheInLeafNodeMap)) := by
  apply runJvm_of_runJvmValFast0 65 _ _ _ rfl
  unfold Algorithm.computePruneThresholds
  jvm_step_blk0 f_Algorithm_computePruneThresholds_prog
  rw [compareUnsigned64_sle']
  by_cases h1 : generationsToCacheInMacroCellMaps.toUInt64 ≤ computedGenerations
  · simp only [h1, decide_true, ↓reduceIte]
    jvm_step_blk f_Algorithm_computePruneThresholds_prog
    rw [compareUnsigned64_sle']
    by_cases h2 : generationsToCacheInLeafNodeMap.toUInt64 ≤ computedGenerations <;>
      simp only [h2, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;> rfl
  · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
    jvm_step_blk f_Algorithm_computePruneThresholds_prog
    rw [compareUnsigned64_sle']
    by_cases h2 : generationsToCacheInLeafNodeMap.toUInt64 ≤ computedGenerations <;>
      simp only [h2, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;> rfl

private theorem ui32_toInt32_eq {a b : UInt32} (h : a.toBitVec = b.toBitVec) : a.toInt32 = b.toInt32 := by
  cases a; cases b; cases h; rfl

private theorem bv32_smod_32 (x : BitVec 32) : x.smod 32#32 = x &&& 31#32 := by
  apply BitVec.eq_of_toNat_eq
  have hlt : x.toNat < 4294967296 := x.isLt
  have hand : (x &&& 31#32).toNat = x.toNat % 32 := by
    change (x.toNat &&& 31) = x.toNat % 32
    rw [show (31 : Nat) = 2^5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [hand]
  simp only [BitVec.smod]
  have h32 : (32#32 : BitVec 32).msb = false := rfl
  rw [h32]
  cases hx : x.msb
  · simp [BitVec.umod]
  · change (if (x.neg.umod 32#32) = 0#32 then x.neg.umod 32#32 else (32#32).sub (x.neg.umod 32#32)).toNat = x.toNat % 32
    have humod : (x.neg.umod 32#32).toNat = (4294967296 - x.toNat) % 32 := by
      have hneg : x.neg = -x := rfl
      rw [hneg]; simp [BitVec.umod, BitVec.toNat_neg]
    split
    · rename_i hz
      have hz0 : (x.neg.umod 32#32).toNat = 0 := congrArg BitVec.toNat hz
      rw [humod] at hz0; omega
    · rename_i hnz
      have hnz0 : (4294967296 - x.toNat) % 32 ≠ 0 := by
        intro h0; apply hnz; apply BitVec.eq_of_toNat_eq; rw [humod, h0]; rfl
      have hsub : ((32#32).sub (x.neg.umod 32#32)) = 32#32 - x.neg.umod 32#32 := rfl
      rw [hsub, BitVec.toNat_sub_of_le]
      · change 32 - (x.neg.umod 32#32).toNat = x.toNat % 32
        rw [humod]; omega
      · exact BitVec.le_def.mpr (by change (x.neg.umod 32#32).toNat ≤ 32; rw [humod]; omega)

private theorem bv32_and31_mod32 (x : BitVec 32) : (x &&& 31#32) % 32#32 = x &&& 31#32 := by
  apply BitVec.eq_of_toNat_eq
  have hand : (x &&& 31#32).toNat = x.toNat % 32 := by
    change (x.toNat &&& 31) = x.toNat % 32
    rw [show (31 : Nat) = 2^5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  change (x &&& 31#32).toNat % 32 = (x &&& 31#32).toNat
  rw [hand]; omega

private theorem stepOffset_eq (l : UInt32) :
    ((1 : UInt32) <<< (l - 2 &&& 31)).toInt32 = Algorithm.stepOffsetDeltaUInt l := by
  simp only [Algorithm.stepOffsetDeltaUInt]
  apply ui32_toInt32_eq
  simp only [UInt32.toBitVec_shiftLeft, UInt32.toBitVec_and, UInt32.toBitVec_sub, Int32.toBitVec_sub]
  change 1#32 <<< ((l.toBitVec - 2#32 &&& 31#32) % 32#32) = 1#32 <<< (l.toBitVec - 2#32).smod 32#32
  rw [bv32_smod_32, bv32_and31_mod32]

private theorem expandStepOffset_eq (l1 l2 : UInt32) :
    ((4294967293 : UInt32) * 1 <<< ((l1 - 1) &&& 31) + 1 <<< ((l2 - 2) &&& 31)).toInt32 =
      Algorithm.expandOffsetDeltaUInt l1 + Algorithm.stepOffsetDeltaUInt l2 := by
  simp only [Algorithm.expandOffsetDeltaUInt, Algorithm.stepOffsetDeltaUInt]
  apply ui32_toInt32_eq
  simp only [UInt32.toBitVec_add, UInt32.toBitVec_mul, UInt32.toBitVec_shiftLeft,
    UInt32.toBitVec_and, UInt32.toBitVec_sub, Int32.toBitVec_mul]
  change 4294967293#32 * (1#32 <<< ((l1.toBitVec - 1#32 &&& 31#32) % 32#32)) +
      (1#32 <<< ((l2.toBitVec - 2#32 &&& 31#32) % 32#32)) =
    (-3#32) * (1#32 <<< (l1.toBitVec - 1#32).smod 32#32) +
      (1#32 <<< (l2.toBitVec - 2#32).smod 32#32)
  rw [bv32_smod_32, bv32_smod_32, bv32_and31_mod32, bv32_and31_mod32]
  rfl

theorem prepareStep_equiv (m : Algorithm.MacroCell) :
    runJvm 75 f_Algorithm_prepareStep_prog (initJvmState [(0, .mc m)]) =
      some (.stepPrep (Algorithm.prepareStep m)) := by
  apply runJvm_of_runJvmValFast0 75 _ _ _ rfl
  unfold Algorithm.prepareStep
  jvm_step_blk0 f_Algorithm_prepareStep_prog
  cases hn : Algorithm.needToExpand m <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ui32_beq_0_0, ui32_beq_1_0, ite_true, ite_false]
  · jvm_step_blk f_Algorithm_prepareStep_prog
    rw [stepOffset_eq]
  · jvm_step_blk f_Algorithm_prepareStep_prog
    rw [expandStepOffset_eq]

theorem level4Node_cellEquals_equiv (m other : Algorithm.MacroCell) :
    runJvm 110 f_Algorithm_Level4Node_cellEquals_prog (initJvmState [(0, .mc m), (1, .mc other)]) =
      some (.i32 (if Algorithm.Level4Node.cellEquals m other then 1 else 0)) := by
  rcases m with ⟨h1, nw1, ne1, sw1, se1⟩ | ⟨h1, nw1, ne1, sw1, se1⟩ <;>
    rcases other with ⟨h2, nw2, ne2, sw2, se2⟩ | ⟨h2, nw2, ne2, sw2, se2⟩
  · apply runJvm_of_runJvmValFast0 110 _ _ _ rfl
    step_mc_tree f_Algorithm_Level4Node_cellEquals_prog
    simp only [Algorithm.Level4Node.cellEquals]
    by_cases hh : (h1 == h2) = true
    · simp only [hh, Bool.true_and, ↓reduceIte]
      jvm_step_blk f_Algorithm_Level4Node_cellEquals_prog; rw [lcmp_bv_eq_zero']
      by_cases hnw : (nw1 == nw2) = true
      · simp only [hnw, Bool.true_and, ↓reduceIte]
        jvm_step_blk f_Algorithm_Level4Node_cellEquals_prog; rw [lcmp_bv_eq_zero']
        by_cases hne : (ne1 == ne2) = true
        · simp only [hne, Bool.true_and, ↓reduceIte]
          jvm_step_blk f_Algorithm_Level4Node_cellEquals_prog; rw [lcmp_bv_eq_zero']
          by_cases hsw : (sw1 == sw2) = true
          · simp only [hsw, Bool.true_and, ↓reduceIte]
            jvm_step_blk f_Algorithm_Level4Node_cellEquals_prog; rw [lcmp_bv_eq_zero']
            by_cases hse : (se1 == se2) = true
            · simp only [hse, ↓reduceIte]; rfl
            · have hsef : (se1 == se2) = false := Bool.eq_false_iff.mpr hse
              simp only [hsef, Bool.false_eq_true, ↓reduceIte]; rfl
          · have hswf : (sw1 == sw2) = false := Bool.eq_false_iff.mpr hsw
            simp only [hswf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl
        · have hnef : (ne1 == ne2) = false := Bool.eq_false_iff.mpr hne
          simp only [hnef, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl
      · have hnwf : (nw1 == nw2) = false := Bool.eq_false_iff.mpr hnw
        simp only [hnwf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl
    · have hhf : (h1 == h2) = false := Bool.eq_false_iff.mpr hh
      simp only [hhf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl
  · apply runJvm_of_runJvmValFast0 110 _ _ _ rfl
    step_mc_tree f_Algorithm_Level4Node_cellEquals_prog; rfl
  · apply runJvm_of_runJvmValFast0 110 _ _ _ rfl
    step_mc_tree f_Algorithm_Level4Node_cellEquals_prog; rfl
  · apply runJvm_of_runJvmValFast0 110 _ _ _ rfl
    step_mc_tree f_Algorithm_Level4Node_cellEquals_prog; rfl

theorem cellNode_cellEquals_equiv (m other : Algorithm.MacroCell) :
    runJvm 110 f_Algorithm_CellNode_cellEquals_prog (initJvmState [(0, .mc m), (1, .mc other)]) =
      some (.i32 (if Algorithm.CellNode.cellEquals m other then 1 else 0)) := by
  rcases m with ⟨h1, nw1, ne1, sw1, se1⟩ | ⟨h1, nw1, ne1, sw1, se1⟩ <;>
    rcases other with ⟨h2, nw2, ne2, sw2, se2⟩ | ⟨h2, nw2, ne2, sw2, se2⟩
  · apply runJvm_of_runJvmValFast0 110 _ _ _ rfl
    step_mc_tree f_Algorithm_CellNode_cellEquals_prog; rfl
  · apply runJvm_of_runJvmValFast0 110 _ _ _ rfl
    step_mc_tree f_Algorithm_CellNode_cellEquals_prog; rfl
  · apply runJvm_of_runJvmValFast0 110 _ _ _ rfl
    step_mc_tree f_Algorithm_CellNode_cellEquals_prog; rfl
  · apply runJvm_of_runJvmValFast0 110 _ _ _ rfl
    step_mc_tree f_Algorithm_CellNode_cellEquals_prog
    simp only [Algorithm.CellNode.cellEquals]
    by_cases hh : (h1 == h2) = true
    · simp only [hh, Bool.true_and, ↓reduceIte]
      jvm_step_blk f_Algorithm_CellNode_cellEquals_prog
      cases hnw : Algorithm.MacroCell.cellEquals nw1 nw2
      · simp only [Bool.false_and, ui32_beq_0_0, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl
      · simp only [Bool.true_and, ui32_beq_1_0, Bool.not_false, ↓reduceIte]
        jvm_step_blk f_Algorithm_CellNode_cellEquals_prog
        cases hne : Algorithm.MacroCell.cellEquals ne1 ne2
        · simp only [Bool.false_and, ui32_beq_0_0, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl
        · simp only [Bool.true_and, ui32_beq_1_0, Bool.not_false, ↓reduceIte]
          jvm_step_blk f_Algorithm_CellNode_cellEquals_prog
          cases hsw : Algorithm.MacroCell.cellEquals sw1 sw2
          · simp only [Bool.false_and, ui32_beq_0_0, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl
          · simp only [Bool.true_and, ui32_beq_1_0, Bool.not_false, ↓reduceIte]
            jvm_step_nonbranch_chunks
    · have hhf : (h1 == h2) = false := Bool.eq_false_iff.mpr hh
      simp only [hhf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl

theorem macroCell_cellEquals_equiv (m other : Algorithm.MacroCell) :
    runJvm 195 f_Algorithm_MacroCell_cellEquals_prog (initJvmState [(0, .mc m), (1, .mc other)]) =
      some (.i32 (if Algorithm.MacroCell.cellEquals m other then 1 else 0)) := by
  rcases m with ⟨h1, nw1, ne1, sw1, se1⟩ | ⟨h1, nw1, ne1, sw1, se1⟩ <;>
    rcases other with ⟨h2, nw2, ne2, sw2, se2⟩ | ⟨h2, nw2, ne2, sw2, se2⟩
  · apply runJvm_of_runJvmValFast0 195 _ _ _ rfl
    step_mc_tree f_Algorithm_MacroCell_cellEquals_prog
    simp only [Algorithm.MacroCell.cellEquals]
    by_cases hh : (h1 == h2) = true
    · simp only [hh, Bool.true_and, ↓reduceIte]
      jvm_step_blk f_Algorithm_MacroCell_cellEquals_prog; rw [lcmp_bv_eq_zero']
      by_cases hnw : (nw1 == nw2) = true
      · simp only [hnw, Bool.true_and, ↓reduceIte]
        jvm_step_blk f_Algorithm_MacroCell_cellEquals_prog; rw [lcmp_bv_eq_zero']
        by_cases hne : (ne1 == ne2) = true
        · simp only [hne, Bool.true_and, ↓reduceIte]
          jvm_step_blk f_Algorithm_MacroCell_cellEquals_prog; rw [lcmp_bv_eq_zero']
          by_cases hsw : (sw1 == sw2) = true
          · simp only [hsw, Bool.true_and, ↓reduceIte]
            jvm_step_blk f_Algorithm_MacroCell_cellEquals_prog; rw [lcmp_bv_eq_zero']
            by_cases hse : (se1 == se2) = true
            · simp only [hse, ↓reduceIte]; rfl
            · have hsef : (se1 == se2) = false := Bool.eq_false_iff.mpr hse
              simp only [hsef, Bool.false_eq_true, ↓reduceIte]; rfl
          · have hswf : (sw1 == sw2) = false := Bool.eq_false_iff.mpr hsw
            simp only [hswf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl
        · have hnef : (ne1 == ne2) = false := Bool.eq_false_iff.mpr hne
          simp only [hnef, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl
      · have hnwf : (nw1 == nw2) = false := Bool.eq_false_iff.mpr hnw
        simp only [hnwf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl
    · have hhf : (h1 == h2) = false := Bool.eq_false_iff.mpr hh
      simp only [hhf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl
  · apply runJvm_of_runJvmValFast0 195 _ _ _ rfl
    step_mc_tree f_Algorithm_MacroCell_cellEquals_prog; rfl
  · apply runJvm_of_runJvmValFast0 195 _ _ _ rfl
    step_mc_tree f_Algorithm_MacroCell_cellEquals_prog; rfl
  · apply runJvm_of_runJvmValFast0 195 _ _ _ rfl
    step_mc_tree f_Algorithm_MacroCell_cellEquals_prog
    simp only [Algorithm.MacroCell.cellEquals]
    by_cases hh : (h1 == h2) = true
    · simp only [hh, Bool.true_and, ↓reduceIte]
      jvm_step_blk f_Algorithm_MacroCell_cellEquals_prog
      cases hnw : Algorithm.MacroCell.cellEquals nw1 nw2
      · simp only [Bool.false_and, ui32_beq_0_0, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl
      · simp only [Bool.true_and, ui32_beq_1_0, Bool.not_false, ↓reduceIte]
        jvm_step_blk f_Algorithm_MacroCell_cellEquals_prog
        cases hne : Algorithm.MacroCell.cellEquals ne1 ne2
        · simp only [Bool.false_and, ui32_beq_0_0, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl
        · simp only [Bool.true_and, ui32_beq_1_0, Bool.not_false, ↓reduceIte]
          jvm_step_blk f_Algorithm_MacroCell_cellEquals_prog
          cases hsw : Algorithm.MacroCell.cellEquals sw1 sw2
          · simp only [Bool.false_and, ui32_beq_0_0, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; rfl
          · simp only [Bool.true_and, ui32_beq_1_0, Bool.not_false, ↓reduceIte]
            jvm_step_nonbranch_chunks
    · have hhf : (h1 == h2) = false := Bool.eq_false_iff.mpr hh
      simp only [hhf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rfl

theorem canonicalizeMacroCellWith_equiv (m : Algorithm.MacroCell)
    (internLevel4 : Algorithm.MacroCell → Algorithm.MacroCell)
    (findExistingCell : Algorithm.MacroCell → Option Algorithm.MacroCell)
    (canonicalizeSubnode : Algorithm.MacroCell → Algorithm.MacroCell)
    (internCell : Algorithm.MacroCell → Algorithm.MacroCell) :
    runJvm 135 f_Algorithm_canonicalizeMacroCellWith_prog
      (initJvmState [(0, .mc m), (1, .fnMcToMc internLevel4), (2, .fnMcToOptMc findExistingCell),
        (3, .fnMcToMc canonicalizeSubnode), (4, .fnMcToMc internCell)]) =
      some (.mc (Algorithm.canonicalizeMacroCellWith m internLevel4 findExistingCell
        canonicalizeSubnode internCell)) := by
  rcases m with ⟨h, nw, ne, sw, se⟩ | ⟨h, nw, ne, sw, se⟩
  · apply runJvm_of_runJvmValFast0 135 _ _ _ rfl
    step_mc_tree f_Algorithm_canonicalizeMacroCellWith_prog; rfl
  · apply runJvm_of_runJvmValFast0 135 _ _ _ rfl
    cases hf : findExistingCell (Algorithm.MacroCell.cellNode h nw ne sw se) with
    | some existing =>
      step_mc_tree f_Algorithm_canonicalizeMacroCellWith_prog
      simp only [Algorithm.canonicalizeMacroCellWith, hf]
      (conv => lhs; arg 1; jvm_whnf_blk)
      (first | rw [afterBlockChunk_cont] | rw [afterBlockChunk_jump] | rw [afterBlockChunk_done])
      (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)
      jvm_step_blk f_Algorithm_canonicalizeMacroCellWith_prog
      rfl
    | none =>
      step_mc_tree f_Algorithm_canonicalizeMacroCellWith_prog
      simp only [Algorithm.canonicalizeMacroCellWith, hf]
      (conv => lhs; arg 1; jvm_whnf_blk)
      (first | rw [afterBlockChunk_cont] | rw [afterBlockChunk_jump] | rw [afterBlockChunk_done])
      (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)
      jvm_step_blk f_Algorithm_canonicalizeMacroCellWith_prog
      jvm_step_blk f_Algorithm_canonicalizeMacroCellWith_prog
      rw [lcmp_bv_eq_zero']
      cases hsz : ((Algorithm.MacroCell.cellNode h nw ne sw se).size == 0)
      · simp only [Bool.false_eq_true, ↓reduceIte]; rfl
      · simp only [↓reduceIte]; rfl

theorem centeredHorizontalSubnode_equiv (w e : Algorithm.MacroCell) :
    runJvm 200 f_Algorithm_centeredHorizontalSubnode_prog (initJvmState [(0, .mc w), (1, .mc e)]) =
      some (.mc (Algorithm.centeredHorizontalSubnode w e)) := by
  apply runJvm_of_runJvmValFast0 200 _ _ _ rfl
  step_mc_tree f_Algorithm_centeredHorizontalSubnode_prog
  all_goals simp [Algorithm.centeredHorizontalSubnode]

theorem centeredVerticalSubnode_equiv (n s : Algorithm.MacroCell) :
    runJvm 200 f_Algorithm_centeredVerticalSubnode_prog (initJvmState [(0, .mc n), (1, .mc s)]) =
      some (.mc (Algorithm.centeredVerticalSubnode n s)) := by
  apply runJvm_of_runJvmValFast0 200 _ _ _ rfl
  step_mc_tree f_Algorithm_centeredVerticalSubnode_prog
  all_goals simp [Algorithm.centeredVerticalSubnode]

theorem centeredSubnode_equiv (m : Algorithm.MacroCell) :
    runJvm 240 f_Algorithm_centeredSubnode_prog (initJvmState [(0, .mc m)]) =
      some (.mc (Algorithm.centeredSubnode m)) := by
  apply runJvm_of_runJvmValFast0 240 _ _ _ rfl
  step_mc_tree f_Algorithm_centeredSubnode_prog
  all_goals simp only [Algorithm.centeredSubnode, Algorithm.centeredSubnodeLevel4]
  all_goals rfl

theorem f_centeredSubSubnodeFast_equiv (m : Algorithm.MacroCell) :
    runJvm 340 f_Algorithm_centeredSubSubnodeFast_prog (initJvmState [(0, .mc m)]) =
      some (.mc (Algorithm.centeredSubSubnodeFast m)) := by
  apply runJvm_of_runJvmValFast0 340 _ _ _ rfl
  step_mc_tree f_Algorithm_centeredSubSubnodeFast_prog
  all_goals rfl

set_option maxRecDepth 10000 in
theorem f_centeredSubSubnodeSizeFast_equiv (m : Algorithm.MacroCell) :
    runJvm 600 f_Algorithm_centeredSubSubnodeSizeFast_prog (initJvmState [(0, .mc m)]) =
      some (.i64 (Algorithm.centeredSubSubnodeSizeFast m)) := by
  apply runJvm_of_runJvmValFast0 600 _ _ _ rfl
  step_mc_tree f_Algorithm_centeredSubSubnodeSizeFast_prog
  all_goals rfl

private theorem shift_and_63_16 : ((16 : UInt32) &&& 63).toUInt64 = 16 := rfl
private theorem shift_and_63_32 : ((32 : UInt32) &&& 63).toUInt64 = 32 := rfl
private theorem shift_and_63_48 : ((48 : UInt32) &&& 63).toUInt64 = 48 := rfl

theorem stepQuadrants_equiv (m : Algorithm.MacroCell) (d : Nat) (hm : Algorithm.WFd m d) :
    runJvm 880 f_Algorithm_stepQuadrants_prog (initJvmState [(0, .mc m)]) =
      some (.stepQuad (Algorithm.stepQuadrants m)) := by
  apply runJvm_of_runJvmValFast0 880 _ _ _ rfl
  step_mc_tree f_Algorithm_stepQuadrants_prog
  all_goals
    first
    | (simp only [Algorithm.stepQuadrants]; done)
    | (have h5 : 5 ≤ d := by dsimp [Algorithm.WFd] at hm; exact hm.1
       have hcs := Algorithm.centeredSubSubnodeFast_eq_centeredSubSubnode_Impl hm h5
       first
       | (simp only [Algorithm.stepQuadrants, ← hcs]; done)
       | (simp only [Algorithm.stepQuadrants]
          simp only [Algorithm.centeredSubnodeLevel4,
            shift_and_63_16, shift_and_63_32, shift_and_63_48]))

theorem stepCellNodeWith_equiv (m : Algorithm.MacroCell) (d : Nat) (hm : Algorithm.WFd m d)
    (stepLevel4 : Algorithm.MacroCell → UInt64) (stepCell : Algorithm.MacroCell → Algorithm.MacroCell) :
    runJvm 920 f_Algorithm_stepCellNodeWith_prog
      (initJvmState [(0, .mc m), (1, .fnMcToU64 stepLevel4), (2, .fnMcToMc stepCell)]) =
      some (.mc (Algorithm.stepCellNodeWith m stepLevel4 stepCell)) := by
  apply runJvm_of_runJvmValFast0 920 _ _ _ rfl
  step_mc_tree f_Algorithm_stepCellNodeWith_prog
  all_goals
    first
    | (simp only [Algorithm.stepCellNodeWith]; done)
    | (have h5 : 5 ≤ d := by dsimp [Algorithm.WFd] at hm; exact hm.1
       have hcs := Algorithm.centeredSubSubnodeFast_eq_centeredSubSubnode_Impl hm h5
       first
       | (simp only [Algorithm.stepCellNodeWith, ← hcs]; done)
       | (simp only [Algorithm.stepCellNodeWith]
          simp only [Algorithm.centeredSubnodeLevel4,
            shift_and_63_16, shift_and_63_32, shift_and_63_48]))

/-! ### Sub-batch 2.3: FlatHashLife FWD methods -/

section SubBatch23
set_option maxHeartbeats 400000

private theorem lcmp_eq_zero (a b : UInt64) (c : Bool) :
    ((if (a == b) = true then (0 : UInt32) else if c = true then 4294967295 else 1) = 0) ↔ a = b := by
  by_cases h : a = b <;> cases c <;> simp [h]

private theorem u8_sext_eq_zero (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 0) ↔ b = 0 := by
  revert b; decide

private theorem u8_sext_eq_one (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 1) ↔ b = 1 := by
  revert b; decide

private theorem u8_sext_eq_five (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 5) ↔ b = 5 := by
  revert b; decide

private theorem u8_sext_eq_six (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 6) ↔ b = 6 := by
  revert b; decide

private theorem u8_sext_eq_seven (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 7) ↔ b = 7 := by
  revert b; decide

private theorem u8_sub1_u32_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((BitVec.setWidth 32 b.toBitVec &&& 255#32) - 1#32))) } : UInt8) = b - 1 := by
  revert b; decide

private theorem u8_sub1_sext_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 1#32))) } : UInt8) = b - 1 := by
  revert b; decide

private theorem u8_sub2_sext_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 2#32))) } : UInt8) = b - 2 := by
  revert b; decide

private theorem u8_add1_sext_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) + 1#32))) } : UInt8) = b + 1 := by
  revert b; decide

private theorem u8_add2_sext_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) + 2#32))) } : UInt8) = b + 2 := by
  revert b; decide

private theorem u8_and255_sext_jvm (b : UInt8) :
    (b.toInt8.toInt32.toUInt32 &&& 255) = b.toUInt32 := by
  revert b; decide

private theorem u8_sub1_and255_u32 (b : UInt8) :
    UInt32.ofBitVec ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 1#32) = b.toUInt32 - 1 := by
  revert b; decide

private theorem u8_sub5_and255_u32 (b : UInt8) :
    UInt32.ofBitVec ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 5#32) = b.toUInt32 - 5 := by
  revert b; decide

private theorem u8_sub1_sub5_and255_u32 (b : UInt8) :
    UInt32.ofBitVec (((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 1#32) - 5#32) = (b.toUInt32 - 1) - 5 := by
  revert b; decide

private theorem u8_ext_u32 (b : UInt8) :
    UInt32.ofBitVec (BitVec.setWidth 32 b.toBitVec) = b.toUInt32 := rfl

private theorem u8_sext_toUInt8 (b : UInt8) :
    b.toInt8.toInt32.toUInt32.toUInt8 = b := by
  revert b; decide

private theorem u8_sub1_u32_exact (b : UInt8) :
    ({ toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 (b.toUInt32 - 1).toBitVec) } : UInt32).toUInt8 = b - 1 := by
  revert b; decide

private theorem u8_sub2_u32_exact (b : UInt8) :
    ({ toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 (b.toUInt32 - 2).toBitVec) } : UInt32).toUInt8 = b - 2 := by
  revert b; decide

private theorem u8_add1_u32_exact (b : UInt8) :
    ({ toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 (b.toUInt32 + 1).toBitVec) } : UInt32).toUInt8 = b + 1 := by
  revert b; decide

private theorem u8_add2_u32_exact (b : UInt8) :
    ({ toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 (b.toUInt32 + 2).toBitVec) } : UInt32).toUInt8 = b + 2 := by
  revert b; decide

private def flatOpaqueConsts : Array Lean.Name := #[
  ``Algorithm.FlatHashLifeArena.internCellNode,
  ``Algorithm.FlatHashLifeArena.internLevel4,
  ``Algorithm.FlatHashLifeArena.expandFrame,
  ``Algorithm.FlatHashLifeArena.expandLevel4Centered,
  ``Algorithm.FlatHashLifeArena.centeredSubnode,
  ``Algorithm.FlatHashLifeArena.centeredHorizontal,
  ``Algorithm.FlatHashLifeArena.centeredVertical,
  ``Algorithm.FlatHashLifeArena.centeredSubSubnode,
  ``Algorithm.FlatHashLifeArena.quadrantNW,
  ``Algorithm.FlatHashLifeArena.quadrantNE,
  ``Algorithm.FlatHashLifeArena.quadrantSW,
  ``Algorithm.FlatHashLifeArena.quadrantSE,
  ``Algorithm.FlatHashLifeArena.stepLevel4,
  ``Algorithm.FlatHashLifeArena.copyL4From,
  ``Algorithm.FlatHashLifeArena.initRemapL4Loop,
  ``Algorithm.FlatHashLifeArena.initRemapCellLoop,
  ``Algorithm.FlatHashLifeArena.initEmptyNodesLoop,
  ``Algorithm.FlatHashLifeArena.copyCellFromLoop,
  ``Algorithm.FlatHashLifeArena.stepCellSerialLoop,
  ``Algorithm.FlatHashLifeArena.canCopySubgraphFrom,
  ``Algorithm.FlatHashLifeArena.setOverflow,
  ``Algorithm.FlatHashLifeArena.setRemapL4,
  ``Algorithm.FlatHashLifeArena.setRemapCell,
  ``Algorithm.FlatHashLifeArena.setCellStepRes,
  ``Algorithm.FlatHashLifeArena.setL4StepRes,
  ``Algorithm.getRemapCell,
  ``Algorithm.getCellStepRes,
  ``Algorithm.computeLevel4NextGen16x16UInt,
  ``Algorithm.centeredSubSubnodeSizeCell,
  ``Algorithm.emptyNodeForLevel,
  ``Algorithm.computePopulation,
  ``Algorithm.popLevel4Id,
  ``Algorithm.popCellId,
  ``Algorithm.centeredSubnodeLevel4, ``Algorithm.popcount64,
  ``Algorithm.copyCellTryStep,
  ``Algorithm.copySubgraphInto
]

private theorem ui32_toNat_add_1 (a : UInt32) : (a + 1).toNat = (a.toNat + 1) % 4294967296 :=
  UInt32.toNat_add a 1

private theorem ui32_toNat_add_2 (a : UInt32) : (a + 2).toNat = (a.toNat + 2) % 4294967296 :=
  UInt32.toNat_add a 2

private theorem ui32_toNat_add_3 (a : UInt32) : (a + 3).toNat = (a.toNat + 3) % 4294967296 :=
  UInt32.toNat_add a 3

private theorem ui32_toNat_add_4 (a : UInt32) : (a + 4).toNat = (a.toNat + 4) % 4294967296 :=
  UInt32.toNat_add a 4

private theorem beq_false_of_ne' {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) : (a == b) = false :=
  beq_false_of_ne h

private theorem bne_true_of_ne' {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) : (a != b) = true := by
  simp [bne, beq_false_of_ne h]

private theorem eq_of_ite_branches {α : Type} {c : Prop} [Decidable c] {t e rhs : α}
    (ht : c → t = rhs) (he : ¬c → e = rhs) : (if c then t else e) = rhs := by
  by_cases h : c <;> simp [h, ht, he]

private theorem compareUnsigned_eq_zero (a b : UInt32) :
    ((if a == b then (0 : UInt32) else if a < b then 4294967295 else 1) = 0) ↔ a = b := by
  by_cases h1 : a == b <;> by_cases h2 : a < b <;> simp [h1, h2]
  · exact LawfulBEq.eq_of_beq h1
  · exact LawfulBEq.eq_of_beq h1
  · exact fun heq => by subst heq; simp at h1
  · exact fun heq => by subst heq; simp at h1

private theorem compareUnsigned64_sge' (a b : UInt64) :
    (0#32).sle (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec = decide (b ≤ a) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b
    · have hlt' : ¬(b ≤ a) := Nat.not_le_of_gt h2
      simp [h1, h2, hlt']
    · have hle' : b ≤ a := Nat.le_of_not_lt h2
      simp [h1, h2, hle']

def isFlatStop : JvmInstr → Bool
  | .invokestatic _ _ _ => true
  | .invokevirtual _ _ _ => true
  | .invokespecial _ _ _ => true
  | .invokeinterface _ _ _ => true
  | i => isBranchInstr i

private theorem isBranchInstr_of_isFlatStop_false {i : JvmInstr} (h : isFlatStop i = false) :
    isBranchInstr i = false := by
  cases i <;> simp [isFlatStop, isBranchInstr] at h ⊢

def stepFlatChunk : Nat → Nat → Nat → List JvmInstr → JvmState → BlockChunkRes
  | _, 0, _, _, _ => .done none
  | 0, f1 + 1, pc, instrs, st => .cont (f1 + 1) pc instrs st
  | m + 1, f1 + 1, pc, instrs, st =>
    match instrs with
    | [] => .done none
    | instr :: rest =>
      if isFlatStop instr then .cont (f1 + 1) pc (instr :: rest) st
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
                stepFlatChunk m f3 (pc + 3) rest' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              | _ => .done none
        | _ =>
          match stepInstr instr { st with pc := pc } with
          | .inl (some st') =>
            if st'.pc = pc + 1 then stepFlatChunk m f1 (pc + 1) rest st'
            else .jump f1 st'
          | .inl none => .done none
          | .inr res => .done res
      | _ =>
        match stepInstr instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then stepFlatChunk m f1 (pc + 1) rest st'
          else .jump f1 st'
        | .inl none => .done none
        | .inr res => .done res

private theorem stepFlatChunk_cons_ne (m f1 pc : Nat) (instr : JvmInstr) (rest : List JvmInstr)
    (st : JvmState) (hno : ¬∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r') :
    stepFlatChunk (m + 1) (f1 + 1) pc (instr :: rest) st =
      if isFlatStop instr then .cont (f1 + 1) pc (instr :: rest) st
      else match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then stepFlatChunk m f1 (pc + 1) rest st'
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
        · simp [stepFlatChunk, hv]
  | _ => rfl

private theorem runJvmValFast_stepFlatChunk_aux (m : Nat) (fuel : Nat) (prog : List JvmInstr)
    (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    runJvmValFast fuel prog pc instrs st = afterBlockChunk (stepFlatChunk m fuel pc instrs st) prog := by
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
              simp only [runJvmValFast, stepFlatChunk, isFlatStop]
              cases st.stack with
              | nil => rfl
              | cons hd tl => cases hd with | i32 x => exact ih f3 (pc + 3) r' _ | _ => rfl
        · by_cases hst : isFlatStop instr = true
          · rw [stepFlatChunk_cons_ne m f1 pc instr rest st hpat]
            simp only [hst, ↓reduceIte, afterBlockChunk]
          · have hstf : isFlatStop instr = false := Bool.eq_false_iff.mpr hst
            have hbrf : isBranchInstr instr = false := isBranchInstr_of_isFlatStop_false hstf
            have hno' : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r') :=
              fun ⟨h1, r', h2⟩ => hpat ⟨r', h1, h2⟩
            rw [stepFlatChunk_cons_ne m f1 pc instr rest st hpat,
              runJvmValFast_step_nonbranch f1 prog pc instr rest st hbrf hno']
            simp only [hstf, Bool.false_eq_true, ↓reduceIte]
            cases hstep : stepInstr instr { st with pc := pc } with
            | inl o =>
              cases o with
              | none => rfl
              | some st' =>
                by_cases hpc : st'.pc = pc + 1
                · simp only [hpc, ↓reduceIte]; exact ih f1 (pc + 1) rest st'
                · simp only [hpc, ↓reduceIte, afterBlockChunk]
            | inr res => cases res <;> rfl

theorem runJvmValFast_stepFlatChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmValFast fuel prog pc instrs st = afterBlockChunk (stepFlatChunk maxSteps fuel pc instrs st) prog :=
  runJvmValFast_stepFlatChunk_aux maxSteps fuel prog pc instrs st

def stepResFlatChunk : Nat → Nat → Nat → List JvmInstr → JvmState → BlockResChunkRes
  | _, 0, _, _, _ => .done none
  | 0, f1 + 1, pc, instrs, st => .cont (f1 + 1) pc instrs st
  | m + 1, f1 + 1, pc, instrs, st =>
    match instrs with
    | [] => .done none
    | instr :: rest =>
      if isFlatStop instr then .cont (f1 + 1) pc (instr :: rest) st
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
                stepResFlatChunk m f3 (pc + 3) rest' { st with pc := pc + 3, stack := .i64 x.toUInt64 :: s }
              | _ => .done none
        | _ =>
          match stepInstr instr { st with pc := pc } with
          | .inl (some st') =>
            if st'.pc = pc + 1 then stepResFlatChunk m f1 (pc + 1) rest st'
            else .jump f1 st'
          | .inl none => .done none
          | .inr (some v) => .done (some (v, { st with pc := pc }))
          | .inr none => .done none
      | _ =>
        match stepInstr instr { st with pc := pc } with
        | .inl (some st') =>
          if st'.pc = pc + 1 then stepResFlatChunk m f1 (pc + 1) rest st'
          else .jump f1 st'
        | .inl none => .done none
        | .inr (some v) => .done (some (v, { st with pc := pc }))
        | .inr none => .done none

private theorem stepResFlatChunk_cons_ne (m f1 pc : Nat) (instr : JvmInstr) (rest : List JvmInstr)
    (st : JvmState) (hno : ¬∃ r', instr = .i2l ∧ rest = .lconst 4294967295 :: .land :: r') :
    stepResFlatChunk (m + 1) (f1 + 1) pc (instr :: rest) st =
      if isFlatStop instr then .cont (f1 + 1) pc (instr :: rest) st
      else match stepInstr instr { st with pc := pc } with
      | .inl (some st') =>
        if st'.pc = pc + 1 then stepResFlatChunk m f1 (pc + 1) rest st'
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
        · simp [stepResFlatChunk, hv]
  | _ => rfl

private theorem runJvmResFast_stepResFlatChunk_aux (m : Nat) (fuel : Nat) (prog : List JvmInstr)
    (pc : Nat) (instrs : List JvmInstr) (st : JvmState) :
    runJvmResFast fuel prog pc instrs st = afterResBlockChunk (stepResFlatChunk m fuel pc instrs st) prog := by
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
              simp only [runJvmResFast, stepResFlatChunk, isFlatStop]
              cases st.stack with
              | nil => rfl
              | cons hd tl => cases hd with | i32 x => exact ih f3 (pc + 3) r' _ | _ => rfl
        · by_cases hst : isFlatStop instr = true
          · rw [stepResFlatChunk_cons_ne m f1 pc instr rest st hpat]
            simp only [hst, ↓reduceIte, afterResBlockChunk]
          · have hstf : isFlatStop instr = false := Bool.eq_false_iff.mpr hst
            have hbrf : isBranchInstr instr = false := isBranchInstr_of_isFlatStop_false hstf
            have hno' : ¬(instr = .i2l ∧ ∃ r', rest = .lconst 4294967295 :: .land :: r') :=
              fun ⟨h1, r', h2⟩ => hpat ⟨r', h1, h2⟩
            rw [stepResFlatChunk_cons_ne m f1 pc instr rest st hpat,
              runJvmResFast_step_nonbranch f1 prog pc instr rest st hbrf hno']
            simp only [hstf, Bool.false_eq_true, ↓reduceIte]
            cases hstep : stepInstr instr { st with pc := pc } with
            | inl o =>
              cases o with
              | none => rfl
              | some st' =>
                by_cases hpc : st'.pc = pc + 1
                · simp only [hpc, ↓reduceIte]; exact ih f1 (pc + 1) rest st'
                · simp only [hpc, ↓reduceIte, afterResBlockChunk]
            | inr res => cases res <;> rfl

theorem runJvmResFast_stepResFlatChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmResFast fuel prog pc instrs st = afterResBlockChunk (stepResFlatChunk maxSteps fuel pc instrs st) prog :=
  runJvmResFast_stepResFlatChunk_aux maxSteps fuel prog pc instrs st

private theorem runJvmValFast_invokestatic_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {ar ar' : List Algorithm.FlatHashLifeArena}
    {u64 u64' : List (Array UInt64)} {asc asc' : List Algorithm.AsciiBytes}
    (hs : stepInvokeStatic ⟨pc, stk, locs, ar, u64, asc⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, ar', u64', asc'⟩)) :
    runJvmValFast (f1 + 1) prog pc (.invokestatic cls method desc :: rest) ⟨pc0, stk, locs, ar, u64, asc⟩ =
      runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, ar', u64', asc'⟩ := by
  simp only [runJvmValFast, stepInstr, hs, ↓reduceIte]

private theorem runJvmResFast_invokestatic_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {ar ar' : List Algorithm.FlatHashLifeArena}
    {u64 u64' : List (Array UInt64)} {asc asc' : List Algorithm.AsciiBytes}
    (hs : stepInvokeStatic ⟨pc, stk, locs, ar, u64, asc⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, ar', u64', asc'⟩)) :
    runJvmResFast (f1 + 1) prog pc (.invokestatic cls method desc :: rest) ⟨pc0, stk, locs, ar, u64, asc⟩ =
      runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, ar', u64', asc'⟩ := by
  simp only [runJvmResFast, stepInstr, hs, ↓reduceIte]

private theorem runJvmValFast_invokevirtual_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {ar ar' : List Algorithm.FlatHashLifeArena}
    {u64 u64' : List (Array UInt64)} {asc asc' : List Algorithm.AsciiBytes}
    (hs : stepInvokeVirtual ⟨pc, stk, locs, ar, u64, asc⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, ar', u64', asc'⟩)) :
    runJvmValFast (f1 + 1) prog pc (.invokevirtual cls method desc :: rest) ⟨pc0, stk, locs, ar, u64, asc⟩ =
      runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, ar', u64', asc'⟩ := by
  simp only [runJvmValFast, stepInstr, hs, ↓reduceIte]

private theorem runJvmResFast_invokevirtual_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {ar ar' : List Algorithm.FlatHashLifeArena}
    {u64 u64' : List (Array UInt64)} {asc asc' : List Algorithm.AsciiBytes}
    (hs : stepInvokeVirtual ⟨pc, stk, locs, ar, u64, asc⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, ar', u64', asc'⟩)) :
    runJvmResFast (f1 + 1) prog pc (.invokevirtual cls method desc :: rest) ⟨pc0, stk, locs, ar, u64, asc⟩ =
      runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, ar', u64', asc'⟩ := by
  simp only [runJvmResFast, stepInstr, hs, ↓reduceIte]

private theorem runJvmValFast_invokespecial_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {ar ar' : List Algorithm.FlatHashLifeArena}
    {u64 u64' : List (Array UInt64)} {asc asc' : List Algorithm.AsciiBytes}
    (hs : stepInvokeSpecial ⟨pc, stk, locs, ar, u64, asc⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, ar', u64', asc'⟩)) :
    runJvmValFast (f1 + 1) prog pc (.invokespecial cls method desc :: rest) ⟨pc0, stk, locs, ar, u64, asc⟩ =
      runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, ar', u64', asc'⟩ := by
  simp only [runJvmValFast, stepInstr, hs, ↓reduceIte]

private theorem runJvmResFast_invokespecial_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {ar ar' : List Algorithm.FlatHashLifeArena}
    {u64 u64' : List (Array UInt64)} {asc asc' : List Algorithm.AsciiBytes}
    (hs : stepInvokeSpecial ⟨pc, stk, locs, ar, u64, asc⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, ar', u64', asc'⟩)) :
    runJvmResFast (f1 + 1) prog pc (.invokespecial cls method desc :: rest) ⟨pc0, stk, locs, ar, u64, asc⟩ =
      runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, ar', u64', asc'⟩ := by
  simp only [runJvmResFast, stepInstr, hs, ↓reduceIte]

private theorem runJvmValFast_invokeinterface_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {ar ar' : List Algorithm.FlatHashLifeArena}
    {u64 u64' : List (Array UInt64)} {asc asc' : List Algorithm.AsciiBytes}
    (hs : stepInvokeInterface ⟨pc, stk, locs, ar, u64, asc⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, ar', u64', asc'⟩)) :
    runJvmValFast (f1 + 1) prog pc (.invokeinterface cls method desc :: rest) ⟨pc0, stk, locs, ar, u64, asc⟩ =
      runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, ar', u64', asc'⟩ := by
  simp only [runJvmValFast, stepInstr, hs, ↓reduceIte]

private theorem runJvmResFast_invokeinterface_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {ar ar' : List Algorithm.FlatHashLifeArena}
    {u64 u64' : List (Array UInt64)} {asc asc' : List Algorithm.AsciiBytes}
    (hs : stepInvokeInterface ⟨pc, stk, locs, ar, u64, asc⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, ar', u64', asc'⟩)) :
    runJvmResFast (f1 + 1) prog pc (.invokeinterface cls method desc :: rest) ⟨pc0, stk, locs, ar, u64, asc⟩ =
      runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, ar', u64', asc'⟩ := by
  simp only [runJvmResFast, stepInstr, hs, ↓reduceIte]

private theorem updateArena_eq_some {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {id : Nat} {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a)
    (f : Algorithm.FlatHashLifeArena → Algorithm.FlatHashLifeArena) :
    updateArena ⟨pc, stk, locs, ar, u64, asc⟩ id f =
      some ⟨pc + 1, stk, locs, ar.set id (f a), u64, asc⟩ := by
  simp only [updateArena, har]

private theorem stepStatic_checkNotNullParameter
    {pc : Nat} {msg obj : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hnull : obj.isNull = false) :
    stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, ar, u64, asc⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, ar, u64, asc⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      (if obj.isNull then .inr none else .inl (some ⟨pc + 1, rest, locs, ar, u64, asc⟩)) := rfl
  rw [hfn, hnull]; rfl

private theorem stepStatic_uintCtor
    {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, stk, locs, ar, u64, asc⟩
      "kotlin/UInt" "constructor-impl" "(I)I" =
      .inl (some ⟨pc + 1, stk, locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_ulongCtor
    {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, stk, locs, ar, u64, asc⟩
      "kotlin/ULong" "constructor-impl" "(J)J" =
      .inl (some ⟨pc + 1, stk, locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_ubyteCtor
    {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, stk, locs, ar, u64, asc⟩
      "kotlin/UByte" "constructor-impl" "(B)B" =
      .inl (some ⟨pc + 1, stk, locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_intCompareUnsigned
    {pc : Nat} {b a : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, b :: a :: rest, locs, ar, u64, asc⟩
      "java/lang/Integer" "compareUnsigned" "(II)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a.asI32 == b.asI32 then 0 else if a.asI32 < b.asI32 then 4294967295 else 1) :: rest,
        locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_intDivideUnsigned
    {pc : Nat} {b a : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, b :: a :: rest, locs, ar, u64, asc⟩
      "java/lang/Integer" "divideUnsigned" "(II)I" =
      .inl (some ⟨pc + 1, .i32 (a.asI32 / b.asI32) :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_uintArrGet
    {pc : Nat} {idx : JvmVal} {id : Nat} {f : ArenaU32Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, idx :: .arenaU32Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/UIntArray" "get-pVg5ArA" "([II)I" =
      .inl (some ⟨pc + 1, .i32 ((getArenaU32 a f)[idx.asI32.toNat]!) :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, idx :: .arenaU32Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/UIntArray" "get-pVg5ArA" "([II)I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 ((getArenaU32 a f)[idx.asI32.toNat]!) :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_uintArrGetSize
    {pc : Nat} {id : Nat} {f : ArenaU32Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .arenaU32Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/UIntArray" "getSize-impl" "([I)I" =
      .inl (some ⟨pc + 1, .i32 (getArenaU32 a f).size.toUInt32 :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .arenaU32Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/UIntArray" "getSize-impl" "([I)I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 (getArenaU32 a f).size.toUInt32 :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_ubyteArrGet
    {pc : Nat} {idx : JvmVal} {id : Nat} {f : ArenaU8Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, idx :: .arenaU8Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/UByteArray" "get-w2LRezQ" "([BI)B" =
      .inl (some ⟨pc + 1, .i32 ((getArenaU8 a f)[idx.asI32.toNat]!).toInt8.toInt32.toUInt32 :: rest,
        locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, idx :: .arenaU8Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/UByteArray" "get-w2LRezQ" "([BI)B" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 ((getArenaU8 a f)[idx.asI32.toNat]!).toInt8.toInt32.toUInt32 :: rest,
          locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_ulongArrGetArena
    {pc : Nat} {idx : JvmVal} {id : Nat} {f : ArenaU64Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, idx :: .arenaU64Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" =
      .inl (some ⟨pc + 1, .i64 ((getArenaU64 a f)[idx.asI32.toNat]!) :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, idx :: .arenaU64Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i64 ((getArenaU64 a f)[idx.asI32.toNat]!) :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_ulongArrGetU64
    {pc : Nat} {idx : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {arr : Array UInt64} (hu : u64[id]? = some arr) :
    stepInvokeStatic ⟨pc, idx :: .u64Ref id :: rest, locs, ar, u64, asc⟩
      "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" =
      .inl (some ⟨pc + 1, .i64 (arr[idx.asI32.toNat]!) :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, idx :: .u64Ref id :: rest, locs, ar, u64, asc⟩
      "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" =
      match u64[id]? with
      | some arr => .inl (some ⟨pc + 1, .i64 (arr[idx.asI32.toNat]!) :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, hu]

private theorem stepStatic_ulongArrSetU64
    {pc : Nat} {val idx : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {arr : Array UInt64} (hu : u64[id]? = some arr) :
    stepInvokeStatic ⟨pc, val :: idx :: .u64Ref id :: rest, locs, ar, u64, asc⟩
      "kotlin/ULongArray" "set-k8EXiF4" "([JIJ)V" =
      .inl (some ⟨pc + 1, rest, locs, ar, u64.set id (arr.set! idx.asI32.toNat val.asI64), asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, val :: idx :: .u64Ref id :: rest, locs, ar, u64, asc⟩
      "kotlin/ULongArray" "set-k8EXiF4" "([JIJ)V" =
      match u64[id]? with
      | some arr => .inl (some ⟨pc + 1, rest, locs, ar, u64.set id (arr.set! idx.asI32.toNat val.asI64), asc⟩)
      | none => .inr none := rfl
  rw [hfn, hu]

private theorem stepStatic_ulongArrSetArena
    {pc : Nat} {val idx : JvmVal} {id : Nat} {f : ArenaU64Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, val :: idx :: .arenaU64Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/ULongArray" "set-k8EXiF4" "([JIJ)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id (setArenaU64 a f ((getArenaU64 a f).set! idx.asI32.toNat val.asI64)), u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, val :: idx :: .arenaU64Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/ULongArray" "set-k8EXiF4" "([JIJ)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => setArenaU64 a f ((getArenaU64 a f).set! idx.asI32.toNat val.asI64))) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_uintArrSet
    {pc : Nat} {val idx : JvmVal} {id : Nat} {f : ArenaU32Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, val :: idx :: .arenaU32Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/UIntArray" "set-VXSXFK8" "([III)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id (setArenaU32 a f ((getArenaU32 a f).set! idx.asI32.toNat val.asI32)), u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, val :: idx :: .arenaU32Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/UIntArray" "set-VXSXFK8" "([III)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => setArenaU32 a f ((getArenaU32 a f).set! idx.asI32.toNat val.asI32))) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_ubyteArrSet
    {pc : Nat} {val idx : JvmVal} {id : Nat} {f : ArenaU8Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, val :: idx :: .arenaU8Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/UByteArray" "set-VurrAj0" "([BIB)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id (setArenaU8 a f ((getArenaU8 a f).set! idx.asI32.toNat val.asI32.toUInt8)), u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, val :: idx :: .arenaU8Ref id f :: rest, locs, ar, u64, asc⟩
      "kotlin/UByteArray" "set-VurrAj0" "([BIB)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => setArenaU8 a f ((getArenaU8 a f).set! idx.asI32.toNat val.asI32.toUInt8))) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_checkNotNull
    {pc : Nat} {msg obj : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hnull : obj.isNull = false) :
    stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, ar, u64, asc⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, ar, u64, asc⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      (if obj.isNull then .inr none else .inl (some ⟨pc + 1, rest, locs, ar, u64, asc⟩)) := rfl
  rw [hfn, hnull]; rfl

private theorem stepStatic_intrinsicsCompare
    {pc : Nat} {b a : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, b :: a :: rest, locs, ar, u64, asc⟩
      "kotlin/jvm/internal/Intrinsics" "compare" "(II)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a.asI32 == b.asI32 then 0 else if a.asI32.toBitVec.slt b.asI32.toBitVec then 4294967295 else 1) :: rest,
        locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_longCompareUnsigned
    {pc : Nat} {b a : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, b :: a :: rest, locs, ar, u64, asc⟩
      "java/lang/Long" "compareUnsigned" "(JJ)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a.asI64 == b.asI64 then 0 else if a.asI64 < b.asI64 then 4294967295 else 1) :: rest,
        locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_intValueOf
    {pc : Nat} {v : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, v :: rest, locs, ar, u64, asc⟩
      "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" =
      .inl (some ⟨pc + 1, .boxedInt v.asI32 :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_ulongBox
    {pc : Nat} {v : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, v :: rest, locs, ar, u64, asc⟩
      "kotlin/ULong" "box-impl" "(J)Lkotlin/ULong;" =
      .inl (some ⟨pc + 1, .boxedULong v.asI64 :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_flat_getRemapCell
    {pc : Nat} {nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_getRemapCell-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.getRemapCell a nodeId.asI32) :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_getRemapCell-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 (Algorithm.getRemapCell a nodeId.asI32) :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_getCellStepRes
    {pc : Nat} {nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_getCellStepRes-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.getCellStepRes a nodeId.asI32) :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_getCellStepRes-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 (Algorithm.getCellStepRes a nodeId.asI32) :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_centeredSubSubnodeSizeCell
    {pc : Nat} {nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_centeredSubSubnodeSizeCell-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)J" =
      .inl (some ⟨pc + 1, .i64 (Algorithm.centeredSubSubnodeSizeCell a nodeId.asI32) :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_centeredSubSubnodeSizeCell-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)J" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i64 (Algorithm.centeredSubSubnodeSizeCell a nodeId.asI32) :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_computeLevel4NextGen
    {pc : Nat} {se sw ne nw : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, se :: sw :: ne :: nw :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0-2jIhpxI"
      "(JJJJ)J" =
      .inl (some ⟨pc + 1,
        .i64 (Algorithm.computeLevel4NextGen16x16UInt nw.asI64 ne.asI64 sw.asI64 se.asI64) :: rest,
        locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_flat_centeredHorizontal
    {pc : Nat} {eId wId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, eId :: wId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredHorizontal-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.centeredHorizontal wId.asI32 eId.asI32).1 :: rest, locs,
        ar.set id (a.centeredHorizontal wId.asI32 eId.asI32).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, eId :: wId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredHorizontal-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.centeredHorizontal wId.asI32 eId.asI32
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_centeredVertical
    {pc : Nat} {sId nId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, sId :: nId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredVertical-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.centeredVertical nId.asI32 sId.asI32).1 :: rest, locs,
        ar.set id (a.centeredVertical nId.asI32 sId.asI32).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, sId :: nId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredVertical-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.centeredVertical nId.asI32 sId.asI32
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_centeredSubnode
    {pc : Nat} {nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredSubnode-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.centeredSubnode nodeId.asI32).1 :: rest, locs,
        ar.set id (a.centeredSubnode nodeId.asI32).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredSubnode-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.centeredSubnode nodeId.asI32
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_centeredSubSubnode
    {pc : Nat} {nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredSubSubnode-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.centeredSubSubnode nodeId.asI32).1 :: rest, locs,
        ar.set id (a.centeredSubSubnode nodeId.asI32).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredSubSubnode-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.centeredSubSubnode nodeId.asI32
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_quadrantNW
    {pc : Nat} {nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantNW-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.quadrantNW nodeId.asI32).1 :: rest, locs,
        ar.set id (a.quadrantNW nodeId.asI32).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantNW-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.quadrantNW nodeId.asI32
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_quadrantNE
    {pc : Nat} {nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantNE-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.quadrantNE nodeId.asI32).1 :: rest, locs,
        ar.set id (a.quadrantNE nodeId.asI32).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantNE-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.quadrantNE nodeId.asI32
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_quadrantSW
    {pc : Nat} {nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantSW-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.quadrantSW nodeId.asI32).1 :: rest, locs,
        ar.set id (a.quadrantSW nodeId.asI32).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantSW-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.quadrantSW nodeId.asI32
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_quadrantSE
    {pc : Nat} {nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantSE-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.quadrantSE nodeId.asI32).1 :: rest, locs,
        ar.set id (a.quadrantSE nodeId.asI32).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantSE-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.quadrantSE nodeId.asI32
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_stepLevel4
    {pc : Nat} {l4Id : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, l4Id :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_stepLevel4-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)J" =
      .inl (some ⟨pc + 1,
        .i64 (a.stepLevel4 l4Id.asI32).1 :: rest, locs,
        ar.set id (a.stepLevel4 l4Id.asI32).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, l4Id :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_stepLevel4-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)J" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.stepLevel4 l4Id.asI32
        .inl (some ⟨pc + 1, .i64 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_stepLevel5
    {pc : Nat} {nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_stepLevel5-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.stepLevel5 nodeId.asI32).1 :: rest, locs,
        ar.set id (a.stepLevel5 nodeId.asI32).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_stepLevel5-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.stepLevel5 nodeId.asI32
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_setRemapL4
    {pc : Nat} {val idx : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, val :: idx :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setRemapL4-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id (a.setRemapL4 idx.asI32 val.asI32), u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, val :: idx :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setRemapL4-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => a.setRemapL4 idx.asI32 val.asI32)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_setRemapCell
    {pc : Nat} {val idx : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, val :: idx :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setRemapCell-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id (a.setRemapCell idx.asI32 val.asI32), u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, val :: idx :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setRemapCell-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => a.setRemapCell idx.asI32 val.asI32)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_setCellStepRes
    {pc : Nat} {val idx : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, val :: idx :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setCellStepRes-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id (a.setCellStepRes idx.asI32 val.asI32), u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, val :: idx :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setCellStepRes-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => a.setCellStepRes idx.asI32 val.asI32)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_setL4StepRes
    {pc : Nat} {val idx : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, val :: idx :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setL4StepRes-c82oGLE"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IJ)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id (a.setL4StepRes idx.asI32 val.asI64), u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, val :: idx :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setL4StepRes-c82oGLE"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IJ)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => a.setL4StepRes idx.asI32 val.asI64)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_setOverflow
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setOverflow"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id a.setOverflow, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setOverflow"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => a.setOverflow)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_expandFrame
    {pc : Nat} {base nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, base :: nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_expandFrame-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id (a.expandFrame nodeId.asI32 base.asI32), u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, base :: nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_expandFrame-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => a.expandFrame nodeId.asI32 base.asI32)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_initRemapL4Loop
    {pc : Nat} {limit i : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, limit :: i :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_initRemapL4Loop-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id (a.initRemapL4Loop i.asI32 limit.asI32), u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, limit :: i :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_initRemapL4Loop-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => a.initRemapL4Loop i.asI32 limit.asI32)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_initRemapCellLoop
    {pc : Nat} {limit i : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, limit :: i :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_initRemapCellLoop-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id (a.initRemapCellLoop i.asI32 limit.asI32), u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, limit :: i :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_initRemapCellLoop-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => a.initRemapCellLoop i.asI32 limit.asI32)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_stepCellSerialLoop
    {pc : Nat} {fuel limit sp : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, fuel :: limit :: sp :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_stepCellSerialLoop-7IvYBaQ"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;III)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id (a.stepCellSerialLoop sp.asI32 limit.asI32 fuel.asI32), u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, fuel :: limit :: sp :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_stepCellSerialLoop-7IvYBaQ"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;III)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => a.stepCellSerialLoop sp.asI32 limit.asI32 fuel.asI32)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_copyL4From
    {pc : Nat} {copyMemos l4Id : JvmVal} {srcId dstId : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {dst src : Algorithm.FlatHashLifeArena} (hdst : ar[dstId]? = some dst) (hsrc : ar[srcId]? = some src) :
    stepInvokeStatic ⟨pc, copyMemos :: l4Id :: .arenaRef srcId :: .arenaRef dstId :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_copyL4From-BzPDsQc"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IZ)I" =
      .inl (some ⟨pc + 1,
        .i32 (dst.copyL4From src l4Id.asI32 (copyMemos.asI32 != 0)).1 :: rest, locs,
        ar.set dstId (dst.copyL4From src l4Id.asI32 (copyMemos.asI32 != 0)).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, copyMemos :: l4Id :: .arenaRef srcId :: .arenaRef dstId :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_copyL4From-BzPDsQc"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IZ)I" =
      match ar[dstId]?, ar[srcId]? with
      | some dst, some src =>
        let (r, dst') := dst.copyL4From src l4Id.asI32 (copyMemos.asI32 != 0)
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set dstId dst', u64, asc⟩)
      | _, _ => .inr none := rfl
  rw [hfn, hdst, hsrc]

private theorem stepStatic_flat_copyCellFromLoop
    {pc : Nat} {fuel sp stackBase copyMemos : JvmVal} {srcId dstId : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)}
    {asc : List Algorithm.AsciiBytes} {dst src : Algorithm.FlatHashLifeArena}
    (hdst : ar[dstId]? = some dst) (hsrc : ar[srcId]? = some src) :
    stepInvokeStatic ⟨pc, fuel :: sp :: stackBase :: copyMemos :: .arenaRef srcId :: .arenaRef dstId :: rest,
        locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_copyCellFromLoop-sA3nruY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;ZIII)V" =
      .inl (some ⟨pc + 1, rest, locs,
        ar.set dstId (dst.copyCellFromLoop src (copyMemos.asI32 != 0) stackBase.asI32 sp.asI32 fuel.asI32),
        u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, fuel :: sp :: stackBase :: copyMemos :: .arenaRef srcId :: .arenaRef dstId :: rest,
        locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_copyCellFromLoop-sA3nruY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;ZIII)V" =
      match ar[dstId]?, ar[srcId]? with
      | some dst, some src =>
        .inl (some ⟨pc + 1, rest, locs,
          ar.set dstId (dst.copyCellFromLoop src (copyMemos.asI32 != 0) stackBase.asI32 sp.asI32 fuel.asI32),
          u64, asc⟩)
      | _, _ => .inr none := rfl
  rw [hfn, hdst, hsrc]

private theorem stepVirtual_arena_canCopySubgraphFrom
    {pc : Nat} {srcId dstId : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {dst src : Algorithm.FlatHashLifeArena} (hdst : ar[dstId]? = some dst) (hsrc : ar[srcId]? = some src) :
    stepInvokeVirtual ⟨pc, .arenaRef srcId :: .arenaRef dstId :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena"
      "canCopySubgraphFrom" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;)Z" =
      .inl (some ⟨pc + 1, .i32 (if dst.canCopySubgraphFrom src then 1 else 0) :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, .arenaRef srcId :: .arenaRef dstId :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena"
      "canCopySubgraphFrom" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;)Z" =
      match ar[dstId]?, ar[srcId]? with
      | some dst, some src =>
        .inl (some ⟨pc + 1, .i32 (if dst.canCopySubgraphFrom src then 1 else 0) :: rest, locs, ar, u64, asc⟩)
      | _, _ => .inr none := rfl
  rw [hfn, hdst, hsrc]

private theorem stepVirtual_arena_getCellCount
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellCount-pVg5ArA" "()I" =
      .inl (some ⟨pc + 1, .i32 a.cellCount :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellCount-pVg5ArA" "()I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 a.cellCount :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepVirtual_arena_getCellMask
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellMask-pVg5ArA" "()I" =
      .inl (some ⟨pc + 1, .i32 a.cellMask :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellMask-pVg5ArA" "()I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 a.cellMask :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepVirtual_arena_getL4Count
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Count-pVg5ArA" "()I" =
      .inl (some ⟨pc + 1, .i32 a.l4Count :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Count-pVg5ArA" "()I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 a.l4Count :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepVirtual_arena_getOverflow
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getOverflow-w2LRezQ" "()B" =
      .inl (some ⟨pc + 1, .i32 a.overflow.toInt8.toInt32.toUInt32 :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getOverflow-w2LRezQ" "()B" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 a.overflow.toInt8.toInt32.toUInt32 :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepVirtual_arena_getCellLevel
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellLevel-TcUX1vc" "()[B" =
      .inl (some ⟨pc + 1, .arenaU8Ref id .cellLevel :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getL4HasRes
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4HasRes-TcUX1vc" "()[B" =
      .inl (some ⟨pc + 1, .arenaU8Ref id .l4HasRes :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getCellNe
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellNe--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, .arenaU32Ref id .cellNe :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getCellNw
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellNw--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, .arenaU32Ref id .cellNw :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getCellSw
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellSw--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, .arenaU32Ref id .cellSw :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getCellSe
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellSe--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, .arenaU32Ref id .cellSe :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getCellStepRes
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellStepRes--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, .arenaU32Ref id .cellStepRes :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getRemapCell
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getRemapCell--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, .arenaU32Ref id .remapCell :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getRemapL4
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getRemapL4--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, .arenaU32Ref id .remapL4 :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getCellPop
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellPop-Y2RjT0g" "()[J" =
      .inl (some ⟨pc + 1, .arenaU64Ref id .cellPop :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getL4Nw
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Nw-Y2RjT0g" "()[J" =
      .inl (some ⟨pc + 1, .arenaU64Ref id .l4Nw :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getL4Ne
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Ne-Y2RjT0g" "()[J" =
      .inl (some ⟨pc + 1, .arenaU64Ref id .l4Ne :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getL4Sw
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Sw-Y2RjT0g" "()[J" =
      .inl (some ⟨pc + 1, .arenaU64Ref id .l4Sw :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getL4Se
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Se-Y2RjT0g" "()[J" =
      .inl (some ⟨pc + 1, .arenaU64Ref id .l4Se :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getL4StepRes
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4StepRes-Y2RjT0g" "()[J" =
      .inl (some ⟨pc + 1, .arenaU64Ref id .l4StepRes :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_internCellNode
    {pc : Nat} {se sw ne nw lvl : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeVirtual ⟨pc, se :: sw :: ne :: nw :: lvl :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "internCellNode-gt5aIGQ" "(BIIII)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.internCellNode lvl.asI32.toUInt8 nw.asI32 ne.asI32 sw.asI32 se.asI32).1 :: rest, locs,
        ar.set id (a.internCellNode lvl.asI32.toUInt8 nw.asI32 ne.asI32 sw.asI32 se.asI32).2, u64, asc⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, se :: sw :: ne :: nw :: lvl :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "internCellNode-gt5aIGQ" "(BIIII)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.internCellNode lvl.asI32.toUInt8 nw.asI32 ne.asI32 sw.asI32 se.asI32
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepVirtual_arena_internLevel4
    {pc : Nat} {se sw ne nw : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeVirtual ⟨pc, se :: sw :: ne :: nw :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "internLevel4-PT-fW9Q" "(JJJJ)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.internLevel4 nw.asI64 ne.asI64 sw.asI64 se.asI64).1 :: rest, locs,
        ar.set id (a.internLevel4 nw.asI64 ne.asI64 sw.asI64 se.asI64).2, u64, asc⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, se :: sw :: ne :: nw :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "internLevel4-PT-fW9Q" "(JJJJ)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.internLevel4 nw.asI64 ne.asI64 sw.asI64 se.asI64
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_expandFrameIfNeeded
    {pc : Nat} {base nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, base :: nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, ar.set id (a.expandFrameIfNeeded nodeId.asI32 base.asI32), u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, base :: nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, ar, u64, asc⟩ id (fun a => a.expandFrameIfNeeded nodeId.asI32 base.asI32)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_combineQuadrants
    {pc : Nat} {se sw ne nw lvl nodeId : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, se :: sw :: ne :: nw :: lvl :: nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_combineQuadrants-t447iZE"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IBIIII)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.combineQuadrants nodeId.asI32 lvl.asI32.toUInt8 nw.asI32 ne.asI32 sw.asI32 se.asI32).1 :: rest, locs,
        ar.set id (a.combineQuadrants nodeId.asI32 lvl.asI32.toUInt8 nw.asI32 ne.asI32 sw.asI32 se.asI32).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, se :: sw :: ne :: nw :: lvl :: nodeId :: .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_combineQuadrants-t447iZE"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IBIIII)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.combineQuadrants nodeId.asI32 lvl.asI32.toUInt8 nw.asI32 ne.asI32 sw.asI32 se.asI32
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set id a', u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_copyCellTryStep
    {pc : Nat} {copyMemos cellId : JvmVal} {srcId dstId : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {dst src : Algorithm.FlatHashLifeArena} (hdst : ar[dstId]? = some dst) (hsrc : ar[srcId]? = some src) :
    stepInvokeStatic ⟨pc, copyMemos :: cellId :: .arenaRef srcId :: .arenaRef dstId :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_copyCellTryStep-BzPDsQc"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IZ)I" =
      .inl (some ⟨pc + 1,
        .i32 (Algorithm.copyCellTryStep dst src cellId.asI32 (copyMemos.asI32 != 0)).1 :: rest, locs,
        ar.set dstId (Algorithm.copyCellTryStep dst src cellId.asI32 (copyMemos.asI32 != 0)).2, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, copyMemos :: cellId :: .arenaRef srcId :: .arenaRef dstId :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_copyCellTryStep-BzPDsQc"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IZ)I" =
      match ar[dstId]?, ar[srcId]? with
      | some dst, some src =>
        let (r, dst') := Algorithm.copyCellTryStep dst src cellId.asI32 (copyMemos.asI32 != 0)
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, ar.set dstId dst', u64, asc⟩)
      | _, _ => .inr none := rfl
  rw [hfn, hdst, hsrc]

private theorem stepStatic_flat_leafContains
    {pc : Nat} {y x leaf : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, y :: x :: leaf :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_leafContains-fMEO4hA" "(JII)Z" =
      .inl (some ⟨pc + 1, .i32 (if Algorithm.leafContains leaf.asI64 x.asI32 y.asI32 then 1 else 0) :: rest,
        locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_makeCellNode
    {pc : Nat} {se sw ne nw : Algorithm.MacroCell} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .mc se :: .mc sw :: .mc ne :: .mc nw :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt"
      "f_Algorithm_makeCellNode"
      "(Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;)Lcom/alexvanyo/composelife/model/MacroCell;" =
      .inl (some ⟨pc + 1, .mc (Algorithm.makeCellNode nw ne sw se) :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_decodeCharAt
    {pc : Nat} {limit p : JvmVal} {bytes : ByteArray} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, limit :: p :: .byteArr bytes :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/PlaintextLeanKt"
      "f_Algorithm_decodeCharAt-BltQuoY" "([BII)Lkotlin/Pair;" =
      .inl (some ⟨pc + 1,
        .pair (.boxedUInt (Algorithm.decodeCharAt bytes p.asI32 limit.asI32).1)
          (.boxedUInt (Algorithm.decodeCharAt bytes p.asI32 limit.asI32).2) :: rest,
        locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_formatCoordLine
    {pc : Nat} {y x : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, y :: x :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/Life106LeanKt"
      "f_Algorithm_formatCoordLine-feOb9K0" "(II)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (Algorithm.formatCoordLine x.asI32 y.asI32) :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_growBufPush_105
    {pc : Nat} {s : String} {b : Algorithm.GrowBuf String} {rest : List JvmVal}
    {locs : Nat → JvmVal} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .str s :: .strGrowBuf b :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_GrowBuf_push___redArg" "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .strGrowBuf (b.push s) :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_growBufPush_106
    {pc : Nat} {s : String} {b : Algorithm.GrowBuf String} {rest : List JvmVal}
    {locs : Nat → JvmVal} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .str s :: .strGrowBuf b :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/Life106LeanKt"
      "f_Algorithm_GrowBuf_push___redArg" "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .strGrowBuf (b.push s) :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_growBufPush_plain
    {pc : Nat} {s : String} {b : Algorithm.GrowBuf String} {rest : List JvmVal}
    {locs : Nat → JvmVal} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .str s :: .strGrowBuf b :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/PlaintextLeanKt"
      "f_Algorithm_GrowBuf_push___redArg" "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .strGrowBuf (b.push s) :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepStatic_u64BufPush_105
    {pc : Nat} {x : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {arr : Array UInt64} (hu : u64[id]? = some arr) :
    stepInvokeStatic ⟨pc, x :: .u64Ref id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_U64Buf_push-3yFGk1Y" "([JJ)[J" =
      .inl (some ⟨pc + 1, .u64Ref u64.length :: rest, locs, ar,
        u64 ++ [Algorithm.U64Buf.push arr x.asI64], asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, x :: .u64Ref id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_U64Buf_push-3yFGk1Y" "([JJ)[J" =
      match u64[id]? with
      | some arr => .inl (some ⟨pc + 1, .u64Ref u64.length :: rest, locs, ar,
          u64 ++ [Algorithm.U64Buf.push arr x.asI64], asc⟩)
      | none => .inr none := rfl
  rw [hfn, hu]

private theorem stepStatic_asciiToStringRange_105
    {pc : Nat} {e s : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {g : Algorithm.AsciiBytes} (hasc : asc[id]? = some g) :
    stepInvokeStatic ⟨pc, e :: s :: .asciiRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_AsciiBytes_toStringRange-BltQuoY" "([BII)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (g.toStringRange s.asI32 e.asI32) :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, e :: s :: .asciiRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_AsciiBytes_toStringRange-BltQuoY" "([BII)Ljava/lang/String;" =
      match asc[id]? with
      | some g => .inl (some ⟨pc + 1, .str (g.toStringRange s.asI32 e.asI32) :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, hasc]

private theorem stepStatic_asciiToStringRange_plain
    {pc : Nat} {e s : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {g : Algorithm.AsciiBytes} (hasc : asc[id]? = some g) :
    stepInvokeStatic ⟨pc, e :: s :: .asciiRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/PlaintextLeanKt"
      "f_Algorithm_AsciiBytes_toStringRange-BltQuoY" "([BII)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (g.toStringRange s.asI32 e.asI32) :: rest, locs, ar, u64, asc⟩) := by
  have hfn : stepInvokeStatic ⟨pc, e :: s :: .asciiRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/PlaintextLeanKt"
      "f_Algorithm_AsciiBytes_toStringRange-BltQuoY" "([BII)Ljava/lang/String;" =
      match asc[id]? with
      | some g => .inl (some ⟨pc + 1, .str (g.toStringRange s.asI32 e.asI32) :: rest, locs, ar, u64, asc⟩)
      | none => .inr none := rfl
  rw [hfn, hasc]

private theorem stepStatic_asciiSet_105
    {pc : Nat} {v i : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {g : Algorithm.AsciiBytes} (hasc : asc[id]? = some g) (hb : v.asI32.toUInt8 < 128) :
    stepInvokeStatic ⟨pc, v :: i :: .asciiRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" =
      .inl (some ⟨pc + 1, rest, locs, ar, u64, asc.set id (g.set i.asI32 v.asI32.toUInt8 hb)⟩) := by
  have hfn : stepInvokeStatic ⟨pc, v :: i :: .asciiRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" =
      match asc[id]? with
      | some g =>
        if hb' : v.asI32.toUInt8 < 128 then
          .inl (some ⟨pc + 1, rest, locs, ar, u64, asc.set id (g.set i.asI32 v.asI32.toUInt8 hb')⟩)
        else .inr none
      | none => .inr none := rfl
  rw [hfn, hasc]; simp only [hb, ↓reduceDIte]

private theorem stepStatic_asciiSet_plain
    {pc : Nat} {v i : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {g : Algorithm.AsciiBytes} (hasc : asc[id]? = some g) (hb : v.asI32.toUInt8 < 128) :
    stepInvokeStatic ⟨pc, v :: i :: .asciiRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/PlaintextLeanKt"
      "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" =
      .inl (some ⟨pc + 1, rest, locs, ar, u64, asc.set id (g.set i.asI32 v.asI32.toUInt8 hb)⟩) := by
  have hfn : stepInvokeStatic ⟨pc, v :: i :: .asciiRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/PlaintextLeanKt"
      "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" =
      match asc[id]? with
      | some g =>
        if hb' : v.asI32.toUInt8 < 128 then
          .inl (some ⟨pc + 1, rest, locs, ar, u64, asc.set id (g.set i.asI32 v.asI32.toUInt8 hb')⟩)
        else .inr none
      | none => .inr none := rfl
  rw [hfn, hasc]; simp only [hb, ↓reduceDIte]

private theorem stepStatic_asciiSet_rle
    {pc : Nat} {v i : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {g : Algorithm.AsciiBytes} (hasc : asc[id]? = some g) (hb : v.asI32.toUInt8 < 128) :
    stepInvokeStatic ⟨pc, v :: i :: .asciiRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/RleLeanKt"
      "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" =
      .inl (some ⟨pc + 1, rest, locs, ar, u64, asc.set id (g.set i.asI32 v.asI32.toUInt8 hb)⟩) := by
  have hfn : stepInvokeStatic ⟨pc, v :: i :: .asciiRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/model/RleLeanKt"
      "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" =
      match asc[id]? with
      | some g =>
        if hb' : v.asI32.toUInt8 < 128 then
          .inl (some ⟨pc + 1, rest, locs, ar, u64, asc.set id (g.set i.asI32 v.asI32.toUInt8 hb')⟩)
        else .inr none
      | none => .inr none := rfl
  rw [hfn, hasc]; simp only [hb, ↓reduceDIte]

private theorem stepVirtual_arena_getCellNext
    {pc id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellNext--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, .arenaU32Ref id .cellNext :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_arena_getL4Next
    {pc id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .arenaRef id :: rest, locs, ar, u64, asc⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Next--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, .arenaU32Ref id .l4Next :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_pair_getSecond
    {pc : Nat} {a b : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .pair a b :: rest, locs, ar, u64, asc⟩
      "kotlin/Pair" "getSecond" "()Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, b :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepVirtual_uint_unbox
    {pc : Nat} {v : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .boxedUInt v :: rest, locs, ar, u64, asc⟩
      "kotlin/UInt" "unbox-impl" "()I" =
      .inl (some ⟨pc + 1, .i32 v :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepSpecial_pair_init
    {pc : Nat} {a b : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeSpecial ⟨pc, b :: a :: .allocRef "kotlin/Pair" :: .allocRef "kotlin/Pair" :: rest, locs, ar, u64, asc⟩
      "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V" =
      .inl (some ⟨pc + 1, .pair a b :: rest, locs, ar, u64, asc⟩) := rfl

private theorem stepInterface_fn1_hlToHl
    {pc : Nat} {fn : Algorithm.HashLifeStepState → Algorithm.HashLifeStepState}
    {hs : Algorithm.HashLifeStepState} {rest : List JvmVal} {locs : Nat → JvmVal}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeInterface ⟨pc, .hlState hs :: .fnHlToHl fn :: rest, locs, ar, u64, asc⟩
      "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .hlState (fn hs) :: rest, locs, ar, u64, asc⟩) := rfl

private def extractStrLit? (e : Lean.Expr) : Lean.MetaM (Option String) := do
  let ew ← Lean.Meta.whnf e
  match ew.consumeMData with
  | .lit (.strVal s) => return some s
  | _ => return none

private partial def normListSpine (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let ew ← Lean.Meta.whnf e
  if ew.isAppOfArity ``List.cons 3 then
    let args := ew.getAppArgs
    let tl' ← normListSpine args[2]!
    return Lean.mkAppN ew.getAppFn #[args[0]!, args[1]!, tl']
  return ew

private def normFlatStateExpr (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let sw ← Lean.Meta.whnf e
  if sw.isAppOfArity ``JvmState.mk 6 then
    let args := sw.getAppArgs
    let stk' ← normListSpine args[1]!
    let ar' ← normListSpine args[3]!
    let u64' ← normListSpine args[4]!
    let asc' ← normListSpine args[5]!
    return Lean.mkAppN sw.getAppFn #[args[0]!, stk', args[2]!, ar', u64', asc']
  return e

private partial def normFlatRunTail (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  if e.isAppOfArity ``Option.map 4 then
    let ma := e.getAppArgs
    return Lean.mkAppN e.getAppFn #[ma[0]!, ma[1]!, ma[2]!, ← normFlatRunTail ma[3]!]
  else if e.isAppOfArity ``runJvmValFast 5 || e.isAppOfArity ``runJvmResFast 5 then
    let ba := e.getAppArgs
    let fuel' ← Lean.Meta.whnf ba[0]!
    let pc' ← Lean.Meta.whnf ba[2]!
    let st' ← normFlatStateExpr ba[4]!
    return Lean.mkAppN e.getAppFn #[fuel', ba[1]!, pc', ba[3]!, st']
  return e

elab "norm_flat_run" : conv => do
  let lhs ← Lean.Elab.Tactic.Conv.getLhs
  let lhs' ← normFlatRunTail lhs
  Lean.Elab.Tactic.Conv.changeLhs lhs'

private def flatInvokeLookup :
    Lean.Name → String → String → String → List (Lean.Name × Nat)
  | ``JvmInstr.invokestatic, "kotlin/jvm/internal/Intrinsics", "checkNotNullParameter", _ =>
    [(``stepStatic_checkNotNullParameter, 1)]
  | ``JvmInstr.invokestatic, "kotlin/UInt", "constructor-impl", "(I)I" =>
    [(``stepStatic_uintCtor, 0)]
  | ``JvmInstr.invokestatic, "kotlin/ULong", "constructor-impl", "(J)J" =>
    [(``stepStatic_ulongCtor, 0)]
  | ``JvmInstr.invokestatic, "kotlin/UByte", "constructor-impl", "(B)B" =>
    [(``stepStatic_ubyteCtor, 0)]
  | ``JvmInstr.invokestatic, "java/lang/Integer", "compareUnsigned", "(II)I" =>
    [(``stepStatic_intCompareUnsigned, 0)]
  | ``JvmInstr.invokestatic, "java/lang/Integer", "divideUnsigned", "(II)I" =>
    [(``stepStatic_intDivideUnsigned, 0)]
  | ``JvmInstr.invokestatic, "kotlin/UIntArray", "get-pVg5ArA", "([II)I" =>
    [(``stepStatic_uintArrGet, 1)]
  | ``JvmInstr.invokestatic, "kotlin/UIntArray", "getSize-impl", "([I)I" =>
    [(``stepStatic_uintArrGetSize, 1)]
  | ``JvmInstr.invokestatic, "kotlin/UByteArray", "get-w2LRezQ", "([BI)B" =>
    [(``stepStatic_ubyteArrGet, 1)]
  | ``JvmInstr.invokestatic, "kotlin/ULongArray", "get-s-VKNKU", "([JI)J" =>
    [(``stepStatic_ulongArrGetArena, 1), (``stepStatic_ulongArrGetU64, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_getRemapCell-Qn1smSk", _ =>
    [(``stepStatic_flat_getRemapCell, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_getCellStepRes-Qn1smSk", _ =>
    [(``stepStatic_flat_getCellStepRes, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_centeredSubSubnodeSizeCell-Qn1smSk", _ =>
    [(``stepStatic_flat_centeredSubSubnodeSizeCell, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0-2jIhpxI", _ =>
    [(``stepStatic_flat_computeLevel4NextGen, 0)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_centeredHorizontal-BltQuoY", _ =>
    [(``stepStatic_flat_centeredHorizontal, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_centeredVertical-BltQuoY", _ =>
    [(``stepStatic_flat_centeredVertical, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_centeredSubnode-Qn1smSk", _ =>
    [(``stepStatic_flat_centeredSubnode, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_centeredSubSubnode-Qn1smSk", _ =>
    [(``stepStatic_flat_centeredSubSubnode, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_quadrantNW-Qn1smSk", _ =>
    [(``stepStatic_flat_quadrantNW, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_quadrantNE-Qn1smSk", _ =>
    [(``stepStatic_flat_quadrantNE, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_quadrantSW-Qn1smSk", _ =>
    [(``stepStatic_flat_quadrantSW, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_quadrantSE-Qn1smSk", _ =>
    [(``stepStatic_flat_quadrantSE, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_stepLevel4-Qn1smSk", _ =>
    [(``stepStatic_flat_stepLevel4, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_stepLevel5-Qn1smSk", _ =>
    [(``stepStatic_flat_stepLevel5, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_setRemapL4-BltQuoY", _ =>
    [(``stepStatic_flat_setRemapL4, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_setRemapCell-BltQuoY", _ =>
    [(``stepStatic_flat_setRemapCell, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_setCellStepRes-BltQuoY", _ =>
    [(``stepStatic_flat_setCellStepRes, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_setL4StepRes-c82oGLE", _ =>
    [(``stepStatic_flat_setL4StepRes, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_setOverflow", _ =>
    [(``stepStatic_flat_setOverflow, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_expandFrame-BltQuoY", _ =>
    [(``stepStatic_flat_expandFrame, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_initRemapL4Loop-BltQuoY", _ =>
    [(``stepStatic_flat_initRemapL4Loop, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_initRemapCellLoop-BltQuoY", _ =>
    [(``stepStatic_flat_initRemapCellLoop, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_stepCellSerialLoop-7IvYBaQ", _ =>
    [(``stepStatic_flat_stepCellSerialLoop, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_copyL4From-BzPDsQc", _ =>
    [(``stepStatic_flat_copyL4From, 2)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_copyCellFromLoop-sA3nruY", _ =>
    [(``stepStatic_flat_copyCellFromLoop, 2)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "canCopySubgraphFrom", _ =>
    [(``stepVirtual_arena_canCopySubgraphFrom, 2)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellCount-pVg5ArA", _ =>
    [(``stepVirtual_arena_getCellCount, 1)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellMask-pVg5ArA", _ =>
    [(``stepVirtual_arena_getCellMask, 1)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Count-pVg5ArA", _ =>
    [(``stepVirtual_arena_getL4Count, 1)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getOverflow-w2LRezQ", _ =>
    [(``stepVirtual_arena_getOverflow, 1)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellLevel-TcUX1vc", _ =>
    [(``stepVirtual_arena_getCellLevel, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4HasRes-TcUX1vc", _ =>
    [(``stepVirtual_arena_getL4HasRes, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellNe--hP7Qyg", _ =>
    [(``stepVirtual_arena_getCellNe, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellNw--hP7Qyg", _ =>
    [(``stepVirtual_arena_getCellNw, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellSw--hP7Qyg", _ =>
    [(``stepVirtual_arena_getCellSw, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellSe--hP7Qyg", _ =>
    [(``stepVirtual_arena_getCellSe, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellStepRes--hP7Qyg", _ =>
    [(``stepVirtual_arena_getCellStepRes, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getRemapCell--hP7Qyg", _ =>
    [(``stepVirtual_arena_getRemapCell, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getRemapL4--hP7Qyg", _ =>
    [(``stepVirtual_arena_getRemapL4, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellPop-Y2RjT0g", _ =>
    [(``stepVirtual_arena_getCellPop, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Nw-Y2RjT0g", _ =>
    [(``stepVirtual_arena_getL4Nw, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Ne-Y2RjT0g", _ =>
    [(``stepVirtual_arena_getL4Ne, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Sw-Y2RjT0g", _ =>
    [(``stepVirtual_arena_getL4Sw, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Se-Y2RjT0g", _ =>
    [(``stepVirtual_arena_getL4Se, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4StepRes-Y2RjT0g", _ =>
    [(``stepVirtual_arena_getL4StepRes, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "internCellNode-gt5aIGQ", _ =>
    [(``stepVirtual_arena_internCellNode, 1)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "internLevel4-PT-fW9Q", _ =>
    [(``stepVirtual_arena_internLevel4, 1)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellNext--hP7Qyg", _ =>
    [(``stepVirtual_arena_getCellNext, 0)]
  | ``JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Next--hP7Qyg", _ =>
    [(``stepVirtual_arena_getL4Next, 0)]
  | ``JvmInstr.invokevirtual, "kotlin/Pair", "getSecond", _ =>
    [(``stepVirtual_pair_getSecond, 0)]
  | ``JvmInstr.invokevirtual, "kotlin/UInt", "unbox-impl", _ =>
    [(``stepVirtual_uint_unbox, 0)]
  | ``JvmInstr.invokespecial, "kotlin/Pair", "<init>", _ =>
    [(``stepSpecial_pair_init, 0)]
  | ``JvmInstr.invokeinterface, "kotlin/jvm/functions/Function1", "invoke", _ =>
    [(``stepInterface_fn1_hlToHl, 0)]
  | ``JvmInstr.invokestatic, "kotlin/jvm/internal/Intrinsics", "checkNotNull", _ =>
    [(``stepStatic_checkNotNull, 1)]
  | ``JvmInstr.invokestatic, "kotlin/jvm/internal/Intrinsics", "compare", "(II)I" =>
    [(``stepStatic_intrinsicsCompare, 0)]
  | ``JvmInstr.invokestatic, "java/lang/Long", "compareUnsigned", "(JJ)I" =>
    [(``stepStatic_longCompareUnsigned, 0)]
  | ``JvmInstr.invokestatic, "java/lang/Integer", "valueOf", _ =>
    [(``stepStatic_intValueOf, 0)]
  | ``JvmInstr.invokestatic, "kotlin/ULong", "box-impl", _ =>
    [(``stepStatic_ulongBox, 0)]
  | ``JvmInstr.invokestatic, "kotlin/ULongArray", "set-k8EXiF4", "([JIJ)V" =>
    [(``stepStatic_ulongArrSetU64, 1), (``stepStatic_ulongArrSetArena, 1)]
  | ``JvmInstr.invokestatic, "kotlin/UIntArray", "set-VXSXFK8", "([III)V" =>
    [(``stepStatic_uintArrSet, 1)]
  | ``JvmInstr.invokestatic, "kotlin/UByteArray", "set-VurrAj0", "([BIB)V" =>
    [(``stepStatic_ubyteArrSet, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded-BltQuoY", _ =>
    [(``stepStatic_flat_expandFrameIfNeeded, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_combineQuadrants-t447iZE", _ =>
    [(``stepStatic_flat_combineQuadrants, 1)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_copyCellTryStep-BzPDsQc", _ =>
    [(``stepStatic_flat_copyCellTryStep, 2)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_leafContains-fMEO4hA", _ =>
    [(``stepStatic_flat_leafContains, 0)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_makeCellNode", _ =>
    [(``stepStatic_makeCellNode, 0)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_decodeCharAt-BltQuoY", _ =>
    [(``stepStatic_decodeCharAt, 0)]
  | ``JvmInstr.invokestatic, _, "f_Algorithm_formatCoordLine-feOb9K0", _ =>
    [(``stepStatic_formatCoordLine, 0)]
  | ``JvmInstr.invokestatic, "com/alexvanyo/composelife/model/Life105LeanKt", "f_Algorithm_U64Buf_push-3yFGk1Y", _ =>
    [(``stepStatic_u64BufPush_105, 1)]
  | ``JvmInstr.invokestatic, "com/alexvanyo/composelife/model/Life105LeanKt", "f_Algorithm_AsciiBytes_toStringRange-BltQuoY", _ =>
    [(``stepStatic_asciiToStringRange_105, 1)]
  | ``JvmInstr.invokestatic, "com/alexvanyo/composelife/model/PlaintextLeanKt", "f_Algorithm_AsciiBytes_toStringRange-BltQuoY", _ =>
    [(``stepStatic_asciiToStringRange_plain, 1)]
  | ``JvmInstr.invokestatic, "com/alexvanyo/composelife/model/Life105LeanKt", "f_Algorithm_GrowBuf_push___redArg", _ =>
    [(``stepStatic_growBufPush_105, 0)]
  | ``JvmInstr.invokestatic, "com/alexvanyo/composelife/model/Life106LeanKt", "f_Algorithm_GrowBuf_push___redArg", _ =>
    [(``stepStatic_growBufPush_106, 0)]
  | ``JvmInstr.invokestatic, "com/alexvanyo/composelife/model/PlaintextLeanKt", "f_Algorithm_GrowBuf_push___redArg", _ =>
    [(``stepStatic_growBufPush_plain, 0)]
  | _, _, _, _ => []

private def tryStepFlatInvoke : Lean.Elab.Tactic.TacticM Bool := do
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let (inner, isMap) := unwrapRunLhs lhs
  let isRes := inner.isAppOfArity ``runJvmResFast 5
  let isVal := inner.isAppOfArity ``runJvmValFast 5
  if !isRes && !isVal then return false
  let instrs ← Lean.Meta.whnf (inner.getArg! 3)
  if !instrs.isAppOfArity ``List.cons 3 then return false
  let instr ← Lean.Meta.whnf (instrs.getArg! 1)
  let some opName := instr.getAppFn.constName? | return false
  if opName != ``JvmInstr.invokestatic && opName != ``JvmInstr.invokevirtual &&
     opName != ``JvmInstr.invokespecial && opName != ``JvmInstr.invokeinterface then
    return false
  let args := instr.getAppArgs
  if args.size < 3 then return false
  let (some cls, some method, some desc) :=
    (← extractStrLit? args[0]!, ← extractStrLit? args[1]!, ← extractStrLit? args[2]!) | return false
  let bridgeName :=
    if !isRes then
      if opName == ``JvmInstr.invokestatic then ``runJvmValFast_invokestatic_step
      else if opName == ``JvmInstr.invokevirtual then ``runJvmValFast_invokevirtual_step
      else if opName == ``JvmInstr.invokespecial then ``runJvmValFast_invokespecial_step
      else ``runJvmValFast_invokeinterface_step
    else
      if opName == ``JvmInstr.invokestatic then ``runJvmResFast_invokestatic_step
      else if opName == ``JvmInstr.invokevirtual then ``runJvmResFast_invokevirtual_step
      else if opName == ``JvmInstr.invokespecial then ``runJvmResFast_invokespecial_step
      else ``runJvmResFast_invokeinterface_step
  let bridgeId := Lean.mkIdent bridgeName
  for (thmName, nHyps) in flatInvokeLookup opName cls method desc do
    let thmId := Lean.mkIdent thmName
    let saved ← Lean.Elab.Tactic.getGoals
    try
      if isMap then
        if nHyps == 0 then
          Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 2; rw [$bridgeId ($thmId)])))
        else if nHyps == 1 then
          Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 2; rw [$bridgeId ($thmId rfl)])))
        else
          Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 2; rw [$bridgeId ($thmId rfl rfl)])))
      else
        if nHyps == 0 then
          Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; rw [$bridgeId ($thmId)])))
        else if nHyps == 1 then
          Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; rw [$bridgeId ($thmId rfl)])))
        else
          Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; rw [$bridgeId ($thmId rfl rfl)])))
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)))
      return true
    catch _ =>
      Lean.Elab.Tactic.setGoals saved
  return false

private def isRunJvmAtFlatNonStop : Lean.Elab.Tactic.TacticM Bool := do
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return false
  let (inner, _) := unwrapRunLhs lhs
  if inner.isAppOfArity ``runJvmValFast 5 || inner.isAppOfArity ``runJvmResFast 5 then
    let instrs ← Lean.Meta.whnf (inner.getArg! 3)
    if instrs.isAppOfArity ``List.cons 3 then
      let instr := instrs.getArg! 1
      let br ← Lean.Meta.whnf (Lean.mkApp (Lean.mkConst ``isFlatStop) instr)
      return br.isConstOf ``Bool.false
  return false

elab "flat_step_one_chunk" : tactic => do
  let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  let some (_, lhs, _) := tgt.eq? | return ()
  let (inner, isMap) := unwrapRunLhs lhs
  let isRes := inner.isAppOfArity ``runJvmResFast 5
  if isRes then
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_stepResFlatChunk 120]))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_stepFlatChunk 120]))
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    if isMap then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 2; arg 1; jvm_whnf_blk)))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 1; jvm_whnf_blk)))
    let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
    let some (_, lhs2, _) := tgt2.eq? | return ()
    let (afterApp, _) := unwrapRunLhs lhs2
    let chunkRes := (afterApp.getArg! 0).consumeMData
    if let some cn := chunkRes.getAppFn.constName? then
      if !isRes then
        if cn == ``BlockChunkRes.cont then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_cont]))
        else if cn == ``BlockChunkRes.jump then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_jump]))
        else if cn == ``BlockChunkRes.done then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_done]))
      else
        if cn == ``BlockResChunkRes.cont then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_cont]))
        else if cn == ``BlockResChunkRes.jump then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_jump]))
        else if cn == ``BlockResChunkRes.done then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_done]))
          rwOptionMapResult
    if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals)))
      Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; jvm_whnf_run_args)))

elab "flat_step_nonbranch_chunks" : tactic => do
  for _ in [:400] do
    if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then break
    if ← tryStepFlatInvoke then
      continue
    else if ← isRunJvmAtFlatNonStop then
      Lean.Elab.Tactic.evalTactic (← `(tactic| flat_step_one_chunk))
    else if ← isRunJvmAtForwardGoto then
      let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      let some (_, lhs, _) := tgt.eq? | break
      let (inner, isMap) := unwrapRunLhs lhs
      let isRes := inner.isAppOfArity ``runJvmResFast 5
      if isRes then
        Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmResFast_at_branch_cons (hbr := rfl)]))
      else
        Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_at_branch_cons (hbr := rfl)]))
      if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
        if isMap then
          Lean.Elab.Tactic.evalTactic (← `(tactic| (
            (conv => lhs; arg 2; arg 1; whnf)
            (conv => lhs; arg 2; arg 3; whnf)
            (conv => lhs; arg 2; arg 4; whnf)
            (conv => lhs; arg 2; arg 6; jvm_whnf_blk))))
          let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
          let some (_, lhs2, _) := tgt2.eq? | break
          let (evalApp, _) := unwrapRunLhs lhs2
          rwEvalBranchByInstr isRes (evalApp.getArg! 3)
          if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
            Lean.Elab.Tactic.evalTactic (← `(tactic| (
              (conv => lhs; try rw [option_map_ite])
              (conv => lhs; norm_jvm_locals; jvm_whnf_run_args))))
        else
          Lean.Elab.Tactic.evalTactic (← `(tactic| (
            (conv => lhs; arg 1; whnf)
            (conv => lhs; arg 3; whnf)
            (conv => lhs; arg 4; whnf)
            (conv => lhs; arg 6; jvm_whnf_blk))))
          let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
          let some (_, lhs2, _) := tgt2.eq? | break
          rwEvalBranchByInstr isRes (lhs2.getArg! 3)
          if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
            Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)))
    else
      break

elab "flat_step_blk" _prog:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| flat_step_nonbranch_chunks))
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_branch_tail))

elab "step_flat_tree" prog:ident : tactic =>
  Lean.Meta.withCanUnfoldPred
    (fun cfg cinfo =>
      if flatOpaqueConsts.contains cinfo.name then return false
      else Lean.Meta.canUnfoldDefault cfg cinfo) do
  Lean.Elab.Tactic.evalTactic (← `(tactic| flat_step_blk $prog))
  for _ in [:64] do
    let gs ← Lean.Elab.Tactic.getUnsolvedGoals
    if gs.isEmpty then break
    let mut rem : List Lean.MVarId := []
    let mut progressed := false
    for g in gs do
      Lean.Elab.Tactic.setGoals [g]
      let tgt ← Lean.Elab.Tactic.getMainTarget
      if let some (_, lhs, _) := tgt.eq? then
        if lhs.consumeMData.isAppOfArity ``ite 5 then
          Lean.Elab.Tactic.evalTactic (← `(tactic| refine eq_of_ite_branches ?_ ?_))
          let afterSplit ← Lean.Elab.Tactic.getUnsolvedGoals
          for sg in afterSplit do
            Lean.Elab.Tactic.setGoals [sg]
            Lean.Elab.Tactic.evalTactic (← `(tactic| (
              intro hcond
              try (repeat first
                | rw [compareUnsigned_slt'] at hcond
                | rw [compareUnsigned_sle'] at hcond
                | rw [compareUnsigned_sgt'] at hcond
                | rw [compareUnsigned_sge'] at hcond
                | rw [compareUnsigned_eq_zero] at hcond
                | rw [compareUnsigned64_slt'] at hcond
                | rw [compareUnsigned64_sle'] at hcond
                | rw [compareUnsigned64_sgt'] at hcond
                | rw [compareUnsigned64_sge'] at hcond
                | rw [lcmp_eq_zero] at hcond
                | rw [lcmp_beq_eq_zero] at hcond
                | rw [lcmp_eq_zero'] at hcond)
              try simp only [getArenaU32, getArenaU64, getArenaU8,
                u8_sext_eq_zero, u8_sext_eq_one, u8_sext_eq_five, u8_sext_eq_six, u8_sext_eq_seven,
                u8_sext_beq_zero, u8_sext_beq_one, u8_sext_beq_five, u8_sext_beq_six, u8_sext_beq_seven,
                u8_sub1_u32_jvm, u8_sub1_sext_jvm, u8_sub2_sext_jvm, u8_add1_sext_jvm, u8_add2_sext_jvm,
                u8_and255_sext_jvm, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at hcond
              flat_step_blk $prog)))
            rem := rem ++ (← Lean.Elab.Tactic.getUnsolvedGoals)
          progressed := true
        else
          let (inner, _) := unwrapRunLhs lhs
          if inner.isAppOfArity ``runJvmValFast 5 || inner.isAppOfArity ``runJvmResFast 5 then
            Lean.Elab.Tactic.evalTactic (← `(tactic| flat_step_blk $prog))
            let afterBlk ← Lean.Elab.Tactic.getUnsolvedGoals
            rem := rem ++ afterBlk
            let changed ← match afterBlk with
              | [g'] => do
                if g' == g then pure false
                else pure ((← g'.getType) != tgt)
              | _ => pure true
            if changed then progressed := true
          else
            rem := rem ++ [g]
      else
        rem := rem ++ [g]
    Lean.Elab.Tactic.setGoals rem
    if !progressed then break

private theorem lcmp_beq_eq_zero (a b : UInt64) (c : Bool) :
    ((if a == b then (0 : UInt32) else if c then 4294967295 else 1) == 0) = (a == b) := by
  by_cases h : a = b <;> cases c <;> simp [h]

private theorem lcmp_eq_zero' (a b : UInt64) [d : Decidable (a = b)] (c : Bool) [dc : Decidable (c = true)] :
    ((@ite _ (a = b) d (0 : UInt32) (@ite _ (c = true) dc 4294967295 1)) = 0) ↔ a = b := by
  by_cases h : a = b <;> cases c <;> simp [h]

private theorem u8_sext_beq_zero (b : UInt8) : (b.toInt8.toInt32.toUInt32 == 0) = (b == 0) := by
  revert b; decide

private theorem u8_sext_beq_one (b : UInt8) : (b.toInt8.toInt32.toUInt32 == 1) = (b == 1) := by
  revert b; decide

private theorem u8_sext_beq_five (b : UInt8) : (b.toInt8.toInt32.toUInt32 == 5) = (b == 5) := by
  revert b; decide

private theorem u8_sext_beq_six (b : UInt8) : (b.toInt8.toInt32.toUInt32 == 6) = (b == 6) := by
  revert b; decide

private theorem u8_sext_beq_seven (b : UInt8) : (b.toInt8.toInt32.toUInt32 == 7) = (b == 7) := by
  revert b; decide

private theorem ui32_shl3_mask_eq_mul8 (x : UInt32) : x <<< ((3 : UInt32) &&& 31) = x * 8 := by
  bv_normalize

private theorem ui32_shl3_eq_mul8 (x : UInt32) : x <<< (3 : UInt32) = x * 8 := by
  bv_normalize

private theorem u8_sub1_jvm_exact (b : UInt8) :
    (UInt32.ofBitVec (BitVec.signExtend 32 (BitVec.setWidth 8 ((b.toUInt32 &&& 255) - 1).toBitVec))).toUInt8 = b - 1 := by
  revert b; decide

private theorem ite_bool_1_0_eq_zero (b : Bool) : ((if b = true then (1 : UInt32) else 0) = 0) ↔ b = false := by
  cases b <;> decide

private theorem beq_false_iff_ne' {α : Type} [BEq α] [LawfulBEq α] (a b : α) :
    ((a == b) = false) ↔ a ≠ b := by
  simp

private theorem ui32_eq_of_beq_true {a b : UInt32} (h : (a == b) = true) : a = b :=
  LawfulBEq.eq_of_beq h

private theorem ui32_ne_of_beq_false {a b : UInt32} (h : (a == b) = false) : a ≠ b :=
  fun heq => by subst heq; simp at h

private theorem u32_one_bne_zero : ((1 : UInt32) != 0) = true := rfl

private theorem u32_zero_bne_zero : ((0 : UInt32) != 0) = false := rfl

elab "close_flat_leaf" : tactic =>
  Lean.Meta.withCanUnfoldPred
    (fun cfg cinfo =>
      if flatOpaqueConsts.contains cinfo.name then return false
      else Lean.Meta.canUnfoldDefault cfg cinfo) do
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    try (repeat first | rw [lcmp_beq_eq_zero] at * | rw [lcmp_eq_zero] at * | rw [lcmp_eq_zero'] at *)
    try simp only [Algorithm.UNCOMPUTED, Algorithm.stepFrameWidth, getArenaU32, getArenaU64, getArenaU8,
      ui32_toNat_add_1, ui32_toNat_add_2, ui32_toNat_add_3, ui32_toNat_add_4,
      ui32_shl3_mask_eq_mul8, ui32_shl3_eq_mul8,
      u8_sext_eq_zero, u8_sext_eq_one, u8_sext_eq_five, u8_sext_eq_six, u8_sext_eq_seven,
      u8_sext_beq_zero, u8_sext_beq_one, u8_sext_beq_five, u8_sext_beq_six, u8_sext_beq_seven,
      u8_sub1_u32_jvm, u8_sub1_jvm_exact, u8_sub1_sext_jvm, u8_sub2_sext_jvm, u8_add1_sext_jvm, u8_add2_sext_jvm,
      u8_and255_sext_jvm, u8_sext_toUInt8, u8_sub1_u32_exact, u8_sub2_u32_exact, u8_add1_u32_exact, u8_add2_u32_exact,
      u32_one_bne_zero, u32_zero_bne_zero,
      lcmp_beq_eq_zero, lcmp_eq_zero, lcmp_eq_zero', ite_bool_1_0_eq_zero, beq_false_iff_ne',
      Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      true_or, or_true, false_or, or_false, true_and, and_true,
      not_true_eq_false, not_false_eq_true, Classical.not_not, not_and, not_or,
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *
    all_goals (repeat (
      first
      | rfl
      | contradiction
      | (exfalso; simp_all only [Classical.not_not, not_true_eq_false, not_false_eq_true,
           ite_true, ite_false, eq_self_iff_true, decide_eq_true_eq]; done)
      | (split <;>
          (try simp only [eq_self_iff_true, beq_self_eq_true, decide_true, decide_false,
             Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false,
             u32_one_bne_zero, u32_zero_bne_zero,
             ite_bool_1_0_eq_zero, beq_false_iff_ne',
             true_or, or_true, false_or, or_false, true_and, and_true,
             not_true_eq_false, not_false_eq_true, Classical.not_not, not_and, not_or,
             beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, *] at *) <;>
          (try (first
             | rfl
             | contradiction
             | (exfalso; simp_all only [Classical.not_not, not_true_eq_false, not_false_eq_true,
                  ite_true, ite_false, eq_self_iff_true, decide_eq_true_eq]; done)
             | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le,
                  UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *; omega; done)
             | (omega; done))))
      | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le,
           UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *; omega; done)
      | (omega; done)))
  )))

theorem getRemapCell_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    runJvm 30 f_Algorithm_getRemapCell_prog (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena]) =
      some (.i32 (Algorithm.getRemapCell arena nodeId)) := by
  apply runJvm_of_runJvmValFast0 30 _ _ _ rfl
  step_flat_tree f_Algorithm_getRemapCell_prog
  all_goals (simp only [Algorithm.getRemapCell]; close_flat_leaf)

theorem getCellStepRes_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    runJvm 30 f_Algorithm_getCellStepRes_prog (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena]) =
      some (.i32 (Algorithm.getCellStepRes arena nodeId)) := by
  apply runJvm_of_runJvmValFast0 30 _ _ _ rfl
  step_flat_tree f_Algorithm_getCellStepRes_prog
  all_goals (simp only [Algorithm.getCellStepRes]; close_flat_leaf)

theorem flatHashLifeArena_expandFrameIfNeeded_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId base : UInt32) :
    (runJvmRes 30 f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId), (2, .i32 base)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.unit, [arena.expandFrameIfNeeded nodeId base]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 30 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.expandFrameIfNeeded]; close_flat_leaf)

theorem flatHashLifeArena_needToExpandCell_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    runJvm 40 f_Algorithm_FlatHashLifeArena_needToExpandCell_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena]) =
      some (.i32 (if arena.needToExpandCell nodeId then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 40 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_needToExpandCell_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.needToExpandCell]; close_flat_leaf)

theorem flatHashLifeArena_combineQuadrants_equiv (arena : Algorithm.FlatHashLifeArena)
    (nodeId : UInt32) (lvl : UInt8) (r_nw r_ne r_sw r_se : UInt32) :
    (runJvmRes 60 f_Algorithm_FlatHashLifeArena_combineQuadrants_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId), (2, .i32 lvl.toUInt32),
        (3, .i32 r_nw), (4, .i32 r_ne), (5, .i32 r_sw), (6, .i32 r_se)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.combineQuadrants nodeId lvl r_nw r_ne r_sw r_se).1,
        [(arena.combineQuadrants nodeId lvl r_nw r_ne r_sw r_se).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 60 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_combineQuadrants_prog
  all_goals
    try rw [u8_sub1_u32_jvm]
    simp only [Algorithm.FlatHashLifeArena.combineQuadrants]
    close_flat_leaf

theorem copySubgraphInto_equiv (dst src : Algorithm.FlatHashLifeArena) (rootId : UInt32) (copyMemos : Bool) :
    (runJvmRes 80 f_Algorithm_copySubgraphInto_prog
      (initJvmState [(0, .arenaRef 0), (1, .arenaRef 1), (2, .i32 rootId),
        (3, .i32 (if copyMemos then 1 else 0))] [dst, src])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.unit, [Algorithm.copySubgraphInto dst src rootId copyMemos, src]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 80 _ _ _ rfl
  step_flat_tree f_Algorithm_copySubgraphInto_prog
  all_goals (simp only [Algorithm.copySubgraphInto]; close_flat_leaf)

theorem flatHashLifeArena_stepLevel4_equiv (arena : Algorithm.FlatHashLifeArena) (l4Id : UInt32) :
    (runJvmRes 80 f_Algorithm_FlatHashLifeArena_stepLevel4_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 l4Id)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i64 (arena.stepLevel4 l4Id).1, [(arena.stepLevel4 l4Id).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 80 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_stepLevel4_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.stepLevel4]; close_flat_leaf)

theorem flatHashLifeArena_stepCellSerial_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 80 f_Algorithm_FlatHashLifeArena_stepCellSerial_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.stepCellSerial nodeId).1, [(arena.stepCellSerial nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 80 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_stepCellSerial_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.stepCellSerial]; close_flat_leaf)

theorem flatHashLifeArena_stepLevel5_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 110 f_Algorithm_FlatHashLifeArena_stepLevel5_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.stepLevel5 nodeId).1, [(arena.stepLevel5 nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 110 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_stepLevel5_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.stepLevel5]; close_flat_leaf)

theorem flatHashLifeArena_copyL4From_equiv (dst src : Algorithm.FlatHashLifeArena)
    (l4Id : UInt32) (copyMemos : Bool) :
    (runJvmRes 120 f_Algorithm_FlatHashLifeArena_copyL4From_prog
      (initJvmState [(0, .arenaRef 0), (1, .arenaRef 1), (2, .i32 l4Id),
        (3, .i32 (if copyMemos then 1 else 0))] [dst, src])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (dst.copyL4From src l4Id copyMemos).1,
        [(dst.copyL4From src l4Id copyMemos).2, src]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 120 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_copyL4From_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.copyL4From]; close_flat_leaf)

theorem flatHashLifeArena_expandLevel4Centered_equiv (arena : Algorithm.FlatHashLifeArena) (l4Id : UInt32) :
    (runJvmRes 200 f_Algorithm_FlatHashLifeArena_expandLevel4Centered_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 l4Id)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.expandLevel4Centered l4Id).1, [(arena.expandLevel4Centered l4Id).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 200 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_expandLevel4Centered_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.expandLevel4Centered]; close_flat_leaf)

theorem flatHashLifeArena_centeredSubnode_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 200 f_Algorithm_FlatHashLifeArena_centeredSubnode_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.centeredSubnode nodeId).1, [(arena.centeredSubnode nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 200 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_centeredSubnode_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.centeredSubnode]; close_flat_leaf)

theorem flatHashLifeArena_centeredHorizontal_equiv (arena : Algorithm.FlatHashLifeArena) (wId eId : UInt32) :
    (runJvmRes 200 f_Algorithm_FlatHashLifeArena_centeredHorizontal_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 wId), (2, .i32 eId)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.centeredHorizontal wId eId).1, [(arena.centeredHorizontal wId eId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 200 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_centeredHorizontal_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.centeredHorizontal]; close_flat_leaf)

theorem flatHashLifeArena_centeredVertical_equiv (arena : Algorithm.FlatHashLifeArena) (nId sId : UInt32) :
    (runJvmRes 200 f_Algorithm_FlatHashLifeArena_centeredVertical_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nId), (2, .i32 sId)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.centeredVertical nId sId).1, [(arena.centeredVertical nId sId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 200 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_centeredVertical_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.centeredVertical]; close_flat_leaf)

theorem flatHashLifeArena_centeredSubSubnode_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 200 f_Algorithm_FlatHashLifeArena_centeredSubSubnode_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.centeredSubSubnode nodeId).1, [(arena.centeredSubSubnode nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 200 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_centeredSubSubnode_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.centeredSubSubnode]; close_flat_leaf)

theorem flatHashLifeArena_expandCentered_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 300 f_Algorithm_FlatHashLifeArena_expandCentered_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.expandCentered nodeId).1, [(arena.expandCentered nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 300 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_expandCentered_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.expandCentered, Algorithm.emptyNodeForLevel]; close_flat_leaf)

theorem flatHashLifeArena_expandFrame_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId base : UInt32) :
    (runJvmRes 300 f_Algorithm_FlatHashLifeArena_expandFrame_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId), (2, .i32 base)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.unit, [arena.expandFrame nodeId base]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 300 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_expandFrame_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.expandFrame]; close_flat_leaf)

private theorem shift_and_63_1 : ((1 : UInt32) &&& 63).toUInt64 = 1 := rfl
private theorem shift_and_63_2 : ((2 : UInt32) &&& 63).toUInt64 = 2 := rfl
private theorem shift_and_63_4 : ((4 : UInt32) &&& 63).toUInt64 = 4 := rfl
private theorem shift_and_63_56 : ((56 : UInt32) &&& 63).toUInt64 = 56 := rfl
private theorem shift_and_63_16_f : (((16 : UInt32) &&& 63).toUInt64) = 16 := rfl
private theorem shift_and_63_32_f : (((32 : UInt32) &&& 63).toUInt64) = 32 := rfl
private theorem shift_and_63_48_f : (((48 : UInt32) &&& 63).toUInt64) = 48 := rfl
private theorem ui64_add_zero (x : UInt64) : x + 0 = x := by bv_normalize
private theorem ui64_zero_add (x : UInt64) : 0 + x = x := by bv_normalize
private theorem u8_toUInt32_beq_five (b : UInt8) : (b.toUInt32 == 5) = (b == 5) := by
  revert b; decide
private theorem u8_6_eq_5 : ((6 : UInt8) = 5) = False := by decide
private theorem u8_7_eq_5 : ((7 : UInt8) = 5) = False := by decide
private theorem u8_7_eq_6 : ((7 : UInt8) = 6) = False := by decide

private theorem centeredSubnodeLevel4_jvm_fold (a b c d : UInt64) :
    (((a >>> ((48 : UInt32) &&& 63).toUInt64).toUInt32 &&& 65535).toUInt64 |||
      ((b >>> ((32 : UInt32) &&& 63).toUInt64).toUInt32 &&& 65535).toUInt64 <<< ((16 : UInt32) &&& 63).toUInt64 |||
      ((c >>> ((16 : UInt32) &&& 63).toUInt64).toUInt32 &&& 65535).toUInt64 <<< ((32 : UInt32) &&& 63).toUInt64 |||
      (d.toUInt32 &&& 65535).toUInt64 <<< ((48 : UInt32) &&& 63).toUInt64) =
    Algorithm.centeredSubnodeLevel4 a b c d := by
  simp only [Algorithm.centeredSubnodeLevel4, shift_and_63_16_f, shift_and_63_32_f, shift_and_63_48_f]

theorem copyCellTryStep_equiv (dst src : Algorithm.FlatHashLifeArena) (cellId : UInt32) (copyMemos : Bool) :
    (runJvmRes 350 f_Algorithm_copyCellTryStep_prog
      (initJvmState [(0, .arenaRef 0), (1, .arenaRef 1), (2, .i32 cellId),
        (3, .i32 (if copyMemos then 1 else 0))] [dst, src])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (Algorithm.copyCellTryStep dst src cellId copyMemos).1,
        [(Algorithm.copyCellTryStep dst src cellId copyMemos).2, src]) := by
  cases copyMemos
  · simp only [Bool.false_eq_true, ite_false]
    apply runJvmRes_map_of_runJvmResFast0 _ 350 _ _ _ rfl
    step_flat_tree f_Algorithm_copyCellTryStep_prog
    all_goals (simp only [Algorithm.copyCellTryStep]; close_flat_leaf)
  · simp only [ite_true]
    apply runJvmRes_map_of_runJvmResFast0 _ 350 _ _ _ rfl
    step_flat_tree f_Algorithm_copyCellTryStep_prog
    all_goals (simp only [Algorithm.copyCellTryStep]; close_flat_leaf)

theorem flatHashLifeArena_quadrantNW_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 500 f_Algorithm_FlatHashLifeArena_quadrantNW_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.quadrantNW nodeId).1, [(arena.quadrantNW nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 500 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_quadrantNW_prog
  all_goals (try (repeat rw [centeredSubnodeLevel4_jvm_fold]); simp only [Algorithm.FlatHashLifeArena.quadrantNW]; close_flat_leaf)

theorem flatHashLifeArena_quadrantNE_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 500 f_Algorithm_FlatHashLifeArena_quadrantNE_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.quadrantNE nodeId).1, [(arena.quadrantNE nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 500 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_quadrantNE_prog
  all_goals (try (repeat rw [centeredSubnodeLevel4_jvm_fold]); simp only [Algorithm.FlatHashLifeArena.quadrantNE]; close_flat_leaf)

theorem flatHashLifeArena_quadrantSW_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 500 f_Algorithm_FlatHashLifeArena_quadrantSW_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.quadrantSW nodeId).1, [(arena.quadrantSW nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 500 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_quadrantSW_prog
  all_goals (try (repeat rw [centeredSubnodeLevel4_jvm_fold]); simp only [Algorithm.FlatHashLifeArena.quadrantSW]; close_flat_leaf)

theorem flatHashLifeArena_quadrantSE_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 500 f_Algorithm_FlatHashLifeArena_quadrantSE_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.i32 (arena.quadrantSE nodeId).1, [(arena.quadrantSE nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 500 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_quadrantSE_prog
  all_goals (try (repeat rw [centeredSubnodeLevel4_jvm_fold]); simp only [Algorithm.FlatHashLifeArena.quadrantSE]; close_flat_leaf)

theorem computePopulation_equiv (arena : Algorithm.FlatHashLifeArena) (lvl : UInt8) (nw ne sw se : UInt32) :
    runJvm 1500 f_Algorithm_computePopulation_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 lvl.toUInt32),
        (2, .i32 nw), (3, .i32 ne), (4, .i32 sw), (5, .i32 se)] [arena]) =
      some (.i64 (Algorithm.computePopulation arena lvl nw ne sw se)) := by
  apply runJvm_of_runJvmValFast0 1500 _ _ _ rfl
  step_flat_tree f_Algorithm_computePopulation_prog
  all_goals (
    try simp only [getArenaU64, decide_eq_true_eq, u8_toUInt32_beq_five, beq_iff_eq] at *
    try simp only [Algorithm.computePopulation, Algorithm.popLevel4Id, Algorithm.popCellId,
      Algorithm.popcount64, shift_and_63_1, shift_and_63_2, shift_and_63_4, shift_and_63_56,
      beq_self_eq_true, beq_iff_eq, ite_true, ite_false, ui64_add_zero, ui64_zero_add, UInt64.add_assoc, *])

theorem centeredSubSubnodeSizeCell_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    runJvm 2000 f_Algorithm_centeredSubSubnodeSizeCell_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId)] [arena]) =
      some (.i64 (Algorithm.centeredSubSubnodeSizeCell arena nodeId)) := by
  apply runJvm_of_runJvmValFast0 2000 _ _ _ rfl
  step_flat_tree f_Algorithm_centeredSubSubnodeSizeCell_prog
  all_goals (
    try simp only [decide_eq_true_eq] at *
    try simp only [getArenaU64, getArenaU32, getArenaU8,
      u8_sext_beq_five, u8_sext_beq_six, u8_sext_beq_seven, beq_iff_eq] at *
    try simp only [decide_eq_true_eq] at *
    try simp only [Algorithm.centeredSubSubnodeSizeCell, Algorithm.popLevel4Id, Algorithm.popcount64,
      centeredSubnodeLevel4_jvm_fold, shift_and_63_1, shift_and_63_2, shift_and_63_4, shift_and_63_56,
      u8_6_eq_5, u8_7_eq_5, u8_7_eq_6,
      beq_self_eq_true, beq_iff_eq, ite_true, ite_false, ui64_add_zero, ui64_zero_add, UInt64.add_assoc, *])

end SubBatch23

section Batch3

private theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl

private theorem lvl_shift_lt (lvl : UInt32) (h : lvl < 32) :
    ((lvl &&& 63).toUInt64) = lvl.toUInt64 := by
  have h1 : lvl &&& 63 = lvl := by
    apply UInt32.eq_of_toBitVec_eq
    have hbv : lvl.toBitVec < 32#32 := h
    bv_check "lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.lvl_shift_lt.lrat"
  simp [h1]

private theorem ui32_add1_toNat {a b : UInt32} (h : a < b) :
    (a + 1).toNat = a.toNat + 1 := by
  have ha : a.toNat < b.toNat := h
  have hb : b.toNat < 2 ^ 32 := UInt32.toNat_lt b
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_one]
  exact Nat.mod_eq_of_lt (by omega)

private theorem ui32_sub1_toNat {a : UInt32} (h : a ≠ 0) :
    (a - 1).toNat = a.toNat - 1 := by
  have hpos : 0 < a.toNat := Nat.pos_of_ne_zero fun hz =>
    h (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hz))
  have hle : (1 : UInt32) ≤ a := by
    show 1 ≤ a.toNat; omega
  rw [UInt32.toNat_sub_of_le a 1 hle]
  rfl

private theorem levelForSpanLoop_aux (n : Nat) :
    ∀ (k : Nat) (span : UInt64) (lvl : UInt32) (_hn : 32 - lvl.toNat ≤ n) (base : Nat → JvmVal),
    runJvmValFast (k + (n + 1) * 40) f_Algorithm_levelForSpanLoop_prog 0 f_Algorithm_levelForSpanLoop_prog
      ⟨0, [], setLocal (setLocal base 0 (.i64 span)) 2 (.i32 lvl), [], [], []⟩ =
      some (.i32 (Algorithm.levelForSpanLoop span lvl)) := by
  induction n with
  | zero =>
    intro k span lvl _hn base
    have hge : ¬ (lvl < 32) := by
      intro hlt; have : lvl.toNat < 32 := hlt; omega
    rw [show k + (0 + 1) * 40 = k + 40 by omega]
    flat_step_blk f_Algorithm_levelForSpanLoop_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_levelForSpanLoop_prog
    rw [Algorithm.levelForSpanLoop]
    simp [hge]
  | succ n ih =>
    intro k span lvl _hn base
    rw [show k + (n + 1 + 1) * 40 = (k + (n + 1) * 40) + 40 by omega]
    flat_step_blk f_Algorithm_levelForSpanLoop_prog
    rw [compareUnsigned_slt']
    by_cases hlt : lvl < 32
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_levelForSpanLoop_prog
      rw [compareUnsigned64_slt']
      by_cases hltsp : ((1 : UInt64) <<< (lvl &&& 63).toUInt64) < span
      · simp only [hltsp, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_levelForSpanLoop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((n + 1) * 40), Nat.add_comm ((n + 1) * 40)]
        rw [Algorithm.levelForSpanLoop]
        have hltsp' : ((1 : UInt64) <<< lvl.toUInt64) < span := by
          rwa [lvl_shift_lt lvl hlt] at hltsp
        simp only [hlt, hltsp', and_self, ↓reduceDIte]
        have hnext : 32 - (lvl + 1).toNat ≤ n := by
          have := ui32_add1_toNat hlt; omega
        exact ih _ span (lvl + 1) hnext _
      · simp only [hltsp, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_levelForSpanLoop_prog
        rw [Algorithm.levelForSpanLoop]
        have hnot : ¬ ((1 : UInt64) <<< lvl.toUInt64 < span) := by
          rwa [lvl_shift_lt lvl hlt] at hltsp
        simp [hlt, hnot]
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_levelForSpanLoop_prog
      rw [Algorithm.levelForSpanLoop]
      simp [hlt]

theorem levelForSpanLoop_equiv (span : UInt64) (lvl : UInt32) :
    runJvm 1320 f_Algorithm_levelForSpanLoop_prog
      (initJvmState [(0, .i64 span), (2, .i32 lvl)]) =
      some (.i32 (Algorithm.levelForSpanLoop span lvl)) := by
  apply runJvm_of_runJvmValFast0 1320 _ _ _ rfl
  exact levelForSpanLoop_aux 32 0 span lvl (by omega) _

private theorem countChars_aux (m : Nat) :
    ∀ (k : Nat) (bytes : ByteArray) (limit p cnt : UInt32)
      (_hn : limit.toNat - p.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 50) f_Algorithm_countChars_prog 3 (f_Algorithm_countChars_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal (setLocal base 0 (.byteArr bytes)) 1 (.i32 limit)) 2 (.i32 p)) 3 (.i32 cnt),
        [], [], []⟩ =
      some (.i32 (Algorithm.countChars bytes limit p cnt)) := by
  induction m with
  | zero =>
    intro k bytes limit p cnt _hn base
    have hge : ¬ (p < limit) := by
      intro hlt; have : p.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 50 = k + 50 by omega]
    flat_step_blk f_Algorithm_countChars_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_countChars_prog
    rw [Algorithm.countChars]
    simp [hge]
  | succ m ih =>
    intro k bytes limit p cnt _hn base
    rw [show k + (m + 1 + 1) * 50 = (k + (m + 1) * 50) + 50 by omega]
    flat_step_blk f_Algorithm_countChars_prog
    rw [compareUnsigned_slt']
    by_cases hlt : p < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_countChars_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 50), Nat.add_comm ((m + 1) * 50)]
      rw [Algorithm.countChars]
      simp only [hlt, ↓reduceDIte]
      have hd := Algorithm.decodeCharAt_next bytes p limit hlt
      have hnext : limit.toNat - (Algorithm.decodeCharAt bytes p limit).2.toNat ≤ m := by omega
      exact ih _ bytes limit (Algorithm.decodeCharAt bytes p limit).2 (cnt + 1) hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_countChars_prog
      rw [Algorithm.countChars]
      simp [hlt]

theorem countChars_equiv (bytes : ByteArray) (limit p n : UInt32) :
    runJvm ((limit.toNat - p.toNat + 1) * 50 + 3) f_Algorithm_countChars_prog
      (initJvmState [(0, .byteArr bytes), (1, .i32 limit), (2, .i32 p), (3, .i32 n)]) =
      some (.i32 (Algorithm.countChars bytes limit p n)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - p.toNat + 1) * 50)]
  exact countChars_aux (limit.toNat - p.toNat) 0 bytes limit p n (by omega) _

private theorem emptyMacroCellUInt32_loop_aux (m : Nat) :
    ∀ (k : Nat) (level curLevel : UInt32) (curNode : Algorithm.MacroCell)
      (_hn : level.toNat - curLevel.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 40) f_Algorithm_emptyMacroCellUInt32_loop_prog 3
      (f_Algorithm_emptyMacroCellUInt32_loop_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal base 0 (.i32 level)) 1 (.i32 curLevel)) 2 (.mc curNode),
        [], [], []⟩ =
      some (.mc (Algorithm.emptyMacroCellUInt32.loop level curLevel curNode)) := by
  induction m with
  | zero =>
    intro k level curLevel curNode _hn base
    have hge : ¬ (curLevel < level) := by
      intro hlt; have : curLevel.toNat < level.toNat := hlt; omega
    rw [show k + (0 + 1) * 40 = k + 40 by omega]
    flat_step_blk f_Algorithm_emptyMacroCellUInt32_loop_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_emptyMacroCellUInt32_loop_prog
    rw [Algorithm.emptyMacroCellUInt32.loop]
    simp [hge]
  | succ m ih =>
    intro k level curLevel curNode _hn base
    rw [show k + (m + 1 + 1) * 40 = (k + (m + 1) * 40) + 40 by omega]
    flat_step_blk f_Algorithm_emptyMacroCellUInt32_loop_prog
    rw [compareUnsigned_slt']
    by_cases hlt : curLevel < level
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_emptyMacroCellUInt32_loop_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 40), Nat.add_comm ((m + 1) * 40)]
      rw [Algorithm.emptyMacroCellUInt32.loop]
      simp only [hlt, ↓reduceDIte]
      have hnext : level.toNat - (curLevel + 1).toNat ≤ m := by
        have := ui32_add1_toNat hlt; omega
      exact ih _ level (curLevel + 1) (Algorithm.makeCellNode curNode curNode curNode curNode) hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_emptyMacroCellUInt32_loop_prog
      rw [Algorithm.emptyMacroCellUInt32.loop]
      simp [hlt]

theorem emptyMacroCellUInt32_loop_equiv (level curLevel : UInt32) (curNode : Algorithm.MacroCell) :
    runJvm ((level.toNat - curLevel.toNat + 1) * 40 + 3) f_Algorithm_emptyMacroCellUInt32_loop_prog
      (initJvmState [(0, .i32 level), (1, .i32 curLevel), (2, .mc curNode)]) =
      some (.mc (Algorithm.emptyMacroCellUInt32.loop level curLevel curNode)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((level.toNat - curLevel.toNat + 1) * 40)]
  exact emptyMacroCellUInt32_loop_aux (level.toNat - curLevel.toNat) 0 level curLevel curNode (by omega) _

private theorem stepNGenerationsWith_aux (m : Nat) :
    ∀ (k : Nat) (step : UInt32) (st : Algorithm.HashLifeStepState)
      (stepOneGen : Algorithm.HashLifeStepState → Algorithm.HashLifeStepState)
      (_hn : step.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 40) f_Algorithm_stepNGenerationsWith_prog 3 (f_Algorithm_stepNGenerationsWith_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal base 0 (.i32 step)) 1 (.hlState st)) 2 (.fnHlToHl stepOneGen),
        [], [], []⟩ =
      some (.hlState (Algorithm.stepNGenerationsWith step st stepOneGen)) := by
  induction m with
  | zero =>
    intro k step st stepOneGen _hn base
    have hz : step = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by simp; omega))
    rw [show k + (0 + 1) * 40 = k + 40 by omega]
    flat_step_blk f_Algorithm_stepNGenerationsWith_prog
    simp only [hz, beq_self_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_stepNGenerationsWith_prog
    rw [Algorithm.stepNGenerationsWith]
    simp
  | succ m ih =>
    intro k step st stepOneGen _hn base
    rw [show k + (m + 1 + 1) * 40 = (k + (m + 1) * 40) + 40 by omega]
    flat_step_blk f_Algorithm_stepNGenerationsWith_prog
    by_cases hz : step = 0
    · simp only [hz, beq_self_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_stepNGenerationsWith_prog
      rw [Algorithm.stepNGenerationsWith]
      simp
    · simp only [beq_iff_eq, hz, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_stepNGenerationsWith_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 40), Nat.add_comm ((m + 1) * 40)]
      rw [Algorithm.stepNGenerationsWith]
      simp only [hz]
      have hnext : (step - 1).toNat ≤ m := by
        have := ui32_sub1_toNat hz; omega
      exact ih _ (step - 1) (stepOneGen st) stepOneGen hnext _

theorem stepNGenerationsWith_equiv (step : UInt32) (st : Algorithm.HashLifeStepState)
    (stepOneGen : Algorithm.HashLifeStepState → Algorithm.HashLifeStepState) :
    runJvm ((step.toNat + 1) * 40 + 3) f_Algorithm_stepNGenerationsWith_prog
      (initJvmState [(0, .i32 step), (1, .hlState st), (2, .fnHlToHl stepOneGen)]) =
      some (.hlState (Algorithm.stepNGenerationsWith step st stepOneGen)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((step.toNat + 1) * 40)]
  exact stepNGenerationsWith_aux step.toNat 0 step st stepOneGen (by omega) _

private theorem copyU64_aux (m : Nat) :
    ∀ (k : Nat) (src : Array UInt64) (n i : UInt32) (dst : Array UInt64)
      (_hn : n.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 40) f_Algorithm_copyU64_prog 0 f_Algorithm_copyU64_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal base 0 (.u64Ref 0)) 1 (.i32 n)) 2 (.i32 i)) 3 (.u64Ref 1),
        [], [src, dst], []⟩).map (fun p => (p.1, p.2.u64Arrays)) =
      some (.unit, [src, Algorithm.copyU64 src n i dst]) := by
  induction m with
  | zero =>
    intro k src n i dst _hn base
    have hge : ¬ (i < n) := by
      intro hlt; have : i.toNat < n.toNat := hlt; omega
    rw [show k + (0 + 1) * 40 = k + 40 by omega]
    flat_step_blk f_Algorithm_copyU64_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_copyU64_prog
    rw [Algorithm.copyU64]
    simp [hge]
  | succ m ih =>
    intro k src n i dst _hn base
    rw [show k + (m + 1 + 1) * 40 = (k + (m + 1) * 40) + 40 by omega]
    flat_step_blk f_Algorithm_copyU64_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < n
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_copyU64_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 40), Nat.add_comm ((m + 1) * 40)]
      rw [Algorithm.copyU64]
      simp only [hlt, ↓reduceDIte]
      have hnext : n.toNat - (i + 1).toNat ≤ m := by
        have := ui32_add1_toNat hlt; omega
      exact ih _ src n (i + 1) (dst.set! i.toNat src[i.toNat]!) hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_copyU64_prog
      rw [Algorithm.copyU64]
      simp [hlt]

theorem copyU64_equiv (src : Array UInt64) (n i : UInt32) (dst : Array UInt64) :
    (runJvmRes ((n.toNat - i.toNat + 1) * 40) f_Algorithm_copyU64_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 n), (2, .i32 i), (3, .u64Ref 1)] [] [src, dst])).map
        (fun p => (p.1, p.2.u64Arrays)) =
      some (.unit, [src, Algorithm.copyU64 src n i dst]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  rw [← Nat.zero_add ((n.toNat - i.toNat + 1) * 40)]
  exact copyU64_aux (n.toNat - i.toNat) 0 src n i dst (by omega) _

theorem copyU64_1_equiv (src : Array UInt64) (n i : UInt32) (dst : Array UInt64) :
    (runJvmRes ((n.toNat - i.toNat + 1) * 40) f_Algorithm_copyU64_1_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 n), (2, .i32 i), (3, .u64Ref 1)] [] [src, dst])).map
        (fun p => (p.1, p.2.u64Arrays)) =
      some (.unit, [src, Algorithm.copyU64 src n i dst]) :=
  copyU64_equiv src n i dst

theorem copyU64_2_equiv (src : Array UInt64) (n i : UInt32) (dst : Array UInt64) :
    (runJvmRes ((n.toNat - i.toNat + 1) * 40) f_Algorithm_copyU64_2_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 n), (2, .i32 i), (3, .u64Ref 1)] [] [src, dst])).map
        (fun p => (p.1, p.2.u64Arrays)) =
      some (.unit, [src, Algorithm.copyU64 src n i dst]) :=
  copyU64_equiv src n i dst

theorem copyU64_3_equiv (src : Array UInt64) (n i : UInt32) (dst : Array UInt64) :
    (runJvmRes ((n.toNat - i.toNat + 1) * 40) f_Algorithm_copyU64_3_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 n), (2, .i32 i), (3, .u64Ref 1)] [] [src, dst])).map
        (fun p => (p.1, p.2.u64Arrays)) =
      some (.unit, [src, Algorithm.copyU64 src n i dst]) :=
  copyU64_equiv src n i dst

theorem copyU64_4_equiv (src : Array UInt64) (n i : UInt32) (dst : Array UInt64) :
    (runJvmRes ((n.toNat - i.toNat + 1) * 40) f_Algorithm_copyU64_4_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 n), (2, .i32 i), (3, .u64Ref 1)] [] [src, dst])).map
        (fun p => (p.1, p.2.u64Arrays)) =
      some (.unit, [src, Algorithm.copyU64 src n i dst]) :=
  copyU64_equiv src n i dst

private theorem gridRows_aux (m : Nat) :
    ∀ (k : Nat) (g : Algorithm.AsciiBytes) (width height r : UInt32) (acc : Algorithm.GrowBuf String)
      (_hn : height.toNat - r.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 60) f_Algorithm_gridRows_prog 0 f_Algorithm_gridRows_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal base 0 (.asciiRef 0)) 1 (.i32 width))
        2 (.i32 height)) 3 (.i32 r)) 4 (.strGrowBuf acc), [], [], [g]⟩ =
      some (.strGrowBuf (Algorithm.gridRows g width height r acc)) := by
  induction m with
  | zero =>
    intro k g width height r acc _hn base
    have hge : ¬ (r < height) := by
      intro hlt; have : r.toNat < height.toNat := hlt; omega
    rw [show k + (0 + 1) * 60 = k + 60 by omega]
    flat_step_blk f_Algorithm_gridRows_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_gridRows_prog
    rw [Algorithm.gridRows]
    simp [hge]
  | succ m ih =>
    intro k g width height r acc _hn base
    rw [show k + (m + 1 + 1) * 60 = (k + (m + 1) * 60) + 60 by omega]
    flat_step_blk f_Algorithm_gridRows_prog
    rw [compareUnsigned_slt']
    by_cases hlt : r < height
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_gridRows_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 60), Nat.add_comm ((m + 1) * 60)]
      rw [Algorithm.gridRows]
      simp only [hlt, ↓reduceDIte]
      have hnext : height.toNat - (r + 1).toNat ≤ m := by
        have := ui32_add1_toNat hlt; omega
      exact ih _ g width height (r + 1) (acc.push (g.toStringRange (r * width) (r * width + width))) hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_gridRows_prog
      rw [Algorithm.gridRows]
      simp [hlt]

theorem gridRows_equiv (g : Algorithm.AsciiBytes) (width height r : UInt32) (acc : Algorithm.GrowBuf String) :
    runJvm ((height.toNat - r.toNat + 1) * 60) f_Algorithm_gridRows_prog
      (initJvmState [(0, .asciiRef 0), (1, .i32 width), (2, .i32 height), (3, .i32 r), (4, .strGrowBuf acc)]
        [] [] [g]) =
      some (.strGrowBuf (Algorithm.gridRows g width height r acc)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  rw [← Nat.zero_add ((height.toNat - r.toNat + 1) * 60)]
  exact gridRows_aux (height.toNat - r.toNat) 0 g width height r acc (by omega) _

private theorem gridRows_1_aux (m : Nat) :
    ∀ (k : Nat) (g : Algorithm.AsciiBytes) (width height r : UInt32) (acc : Algorithm.GrowBuf String)
      (_hn : height.toNat - r.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 60) f_Algorithm_gridRows_1_prog 0 f_Algorithm_gridRows_1_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal base 0 (.asciiRef 0)) 1 (.i32 width))
        2 (.i32 height)) 3 (.i32 r)) 4 (.strGrowBuf acc), [], [], [g]⟩ =
      some (.strGrowBuf (Algorithm.gridRows g width height r acc)) := by
  induction m with
  | zero =>
    intro k g width height r acc _hn base
    have hge : ¬ (r < height) := by
      intro hlt; have : r.toNat < height.toNat := hlt; omega
    rw [show k + (0 + 1) * 60 = k + 60 by omega]
    flat_step_blk f_Algorithm_gridRows_1_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_gridRows_1_prog
    rw [Algorithm.gridRows]
    simp [hge]
  | succ m ih =>
    intro k g width height r acc _hn base
    rw [show k + (m + 1 + 1) * 60 = (k + (m + 1) * 60) + 60 by omega]
    flat_step_blk f_Algorithm_gridRows_1_prog
    rw [compareUnsigned_slt']
    by_cases hlt : r < height
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_gridRows_1_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 60), Nat.add_comm ((m + 1) * 60)]
      rw [Algorithm.gridRows]
      simp only [hlt, ↓reduceDIte]
      have hnext : height.toNat - (r + 1).toNat ≤ m := by
        have := ui32_add1_toNat hlt; omega
      exact ih _ g width height (r + 1) (acc.push (g.toStringRange (r * width) (r * width + width))) hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_gridRows_1_prog
      rw [Algorithm.gridRows]
      simp [hlt]

theorem gridRows_1_equiv (g : Algorithm.AsciiBytes) (width height r : UInt32) (acc : Algorithm.GrowBuf String) :
    runJvm ((height.toNat - r.toNat + 1) * 60) f_Algorithm_gridRows_1_prog
      (initJvmState [(0, .asciiRef 0), (1, .i32 width), (2, .i32 height), (3, .i32 r), (4, .strGrowBuf acc)]
        [] [] [g]) =
      some (.strGrowBuf (Algorithm.gridRows g width height r acc)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  rw [← Nat.zero_add ((height.toNat - r.toNat + 1) * 60)]
  exact gridRows_1_aux (height.toNat - r.toNat) 0 g width height r acc (by omega) _

private theorem serializeLife106_loop_aux (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (i limit : UInt32) (acc : Algorithm.GrowBuf String)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 60) f_Algorithm_serializeLife106_loop_prog 3
      (f_Algorithm_serializeLife106_loop_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal (setLocal base 0 (.u64Ref 0)) 1 (.i32 i)) 2 (.i32 limit)) 3 (.strGrowBuf acc),
        [], [cells], []⟩ =
      some (.strGrowBuf (Algorithm.serializeLife106.loop cells i limit acc)) := by
  induction m with
  | zero =>
    intro k cells i limit acc _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 60 = k + 60 by omega]
    flat_step_blk f_Algorithm_serializeLife106_loop_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_serializeLife106_loop_prog
    rw [Algorithm.serializeLife106.loop]
    simp [hge]
  | succ m ih =>
    intro k cells i limit acc _hn base
    rw [show k + (m + 1 + 1) * 60 = (k + (m + 1) * 60) + 60 by omega]
    flat_step_blk f_Algorithm_serializeLife106_loop_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_serializeLife106_loop_prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
      rw [Nat.add_left_comm k ((m + 1) * 60), Nat.add_comm ((m + 1) * 60)]
      rw [Algorithm.serializeLife106.loop]
      simp only [hlt, ↓reduceDIte]
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        have := ui32_add1_toNat hlt; omega
      exact ih _ cells (i + 1) limit
        (acc.push (Algorithm.formatCoordLine (Algorithm.cellKeyX cells[i.toNat]!) (Algorithm.cellKeyY cells[i.toNat]!)))
        hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_serializeLife106_loop_prog
      rw [Algorithm.serializeLife106.loop]
      simp [hlt]

theorem serializeLife106_loop_equiv (cells : Array UInt64) (i limit : UInt32) (acc : Algorithm.GrowBuf String) :
    runJvm ((limit.toNat - i.toNat + 1) * 60 + 3) f_Algorithm_serializeLife106_loop_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 i), (2, .i32 limit), (3, .strGrowBuf acc)] [] [cells]) =
      some (.strGrowBuf (Algorithm.serializeLife106.loop cells i limit acc)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 60)]
  exact serializeLife106_loop_aux (limit.toNat - i.toNat) 0 cells i limit acc (by omega) _

private theorem fuel_split {C : Nat} (k F r : Nat) (h : C ≤ r) :
    k + r + F = k + (r - C) + F + C := by omega

private theorem ui32_toInt32_mk (w : UInt32) : ({ toUInt32 := w } : Int32) = w.toInt32 := rfl

private theorem cellKeyX_sub_minX (k : UInt64) (minX : Int32) :
    ((Algorithm.cellKeyX k).toInt32 - minX).toUInt32 = (k >>> 32).toUInt32 - minX.toUInt32 := by
  unfold Algorithm.cellKeyX; bv_normalize

private theorem cellKeyY_sub_minY (k : UInt64) (minY : Int32) :
    ((Algorithm.cellKeyY k).toInt32 - minY).toUInt32 = k.toUInt32 - minY.toUInt32 := by
  unfold Algorithm.cellKeyY; bv_normalize

private theorem shift_32_and_63 : ((32 : UInt32) &&& 63).toUInt64 = 32 := rfl

private theorem int32_toUInt32_toInt32 (x : Int32) : x.toUInt32.toInt32 = x := by
  cases x; rfl

private theorem ui32_toInt32_x_eq (k : UInt64) : (Algorithm.cellKeyX k).toInt32 = (k >>> 32).toUInt32.toInt32 := rfl

private theorem ui32_toInt32_y_eq (k : UInt64) : (Algorithm.cellKeyY k).toInt32 = k.toUInt32.toInt32 := rfl

private theorem min_u64_eq (a b : UInt64) : min a b = if a ≤ b then a else b := rfl
private theorem max_u64_eq (a b : UInt64) : max a b = if a ≤ b then b else a := rfl
private theorem keyHi_eq (k : UInt64) : Algorithm.keyHi k = k >>> 32 := rfl
private theorem keyLo_eq (k : UInt64) : Algorithm.keyLo k = k &&& 4294967295 := rfl

private theorem u8_toUInt32_toUInt8 (b : UInt8) : b.toUInt32.toUInt8 = b := by
  apply UInt8.eq_of_toBitVec_eq; bv_normalize

private theorem cellBounds_slt (a b : UInt32) :
    (a.toBitVec.slt b.toBitVec) = decide (a.toInt32 < b.toInt32) := rfl

local macro "prove_fillGrid_zero" prog:ident : tactic => `(tactic| (
  intro k cells minX minY width height alive halive i limit g _hn base
  have hge : ¬ (i < limit) := by
    intro hlt; have : i.toNat < limit.toNat := hlt; omega
  rw [show k + (0 + 1) * 90 = k + 90 by omega]
  flat_step_blk $prog
  rw [compareUnsigned_slt']
  simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
  flat_step_blk $prog
  unfold Algorithm.fillGrid
  simp [hge]))

local macro "prove_fillGrid_succ" m:ident prog:ident setThm:ident ih:ident : tactic => `(tactic| (
  intro k cells minX minY width height alive halive i limit g _hn base
  rw [show k + ($m + 1 + 1) * 90 = (k + ($m + 1) * 90) + 90 by omega]
  flat_step_blk $prog
  rw [compareUnsigned_slt']
  by_cases hlt : i < limit
  · simp only [hlt, decide_true, ↓reduceIte]
    have hltNat : i.toNat < limit.toNat := hlt
    have hnext : limit.toNat - (i + 1).toNat ≤ $m := by
      rw [ui32_add1_toNat hlt]; omega
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk $prog
    rw [shift_32_and_63, compareUnsigned_sge']
    by_cases hx : width ≤ (cells[i.toNat]! >>> 32).toUInt32 - minX.toUInt32
    · simp only [hx, decide_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk $prog
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      try (repeat rw [Nat.succ_eq_add_one])
      simp only [nat_add_eq, Nat.add_assoc]
      rw [Nat.add_left_comm k (($m + 1) * 90), Nat.add_comm (($m + 1) * 90)]
      have hnot : ¬ ((cells[i.toNat]! >>> 32).toUInt32 - minX.toUInt32 < width) := Nat.not_lt.mpr hx
      unfold Algorithm.fillGrid
      simp only [hlt, ↓reduceDIte, cellKeyX_sub_minX, hnot, decide_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      exact $ih _ cells minX minY width height alive halive (i + 1) limit g hnext _
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk $prog
      rw [compareUnsigned_sge']
      by_cases hy : height ≤ cells[i.toNat]!.toUInt32 - minY.toUInt32
      · simp only [hy, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk $prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try (repeat rw [Nat.succ_eq_add_one])
        simp only [nat_add_eq, Nat.add_assoc]
        (try rw [show ($m + 1).mul 89 + ($m + 1) = ($m + 1) * 90 from rfl])
        (try rw [Nat.add_left_comm k (($m + 1) * 90), Nat.add_comm (($m + 1) * 90)])
        have hnot : ¬ (cells[i.toNat]!.toUInt32 - minY.toUInt32 < height) := Nat.not_lt.mpr hy
        have hokx : (cells[i.toNat]! >>> 32).toUInt32 - minX.toUInt32 < width := Nat.lt_of_not_le hx
        unfold Algorithm.fillGrid
        simp only [hlt, ↓reduceDIte, cellKeyX_sub_minX, cellKeyY_sub_minY, hokx, hnot,
          decide_true, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact $ih _ cells minX minY width height alive halive (i + 1) limit g hnext _
      · simp only [hy, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_nonbranch_chunks
        (conv => lhs; arg 2; rw [runJvmResFast_invokestatic_step ($setThm rfl (by simpa [JvmVal.asI32, u8_toUInt32_toUInt8] using halive))])
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk $prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try (repeat rw [Nat.succ_eq_add_one])
        simp only [nat_add_eq, Nat.add_assoc]
        (try rw [show ($m + 1).mul 89 + ($m + 1) = ($m + 1) * 90 from rfl])
        (try rw [Nat.add_left_comm k (($m + 1) * 90), Nat.add_comm (($m + 1) * 90)])
        have hokx : (cells[i.toNat]! >>> 32).toUInt32 - minX.toUInt32 < width := Nat.lt_of_not_le hx
        have hoky : cells[i.toNat]!.toUInt32 - minY.toUInt32 < height := Nat.lt_of_not_le hy
        unfold Algorithm.fillGrid
        simp only [hlt, ↓reduceDIte, cellKeyX_sub_minX, cellKeyY_sub_minY, hokx, hoky,
          decide_true, Bool.and_self, ↓reduceIte, u8_toUInt32_toUInt8]
        exact $ih _ cells minX minY width height alive halive (i + 1) limit _ hnext _
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk $prog
    unfold Algorithm.fillGrid
    simp [hlt]))

private theorem fillGrid_0_step (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (minX minY : Int32) (width height : UInt32)
      (alive : UInt8) (halive : alive < 128) (i limit : UInt32) (g : Algorithm.AsciiBytes)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 90) f_Algorithm_fillGrid___redArg_prog 0 f_Algorithm_fillGrid___redArg_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 (.u64Ref 0)) 1 (.i32 minX.toUInt32)) 2 (.i32 minY.toUInt32)) 3 (.i32 width))
        4 (.i32 height)) 5 (.i32 alive.toUInt32)) 6 (.i32 i)) 7 (.i32 limit)) 8 (.asciiRef 0),
        [], [cells], [g]⟩).map (fun p => (p.1, p.2.asciiArrays)) =
      some (.unit, [Algorithm.fillGrid cells minX minY width height alive halive i limit g]) := by
  induction m with
  | zero => prove_fillGrid_zero f_Algorithm_fillGrid___redArg_prog
  | succ m ih => prove_fillGrid_succ m f_Algorithm_fillGrid___redArg_prog stepStatic_asciiSet_105 ih

private theorem fillGrid_1_step (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (minX minY : Int32) (width height : UInt32)
      (alive : UInt8) (halive : alive < 128) (i limit : UInt32) (g : Algorithm.AsciiBytes)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 90) f_Algorithm_fillGrid___redArg_1_prog 0 f_Algorithm_fillGrid___redArg_1_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 (.u64Ref 0)) 1 (.i32 minX.toUInt32)) 2 (.i32 minY.toUInt32)) 3 (.i32 width))
        4 (.i32 height)) 5 (.i32 alive.toUInt32)) 6 (.i32 i)) 7 (.i32 limit)) 8 (.asciiRef 0),
        [], [cells], [g]⟩).map (fun p => (p.1, p.2.asciiArrays)) =
      some (.unit, [Algorithm.fillGrid cells minX minY width height alive halive i limit g]) := by
  induction m with
  | zero => prove_fillGrid_zero f_Algorithm_fillGrid___redArg_1_prog
  | succ m ih => prove_fillGrid_succ m f_Algorithm_fillGrid___redArg_1_prog stepStatic_asciiSet_plain ih

private theorem fillGrid_2_step (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (minX minY : Int32) (width height : UInt32)
      (alive : UInt8) (halive : alive < 128) (i limit : UInt32) (g : Algorithm.AsciiBytes)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 90) f_Algorithm_fillGrid___redArg_2_prog 0 f_Algorithm_fillGrid___redArg_2_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 (.u64Ref 0)) 1 (.i32 minX.toUInt32)) 2 (.i32 minY.toUInt32)) 3 (.i32 width))
        4 (.i32 height)) 5 (.i32 alive.toUInt32)) 6 (.i32 i)) 7 (.i32 limit)) 8 (.asciiRef 0),
        [], [cells], [g]⟩).map (fun p => (p.1, p.2.asciiArrays)) =
      some (.unit, [Algorithm.fillGrid cells minX minY width height alive halive i limit g]) := by
  induction m with
  | zero => prove_fillGrid_zero f_Algorithm_fillGrid___redArg_2_prog
  | succ m ih => prove_fillGrid_succ m f_Algorithm_fillGrid___redArg_2_prog stepStatic_asciiSet_rle ih

theorem fillGrid_equiv (cells : Array UInt64) (minX minY : Int32) (width height : UInt32)
    (alive : UInt8) (halive : alive < 128) (i limit : UInt32) (g : Algorithm.AsciiBytes) :
    (runJvmRes ((limit.toNat - i.toNat + 1) * 90) f_Algorithm_fillGrid___redArg_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 minX.toUInt32), (2, .i32 minY.toUInt32),
        (3, .i32 width), (4, .i32 height), (5, .i32 alive.toUInt32), (6, .i32 i),
        (7, .i32 limit), (8, .asciiRef 0)] [] [cells] [g])).map
        (fun p => (p.1, p.2.asciiArrays)) =
      some (.unit, [Algorithm.fillGrid cells minX minY width height alive halive i limit g]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 90)]
  exact fillGrid_0_step (limit.toNat - i.toNat) 0 cells minX minY width height alive halive i limit g (by omega) _

theorem fillGrid_1_equiv (cells : Array UInt64) (minX minY : Int32) (width height : UInt32)
    (alive : UInt8) (halive : alive < 128) (i limit : UInt32) (g : Algorithm.AsciiBytes) :
    (runJvmRes ((limit.toNat - i.toNat + 1) * 90) f_Algorithm_fillGrid___redArg_1_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 minX.toUInt32), (2, .i32 minY.toUInt32),
        (3, .i32 width), (4, .i32 height), (5, .i32 alive.toUInt32), (6, .i32 i),
        (7, .i32 limit), (8, .asciiRef 0)] [] [cells] [g])).map
        (fun p => (p.1, p.2.asciiArrays)) =
      some (.unit, [Algorithm.fillGrid cells minX minY width height alive halive i limit g]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 90)]
  exact fillGrid_1_step (limit.toNat - i.toNat) 0 cells minX minY width height alive halive i limit g (by omega) _

theorem fillGrid_2_equiv (cells : Array UInt64) (minX minY : Int32) (width height : UInt32)
    (alive : UInt8) (halive : alive < 128) (i limit : UInt32) (g : Algorithm.AsciiBytes) :
    (runJvmRes ((limit.toNat - i.toNat + 1) * 90) f_Algorithm_fillGrid___redArg_2_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 minX.toUInt32), (2, .i32 minY.toUInt32),
        (3, .i32 width), (4, .i32 height), (5, .i32 alive.toUInt32), (6, .i32 i),
        (7, .i32 limit), (8, .asciiRef 0)] [] [cells] [g])).map
        (fun p => (p.1, p.2.asciiArrays)) =
      some (.unit, [Algorithm.fillGrid cells minX minY width height alive halive i limit g]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 90)]
  exact fillGrid_2_step (limit.toNat - i.toNat) 0 cells minX minY width height alive halive i limit g (by omega) _

private theorem cellBounds_aux (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (i limit : UInt32) (minX maxX minY maxY : Int32)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 160) f_Algorithm_cellBounds_prog 0 f_Algorithm_cellBounds_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 (.u64Ref 0)) 1 (.i32 i)) 2 (.i32 limit)) 3 (.i32 minX.toUInt32)) 4 (.i32 maxX.toUInt32))
        5 (.i32 minY.toUInt32)) 6 (.i32 maxY.toUInt32), [], [cells], []⟩ =
      some (boxCellBox (Algorithm.cellBounds cells i limit minX maxX minY maxY)) := by
  induction m with
  | zero =>
    intro k cells i limit minX maxX minY maxY _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 160 = k + 160 by omega]
    flat_step_blk f_Algorithm_cellBounds_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_cellBounds_prog
    unfold Algorithm.cellBounds
    simp [hge, boxCellBox]
  | succ m ih =>
    intro k cells i limit minX maxX minY maxY _hn base
    rw [show k + (m + 1 + 1) * 160 = (k + (m + 1) * 160) + 160 by omega]
    flat_step_blk f_Algorithm_cellBounds_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      have hltNat : i.toNat < limit.toNat := hlt
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        rw [ui32_add1_toNat hlt]; omega
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_cellBounds_prog
      let kv := cells[i.toNat]!
      let x := (kv >>> 32).toUInt32.toInt32
      let y := kv.toUInt32.toInt32
      let minX' := if x < minX then x else minX
      let maxX' := if maxX < x then x else maxX
      let minY' := if y < minY then y else minY
      let maxY' := if maxY < y then y else maxY
      have hx_def : (cells[i.toNat]! >>> 32).toUInt32.toInt32 = x := rfl
      have hy_def : cells[i.toNat]!.toUInt32.toInt32 = y := rfl
      have hjoin3 : ∀ k3 (locs : Nat → JvmVal),
          locs 0 = .u64Ref 0 → locs 2 = .i32 limit → locs 6 = .i32 maxY.toUInt32 →
          locs 10 = .i32 y.toUInt32 → locs 11 = .i32 (i + 1) → locs 12 = .i32 maxX'.toUInt32 →
          locs 13 = .i32 minX'.toUInt32 → locs 14 = .i32 minY'.toUInt32 →
          (if maxY.toUInt32.toBitVec.slt y.toUInt32.toBitVec = true then
            runJvmValFast (k3 + (m + 1) * 160 + 50) f_Algorithm_cellBounds_prog 114
              (f_Algorithm_cellBounds_prog.drop 114) ⟨114, [], locs, [], [cells], []⟩
          else
            runJvmValFast (k3 + (m + 1) * 160 + 50) f_Algorithm_cellBounds_prog 93
              (f_Algorithm_cellBounds_prog.drop 93) ⟨93, [], locs, [], [cells], []⟩) =
            some (boxCellBox (Algorithm.cellBounds cells i limit minX maxX minY maxY)) := by
        intro k3 locs h0 h2 h6 h10 h11 h12 h13 h14
        rw [cellBounds_slt, int32_toUInt32_toInt32, int32_toUInt32_toInt32]
        unfold Algorithm.cellBounds
        simp only [hlt, ↓reduceDIte, ui32_toInt32_x_eq, ui32_toInt32_y_eq]
        by_cases hy2 : maxY < y
        · simp only [hy2, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBounds_prog
          (conv => lhs; simp only [h0, h2, h6, h10, h11, h12, h13, h14]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k3 ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
          have hy2' : maxY < cells[i.toNat]!.toUInt32.toInt32 := hy2
          (conv => rhs; simp only [hy2', ↓reduceIte])
          exact ih _ cells (i + 1) limit minX' maxX' minY' y hnext _
        · simp only [hy2, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBounds_prog
          (conv => lhs; simp only [h0, h2, h6, h10, h11, h12, h13, h14]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k3 ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
          have hy2' : ¬ (maxY < cells[i.toNat]!.toUInt32.toInt32) := hy2
          (conv => rhs; simp only [hy2', ↓reduceIte])
          exact ih _ cells (i + 1) limit minX' maxX' minY' maxY hnext _
      have hjoin2 : ∀ k2 (locs : Nat → JvmVal),
          locs 0 = .u64Ref 0 → locs 2 = .i32 limit → locs 5 = .i32 minY.toUInt32 →
          locs 6 = .i32 maxY.toUInt32 → locs 10 = .i32 y.toUInt32 → locs 11 = .i32 (i + 1) →
          locs 15 = .i32 minX'.toUInt32 → locs 16 = .i32 maxX'.toUInt32 →
          (if y.toUInt32.toBitVec.slt minY.toUInt32.toBitVec = true then
            runJvmValFast (k2 + (m + 1) * 160 + 80) f_Algorithm_cellBounds_prog 84
              (f_Algorithm_cellBounds_prog.drop 84) ⟨84, [], locs, [], [cells], []⟩
          else
            runJvmValFast (k2 + (m + 1) * 160 + 80) f_Algorithm_cellBounds_prog 77
              (f_Algorithm_cellBounds_prog.drop 77) ⟨77, [], locs, [], [cells], []⟩) =
            some (boxCellBox (Algorithm.cellBounds cells i limit minX maxX minY maxY)) := by
        intro k2 locs h0 h2 h5 h6 h10 h11 h15 h16
        rw [cellBounds_slt, int32_toUInt32_toInt32, int32_toUInt32_toInt32]
        by_cases hy1 : y < minY
        · simp only [hy1, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBounds_prog
          (conv => lhs; simp only [h0, h2, h5, h6, h10, h11, h15, h16]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k2 ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
          rw [fuel_split (C := 50) k2 ((m + 1) * 160) _ (by omega)]
          have hminY : minY' = y := by simp only [minY', hy1, ↓reduceIte]
          refine hjoin3 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h6
          · exact h10
          · exact h11
          · rfl
          · rfl
          · rw [hminY]; rfl
        · simp only [hy1, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBounds_prog
          (conv => lhs; simp only [h0, h2, h5, h6, h10, h11, h15, h16]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k2 ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
          rw [fuel_split (C := 50) k2 ((m + 1) * 160) _ (by omega)]
          have hminY : minY' = minY := by simp only [minY', hy1, ↓reduceIte]
          refine hjoin3 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h6
          · exact h10
          · exact h11
          · rfl
          · rfl
          · rw [hminY]; rfl
      have hjoin1 : ∀ k1 (locs : Nat → JvmVal),
          locs 0 = .u64Ref 0 → locs 2 = .i32 limit → locs 4 = .i32 maxX.toUInt32 →
          locs 5 = .i32 minY.toUInt32 → locs 6 = .i32 maxY.toUInt32 → locs 9 = .i32 x.toUInt32 →
          locs 10 = .i32 y.toUInt32 → locs 11 = .i32 (i + 1) → locs 17 = .i32 minX'.toUInt32 →
          (if maxX.toUInt32.toBitVec.slt x.toUInt32.toBitVec = true then
            runJvmValFast (k1 + (m + 1) * 160 + 100) f_Algorithm_cellBounds_prog 70
              (f_Algorithm_cellBounds_prog.drop 70) ⟨70, [], locs, [], [cells], []⟩
          else
            runJvmValFast (k1 + (m + 1) * 160 + 100) f_Algorithm_cellBounds_prog 65
              (f_Algorithm_cellBounds_prog.drop 65) ⟨65, [], locs, [], [cells], []⟩) =
            some (boxCellBox (Algorithm.cellBounds cells i limit minX maxX minY maxY)) := by
        intro k1 locs h0 h2 h4 h5 h6 h9 h10 h11 h17
        rw [cellBounds_slt, int32_toUInt32_toInt32, int32_toUInt32_toInt32]
        by_cases hx2 : maxX < x
        · simp only [hx2, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBounds_prog
          (conv => lhs; simp only [h0, h2, h4, h5, h6, h9, h10, h11, h17]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k1 ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
          rw [fuel_split (C := 80) k1 ((m + 1) * 160) _ (by omega)]
          have hmaxX : maxX' = x := by simp only [maxX', hx2, ↓reduceIte]
          refine hjoin2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h5
          · exact h6
          · exact h10
          · exact h11
          · rfl
          · rw [hmaxX]; rfl
        · simp only [hx2, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBounds_prog
          (conv => lhs; simp only [h0, h2, h4, h5, h6, h9, h10, h11, h17]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k1 ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
          rw [fuel_split (C := 80) k1 ((m + 1) * 160) _ (by omega)]
          have hmaxX : maxX' = maxX := by simp only [maxX', hx2, ↓reduceIte]
          refine hjoin2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h5
          · exact h6
          · exact h10
          · exact h11
          · rfl
          · rw [hmaxX]; rfl
      rw [cellBounds_slt, shift_32_and_63, show minX.toUInt32.toInt32 = minX from int32_toUInt32_toInt32 minX, hx_def]
      by_cases hx1 : x < minX
      · simp only [hx1, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_cellBounds_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
        rw [fuel_split (C := 100) k ((m + 1) * 160) _ (by omega)]
        have hminX : minX' = x := by simp only [minX', hx1, ↓reduceIte]
        exact hjoin1 _ _ rfl rfl rfl rfl rfl rfl rfl rfl (by rw [hminX]; rfl)
      · simp only [hx1, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_cellBounds_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 160), Nat.add_comm ((m + 1) * 160)]
        rw [fuel_split (C := 100) k ((m + 1) * 160) _ (by omega)]
        have hminX : minX' = minX := by simp only [minX', hx1, ↓reduceIte]
        exact hjoin1 _ _ rfl rfl rfl rfl rfl rfl rfl rfl (by rw [hminX]; rfl)
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_cellBounds_prog
      unfold Algorithm.cellBounds
      simp [hlt, boxCellBox]

theorem cellBounds_equiv (cells : Array UInt64) (i limit : UInt32) (minX maxX minY maxY : Int32) :
    runJvm ((limit.toNat - i.toNat + 1) * 160) f_Algorithm_cellBounds_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 i), (2, .i32 limit),
        (3, .i32 minX.toUInt32), (4, .i32 maxX.toUInt32),
        (5, .i32 minY.toUInt32), (6, .i32 maxY.toUInt32)] [] [cells]) =
      some (boxCellBox (Algorithm.cellBounds cells i limit minX maxX minY maxY)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 160)]
  exact cellBounds_aux (limit.toNat - i.toNat) 0 cells i limit minX maxX minY maxY (by omega) _

theorem cellBounds_1_equiv (cells : Array UInt64) (i limit : UInt32) (minX maxX minY maxY : Int32) :
    runJvm ((limit.toNat - i.toNat + 1) * 160) f_Algorithm_cellBounds_1_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 i), (2, .i32 limit),
        (3, .i32 minX.toUInt32), (4, .i32 maxX.toUInt32),
        (5, .i32 minY.toUInt32), (6, .i32 maxY.toUInt32)] [] [cells]) =
      some (boxCellBox (Algorithm.cellBounds cells i limit minX maxX minY maxY)) :=
  cellBounds_equiv cells i limit minX maxX minY maxY

private theorem initRemapL4Loop_aux (m : Nat) :
    ∀ (k : Nat) (arena : Algorithm.FlatHashLifeArena) (i limit : UInt32)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 50) f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog 3
      (f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal base 0 (.arenaRef 0)) 1 (.i32 i)) 2 (.i32 limit),
        [arena], [], []⟩).map (fun p => (p.1, p.2.arenas)) =
      some (.unit, [arena.initRemapL4Loop i limit]) := by
  induction m with
  | zero =>
    intro k arena i limit _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 50 = k + 50 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
    rw [Algorithm.FlatHashLifeArena.initRemapL4Loop]
    simp [hge]
  | succ m ih =>
    intro k arena i limit _hn base
    rw [show k + (m + 1 + 1) * 50 = (k + (m + 1) * 50) + 50 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      have hltNat : i.toNat < limit.toNat := hlt
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        rw [ui32_add1_toNat hlt]; omega
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
      by_cases hz : i = 0
      · have hzb : (i == 0) = true := beq_iff_eq.mpr hz
        simp only [hzb, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 50), Nat.add_comm ((m + 1) * 50)]
        rw [Algorithm.FlatHashLifeArena.initRemapL4Loop]
        simp only [hlt, hzb, ↓reduceDIte, ↓reduceIte]
        exact ih _ _ (i + 1) limit hnext _
      · have hzb : (i == 0) = false := beq_false_of_ne hz
        simp only [hzb, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 50), Nat.add_comm ((m + 1) * 50)]
        rw [Algorithm.FlatHashLifeArena.initRemapL4Loop]
        simp only [hlt, hzb, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]
        exact ih _ _ (i + 1) limit hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
      rw [Algorithm.FlatHashLifeArena.initRemapL4Loop]
      simp [hlt]

theorem initRemapL4Loop_equiv (arena : Algorithm.FlatHashLifeArena) (i limit : UInt32) :
    (runJvmRes ((limit.toNat - i.toNat + 1) * 50 + 3) f_Algorithm_FlatHashLifeArena_initRemapL4Loop_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 i), (2, .i32 limit)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.unit, [arena.initRemapL4Loop i limit]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 50)]
  exact initRemapL4Loop_aux (limit.toNat - i.toNat) 0 arena i limit (by omega) _

private theorem initRemapCellLoop_aux (m : Nat) :
    ∀ (k : Nat) (arena : Algorithm.FlatHashLifeArena) (i limit : UInt32)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 50) f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog 3
      (f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal base 0 (.arenaRef 0)) 1 (.i32 i)) 2 (.i32 limit),
        [arena], [], []⟩).map (fun p => (p.1, p.2.arenas)) =
      some (.unit, [arena.initRemapCellLoop i limit]) := by
  induction m with
  | zero =>
    intro k arena i limit _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 50 = k + 50 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
    rw [Algorithm.FlatHashLifeArena.initRemapCellLoop]
    simp [hge]
  | succ m ih =>
    intro k arena i limit _hn base
    rw [show k + (m + 1 + 1) * 50 = (k + (m + 1) * 50) + 50 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      have hltNat : i.toNat < limit.toNat := hlt
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        rw [ui32_add1_toNat hlt]; omega
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
      rw [compareUnsigned_slt']
      by_cases hi56 : i < 56
      · simp only [hi56, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 50), Nat.add_comm ((m + 1) * 50)]
        rw [Algorithm.FlatHashLifeArena.initRemapCellLoop]
        simp only [hlt, hi56, ↓reduceDIte, ↓reduceIte]
        exact ih _ _ (i + 1) limit hnext _
      · simp only [hi56, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 50), Nat.add_comm ((m + 1) * 50)]
        rw [Algorithm.FlatHashLifeArena.initRemapCellLoop]
        simp only [hlt, hi56, ↓reduceDIte, ↓reduceIte]
        exact ih _ _ (i + 1) limit hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
      rw [Algorithm.FlatHashLifeArena.initRemapCellLoop]
      simp [hlt]

theorem initRemapCellLoop_equiv (arena : Algorithm.FlatHashLifeArena) (i limit : UInt32) :
    (runJvmRes ((limit.toNat - i.toNat + 1) * 50 + 3) f_Algorithm_FlatHashLifeArena_initRemapCellLoop_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 i), (2, .i32 limit)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.unit, [arena.initRemapCellLoop i limit]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 50)]
  exact initRemapCellLoop_aux (limit.toNat - i.toNat) 0 arena i limit (by omega) _

private theorem life105Bounds_aux (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (i limit : UInt32) (minX minY maxY : Int32)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 140) f_Algorithm_life105Bounds_prog 3
      (f_Algorithm_life105Bounds_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 (.u64Ref 0)) 1 (.i32 i)) 2 (.i32 limit)) 3 (.i32 minX.toUInt32)) 4 (.i32 minY.toUInt32))
        5 (.i32 maxY.toUInt32), [], [cells], []⟩ =
      some (let b := Algorithm.life105Bounds cells i limit minX minY maxY
            .pair (.boxedInt b.1.toUInt32) (.pair (.boxedInt b.2.1.toUInt32) (.boxedInt b.2.2.toUInt32))) := by
  induction m with
  | zero =>
    intro k cells i limit minX minY maxY _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 140 = k + 140 by omega]
    flat_step_blk f_Algorithm_life105Bounds_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_life105Bounds_prog
    unfold Algorithm.life105Bounds
    simp [hge]
  | succ m ih =>
    intro k cells i limit minX minY maxY _hn base
    rw [show k + (m + 1 + 1) * 140 = (k + (m + 1) * 140) + 140 by omega]
    flat_step_blk f_Algorithm_life105Bounds_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      have hltNat : i.toNat < limit.toNat := hlt
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        rw [ui32_add1_toNat hlt]; omega
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_life105Bounds_prog
      let kv := cells[i.toNat]!
      let x := (kv >>> 32).toUInt32.toInt32
      let y := kv.toUInt32.toInt32
      let minX' := if x < minX then x else minX
      let minY' := if y < minY then y else minY
      have hx_def : (cells[i.toNat]! >>> 32).toUInt32.toInt32 = x := rfl
      have hy_def : cells[i.toNat]!.toUInt32.toInt32 = y := rfl
      have hjoin2 : ∀ k2 (locs : Nat → JvmVal),
          locs 0 = .u64Ref 0 → locs 2 = .i32 limit → locs 5 = .i32 maxY.toUInt32 →
          locs 9 = .i32 y.toUInt32 → locs 10 = .i32 (i + 1) → locs 11 = .i32 minX'.toUInt32 →
          locs 12 = .i32 minY'.toUInt32 →
          (if maxY.toUInt32.toBitVec.slt y.toUInt32.toBitVec = true then
            runJvmValFast (k2 + (m + 1) * 140 + 50) f_Algorithm_life105Bounds_prog 88
              (f_Algorithm_life105Bounds_prog.drop 88) ⟨88, [], locs, [], [cells], []⟩
          else
            runJvmValFast (k2 + (m + 1) * 140 + 50) f_Algorithm_life105Bounds_prog 69
              (f_Algorithm_life105Bounds_prog.drop 69) ⟨69, [], locs, [], [cells], []⟩) =
            some (let b := Algorithm.life105Bounds cells i limit minX minY maxY
                  .pair (.boxedInt b.1.toUInt32) (.pair (.boxedInt b.2.1.toUInt32) (.boxedInt b.2.2.toUInt32))) := by
        intro k2 locs h0 h2 h5 h9 h10 h11 h12
        rw [cellBounds_slt, int32_toUInt32_toInt32, int32_toUInt32_toInt32]
        unfold Algorithm.life105Bounds
        simp only [hlt, ↓reduceDIte, ui32_toInt32_x_eq, ui32_toInt32_y_eq]
        by_cases hy2 : maxY < y
        · simp only [hy2, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_life105Bounds_prog
          (conv => lhs; simp only [h0, h2, h5, h9, h10, h11, h12]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k2 ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
          have hy2' : maxY < cells[i.toNat]!.toUInt32.toInt32 := hy2
          (conv => rhs; simp only [hy2', ↓reduceIte])
          exact ih _ cells (i + 1) limit minX' minY' y hnext _
        · simp only [hy2, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_life105Bounds_prog
          (conv => lhs; simp only [h0, h2, h5, h9, h10, h11, h12]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k2 ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
          have hy2' : ¬ (maxY < cells[i.toNat]!.toUInt32.toInt32) := hy2
          (conv => rhs; simp only [hy2', ↓reduceIte])
          exact ih _ cells (i + 1) limit minX' minY' maxY hnext _
      have hjoin1 : ∀ k1 (locs : Nat → JvmVal),
          locs 0 = .u64Ref 0 → locs 2 = .i32 limit → locs 4 = .i32 minY.toUInt32 →
          locs 5 = .i32 maxY.toUInt32 → locs 9 = .i32 y.toUInt32 → locs 10 = .i32 (i + 1) →
          locs 13 = .i32 minX'.toUInt32 →
          (if y.toUInt32.toBitVec.slt minY.toUInt32.toBitVec = true then
            runJvmValFast (k1 + (m + 1) * 140 + 80) f_Algorithm_life105Bounds_prog 62
              (f_Algorithm_life105Bounds_prog.drop 62) ⟨62, [], locs, [], [cells], []⟩
          else
            runJvmValFast (k1 + (m + 1) * 140 + 80) f_Algorithm_life105Bounds_prog 57
              (f_Algorithm_life105Bounds_prog.drop 57) ⟨57, [], locs, [], [cells], []⟩) =
            some (let b := Algorithm.life105Bounds cells i limit minX minY maxY
                  .pair (.boxedInt b.1.toUInt32) (.pair (.boxedInt b.2.1.toUInt32) (.boxedInt b.2.2.toUInt32))) := by
        intro k1 locs h0 h2 h4 h5 h9 h10 h13
        rw [cellBounds_slt, int32_toUInt32_toInt32, int32_toUInt32_toInt32]
        by_cases hy1 : y < minY
        · simp only [hy1, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_life105Bounds_prog
          (conv => lhs; simp only [h0, h2, h4, h5, h9, h10, h13]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k1 ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
          rw [fuel_split (C := 50) k1 ((m + 1) * 140) _ (by omega)]
          have hminY : minY' = y := by simp only [minY', hy1, ↓reduceIte]
          refine hjoin2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h5
          · exact h9
          · exact h10
          · rfl
          · rw [hminY]; rfl
        · simp only [hy1, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_life105Bounds_prog
          (conv => lhs; simp only [h0, h2, h4, h5, h9, h10, h13]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k1 ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
          rw [fuel_split (C := 50) k1 ((m + 1) * 140) _ (by omega)]
          have hminY : minY' = minY := by simp only [minY', hy1, ↓reduceIte]
          refine hjoin2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h5
          · exact h9
          · exact h10
          · rfl
          · rw [hminY]; rfl
      rw [cellBounds_slt, shift_32_and_63, show minX.toUInt32.toInt32 = minX from int32_toUInt32_toInt32 minX, hx_def]
      by_cases hx1 : x < minX
      · simp only [hx1, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_life105Bounds_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
        rw [fuel_split (C := 80) k ((m + 1) * 140) _ (by omega)]
        have hminX : minX' = x := by simp only [minX', hx1, ↓reduceIte]
        exact hjoin1 _ _ rfl rfl rfl rfl rfl rfl (by rw [hminX]; rfl)
      · simp only [hx1, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_life105Bounds_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
        rw [fuel_split (C := 80) k ((m + 1) * 140) _ (by omega)]
        have hminX : minX' = minX := by simp only [minX', hx1, ↓reduceIte]
        exact hjoin1 _ _ rfl rfl rfl rfl rfl rfl (by rw [hminX]; rfl)
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_life105Bounds_prog
      unfold Algorithm.life105Bounds
      simp [hlt]

theorem life105Bounds_equiv (cells : Array UInt64) (i limit : UInt32) (minX minY maxY : Int32) :
    runJvm ((limit.toNat - i.toNat + 1) * 140 + 3) f_Algorithm_life105Bounds_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 i), (2, .i32 limit),
        (3, .i32 minX.toUInt32), (4, .i32 minY.toUInt32), (5, .i32 maxY.toUInt32)] [] [cells]) =
      some (let b := Algorithm.life105Bounds cells i limit minX minY maxY
            .pair (.boxedInt b.1.toUInt32) (.pair (.boxedInt b.2.1.toUInt32) (.boxedInt b.2.2.toUInt32))) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 140)]
  exact life105Bounds_aux (limit.toNat - i.toNat) 0 cells i limit minX minY maxY (by omega) _

private def getU64Res (p : JvmVal × JvmState) : Option (Array UInt64) :=
  match p.1 with | .u64Ref id => p.2.u64Arrays[id]? | _ => none

private theorem life105Rest_aux (m : Nat) :
    ∀ (k : Nat) (cells acc : Array UInt64) (minX : Int32) (i limit : UInt32)
      (u64 : List (Array UInt64)) (cellsId accId : Nat),
      u64[cellsId]? = some cells → u64[accId]? = some acc →
      (_hn : limit.toNat - i.toNat ≤ m) → ∀ (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 90) f_Algorithm_life105Rest_prog 6
      (f_Algorithm_life105Rest_prog.drop 6)
      ⟨6, [], setLocal (setLocal (setLocal (setLocal (setLocal base
        0 (.u64Ref cellsId)) 1 (.i32 minX.toUInt32)) 2 (.i32 i)) 3 (.i32 limit)) 4 (.u64Ref accId),
        [], u64, []⟩).map getU64Res =
      some (some (Algorithm.life105Rest cells minX i limit acc)) := by
  induction m with
  | zero =>
    intro k cells acc minX i limit u64 cellsId accId _hcells hacc _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 90 = k + 90 by omega]
    flat_step_blk f_Algorithm_life105Rest_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_life105Rest_prog
    unfold Algorithm.life105Rest
    simp [getU64Res, hge, hacc]
  | succ m ih =>
    intro k cells acc minX i limit u64 cellsId accId hcells hacc _hn base
    rw [show k + (m + 1 + 1) * 90 = (k + (m + 1) * 90) + 90 by omega]
    flat_step_blk f_Algorithm_life105Rest_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      have hltNat : i.toNat < limit.toNat := hlt
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        rw [ui32_add1_toNat hlt]; omega
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_nonbranch_chunks
      (conv => lhs; arg 2; rw [runJvmResFast_invokestatic_step (stepStatic_ulongArrGetU64 hcells)])
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_life105Rest_prog
      rw [compareUnsigned_slt', shift_32_and_63]
      by_cases hin : (cells[i.toNat]! >>> 32).toUInt32 - minX.toUInt32 < 80
      · simp only [hin, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_life105Rest_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 90), Nat.add_comm ((m + 1) * 90)]
        unfold Algorithm.life105Rest
        simp only [hlt, ↓reduceDIte, Algorithm.inLife105Block, cellKeyX_sub_minX, hin, decide_true, ↓reduceIte]
        exact ih _ cells acc minX (i + 1) limit u64 cellsId accId hcells hacc hnext _
      · simp only [hin, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_nonbranch_chunks
        (conv => lhs; arg 2; rw [runJvmResFast_invokestatic_step (stepStatic_u64BufPush_105 hacc)])
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_life105Rest_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        simp only [nat_add_eq, Nat.succ_eq_add_one, Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 90), Nat.add_comm ((m + 1) * 90)]
        unfold Algorithm.life105Rest
        simp only [hlt, ↓reduceDIte, Algorithm.inLife105Block, cellKeyX_sub_minX, hin,
          decide_false, Bool.false_eq_true, ↓reduceIte]
        have hcells' : (u64 ++ [Algorithm.U64Buf.push acc cells[i.toNat]!])[cellsId]? = some cells := by
          rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hcells).1]; exact hcells
        have hacc' : (u64 ++ [Algorithm.U64Buf.push acc cells[i.toNat]!])[u64.length]? =
            some (Algorithm.U64Buf.push acc cells[i.toNat]!) := by simp
        exact ih _ cells (Algorithm.U64Buf.push acc cells[i.toNat]!) minX (i + 1) limit
          (u64 ++ [Algorithm.U64Buf.push acc cells[i.toNat]!]) cellsId u64.length hcells' hacc' hnext _
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_life105Rest_prog
      unfold Algorithm.life105Rest
      simp [getU64Res, hlt, hacc]

theorem life105Rest_equiv (cells acc : Array UInt64) (minX : Int32) (i limit : UInt32) :
    (runJvmRes ((limit.toNat - i.toNat + 1) * 90 + 6) f_Algorithm_life105Rest_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 minX.toUInt32), (2, .i32 i),
        (3, .i32 limit), (4, .u64Ref 1)] [] [cells, acc])).map
        (fun p => match p.1 with | .u64Ref id => p.2.u64Arrays[id]? | _ => none) =
      some (some (Algorithm.life105Rest cells minX i limit acc)) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  change Option.map getU64Res _ = _
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 90)]
  exact life105Rest_aux (limit.toNat - i.toNat) 0 cells acc minX i limit [cells, acc] 0 1 rfl rfl (by omega) _

private theorem cellBoundsLoop_aux (m : Nat) :
    ∀ (k : Nat) (cells : Array UInt64) (i limit : UInt32) (minX minY maxX maxY : UInt64)
      (_hn : limit.toNat - i.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 180) f_Algorithm_cellBoundsLoop_prog 3
      (f_Algorithm_cellBoundsLoop_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 (.u64Ref 0)) 1 (.i32 i)) 2 (.i32 limit)) 3 (.i64 minX)) 5 (.i64 minY))
        7 (.i64 maxX)) 9 (.i64 maxY), [], [cells], []⟩ =
      some (let b := Algorithm.cellBoundsLoop cells i limit minX minY maxX maxY
            .pair (.boxedULong b.1) (.pair (.boxedULong b.2.1) (.pair (.boxedULong b.2.2.1) (.boxedULong b.2.2.2)))) := by
  induction m with
  | zero =>
    intro k cells i limit minX minY maxX maxY _hn base
    have hge : ¬ (i < limit) := by
      intro hlt; have : i.toNat < limit.toNat := hlt; omega
    rw [show k + (0 + 1) * 180 = k + 180 by omega]
    flat_step_blk f_Algorithm_cellBoundsLoop_prog
    rw [compareUnsigned_slt']
    simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_cellBoundsLoop_prog
    rw [Algorithm.cellBoundsLoop]
    simp [hge]
  | succ m ih =>
    intro k cells i limit minX minY maxX maxY _hn base
    rw [show k + (m + 1 + 1) * 180 = (k + (m + 1) * 180) + 180 by omega]
    flat_step_blk f_Algorithm_cellBoundsLoop_prog
    rw [compareUnsigned_slt']
    by_cases hlt : i < limit
    · simp only [hlt, decide_true, ↓reduceIte]
      have hltNat : i.toNat < limit.toNat := hlt
      have hnext : limit.toNat - (i + 1).toNat ≤ m := by
        rw [ui32_add1_toNat hlt]; omega
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_cellBoundsLoop_prog
      let kv := cells[i.toNat]!
      let x := kv >>> 32
      let y := kv &&& 4294967295
      have hx_def : cells[i.toNat]! >>> 32 = x := rfl
      have hy_def : cells[i.toNat]! &&& 4294967295 = y := rfl
      let minX' := min minX x
      let minY' := min minY y
      let maxX' := max maxX x
      have hjoin3 : ∀ k3 (locs : Nat → JvmVal),
          locs 0 = .u64Ref 0 → locs 2 = .i32 limit → locs 9 = .i64 maxY →
          locs 13 = .i32 (i + 1) → locs 14 = .i64 minY' → locs 16 = .i64 y →
          locs 18 = .i64 minX' → locs 20 = .i64 maxX' →
          (if (if (maxY == y) = true then (0 : UInt32) else if maxY < y then 4294967295 else 1).toBitVec.sle 0#32 = true then
            runJvmValFast (k3 + (m + 1) * 180 + 60) f_Algorithm_cellBoundsLoop_prog 132
              (f_Algorithm_cellBoundsLoop_prog.drop 132) ⟨132, [], locs, [], [cells], []⟩
          else
            runJvmValFast (k3 + (m + 1) * 180 + 60) f_Algorithm_cellBoundsLoop_prog 111
              (f_Algorithm_cellBoundsLoop_prog.drop 111) ⟨111, [], locs, [], [cells], []⟩) =
            some (let b := Algorithm.cellBoundsLoop cells i limit minX minY maxX maxY
                  .pair (.boxedULong b.1) (.pair (.boxedULong b.2.1) (.pair (.boxedULong b.2.2.1) (.boxedULong b.2.2.2)))) := by
        intro k3 locs h0 h2 h9 h13 h14 h16 h18 h20
        rw [compareUnsigned64_sle']
        rw [Algorithm.cellBoundsLoop]
        simp only [hlt, ↓reduceDIte, keyHi_eq, keyLo_eq]
        by_cases hy2 : maxY ≤ y
        · simp only [hy2, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; simp only [h0, h2, h9, h13, h14, h16, h18, h20]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k3 ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
          have hmaxY : max maxY y = y := by rw [max_u64_eq, ite_eq_left_iff]; intro h; exact absurd hy2 h
          rw [show min minX (kv >>> 32) = minX' from rfl,
              show min minY (kv &&& 4294967295) = minY' from rfl,
              show max maxX (kv >>> 32) = maxX' from rfl,
              show max maxY (kv &&& 4294967295) = y from hmaxY]
          exact ih _ cells (i + 1) limit minX' minY' maxX' y hnext _
        · simp only [hy2, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; simp only [h0, h2, h9, h13, h14, h16, h18, h20]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k3 ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
          have hmaxY : max maxY y = maxY := by rw [max_u64_eq, ite_eq_right_iff]; intro h; exact absurd h hy2
          rw [show min minX (kv >>> 32) = minX' from rfl,
              show min minY (kv &&& 4294967295) = minY' from rfl,
              show max maxX (kv >>> 32) = maxX' from rfl,
              show max maxY (kv &&& 4294967295) = maxY from hmaxY]
          exact ih _ cells (i + 1) limit minX' minY' maxX' maxY hnext _
      have hjoin2 : ∀ k2 (locs : Nat → JvmVal),
          locs 0 = .u64Ref 0 → locs 2 = .i32 limit → locs 7 = .i64 maxX →
          locs 9 = .i64 maxY → locs 13 = .i32 (i + 1) → locs 22 = .i64 x →
          locs 24 = .i64 y → locs 26 = .i64 minX' → locs 28 = .i64 minY' →
          (if (if (maxX == x) = true then (0 : UInt32) else if maxX < x then 4294967295 else 1).toBitVec.sle 0#32 = true then
            runJvmValFast (k2 + (m + 1) * 180 + 85) f_Algorithm_cellBoundsLoop_prog 99
              (f_Algorithm_cellBoundsLoop_prog.drop 99) ⟨99, [], locs, [], [cells], []⟩
          else
            runJvmValFast (k2 + (m + 1) * 180 + 85) f_Algorithm_cellBoundsLoop_prog 90
              (f_Algorithm_cellBoundsLoop_prog.drop 90) ⟨90, [], locs, [], [cells], []⟩) =
            some (let b := Algorithm.cellBoundsLoop cells i limit minX minY maxX maxY
                  .pair (.boxedULong b.1) (.pair (.boxedULong b.2.1) (.pair (.boxedULong b.2.2.1) (.boxedULong b.2.2.2)))) := by
        intro k2 locs h0 h2 h7 h9 h13 h22 h24 h26 h28
        rw [compareUnsigned64_sle']
        by_cases hx2 : maxX ≤ x
        · simp only [hx2, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; simp only [h0, h2, h7, h9, h13, h22, h24, h26, h28]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k2 ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
          rw [fuel_split (C := 60) k2 ((m + 1) * 180) _ (by omega)]
          have hmaxX : max maxX x = x := by rw [max_u64_eq, ite_eq_left_iff]; intro h; exact absurd hx2 h
          refine hjoin3 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h9
          · exact h13
          · rfl
          · rfl
          · rfl
          · rw [show maxX' = max maxX x from rfl, hmaxX]; rfl
        · simp only [hx2, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; simp only [h0, h2, h7, h9, h13, h22, h24, h26, h28]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k2 ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
          rw [fuel_split (C := 60) k2 ((m + 1) * 180) _ (by omega)]
          have hmaxX : max maxX x = maxX := by rw [max_u64_eq, ite_eq_right_iff]; intro h; exact absurd h hx2
          refine hjoin3 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h9
          · exact h13
          · rfl
          · rfl
          · rfl
          · rw [show maxX' = max maxX x from rfl, hmaxX]; rfl
      have hjoin1 : ∀ k1 (locs : Nat → JvmVal),
          locs 0 = .u64Ref 0 → locs 2 = .i32 limit → locs 5 = .i64 minY →
          locs 7 = .i64 maxX → locs 9 = .i64 maxY → locs 13 = .i32 (i + 1) →
          locs 22 = .i64 x → locs 30 = .i64 minX' → locs 32 = .i64 y →
          (if (if (minY == y) = true then (0 : UInt32) else if minY < y then 4294967295 else 1).toBitVec.sle 0#32 = true then
            runJvmValFast (k1 + (m + 1) * 180 + 110) f_Algorithm_cellBoundsLoop_prog 80
              (f_Algorithm_cellBoundsLoop_prog.drop 80) ⟨80, [], locs, [], [cells], []⟩
          else
            runJvmValFast (k1 + (m + 1) * 180 + 110) f_Algorithm_cellBoundsLoop_prog 73
              (f_Algorithm_cellBoundsLoop_prog.drop 73) ⟨73, [], locs, [], [cells], []⟩) =
            some (let b := Algorithm.cellBoundsLoop cells i limit minX minY maxX maxY
                  .pair (.boxedULong b.1) (.pair (.boxedULong b.2.1) (.pair (.boxedULong b.2.2.1) (.boxedULong b.2.2.2)))) := by
        intro k1 locs h0 h2 h5 h7 h9 h13 h22 h30 h32
        rw [compareUnsigned64_sle']
        by_cases hy1 : minY ≤ y
        · simp only [hy1, decide_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; simp only [h0, h2, h5, h7, h9, h13, h22, h30, h32]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k1 ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
          rw [fuel_split (C := 85) k1 ((m + 1) * 180) _ (by omega)]
          have hminY : min minY y = minY := by rw [min_u64_eq, ite_eq_left_iff]; intro h; exact absurd hy1 h
          refine hjoin2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h7
          · exact h9
          · exact h13
          · exact h22
          · rfl
          · rfl
          · rw [show minY' = min minY y from rfl, hminY]; rfl
        · simp only [hy1, decide_false, Bool.false_eq_true, ↓reduceIte]
          flat_step_blk f_Algorithm_cellBoundsLoop_prog
          (conv => lhs; simp only [h0, h2, h5, h7, h9, h13, h22, h30, h32]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          try simp only [Nat.succ_eq_add_one]
          try simp only [nat_add_eq]
          simp only [Nat.add_assoc]
          rw [Nat.add_left_comm k1 ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
          rw [fuel_split (C := 85) k1 ((m + 1) * 180) _ (by omega)]
          have hminY : min minY y = y := by rw [min_u64_eq, ite_eq_right_iff]; intro h; exact absurd h hy1
          refine hjoin2 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · exact h0
          · exact h2
          · exact h7
          · exact h9
          · exact h13
          · exact h22
          · rfl
          · rfl
          · rw [show minY' = min minY y from rfl, hminY]; rfl
      rw [compareUnsigned64_sle', shift_32_and_63, hx_def]
      by_cases hx1 : minX ≤ x
      · simp only [hx1, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_cellBoundsLoop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
        rw [fuel_split (C := 110) k ((m + 1) * 180) _ (by omega)]
        rw [hy_def]
        have hminX : min minX x = minX := by rw [min_u64_eq, ite_eq_left_iff]; intro h; exact absurd hx1 h
        exact hjoin1 _ _ rfl rfl rfl rfl rfl rfl rfl (by rw [show minX' = min minX x from rfl, hminX]; rfl) rfl
      · simp only [hx1, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_cellBoundsLoop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 180), Nat.add_comm ((m + 1) * 180)]
        rw [fuel_split (C := 110) k ((m + 1) * 180) _ (by omega)]
        rw [hy_def]
        have hminX : min minX x = x := by rw [min_u64_eq, ite_eq_right_iff]; intro h; exact absurd h hx1
        exact hjoin1 _ _ rfl rfl rfl rfl rfl rfl rfl (by rw [show minX' = min minX x from rfl, hminX]; rfl) rfl
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_cellBoundsLoop_prog
      rw [Algorithm.cellBoundsLoop]
      simp [hlt]

theorem cellBoundsLoop_equiv (cells : Array UInt64) (i limit : UInt32) (minX minY maxX maxY : UInt64) :
    runJvm ((limit.toNat - i.toNat + 1) * 180 + 3) f_Algorithm_cellBoundsLoop_prog
      (initJvmState [(0, .u64Ref 0), (1, .i32 i), (2, .i32 limit),
        (3, .i64 minX), (5, .i64 minY), (7, .i64 maxX), (9, .i64 maxY)] [] [cells]) =
      some (let b := Algorithm.cellBoundsLoop cells i limit minX minY maxX maxY
            .pair (.boxedULong b.1) (.pair (.boxedULong b.2.1) (.pair (.boxedULong b.2.2.1) (.boxedULong b.2.2.2)))) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((limit.toNat - i.toNat + 1) * 180)]
  exact cellBoundsLoop_aux (limit.toNat - i.toNat) 0 cells i limit minX minY maxX maxY (by omega) _


private theorem u8_sext_inj (a b : UInt8) :
    (a.toInt8.toInt32.toUInt32 = b.toInt8.toInt32.toUInt32) ↔ a = b := by
  constructor
  · intro h
    apply UInt8.eq_of_toBitVec_eq
    have hv : a.toInt8.toInt32.toUInt32.toBitVec = b.toInt8.toInt32.toUInt32.toBitVec := congrArg UInt32.toBitVec h
    bv_check "lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.u8_sext_inj.lrat"
  · intro h; subst h; rfl

private theorem initEmptyNodes_lvl_u8 (i : UInt32) :
    (UInt32.ofBitVec (BitVec.signExtend 32 (BitVec.setWidth 8 (i + 5).toBitVec))).toUInt8 = (i + 5).toUInt8 := by
  apply UInt8.eq_of_toBitVec_eq; bv_normalize

private theorem u8_signExt_toUInt8 (i : UInt32) :
    (BitVec.signExtend 32 (BitVec.setWidth 8 (i + 5).toBitVec)).setWidth 8 = (i + 5).toBitVec.setWidth 8 := by
  bv_normalize

private theorem initEmptyNodesLoop_aux (m : Nat) :
    ∀ (k : Nat) (arena : Algorithm.FlatHashLifeArena) (fuel i : UInt32)
      (_hn : fuel.toNat ≤ m) (base : Nat → JvmVal),
    (runJvmResFast (k + (m + 1) * 100) f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog 3
      (f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal base 0 (.arenaRef 0)) 1 (.i32 fuel)) 2 (.i32 i),
        [arena], [], []⟩).map (fun p => (p.1, p.2.arenas)) =
      some (.unit, [arena.initEmptyNodesLoop fuel i]) := by
  induction m with
  | zero =>
    intro k arena fuel i _hn base
    have hfz : fuel = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (by change fuel.toBitVec.toNat = 0; change fuel.toNat ≤ 0 at _hn; exact Nat.eq_zero_of_le_zero _hn))
    rw [show k + (0 + 1) * 100 = k + 100 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
    have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
    simp only [hfzb, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
    rw [Algorithm.FlatHashLifeArena.initEmptyNodesLoop]
    simp [hfz]
  | succ m ih =>
    intro k arena fuel i _hn base
    rw [show k + (m + 1 + 1) * 100 = (k + (m + 1) * 100) + 100 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
    by_cases hfz : fuel = 0
    · have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
      simp only [hfzb, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
      rw [Algorithm.FlatHashLifeArena.initEmptyNodesLoop]
      simp [hfz]
    · have hfzb : (fuel == 0) = false := beq_false_of_ne hfz
      simp only [hfzb, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
      rw [compareUnsigned_sle']
      by_cases hge : (56 : UInt32) ≤ i
      · simp only [hge, decide_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
        have hi : i ≥ 56 := hge
        rw [Algorithm.FlatHashLifeArena.initEmptyNodesLoop]
        simp [hfz, hi]
      · simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        try simp only [Nat.succ_eq_add_one]
        try simp only [nat_add_eq]
        simp only [Nat.add_assoc]
        rw [Nat.add_left_comm k ((m + 1) * 100), Nat.add_comm ((m + 1) * 100)]
        have hnext : (fuel - 1).toNat ≤ m := by rw [ui32_sub1_toNat hfz]; omega
        rw [Algorithm.FlatHashLifeArena.initEmptyNodesLoop]
        have hnotge : ¬ (i ≥ 56) := hge
        simp only [hfz, ↓reduceDIte, hnotge, ↓reduceIte]
        (conv => lhs; dsimp only [setArenaU32, getArenaU32, setArenaU64, getArenaU64, setArenaU8, getArenaU8])
        (try rw [initEmptyNodes_lvl_u8])
        exact ih _ _ (fuel - 1) (i + 1) hnext _

theorem initEmptyNodesLoop_equiv (arena : Algorithm.FlatHashLifeArena) (fuel i : UInt32) :
    (runJvmRes ((fuel.toNat + 1) * 100 + 3) f_Algorithm_FlatHashLifeArena_initEmptyNodesLoop_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 fuel), (2, .i32 i)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.unit, [arena.initEmptyNodesLoop fuel i]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((fuel.toNat + 1) * 100)]
  exact initEmptyNodesLoop_aux (fuel.toNat) 0 arena fuel i (by omega) _

private theorem slt_ite_ne_zero (c : Bool) :
    ¬ (if c = true then (4294967295 : UInt32) else 1) = 0 := by
  cases c <;> decide

private theorem probeLevel4_aux (m : Nat) :
    ∀ (k : Nat) (arena : Algorithm.FlatHashLifeArena) (head : UInt32) (nw ne sw se : UInt64)
      (fuel : UInt32) (_hn : fuel.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 120) f_Algorithm_probeLevel4_prog 3
      (f_Algorithm_probeLevel4_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 (.arenaRef 0)) 1 (.i32 head)) 2 (.i64 nw)) 4 (.i64 ne)) 6 (.i64 sw)) 8 (.i64 se))
        10 (.i32 fuel), [arena], [], []⟩ =
      some (.i32 (Algorithm.probeLevel4 arena head nw ne sw se fuel)) := by
  induction m with
  | zero =>
    intro k arena head nw ne sw se fuel _hn base
    have hfz : fuel = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (by change fuel.toBitVec.toNat = 0; change fuel.toNat ≤ 0 at _hn; exact Nat.eq_zero_of_le_zero _hn))
    rw [show k + (0 + 1) * 120 = k + 120 by omega]
    flat_step_blk f_Algorithm_probeLevel4_prog
    have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
    simp only [hfzb, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_probeLevel4_prog
    rw [Algorithm.probeLevel4]
    simp [hfz, Algorithm.EMPTY_BUCKET]
  | succ m ih =>
    intro k arena head nw ne sw se fuel _hn base
    rw [show k + (m + 1 + 1) * 120 = (k + (m + 1) * 120) + 120 by omega]
    flat_step_blk f_Algorithm_probeLevel4_prog
    by_cases hfz : fuel = 0
    · have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
      simp only [hfzb, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_probeLevel4_prog
      rw [Algorithm.probeLevel4]
      simp [hfz, Algorithm.EMPTY_BUCKET]
    · have hfzb : (fuel == 0) = false := beq_false_of_ne hfz
      simp only [hfzb, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_probeLevel4_prog
      by_cases hemp : head = 4294967295
      · have hempb : (head == 4294967295) = true := beq_iff_eq.mpr hemp
        simp only [hempb, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_probeLevel4_prog
        rw [Algorithm.probeLevel4]
        simp [hfz, hemp, Algorithm.EMPTY_BUCKET]
      · have hempb : (head == 4294967295) = false := beq_false_of_ne hemp
        simp only [hempb, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_probeLevel4_prog
        rw [compareUnsigned_sle']
        by_cases hoob : arena.l4Count ≤ head
        · simp only [hoob, decide_true, ↓reduceIte]
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_probeLevel4_prog
          have hemp' : (head == Algorithm.EMPTY_BUCKET) = false := beq_false_of_ne hemp
          have hge : head ≥ arena.l4Count := hoob
          rw [Algorithm.probeLevel4]
          simp [hfz, hge, Algorithm.EMPTY_BUCKET]
        · simp only [hoob, decide_false, Bool.false_eq_true, ↓reduceIte]
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_probeLevel4_prog
          have hnext : (fuel - 1).toNat ≤ m := by rw [ui32_sub1_toNat hfz]; omega
          have hmiss : ∀ km (locs : Nat → JvmVal),
              locs 0 = .arenaRef 0 → locs 1 = .i32 head → locs 2 = .i64 nw →
              locs 4 = .i64 ne → locs 6 = .i64 sw → locs 8 = .i64 se →
              locs 10 = .i32 fuel → locs 12 = .arenaU32Ref 0 .l4Next →
              runJvmValFast (km + (m + 1) * 120 + 50) f_Algorithm_probeLevel4_prog 56
                (f_Algorithm_probeLevel4_prog.drop 56) ⟨56, [], locs, [arena], [], []⟩ =
                some (.i32 (Algorithm.probeLevel4 arena arena.l4Next[head.toNat]! nw ne sw se (fuel - 1))) := by
            intro km locs h0 h1 h2 h4 h6 h8 h10 h12
            flat_step_blk f_Algorithm_probeLevel4_prog
            (conv => lhs; simp only [h0, h1, h2, h4, h6, h8, h10, h12]; dsimp only [getArenaU32]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_probeLevel4_prog
            (conv => lhs; dsimp only [getArenaU32]; simp only [h0, h1, h2, h4, h6, h8, h10, h12]; dsimp only [JvmVal.asI32]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            try simp only [Nat.succ_eq_add_one]
            try simp only [nat_add_eq]
            simp only [Nat.add_assoc]
            rw [Nat.add_left_comm km ((m + 1) * 120), Nat.add_comm ((m + 1) * 120)]
            exact ih _ arena arena.l4Next[head.toNat]! nw ne sw se (fuel - 1) hnext _
          have hemp' : (head == Algorithm.EMPTY_BUCKET) = false := beq_false_of_ne hemp
          have hnotge : ¬ (head ≥ arena.l4Count) := hoob
          by_cases hnw : arena.l4Nw[head.toNat]! = nw
          · have hnwb : (arena.l4Nw[head.toNat]! == nw) = true := beq_iff_eq.mpr hnw
            (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hnwb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
            (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_probeLevel4_prog
            by_cases hne : arena.l4Ne[head.toNat]! = ne
            · have hneb : (arena.l4Ne[head.toNat]! == ne) = true := beq_iff_eq.mpr hne
              (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hneb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_probeLevel4_prog
              by_cases hsw : arena.l4Sw[head.toNat]! = sw
              · have hswb : (arena.l4Sw[head.toNat]! == sw) = true := beq_iff_eq.mpr hsw
                (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hswb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_probeLevel4_prog
                by_cases hse : arena.l4Se[head.toNat]! = se
                · have hseb : (arena.l4Se[head.toNat]! == se) = true := beq_iff_eq.mpr hse
                  (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hseb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_probeLevel4_prog
                  rw [Algorithm.probeLevel4]
                  simp [hfz, hemp', hnotge, hnwb, hneb, hswb, hseb]
                · have hseb : (arena.l4Se[head.toNat]! == se) = false := beq_false_of_ne hse
                  (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hseb, Bool.not_false, ↓reduceIte])
                  try simp only [Nat.succ_eq_add_one]
                  try simp only [nat_add_eq]
                  simp only [Nat.add_assoc]
                  rw [Nat.add_left_comm k ((m + 1) * 120), Nat.add_comm ((m + 1) * 120)]
                  rw [fuel_split (C := 50) k ((m + 1) * 120) _ (by omega)]
                  rw [Algorithm.probeLevel4]
                  simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                    hnwb, hneb, hswb, hseb, Bool.and_false]
                  refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
              · have hswb : (arena.l4Sw[head.toNat]! == sw) = false := beq_false_of_ne hsw
                (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hswb, Bool.not_false, ↓reduceIte])
                try simp only [Nat.succ_eq_add_one]
                try simp only [nat_add_eq]
                simp only [Nat.add_assoc]
                rw [Nat.add_left_comm k ((m + 1) * 120), Nat.add_comm ((m + 1) * 120)]
                rw [fuel_split (C := 50) k ((m + 1) * 120) _ (by omega)]
                rw [Algorithm.probeLevel4]
                simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                  hnwb, hneb, hswb, Bool.and_false, Bool.false_and]
                refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
            · have hneb : (arena.l4Ne[head.toNat]! == ne) = false := beq_false_of_ne hne
              (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hneb, Bool.not_false, ↓reduceIte])
              try simp only [Nat.succ_eq_add_one]
              try simp only [nat_add_eq]
              simp only [Nat.add_assoc]
              rw [Nat.add_left_comm k ((m + 1) * 120), Nat.add_comm ((m + 1) * 120)]
              rw [fuel_split (C := 50) k ((m + 1) * 120) _ (by omega)]
              rw [Algorithm.probeLevel4]
              simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                hnwb, hneb, Bool.and_false, Bool.false_and]
              refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
          · have hnwb : (arena.l4Nw[head.toNat]! == nw) = false := beq_false_of_ne hnw
            (conv => lhs; rw [lcmp_beq_eq_zero]; simp only [getArenaU64, hnwb, Bool.not_false, ↓reduceIte])
            try simp only [Nat.succ_eq_add_one]
            try simp only [nat_add_eq]
            simp only [Nat.add_assoc]
            rw [Nat.add_left_comm k ((m + 1) * 120), Nat.add_comm ((m + 1) * 120)]
            rw [fuel_split (C := 50) k ((m + 1) * 120) _ (by omega)]
            rw [Algorithm.probeLevel4]
            simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
              hnwb, Bool.false_and]
            refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl

theorem probeLevel4_equiv (arena : Algorithm.FlatHashLifeArena) (head : UInt32) (nw ne sw se : UInt64) (fuel : UInt32) :
    runJvm ((fuel.toNat + 1) * 120 + 3) f_Algorithm_probeLevel4_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 head), (2, .i64 nw), (4, .i64 ne), (6, .i64 sw),
        (8, .i64 se), (10, .i32 fuel)] [arena]) =
      some (.i32 (Algorithm.probeLevel4 arena head nw ne sw se fuel)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((fuel.toNat + 1) * 120)]
  exact probeLevel4_aux (fuel.toNat) 0 arena head nw ne sw se fuel (by omega) _

private theorem probeCellNode_aux (m : Nat) :
    ∀ (k : Nat) (arena : Algorithm.FlatHashLifeArena) (head : UInt32) (lvl : UInt8)
      (nw ne sw se fuel : UInt32) (_hn : fuel.toNat ≤ m) (base : Nat → JvmVal),
    runJvmValFast (k + (m + 1) * 130) f_Algorithm_probeCellNode_prog 3
      (f_Algorithm_probeCellNode_prog.drop 3)
      ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
        0 (.arenaRef 0)) 1 (.i32 head)) 2 (.i32 lvl.toInt8.toInt32.toUInt32)) 3 (.i32 nw))
        4 (.i32 ne)) 5 (.i32 sw)) 6 (.i32 se)) 7 (.i32 fuel), [arena], [], []⟩ =
      some (.i32 (Algorithm.probeCellNode arena head lvl nw ne sw se fuel)) := by
  induction m with
  | zero =>
    intro k arena head lvl nw ne sw se fuel _hn base
    have hfz : fuel = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (by change fuel.toBitVec.toNat = 0; change fuel.toNat ≤ 0 at _hn; exact Nat.eq_zero_of_le_zero _hn))
    rw [show k + (0 + 1) * 130 = k + 130 by omega]
    flat_step_blk f_Algorithm_probeCellNode_prog
    have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
    simp only [hfzb, ↓reduceIte]
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_probeCellNode_prog
    rw [Algorithm.probeCellNode]
    simp [hfz, Algorithm.EMPTY_BUCKET]
  | succ m ih =>
    intro k arena head lvl nw ne sw se fuel _hn base
    rw [show k + (m + 1 + 1) * 130 = (k + (m + 1) * 130) + 130 by omega]
    flat_step_blk f_Algorithm_probeCellNode_prog
    by_cases hfz : fuel = 0
    · have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
      simp only [hfzb, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_probeCellNode_prog
      rw [Algorithm.probeCellNode]
      simp [hfz, Algorithm.EMPTY_BUCKET]
    · have hfzb : (fuel == 0) = false := beq_false_of_ne hfz
      simp only [hfzb, Bool.false_eq_true, ↓reduceIte]
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_probeCellNode_prog
      by_cases hemp : head = 4294967295
      · have hempb : (head == 4294967295) = true := beq_iff_eq.mpr hemp
        simp only [hempb, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_probeCellNode_prog
        rw [Algorithm.probeCellNode]
        simp [hfz, hemp, Algorithm.EMPTY_BUCKET]
      · have hempb : (head == 4294967295) = false := beq_false_of_ne hemp
        simp only [hempb, Bool.false_eq_true, ↓reduceIte]
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_probeCellNode_prog
        rw [compareUnsigned_sle']
        by_cases hoob : arena.cellCount ≤ head
        · simp only [hoob, decide_true, ↓reduceIte]
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_probeCellNode_prog
          have hemp' : (head == Algorithm.EMPTY_BUCKET) = false := beq_false_of_ne hemp
          have hge : head ≥ arena.cellCount := hoob
          rw [Algorithm.probeCellNode]
          simp [hfz, hge, Algorithm.EMPTY_BUCKET]
        · simp only [hoob, decide_false, Bool.false_eq_true, ↓reduceIte]
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_probeCellNode_prog
          have hnext : (fuel - 1).toNat ≤ m := by rw [ui32_sub1_toNat hfz]; omega
          have hmiss : ∀ km (locs : Nat → JvmVal),
              locs 0 = .arenaRef 0 → locs 1 = .i32 head → locs 2 = .i32 lvl.toInt8.toInt32.toUInt32 →
              locs 3 = .i32 nw → locs 4 = .i32 ne → locs 5 = .i32 sw → locs 6 = .i32 se →
              locs 7 = .i32 fuel → locs 9 = .arenaU32Ref 0 .cellNext →
              runJvmValFast (km + (m + 1) * 130 + 50) f_Algorithm_probeCellNode_prog 60
                (f_Algorithm_probeCellNode_prog.drop 60) ⟨60, [], locs, [arena], [], []⟩ =
                some (.i32 (Algorithm.probeCellNode arena arena.cellNext[head.toNat]! lvl nw ne sw se (fuel - 1))) := by
            intro km locs h0 h1 h2 h3 h4 h5 h6 h7 h9
            flat_step_blk f_Algorithm_probeCellNode_prog
            (conv => lhs; simp only [h0, h1, h2, h3, h4, h5, h6, h7, h9]; dsimp only [getArenaU32]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_probeCellNode_prog
            (conv => lhs; dsimp only [getArenaU32]; simp only [h0, h1, h2, h3, h4, h5, h6, h7, h9]; dsimp only [JvmVal.asI32]; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            try simp only [Nat.succ_eq_add_one]
            try simp only [nat_add_eq]
            simp only [Nat.add_assoc]
            rw [Nat.add_left_comm km ((m + 1) * 130), Nat.add_comm ((m + 1) * 130)]
            exact ih _ arena arena.cellNext[head.toNat]! lvl nw ne sw se (fuel - 1) hnext _
          have hemp' : (head == Algorithm.EMPTY_BUCKET) = false := beq_false_of_ne hemp
          have hnotge : ¬ (head ≥ arena.cellCount) := hoob
          by_cases hlvl : arena.cellLevel[head.toNat]! = lvl
          · have hlvlb : (arena.cellLevel[head.toNat]! == lvl) = true := beq_iff_eq.mpr hlvl
            have hlvls : arena.cellLevel[head.toNat]!.toInt8.toInt32.toUInt32 = lvl.toInt8.toInt32.toUInt32 :=
              (u8_sext_inj _ _).mpr hlvl
            (conv => lhs; dsimp only [getArenaU8]; simp only [hlvls, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
            (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_probeCellNode_prog
            by_cases hnw : arena.cellNw[head.toNat]! = nw
            · have hnwb : (arena.cellNw[head.toNat]! == nw) = true := beq_iff_eq.mpr hnw
              (conv => lhs; dsimp only [getArenaU32]; simp only [hnwb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_probeCellNode_prog
              by_cases hne : arena.cellNe[head.toNat]! = ne
              · have hneb : (arena.cellNe[head.toNat]! == ne) = true := beq_iff_eq.mpr hne
                (conv => lhs; dsimp only [getArenaU32]; simp only [hneb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_probeCellNode_prog
                by_cases hsw : arena.cellSw[head.toNat]! = sw
                · have hswb : (arena.cellSw[head.toNat]! == sw) = true := beq_iff_eq.mpr hsw
                  (conv => lhs; dsimp only [getArenaU32]; simp only [hswb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_probeCellNode_prog
                  by_cases hse : arena.cellSe[head.toNat]! = se
                  · have hseb : (arena.cellSe[head.toNat]! == se) = true := beq_iff_eq.mpr hse
                    (conv => lhs; dsimp only [getArenaU32]; simp only [hseb, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_probeCellNode_prog
                    rw [Algorithm.probeCellNode]
                    simp [hfz, hemp', hnotge, hlvlb, hnwb, hneb, hswb, hseb]
                  · have hseb : (arena.cellSe[head.toNat]! == se) = false := beq_false_of_ne hse
                    (conv => lhs; dsimp only [getArenaU32]; simp only [hseb, Bool.not_false, ↓reduceIte])
                    try simp only [Nat.succ_eq_add_one]
                    try simp only [nat_add_eq]
                    simp only [Nat.add_assoc]
                    rw [Nat.add_left_comm k ((m + 1) * 130), Nat.add_comm ((m + 1) * 130)]
                    rw [fuel_split (C := 50) k ((m + 1) * 130) _ (by omega)]
                    rw [Algorithm.probeCellNode]
                    simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                      hlvlb, hnwb, hneb, hswb, hseb, Bool.and_false]
                    refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
                · have hswb : (arena.cellSw[head.toNat]! == sw) = false := beq_false_of_ne hsw
                  (conv => lhs; dsimp only [getArenaU32]; simp only [hswb, Bool.not_false, ↓reduceIte])
                  try simp only [Nat.succ_eq_add_one]
                  try simp only [nat_add_eq]
                  simp only [Nat.add_assoc]
                  rw [Nat.add_left_comm k ((m + 1) * 130), Nat.add_comm ((m + 1) * 130)]
                  rw [fuel_split (C := 50) k ((m + 1) * 130) _ (by omega)]
                  rw [Algorithm.probeCellNode]
                  simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                    hlvlb, hnwb, hneb, hswb, Bool.and_false, Bool.false_and]
                  refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
              · have hneb : (arena.cellNe[head.toNat]! == ne) = false := beq_false_of_ne hne
                (conv => lhs; dsimp only [getArenaU32]; simp only [hneb, Bool.not_false, ↓reduceIte])
                try simp only [Nat.succ_eq_add_one]
                try simp only [nat_add_eq]
                simp only [Nat.add_assoc]
                rw [Nat.add_left_comm k ((m + 1) * 130), Nat.add_comm ((m + 1) * 130)]
                rw [fuel_split (C := 50) k ((m + 1) * 130) _ (by omega)]
                rw [Algorithm.probeCellNode]
                simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                  hlvlb, hnwb, hneb, Bool.and_false, Bool.false_and]
                refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
            · have hnwb : (arena.cellNw[head.toNat]! == nw) = false := beq_false_of_ne hnw
              (conv => lhs; dsimp only [getArenaU32]; simp only [hnwb, Bool.not_false, ↓reduceIte])
              try simp only [Nat.succ_eq_add_one]
              try simp only [nat_add_eq]
              simp only [Nat.add_assoc]
              rw [Nat.add_left_comm k ((m + 1) * 130), Nat.add_comm ((m + 1) * 130)]
              rw [fuel_split (C := 50) k ((m + 1) * 130) _ (by omega)]
              rw [Algorithm.probeCellNode]
              simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
                hlvlb, hnwb, Bool.and_false, Bool.false_and]
              refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
          · have hlvlb : (arena.cellLevel[head.toNat]! == lvl) = false := beq_false_of_ne hlvl
            have hlvls : arena.cellLevel[head.toNat]!.toInt8.toInt32.toUInt32 ≠ lvl.toInt8.toInt32.toUInt32 :=
              mt (u8_sext_inj _ _).mp hlvl
            have hlvlsb : (arena.cellLevel[head.toNat]!.toInt8.toInt32.toUInt32 == lvl.toInt8.toInt32.toUInt32) = false :=
              beq_false_of_ne hlvls
            (conv => lhs; dsimp only [getArenaU8]; simp only [hlvlsb, Bool.not_false, ↓reduceIte])
            try simp only [Nat.succ_eq_add_one]
            try simp only [nat_add_eq]
            simp only [Nat.add_assoc]
            rw [Nat.add_left_comm k ((m + 1) * 130), Nat.add_comm ((m + 1) * 130)]
            rw [fuel_split (C := 50) k ((m + 1) * 130) _ (by omega)]
            rw [Algorithm.probeCellNode]
            simp only [hfz, ↓reduceDIte, hemp', Bool.false_eq_true, ↓reduceIte, hnotge,
              hlvlb, Bool.false_and]
            refine hmiss _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl

theorem probeCellNode_equiv (arena : Algorithm.FlatHashLifeArena) (head : UInt32) (lvl : UInt8)
    (nw ne sw se fuel : UInt32) :
    runJvm ((fuel.toNat + 1) * 130 + 3) f_Algorithm_probeCellNode_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 head), (2, .i32 lvl.toInt8.toInt32.toUInt32),
        (3, .i32 nw), (4, .i32 ne), (5, .i32 sw), (6, .i32 se), (7, .i32 fuel)] [arena]) =
      some (.i32 (Algorithm.probeCellNode arena head lvl nw ne sw se fuel)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((fuel.toNat + 1) * 130)]
  exact probeCellNode_aux (fuel.toNat) 0 arena head lvl nw ne sw se fuel (by omega) _

private theorem bool_i32_ne_zero (b : Bool) :
    ((if b then (1 : UInt32) else 0) != 0) = b := by
  cases b <;> rfl

private theorem u8_sext_toUInt8_id (a : UInt8) :
    a.toInt8.toInt32.toUInt32.toUInt8 = a := by
  apply UInt8.eq_of_toBitVec_eq; bv_normalize

private theorem u8_sext_band255 (a : UInt8) :
    (a.toInt8.toInt32.toUInt32 &&& 255) = a.toUInt32 := by
  apply UInt32.eq_of_toBitVec_eq; bv_check "lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.u8_sext_band255.lrat"

private theorem u8_band255_sle_5 (a : UInt8) :
    ((if (a.toInt8.toInt32.toUInt32 &&& 255) == 5 then (0 : UInt32)
      else if (a.toInt8.toInt32.toUInt32 &&& 255).toBitVec.slt 5#32 then 4294967295 else 1).toBitVec.sle 0#32) ↔
      a ≤ 5 := by
  rw [UInt8.le_iff_toBitVec_le]
  bv_check "lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.u8_band255_sle_5.lrat"

private theorem lshl_63_mask (k : UInt32) :
    ((1 : UInt64) <<< (k &&& 63).toUInt64) = (1 <<< k.toUInt64) := by
  apply UInt64.eq_of_toBitVec_eq; bv_check "lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.lshl_63_mask.lrat"

private theorem lcmp_slt_zero_int64 (a b : Int64) :
    ((if a.toUInt64 == b.toUInt64 then (0 : UInt32)
      else if a.toUInt64.toBitVec.slt b.toUInt64.toBitVec then 4294967295 else 1).toBitVec.slt 0#32) ↔
      a < b := by
  rw [Int64.lt_iff_toBitVec_slt]
  change ((if a.toBitVec == b.toBitVec then (0 : UInt32)
      else if a.toBitVec.slt b.toBitVec then 4294967295 else 1).toBitVec.slt 0#32) ↔ _
  bv_check "lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.lcmp_slt_zero_int64.lrat"

private theorem lcmp_sle_zero_int64 (a b : Int64) :
    ((if a.toUInt64 == b.toUInt64 then (0 : UInt32)
      else if a.toUInt64.toBitVec.slt b.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) ↔
      a ≤ b := by
  rw [Int64.le_iff_toBitVec_sle]
  change ((if a.toBitVec == b.toBitVec then (0 : UInt32)
      else if a.toBitVec.slt b.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) ↔ _
  bv_check "lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.lcmp_sle_zero_int64.lrat"

private theorem lcmp_sgt_zero_int64 (a b : Int64) :
    ((0#32).slt (if a.toUInt64 == b.toUInt64 then (0 : UInt32)
      else if a.toUInt64.toBitVec.slt b.toUInt64.toBitVec then 4294967295 else 1).toBitVec) ↔
      ¬ (a ≤ b) := by
  rw [Int64.le_iff_toBitVec_sle]
  change ((0#32).slt (if a.toBitVec == b.toBitVec then (0 : UInt32)
      else if a.toBitVec.slt b.toBitVec then 4294967295 else 1).toBitVec) ↔ _
  bv_check "lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.lcmp_sgt_zero_int64.lrat"

private theorem int64_toUInt64_sub (a b : Int64) :
    (a - b).toUInt64 = a.toUInt64 - b.toUInt64 :=
  Int64.toUInt64_sub a b

private theorem copyCellFromLoop_aux (m : Nat) :
    ∀ (k : Nat) (dst src : Algorithm.FlatHashLifeArena) (copyMemos : Bool) (stackBase sp fuel : UInt32),
      fuel.toNat ≤ m →
      ∀ (base : Nat → JvmVal),
        (runJvmResFast (k + (m + 1) * 140) f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog 6
          (f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog.drop 6)
          ⟨6, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal base
            0 (.arenaRef 0)) 1 (.arenaRef 1)) 2 (.i32 (if copyMemos then 1 else 0)))
            3 (.i32 stackBase)) 4 (.i32 sp)) 5 (.i32 fuel), [dst, src], [], []⟩).map
          (fun p => (p.1, p.2.arenas)) =
          some (.unit, [dst.copyCellFromLoop src copyMemos stackBase sp fuel, src]) := by
  induction m with
  | zero =>
    intro k dst src copyMemos stackBase sp fuel hn base
    have hfz : fuel = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (by change fuel.toBitVec.toNat = 0; change fuel.toNat ≤ 0 at hn; exact Nat.eq_zero_of_le_zero hn))
    rw [show k + (0 + 1) * 140 = k + 140 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
    have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
    (conv => lhs; rw [ite_eq_left (by simp [hfzb])])
    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
    rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]; dsimp only;
    simp only [hfz, ↓reduceDIte]
  | succ m ih =>
    intro k dst src copyMemos stackBase sp fuel hn base
    rw [show k + (m + 1 + 1) * 140 = (k + (m + 1) * 140) + 140 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
    by_cases hfz : fuel = 0
    · have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
      (conv => lhs; rw [ite_eq_left (by simp [hfzb])])
      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
      rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]; dsimp only;
      simp only [hfz, ↓reduceDIte]
    · have hfzb : (fuel == 0) = false := beq_false_of_ne hfz
      (conv => lhs; rw [ite_eq_right (by simp [hfzb])])
      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
      by_cases hspz : sp = 0
      · have hspzb : (sp == 0) = true := beq_iff_eq.mpr hspz
        (conv => lhs; rw [ite_eq_left (by simp [hspzb])])
        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
        rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]; dsimp only;
        simp [hfz, hspzb]
      · have hspzb : (sp == 0) = false := beq_false_of_ne hspz
        (conv => lhs; rw [ite_eq_right (by simp [hspzb])])
        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
        by_cases hovf : dst.overflow = 0
        · have hovfb : (dst.overflow != 0) = false := by simp [hovf]
          have hovfs : (dst.overflow.toInt8.toInt32.toUInt32 == 0) = true := by rw [u8_sext_beq_zero]; exact beq_iff_eq.mpr hovf
          (conv => lhs; rw [ite_eq_left (by simp only [hovfs])])
          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
          have hnext : (fuel - 1).toNat ≤ m := by rw [ui32_sub1_toNat hfz]; omega
          have hcm : ((if copyMemos then (1 : UInt32) else 0) != 0) = copyMemos := by
            cases copyMemos <;> rfl
          let cellId := Algorithm.getRemapCell dst (stackBase + sp - 1)
          by_cases hoob : src.cellCount ≤ cellId
          · have hoobb : cellId ≥ src.cellCount := hoob
            (conv => lhs; rw [ite_eq_left (by simp only [compareUnsigned_sle', cellId, hoob, decide_true])])
            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
            rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
            rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]; dsimp only;
            simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
            change _ = some (JvmVal.unit,
              [(if src.cellCount ≤ cellId then
                  dst.copyCellFromLoop src copyMemos stackBase (sp - 1) (fuel - 1)
                else _), src])
            simp only [hoobb, ↓reduceIte]
            exact ih _ dst src copyMemos stackBase (sp - 1) (fuel - 1) hnext _
          · have hoobb : ¬ (cellId ≥ src.cellCount) := hoob
            (conv => lhs; rw [ite_eq_right (by simp only [compareUnsigned_sle', cellId, hoob, decide_false]; decide)])
            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
            by_cases hrem : Algorithm.getRemapCell dst cellId = Algorithm.UNCOMPUTED
            · have hremb : (Algorithm.getRemapCell dst cellId != Algorithm.UNCOMPUTED) = false := by
                simp [hrem, Algorithm.UNCOMPUTED]
              have hrems : (Algorithm.getRemapCell dst cellId == 4294967295) = true := by
                simp [hrem, Algorithm.UNCOMPUTED]
              (conv => lhs; rw [ite_eq_left (by simp only [cellId, hrems])])
              (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
              simp only [hcm]
              let resPair := Algorithm.copyCellTryStep dst src cellId copyMemos
              let missingChild := resPair.1
              let d1 := resPair.2
              by_cases hovf1 : d1.overflow = 0
              · have hovf1b : (d1.overflow != 0) = false := by simp [hovf1]
                have hovf1s : (d1.overflow.toInt8.toInt32.toUInt32 == 0) = true := by rw [u8_sext_beq_zero]; exact beq_iff_eq.mpr hovf1
                (conv => lhs; rw [ite_eq_left (by simp only [d1, resPair, cellId, hovf1s])])
                (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
                by_cases hmiss : missingChild = Algorithm.UNCOMPUTED
                · have hmissb : (missingChild == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hmiss
                  have hmisss : (missingChild == 4294967295) = true := by simp [hmiss, Algorithm.UNCOMPUTED]
                  (conv => lhs; rw [ite_eq_left (by simp only [missingChild, resPair, cellId, hmisss])])
                  (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
                  (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
                  try dsimp only [cellId, resPair, missingChild, d1] at hoobb hremb hovf1b hmissb
                  conv =>
                    rhs
                    rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]
                    dsimp only
                    simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hremb]
                    rw [show ((d1.overflow != 0) = false) from hovf1b]
                    rw [show ((missingChild == Algorithm.UNCOMPUTED) = true) from hmissb]
                    simp only [Bool.false_eq_true, ↓reduceIte]
                  exact ih _ d1 src copyMemos stackBase (sp - 1) (fuel - 1) hnext _
                · have hmissb : (missingChild == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hmiss
                  have hmisss : (missingChild == 4294967295) = false := by
                    simpa [Algorithm.UNCOMPUTED] using hmissb
                  (conv => lhs; rw [ite_eq_right (by simp only [missingChild, resPair, cellId, hmisss]; decide)])
                  (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
                  by_cases hdepth : Algorithm.copyStackDepth ≤ sp
                  · have hdepths : (256 : UInt32) ≤ sp := hdepth
                    (conv => lhs; rw [ite_eq_left (by simp only [compareUnsigned_sle', hdepths, decide_true])])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
                    try dsimp only [cellId, resPair, missingChild, d1] at hoobb hremb hovf1b hmissb
                    conv =>
                      rhs
                      rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]
                      dsimp only
                      simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hremb]
                      rw [show ((d1.overflow != 0) = false) from hovf1b]
                      rw [show ((missingChild == Algorithm.UNCOMPUTED) = false) from hmissb]
                      simp only [Bool.false_eq_true, ↓reduceIte, hdepth]
                    exact ih _ d1 src copyMemos stackBase 0 (fuel - 1) hnext _
                  · have hdepths : ¬ ((256 : UInt32) ≤ sp) := hdepth
                    (conv => lhs; rw [ite_eq_right (by simp only [compareUnsigned_sle', hdepths, decide_false]; decide)])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
                    try dsimp only [cellId, resPair, missingChild, d1] at hoobb hremb hovf1b hmissb
                    conv =>
                      rhs
                      rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]
                      dsimp only
                      simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hremb]
                      rw [show ((d1.overflow != 0) = false) from hovf1b]
                      rw [show ((missingChild == Algorithm.UNCOMPUTED) = false) from hmissb]
                      simp only [Bool.false_eq_true, ↓reduceIte, hdepth]
                    exact ih _ (d1.setRemapCell (stackBase + sp) missingChild) src copyMemos
                      stackBase (sp + 1) (fuel - 1) hnext _
              · have hovf1b : (d1.overflow != 0) = true := by simp [hovf1]
                have hovf1s : (d1.overflow.toInt8.toInt32.toUInt32 == 0) = false := by
                  rw [u8_sext_beq_zero]; exact beq_false_of_ne hovf1
                (conv => lhs; rw [ite_eq_right (by simp only [d1, resPair, cellId, hovf1s]; decide)])
                (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
                (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
                try dsimp only [cellId, resPair, missingChild, d1] at hoobb hremb hovf1b
                conv =>
                  rhs
                  rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]
                  dsimp only
                  simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hremb]
                  rw [show ((d1.overflow != 0) = true) from hovf1b]
                  simp only [↓reduceIte]
                exact ih _ d1 src copyMemos stackBase 0 (fuel - 1) hnext _
            · have hremb : (Algorithm.getRemapCell dst cellId != Algorithm.UNCOMPUTED) = true := bne_iff_ne.mpr hrem
              have hrems : (Algorithm.getRemapCell dst cellId == 4294967295) = false := by
                simpa [Algorithm.UNCOMPUTED] using beq_false_of_ne hrem
              (conv => lhs; rw [ite_eq_right (by simp only [cellId, hrems]; decide)])
              (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
              (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
              rw [Nat.add_left_comm k ((m + 1) * 140), Nat.add_comm ((m + 1) * 140)]
              try dsimp only [cellId] at hoobb hremb
              conv =>
                rhs
                rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]
                dsimp only
                simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hremb]
              exact ih _ dst src copyMemos stackBase (sp - 1) (fuel - 1) hnext _
        · have hovfb : (dst.overflow != 0) = true := by simp [hovf]
          have hovfs : (dst.overflow.toInt8.toInt32.toUInt32 == 0) = false := by
            rw [u8_sext_beq_zero]; exact beq_false_of_ne hovf
          (conv => lhs; rw [ite_eq_right (by simp only [hovfs]; decide)])
          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
          rw [Algorithm.FlatHashLifeArena.copyCellFromLoop.eq_1]; dsimp only;
          simp [hfz, hspzb, hovfb]

theorem copyCellFromLoop_equiv (dst src : Algorithm.FlatHashLifeArena) (copyMemos : Bool)
    (stackBase sp fuel : UInt32) :
    (runJvmRes ((fuel.toNat + 1) * 140 + 6) f_Algorithm_FlatHashLifeArena_copyCellFromLoop_prog
      (initJvmState [(0, .arenaRef 0), (1, .arenaRef 1), (2, .i32 (if copyMemos then 1 else 0)),
        (3, .i32 stackBase), (4, .i32 sp), (5, .i32 fuel)] [dst, src])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.unit, [dst.copyCellFromLoop src copyMemos stackBase sp fuel, src]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  (conv => lhs; arg 2; norm_jvm_locals)
  rw [← Nat.zero_add ((fuel.toNat + 1) * 140)]
  exact copyCellFromLoop_aux fuel.toNat 0 dst src copyMemos stackBase sp fuel (Nat.le_refl _) _

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
private theorem stepCellSerialLoop_aux (m : Nat) :
    ∀ (k : Nat) (arena : Algorithm.FlatHashLifeArena) (sp stackLimit fuel : UInt32),
      fuel.toNat ≤ m →
      ∀ (base : Nat → JvmVal),
        (runJvmResFast (k + (m + 1) * 250) f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog 3
          (f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog.drop 3)
          ⟨3, [], setLocal (setLocal (setLocal (setLocal base 0 (.arenaRef 0)) 1 (.i32 sp))
            2 (.i32 stackLimit)) 3 (.i32 fuel), [arena], [], []⟩).map
          (fun p => (p.1, p.2.arenas)) =
          some (.unit, [arena.stepCellSerialLoop sp stackLimit fuel]) := by
  induction m with
  | zero =>
    intro k arena sp stackLimit fuel hn base
    have hfz : fuel = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (by change fuel.toBitVec.toNat = 0; change fuel.toNat ≤ 0 at hn; exact Nat.eq_zero_of_le_zero hn))
    rw [show k + (0 + 1) * 250 = k + 250 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
    have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
    (conv => lhs; rw [ite_eq_left (by simp [hfzb])])
    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
    rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]; dsimp only;
    simp only [hfz, ↓reduceDIte]
  | succ m ih =>
    intro k arena sp stackLimit fuel hn base
    rw [show k + (m + 1 + 1) * 250 = (k + (m + 1) * 250) + 250 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
    by_cases hfz : fuel = 0
    · have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
      (conv => lhs; rw [ite_eq_left (by simp [hfzb])])
      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
      rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]; dsimp only;
      simp only [hfz, ↓reduceDIte]
    · have hfzb : (fuel == 0) = false := beq_false_of_ne hfz
      (conv => lhs; rw [ite_eq_right (by simp [hfzb])])
      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
      by_cases hspz : sp = 0
      · have hspzb : (sp == 0) = true := beq_iff_eq.mpr hspz
        (conv => lhs; rw [ite_eq_left (by simp [hspzb])])
        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
        rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]; dsimp only;
        simp [hfz, hspzb]
      · have hspzb : (sp == 0) = false := beq_false_of_ne hspz
        (conv => lhs; rw [ite_eq_right (by simp [hspzb])])
        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
        by_cases hovf : arena.overflow = 0
        · have hovfb : (arena.overflow != 0) = false := by simp [hovf]
          have hovfs : (arena.overflow.toInt8.toInt32.toUInt32 == 0) = true := by rw [u8_sext_beq_zero]; exact beq_iff_eq.mpr hovf
          (conv => lhs; rw [ite_eq_left (by simp only [hovfs])])
          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
          have hnext : (fuel - 1).toNat ≤ m := by rw [ui32_sub1_toNat hfz]; omega
          let fbase := (sp - 1) * Algorithm.stepFrameWidth
          let nodeId := arena.remapL4[fbase.toNat]!
          by_cases hoob : arena.cellCount ≤ nodeId
          · have hoobb : nodeId ≥ arena.cellCount := hoob
            (conv => lhs; rw [ite_eq_left (by rw [compareUnsigned_sle']; exact decide_eq_true hoob)])
            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
            rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
            conv =>
              rhs
              rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
              dsimp only
              simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
            change _ = some (JvmVal.unit,
              [(if arena.cellCount ≤ nodeId then
                  arena.stepCellSerialLoop (sp - 1) stackLimit (fuel - 1)
                else _)])
            rw [ite_eq_left (by dsimp only [nodeId, fbase, Algorithm.stepFrameWidth] at hoobb; exact hoobb)]
            exact ih _ arena (sp - 1) stackLimit (fuel - 1) hnext _
          · have hoobb : ¬ (nodeId ≥ arena.cellCount) := hoob
            (conv => lhs; rw [ite_eq_right (by rw [compareUnsigned_sle', decide_eq_false (by dsimp only [nodeId, fbase, Algorithm.stepFrameWidth] at hoob; exact hoob)]; exact Bool.false_ne_true)])
            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
            by_cases hres : arena.cellStepRes[nodeId.toNat]! = Algorithm.UNCOMPUTED
            · have hresb : (arena.cellStepRes[nodeId.toNat]! != Algorithm.UNCOMPUTED) = false := by
                simp [hres, Algorithm.UNCOMPUTED]
              have hress : (arena.cellStepRes[nodeId.toNat]! == 4294967295) = true := by
                simp [hres, Algorithm.UNCOMPUTED]
              (conv => lhs; rw [ite_eq_left (by exact hress)])
              (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
              let lvl := arena.cellLevel[nodeId.toNat]!
              by_cases hlvl : lvl ≤ 5
              · have hlvls : ((if (lvl.toInt8.toInt32.toUInt32 &&& 255) == 5 then (0 : UInt32)
                    else if (lvl.toInt8.toInt32.toUInt32 &&& 255).toBitVec.slt 5#32 then 4294967295 else 1).toBitVec.sle 0#32) = true :=
                  (u8_band255_sle_5 lvl).mpr hlvl
                (conv => lhs; rw [ite_eq_left (by exact hlvls)])
                (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                dsimp only [fbase, nodeId, lvl] at hoobb hresb hlvl
                conv =>
                  rhs
                  rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                  dsimp only
                  simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl]
                exact ih _ (arena.stepLevel5 nodeId).2 (sp - 1) stackLimit (fuel - 1) hnext _
              · have hlvls : ((if (lvl.toInt8.toInt32.toUInt32 &&& 255) == 5 then (0 : UInt32)
                    else if (lvl.toInt8.toInt32.toUInt32 &&& 255).toBitVec.slt 5#32 then 4294967295 else 1).toBitVec.sle 0#32) = false :=
                  Bool.eq_false_iff.mpr (mt (u8_band255_sle_5 lvl).mp hlvl)
                (conv => lhs; rw [ite_eq_right (by intro h; simp only [getArenaU8, getArenaU32] at h; exact Bool.false_ne_true (hlvls.symm.trans h))])
                (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                let a4 := arena.expandFrameIfNeeded nodeId fbase
                by_cases hov4 : a4.overflow = 0
                · have hov4b : (a4.overflow != 0) = false := by simp [hov4]
                  have hov4s : (a4.overflow.toInt8.toInt32.toUInt32 == 0) = true := by rw [u8_sext_beq_zero]; exact beq_iff_eq.mpr hov4
                  (conv => lhs; rw [ite_eq_left (by exact hov4s)])
                  (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                  let q_nw := a4.remapL4[(fbase + 1).toNat]!
                  let q_ne := a4.remapL4[(fbase + 2).toNat]!
                  let q_sw := a4.remapL4[(fbase + 3).toNat]!
                  let q_se := a4.remapL4[(fbase + 4).toNat]!
                  let r_nw := Algorithm.getCellStepRes a4 q_nw
                  let r_ne := Algorithm.getCellStepRes a4 q_ne
                  let r_sw := Algorithm.getCellStepRes a4 q_sw
                  let r_se := Algorithm.getCellStepRes a4 q_se
                  have hpush : ∀ km (child : UInt32) (locs : Nat → JvmVal),
                      locs 0 = .arenaRef 0 → locs 1 = .i32 sp → locs 2 = .i32 stackLimit →
                      locs 3 = .i32 fuel → locs 15 = .i32 (sp * 5) →
                      (runJvmResFast (km + (m + 1) * 250 + 50) f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog 249
                        (f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog.drop 249)
                        ⟨249, [.i32 child, .i32 (sp * 5), .arenaRef 0], locs, [a4], [], []⟩).map (fun p => (p.1, p.2.arenas)) =
                        some (.unit, [((a4.setRemapL4 (sp * Algorithm.stepFrameWidth) child).setRemapL4
                          (sp * Algorithm.stepFrameWidth + 1) Algorithm.UNCOMPUTED).stepCellSerialLoop
                            (sp + 1) stackLimit (fuel - 1)]) := by
                    intro km child locs h0 h1 h2 h3 h15
                    have hdrop249 : f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog.drop 249 =
                        [.invokestatic "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt" "f_Algorithm_FlatHashLifeArena_setRemapL4-BltQuoY" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V", .iload 15, .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 16, .aload 0, .iload 16, .iconst 4294967295, .invokestatic "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt" "f_Algorithm_FlatHashLifeArena_setRemapL4-BltQuoY" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V", .iload 1, .iconst 1, .iadd, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 17, .iload 3, .iconst 1, .isub, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 18, .aload 0, .astore 19, .iload 2, .istore 20, .aload 19, .astore 0, .iload 17, .istore 1, .iload 20, .istore 2, .iload 18, .istore 3, .goto 3, .aload 0, .iload 11, .invokestatic "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt" "f_Algorithm_FlatHashLifeArena_stepLevel5-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I", .istore 13, .iload 3, .iconst 1, .isub, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 14, .aload 0, .astore 15, .iload 2, .istore 16, .aload 15, .astore 0, .iload 5, .istore 1, .iload 16, .istore 2, .iload 14, .istore 3, .goto 3, .iload 3, .iconst 1, .isub, .invokestatic "kotlin/UInt" "constructor-impl" "(I)I", .istore 12, .aload 0, .astore 13, .iload 2, .istore 14, .aload 13, .astore 0, .iload 5, .istore 1, .iload 14, .istore 2, .iload 12, .istore 3, .goto 3, .vreturn, .vreturn] := by rfl
                    (conv => lhs; arg 2; rw [hdrop249])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3, h15])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3, h15])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [Nat.add_left_comm km ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                    exact ih _ _ (sp + 1) stackLimit (fuel - 1) hnext _
                  have hneedchild : ∀ km (locs : Nat → JvmVal),
                      locs 0 = .arenaRef 0 → locs 1 = .i32 sp → locs 2 = .i32 stackLimit →
                      locs 3 = .i32 fuel → locs 16 = .i32 q_nw → locs 17 = .i32 q_ne →
                      locs 18 = .i32 q_sw → locs 19 = .i32 q_se →
                      locs 21 = .i32 r_ne → locs 22 = .i32 r_sw →
                      locs 23 = .i32 (if r_nw = Algorithm.UNCOMPUTED then 1 else 0) →
                      (runJvmResFast (km + (m + 1) * 250 + 110) f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog 199
                        (f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog.drop 199)
                        ⟨199, [], locs, [a4], [], []⟩).map (fun p => (p.1, p.2.arenas)) =
                        some (.unit, [if sp ≥ stackLimit then a4.stepCellSerialLoop 0 stackLimit (fuel - 1)
                          else ((a4.setRemapL4 (sp * Algorithm.stepFrameWidth)
                            (if r_nw == Algorithm.UNCOMPUTED then q_nw else if r_ne == Algorithm.UNCOMPUTED then q_ne
                              else if r_sw == Algorithm.UNCOMPUTED then q_sw else q_se)).setRemapL4
                            (sp * Algorithm.stepFrameWidth + 1) Algorithm.UNCOMPUTED).stepCellSerialLoop
                            (sp + 1) stackLimit (fuel - 1)]) := by
                    intro km locs h0 h1 h2 h3 h16 h17 h18 h19 h21 h22 h23
                    (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3, h16, h17, h18, h19, h21, h22, h23]); (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    by_cases hlim : stackLimit ≤ sp
                    · (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI32, h1, h2]; rw [compareUnsigned_sle']; exact decide_eq_true hlim)])
                      (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3])
                      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                      (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3])
                      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                      rw [Nat.add_left_comm km ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                      have hlims : sp ≥ stackLimit := hlim
                      (conv => rhs; simp only [hlims, ↓reduceIte])
                      exact ih _ a4 0 stackLimit (fuel - 1) hnext _
                    · (conv => lhs; rw [ite_eq_right (by simp only [JvmVal.asI32, h1, h2]; rw [compareUnsigned_sle', decide_eq_false hlim]; exact Bool.false_ne_true)])
                      (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3, h16, h17, h18, h19, h21, h22, h23])
                      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                      have hlims : ¬ (sp ≥ stackLimit) := hlim
                      (conv => rhs; simp only [hlims, ↓reduceIte])
                      by_cases hrnw : r_nw = Algorithm.UNCOMPUTED
                      · have hrnwb : (r_nw == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrnw
                        (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI32, h23, hrnw]; simp)])
                        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                        flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                        (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3, h16, h17, h18, h19])
                        (conv => lhs; arg 2; norm_jvm_locals; jvm_whnf_run_args)
                        (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                        rw [Nat.add_left_comm km ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                        rw [fuel_split (C := 50) km ((m + 1) * 250) _ (by omega)]
                        (conv => rhs; simp only [hrnwb, ↓reduceIte])
                        refine hpush _ q_nw _ h0 h1 h2 h3 (by simp only [setLocal]; rfl)
                      · have hrnwb : (r_nw == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrnw
                        (conv => lhs; rw [ite_eq_right (by simp only [JvmVal.asI32, h23, hrnw]; simp)])
                        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                        flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                        by_cases hrne : r_ne = Algorithm.UNCOMPUTED
                        · have hrneb : (r_ne == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrne
                          have hrnes : (r_ne == 4294967295) = true := by simpa [Algorithm.UNCOMPUTED] using hrneb
                          (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI32, h21]; exact hrnes)])
                          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                          flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                          (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3, h16, h17, h18, h19])
                          (conv => lhs; arg 2; norm_jvm_locals; jvm_whnf_run_args)
                          (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                          rw [Nat.add_left_comm km ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                          rw [fuel_split (C := 50) km ((m + 1) * 250) _ (by omega)]
                          (conv => rhs; simp only [hrnwb, hrneb, Bool.false_eq_true, ↓reduceIte])
                          refine hpush _ q_ne _ h0 h1 h2 h3 (by simp only [setLocal]; rfl)
                        · have hrneb : (r_ne == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrne
                          have hrnes : (r_ne == 4294967295) = false := by simpa [Algorithm.UNCOMPUTED] using hrneb
                          (conv => lhs; rw [ite_eq_right (by simp only [JvmVal.asI32, h21, hrnes]; exact Bool.false_ne_true)])
                          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                          flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                          by_cases hrsw : r_sw = Algorithm.UNCOMPUTED
                          · have hrswb : (r_sw == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrsw
                            have hrsws : (r_sw == 4294967295) = true := by simpa [Algorithm.UNCOMPUTED] using hrswb
                            (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI32, h22]; exact hrsws)])
                            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                            flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                            (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3, h16, h17, h18, h19])
                            (conv => lhs; arg 2; norm_jvm_locals; jvm_whnf_run_args)
                            (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                            rw [Nat.add_left_comm km ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                            rw [fuel_split (C := 50) km ((m + 1) * 250) _ (by omega)]
                            (conv => rhs; simp only [hrnwb, hrneb, hrswb, Bool.false_eq_true, ↓reduceIte])
                            refine hpush _ q_sw _ h0 h1 h2 h3 (by simp only [setLocal]; rfl)
                          · have hrswb : (r_sw == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrsw
                            have hrsws : (r_sw == 4294967295) = false := by simpa [Algorithm.UNCOMPUTED] using hrswb
                            (conv => lhs; rw [ite_eq_right (by simp only [JvmVal.asI32, h22, hrsws]; exact Bool.false_ne_true)])
                            (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                            flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                            (conv => lhs; arg 2; arg 5; simp only [h0, h1, h2, h3, h16, h17, h18, h19])
                            (conv => lhs; arg 2; norm_jvm_locals; jvm_whnf_run_args)
                            (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                            rw [Nat.add_left_comm km ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                            rw [fuel_split (C := 50) km ((m + 1) * 250) _ (by omega)]
                            (conv => rhs; simp only [hrnwb, hrneb, hrswb, Bool.false_eq_true, ↓reduceIte])
                            refine hpush _ q_se _ h0 h1 h2 h3 (by simp only [setLocal]; rfl)
                  by_cases hrnw : r_nw = Algorithm.UNCOMPUTED
                  · have hrnwb : (r_nw == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrnw
                    have hrnws : (r_nw == 4294967295) = true := by simpa [Algorithm.UNCOMPUTED] using hrnwb
                    (conv => lhs; rw [ite_eq_right (by change ¬ ((! (r_nw == 4294967295)) = true); rw [hrnws]; exact Bool.false_ne_true)])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                    rw [fuel_split (C := 110) k ((m + 1) * 250) _ (by omega)]
                    dsimp only [nodeId, fbase, lvl, a4, q_nw, r_nw] at hoobb hresb hlvl hov4b hrnwb
                    conv =>
                      rhs
                      rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                      dsimp only
                      simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl, hov4b]
                      rw [ite_eq_left (by simp only [hrnwb, Bool.true_or])]
                    refine hneedchild _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                    all_goals try rfl
                    simp [setLocal, hrnw]
                  · have hrnwb : (r_nw == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrnw
                    have hrnws : (r_nw == 4294967295) = false := by simpa [Algorithm.UNCOMPUTED] using hrnwb
                    (conv => lhs; rw [ite_eq_left (by change (! (r_nw == 4294967295)) = true; rw [hrnws]; rfl)])
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                    by_cases hrne : r_ne = Algorithm.UNCOMPUTED
                    · have hrneb : (r_ne == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrne
                      have hrnes : (r_ne == 4294967295) = true := by simpa [Algorithm.UNCOMPUTED] using hrneb
                      (conv => lhs; rw [ite_eq_left (by dsimp only [Algorithm.getCellStepRes]; change (r_ne == 4294967295) = true; exact hrnes)])
                      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                      rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                      rw [fuel_split (C := 110) k ((m + 1) * 250) _ (by omega)]
                      dsimp only [nodeId, fbase, lvl, a4, q_nw, q_ne, r_nw, r_ne] at hoobb hresb hlvl hov4b hrnwb hrneb
                      conv =>
                        rhs
                        rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                        dsimp only
                        simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl, hov4b]
                        rw [ite_eq_left (by simp only [hrneb, Bool.true_or, Bool.or_true])]
                      refine hneedchild _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                      all_goals try rfl
                      simp [setLocal, hrnw]
                    · have hrneb : (r_ne == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrne
                      have hrnes : (r_ne == 4294967295) = false := by simpa [Algorithm.UNCOMPUTED] using hrneb
                      (conv => lhs; rw [ite_eq_right (by dsimp only [Algorithm.getCellStepRes]; change ¬ ((r_ne == 4294967295) = true); rw [hrnes]; exact Bool.false_ne_true)])
                      (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                      by_cases hrsw : r_sw = Algorithm.UNCOMPUTED
                      · have hrswb : (r_sw == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrsw
                        have hrsws : (r_sw == 4294967295) = true := by simpa [Algorithm.UNCOMPUTED] using hrswb
                        (conv => lhs; rw [ite_eq_left (by dsimp only [Algorithm.getCellStepRes]; change (r_sw == 4294967295) = true; exact hrsws)])
                        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                        (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                        rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                        rw [fuel_split (C := 110) k ((m + 1) * 250) _ (by omega)]
                        dsimp only [nodeId, fbase, lvl, a4, q_nw, q_ne, q_sw, r_nw, r_ne, r_sw] at hoobb hresb hlvl hov4b hrnwb hrneb hrswb
                        conv =>
                          rhs
                          rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                          dsimp only
                          simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl, hov4b]
                          rw [ite_eq_left (by simp only [hrswb, Bool.true_or, Bool.or_true])]
                        refine hneedchild _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                        all_goals try rfl
                        simp [setLocal, hrnw]
                      · have hrswb : (r_sw == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrsw
                        have hrsws : (r_sw == 4294967295) = false := by simpa [Algorithm.UNCOMPUTED] using hrswb
                        (conv => lhs; rw [ite_eq_right (by dsimp only [Algorithm.getCellStepRes]; change ¬ ((r_sw == 4294967295) = true); rw [hrsws]; exact Bool.false_ne_true)])
                        (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                        flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                        by_cases hrse : r_se = Algorithm.UNCOMPUTED
                        · have hrseb : (r_se == Algorithm.UNCOMPUTED) = true := beq_iff_eq.mpr hrse
                          have hrses : (r_se == 4294967295) = true := by simpa [Algorithm.UNCOMPUTED] using hrseb
                          (conv => lhs; rw [ite_eq_left (by dsimp only [Algorithm.getCellStepRes]; change (r_se == 4294967295) = true; exact hrses)])
                          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                          (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                          rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                          rw [fuel_split (C := 110) k ((m + 1) * 250) _ (by omega)]
                          dsimp only [nodeId, fbase, lvl, a4, q_nw, q_ne, q_sw, q_se, r_nw, r_ne, r_sw, r_se] at hoobb hresb hlvl hov4b hrnwb hrneb hrswb hrseb
                          conv =>
                            rhs
                            rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                            dsimp only
                            simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl, hov4b]
                            rw [ite_eq_left (by simp only [hrseb, Bool.or_true])]
                          refine hneedchild _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
                          all_goals try rfl
                          simp [setLocal, hrnw]
                        · have hrseb : (r_se == Algorithm.UNCOMPUTED) = false := beq_false_of_ne hrse
                          have hrses : (r_se == 4294967295) = false := by simpa [Algorithm.UNCOMPUTED] using hrseb
                          (conv => lhs; rw [ite_eq_right (by dsimp only [Algorithm.getCellStepRes]; change ¬ ((r_se == 4294967295) = true); rw [hrses]; exact Bool.false_ne_true)])
                          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                          flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                          (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                          rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                          dsimp only [nodeId, fbase, lvl, a4, q_nw, q_ne, q_sw, q_se, r_nw, r_ne, r_sw, r_se] at hoobb hresb hlvl hov4b hrnwb hrneb hrswb hrseb
                          conv =>
                            rhs
                            rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                            dsimp only
                            simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl, hov4b, hrnwb, hrneb, hrswb, hrseb, Bool.false_or]
                          (conv => lhs; arg 2; simp only [u8_sext_toUInt8_id])
                          exact ih _ (a4.combineQuadrants nodeId lvl r_nw r_ne r_sw r_se).2
                            (sp - 1) stackLimit (fuel - 1) hnext _
                · have hov4b : (a4.overflow != 0) = true := by simp [hov4]
                  have hov4s : (a4.overflow.toInt8.toInt32.toUInt32 == 0) = false := by
                    rw [u8_sext_beq_zero]; exact beq_false_of_ne hov4
                  (conv => lhs; rw [ite_eq_right (by dsimp only [a4, nodeId, fbase, getArenaU32, Algorithm.stepFrameWidth] at hov4s; simp only [getArenaU32]; rw [hov4s]; exact Bool.false_ne_true)])
                  (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
                  (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
                  dsimp only [nodeId, fbase, lvl, a4] at hoobb hresb hlvl hov4b
                  conv =>
                    rhs
                    rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                    dsimp only
                    simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb, hlvl, hov4b]
                  exact ih _ a4 0 stackLimit (fuel - 1) hnext _
            · have hresb : (arena.cellStepRes[nodeId.toNat]! != Algorithm.UNCOMPUTED) = true := bne_iff_ne.mpr hres
              have hress : (arena.cellStepRes[nodeId.toNat]! == 4294967295) = false := by
                simpa [Algorithm.UNCOMPUTED] using beq_false_of_ne hres
              (conv => lhs; rw [ite_eq_right (by dsimp only [nodeId, fbase, getArenaU32, Algorithm.stepFrameWidth] at hress; simp only [getArenaU32]; rw [hress]; exact Bool.false_ne_true)])
              (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
              (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              (conv => lhs; arg 2; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
              rw [Nat.add_left_comm k ((m + 1) * 250), Nat.add_comm ((m + 1) * 250)]
              dsimp only [nodeId, fbase] at hoobb hresb
              conv =>
                rhs
                rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]
                dsimp only
                simp only [hfz, ↓reduceDIte, hspzb, hovfb, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hoobb, hresb]
              exact ih _ arena (sp - 1) stackLimit (fuel - 1) hnext _
        · have hovfb : (arena.overflow != 0) = true := by simp [hovf]
          have hovfs : (arena.overflow.toInt8.toInt32.toUInt32 == 0) = false := by
            rw [u8_sext_beq_zero]; exact beq_false_of_ne hovf
          (conv => lhs; rw [ite_eq_right (by rw [hovfs]; exact Bool.false_ne_true)])
          (conv => lhs; arg 2; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
          rw [Algorithm.FlatHashLifeArena.stepCellSerialLoop.eq_1]; dsimp only;
          simp [hfz, hspzb, hovfb]

theorem stepCellSerialLoop_equiv (arena : Algorithm.FlatHashLifeArena) (sp stackLimit fuel : UInt32) :
    (runJvmRes ((fuel.toNat + 1) * 250 + 3) f_Algorithm_FlatHashLifeArena_stepCellSerialLoop_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 sp), (2, .i32 stackLimit), (3, .i32 fuel)] [arena])).map
        (fun p => (p.1, p.2.arenas)) =
      some (.unit, [arena.stepCellSerialLoop sp stackLimit fuel]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ _ _ _ _ rfl
  (conv => lhs; arg 2; rw [runJvmResFast_stepResFlatChunk 10]; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  (conv => lhs; arg 2; norm_jvm_locals)
  rw [← Nat.zero_add ((fuel.toNat + 1) * 250)]
  exact stepCellSerialLoop_aux fuel.toNat 0 arena sp stackLimit fuel (Nat.le_refl _) _

elab "flat_step_to" tgtPc:num : tactic => do
  let target := tgtPc.getNat
  for _ in [:400] do
    if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then break
    let tgt := (← Lean.Elab.Tactic.getMainTarget).consumeMData
    let some (_, lhs, _) := tgt.eq? | break
    let (inner, isMap) := unwrapRunLhs lhs
    if isMap || !inner.isAppOfArity ``runJvmValFast 5 then break
    let pcExpr ← Lean.Meta.whnf (inner.getArg! 2)
    let some curPc := pcExpr.rawNatLit? | break
    if curPc == target then break
    if ← tryStepFlatInvoke then
      continue
    else if ← isRunJvmAtFlatNonStop then
      let stepN := if curPc < target then min 120 (target - curPc) else 120
      let nStx := Lean.Syntax.mkNumLit (toString stepN)
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_stepFlatChunk $nStx]))
      if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
        Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; arg 1; jvm_whnf_blk)))
        let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
        let some (_, lhs2, _) := tgt2.eq? | break
        let (afterApp, _) := unwrapRunLhs lhs2
        let chunkRes := (afterApp.getArg! 0).consumeMData
        if let some cn := chunkRes.getAppFn.constName? then
          if cn == ``BlockChunkRes.cont then
            Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_cont]))
          else if cn == ``BlockChunkRes.jump then
            Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_jump]))
          else if cn == ``BlockChunkRes.done then
            Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_done]))
        if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
          Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals)))
          Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; jvm_whnf_run_args)))
    else if ← isRunJvmAtForwardGoto then
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [runJvmValFast_at_branch_cons (hbr := rfl)]))
      if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
        Lean.Elab.Tactic.evalTactic (← `(tactic| (
          (conv => lhs; arg 1; whnf)
          (conv => lhs; arg 3; whnf)
          (conv => lhs; arg 4; whnf)
          (conv => lhs; arg 6; jvm_whnf_blk))))
        let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
        let some (_, lhs2, _) := tgt2.eq? | break
        rwEvalBranchByInstr false (lhs2.getArg! 3)
        if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
          Lean.Elab.Tactic.evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)))
    else
      break

private theorem int64_sub_toUInt32 (a b : Int64) :
    (a - b).toUInt64.toUInt32 = a.toUInt64.toUInt32 - b.toUInt64.toUInt32 := by
  apply UInt32.eq_of_toBitVec_eq; bv_check "lrat/JvmEquiv._private.proofs.JvmEquiv.0.Algorithm.JvmVerification.int64_sub_toUInt32.lrat"

private theorem uint64_sub8_toUInt32 (x : Int64) :
    (x.toUInt64 - 8).toUInt32 = x.toUInt64.toUInt32 - (8 : Int64).toUInt64.toUInt32 := by
  apply UInt32.eq_of_toBitVec_eq; bv_normalize

private theorem int64_sub8_toUInt32 (x : Int64) :
    (x - 8).toUInt64.toUInt32 = x.toUInt64.toUInt32 - (8 : Int64).toUInt64.toUInt32 := by
  rw [Int64.toUInt64_sub]
  exact uint64_sub8_toUInt32 x

private theorem fuel_split1 {C : Nat} (k r : Nat) (hr : C ≤ r) : k + r = (k + (r - C)) + C := by omega

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
private theorem containsCellLoop_aux :
    ∀ (m k : Nat) (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) (rx ry : Int64) (fuel : UInt32),
      fuel.toNat ≤ m →
      ∀ (base : Nat → JvmVal),
        runJvmValFast (k + (m + 1) * 330) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog 3
          (f_Algorithm_FlatHashLifeArena_containsCellLoop_prog.drop 3)
          ⟨3, [],
            setLocal (setLocal (setLocal (setLocal (setLocal base 0 (.arenaRef 0)) 1 (.i32 nodeId))
              2 (.i64 rx.toUInt64)) 4 (.i64 ry.toUInt64)) 6 (.i32 fuel),
            [arena], [], []⟩ =
          some (.i32 (if arena.containsCellLoop nodeId rx ry fuel then 1 else 0)) := by
  intro m
  induction m with
  | zero =>
    intro k arena nodeId rx ry fuel hn base
    have hfz : fuel = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (by change fuel.toBitVec.toNat = 0; change fuel.toNat ≤ 0 at hn; exact Nat.eq_zero_of_le_zero hn))
    rw [show k + (0 + 1) * 330 = k + 330 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
    have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
    (conv => lhs; rw [ite_eq_left (by exact hfzb)])
    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
    flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
    (conv => rhs; rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]; dsimp only; simp only [hfz, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte])
  | succ m ih =>
    intro k arena nodeId rx ry fuel hn base
    rw [show k + (m + 1 + 1) * 330 = (k + (m + 1) * 330) + 330 by omega]
    flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
    by_cases hfz : fuel = 0
    · have hfzb : (fuel == 0) = true := beq_iff_eq.mpr hfz
      (conv => lhs; rw [ite_eq_left (by exact hfzb)])
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
      (conv => rhs; rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]; dsimp only; simp only [hfz, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte])
    · have hfzb : (fuel == 0) = false := beq_false_of_ne hfz
      (conv => lhs; rw [ite_eq_right (by rw [hfzb]; exact Bool.false_ne_true)])
      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
      flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
      by_cases hoob : arena.cellCount ≤ nodeId
      · have hoobb : nodeId ≥ arena.cellCount := hoob
        (conv => lhs; rw [ite_eq_left (by rw [compareUnsigned_sle']; exact decide_eq_true hoob)])
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
        (conv => rhs; rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]; dsimp only; simp [hfz, hoobb])
      · have hoobb : ¬ (nodeId ≥ arena.cellCount) := hoob
        (conv => lhs; rw [ite_eq_right (by rw [compareUnsigned_sle', decide_eq_false hoob]; exact Bool.false_ne_true)])
        (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
        flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
        by_cases hrx0 : rx < 0
        · have hrx0s : ((if rx.toUInt64 == 0 then (0 : UInt32)
              else if rx.toUInt64.toBitVec.slt 0#64 then 4294967295 else 1).toBitVec.slt 0#32) = true :=
            (lcmp_slt_zero_int64 rx 0).mpr hrx0
          (conv => lhs; rw [ite_eq_left (by exact hrx0s)])
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
          (conv => rhs; rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]; dsimp only; simp [hfz, hoobb, hrx0])
        · have hrx0s : ((if rx.toUInt64 == 0 then (0 : UInt32)
              else if rx.toUInt64.toBitVec.slt 0#64 then 4294967295 else 1).toBitVec.slt 0#32) = false :=
            Bool.eq_false_iff.mpr (mt (lcmp_slt_zero_int64 rx 0).mp hrx0)
          (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hrx0s.symm.trans h))])
          (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
          flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
          by_cases hry0 : ry < 0
          · have hry0s : ((if ry.toUInt64 == 0 then (0 : UInt32)
                else if ry.toUInt64.toBitVec.slt 0#64 then 4294967295 else 1).toBitVec.slt 0#32) = true :=
              (lcmp_slt_zero_int64 ry 0).mpr hry0
            (conv => lhs; rw [ite_eq_left (by exact hry0s)])
            (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
            (conv => rhs; rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]; dsimp only; simp [hfz, hoobb, hrx0, hry0])
          · have hry0s : ((if ry.toUInt64 == 0 then (0 : UInt32)
                else if ry.toUInt64.toBitVec.slt 0#64 then 4294967295 else 1).toBitVec.slt 0#32) = false :=
              Bool.eq_false_iff.mpr (mt (lcmp_slt_zero_int64 ry 0).mp hry0)
            (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hry0s.symm.trans h))])
            (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
            flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
            let lvl := arena.cellLevel[nodeId.toNat]!.toUInt32
            let half := Algorithm.pow2Int64 (lvl - 1)
            let east := decide (lvl ≤ 63) && decide (rx ≥ half)
            let south := decide (lvl ≤ 63) && decide (ry ≥ half)
            let rx' := if east = true then rx - half else rx
            let ry' := if south = true then ry - half else ry
            let childId :=
              if south = true then
                if east = true then arena.cellSe[nodeId.toNat]! else arena.cellSw[nodeId.toNat]!
              else if east = true then arena.cellNe[nodeId.toNat]! else arena.cellNw[nodeId.toNat]!
            have hnext : (fuel - 1).toNat ≤ m := by rw [ui32_sub1_toNat hfz]; omega
            have hjoin365 : ∀ km (l26 : UInt32) (l24 l27 : UInt64) (locs : Nat → JvmVal),
                locs 7 = .arenaU64Ref 0 .l4Se → locs 8 = .arenaU64Ref 0 .l4Sw →
                locs 9 = .arenaU64Ref 0 .l4Ne → locs 10 = .arenaU64Ref 0 .l4Nw →
                locs 21 = .i64 8 → locs 23 = .i32 childId →
                locs 24 = .i64 l24 → locs 26 = .i32 l26 → locs 27 = .i64 l27 →
                l24 = ry'.toUInt64 →
                l26 = (if rx' ≥ 8 then 1 else 0) →
                l27 = (if rx' ≥ 8 then rx' - 8 else rx').toUInt64 →
                runJvmValFast (km + 45) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog 365
                  (f_Algorithm_FlatHashLifeArena_containsCellLoop_prog.drop 365)
                  ⟨365, [], locs, [arena], [], []⟩ =
                  some (.i32 (if Algorithm.leafContains
                    (if ry' ≥ 8 then
                       if rx' ≥ 8 then arena.l4Se[childId.toNat]! else arena.l4Sw[childId.toNat]!
                     else if rx' ≥ 8 then arena.l4Ne[childId.toNat]! else arena.l4Nw[childId.toNat]!)
                    (if rx' ≥ 8 then rx' - 8 else rx').toUInt64.toUInt32
                    (if ry' ≥ 8 then ry' - 8 else ry').toUInt64.toUInt32 then 1 else 0)) := by
              intro km l26 l24 l27 locs h7 h8 h9 h10 h21 h23 h24 h26 h27 hl24 hl26 hl27
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
              by_cases hqy8 : ry' ≥ 8
              · have hqy8s : ((if (8 : Int64).toUInt64 == ry'.toUInt64 then (0 : UInt32)
                    else if (8 : Int64).toUInt64.toBitVec.slt ry'.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = true :=
                  (lcmp_sle_zero_int64 8 ry').mpr hqy8
                (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI64, h21, h24, hl24]; exact hqy8s)])
                (conv => lhs; arg 5; simp only [h7, h8, h9, h10, h21, h23, h24, h26, h27, hl24, hl26, hl27])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                by_cases hqx8 : rx' ≥ 8
                · have hqx8l : (!(locs 26).asI32 == 0) = true := by simp [h26, hl26, hqx8]; decide
                  (conv => lhs; rw [ite_eq_left hqx8l])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  (conv => lhs; simp only [h7, h8, h9, h10, h21, h23, h24, h27, hl24, hl27, hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  (conv => lhs; simp only [hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32, int64_sub8_toUInt32])
                  (conv => rhs; simp only [hqy8, hqx8, ↓reduceIte, int64_sub8_toUInt32])
                  try rfl
                · have hqx8l : ¬((!(locs 26).asI32 == 0) = true) := by simp [h26, hl26, hqx8]; decide
                  (conv => lhs; rw [ite_eq_right hqx8l])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  (conv => lhs; simp only [h7, h8, h9, h10, h21, h23, h24, h27, hl24, hl27, hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  (conv => lhs; simp only [hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32])
                  (conv => rhs; simp only [hqy8, hqx8, ↓reduceIte, int64_sub8_toUInt32])
                  try rfl
              · have hqy8s : ((if (8 : Int64).toUInt64 == ry'.toUInt64 then (0 : UInt32)
                    else if (8 : Int64).toUInt64.toBitVec.slt ry'.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = false :=
                  Bool.eq_false_iff.mpr (mt (lcmp_sle_zero_int64 8 ry').mp hqy8)
                (conv => lhs; rw [ite_eq_right (by intro h; simp only [JvmVal.asI64, h21, h24, hl24] at h; exact Bool.false_ne_true (hqy8s.symm.trans h))])
                (conv => lhs; arg 5; simp only [h7, h8, h9, h10, h21, h23, h24, h26, h27, hl24, hl26, hl27])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                by_cases hqx8 : rx' ≥ 8
                · have hqx8l : (!(locs 26).asI32 == 0) = true := by simp [h26, hl26, hqx8]; decide
                  (conv => lhs; rw [ite_eq_left hqx8l])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  (conv => lhs; simp only [h7, h8, h9, h10, h21, h23, h24, h27, hl24, hl27, hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  (conv => lhs; simp only [hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32])
                  (conv => rhs; simp only [hqy8, hqx8, ↓reduceIte])
                  rfl
                · have hqx8l : ¬((!(locs 26).asI32 == 0) = true) := by simp [h26, hl26, hqx8]; decide
                  (conv => lhs; rw [ite_eq_right hqx8l])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  (conv => lhs; simp only [h7, h8, h9, h10, h21, h23, h24, h27, hl24, hl27, hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  (conv => lhs; simp only [hqy8, hqx8, ↓reduceIte, getArenaU64, uint64_sub8_toUInt32])
                  (conv => rhs; simp only [hqy8, hqx8, ↓reduceIte])
                  rfl
            have hjoin293 : ∀ km (locs : Nat → JvmVal),
                locs 0 = .arenaRef 0 → locs 6 = .i32 fuel →
                locs 7 = .arenaU64Ref 0 .l4Se → locs 8 = .arenaU64Ref 0 .l4Sw →
                locs 9 = .arenaU64Ref 0 .l4Ne → locs 10 = .arenaU64Ref 0 .l4Nw →
                locs 31 = .i32 lvl → locs 32 = .i32 arena.l4Count →
                locs 33 = .i32 0 → locs 34 = .i32 1 →
                locs 35 = .i64 rx'.toUInt64 → locs 37 = .i64 ry'.toUInt64 →
                locs 39 = .i32 childId →
                runJvmValFast (km + (m + 1) * 330 + 80) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog 293
                  (f_Algorithm_FlatHashLifeArena_containsCellLoop_prog.drop 293)
                  ⟨293, [], locs, [arena], [], []⟩ =
                  some (.i32 (if (if lvl ≤ 5 then Algorithm.containsLevel4 arena childId rx' ry'
                    else arena.containsCellLoop childId rx' ry' (fuel - 1)) then 1 else 0)) := by
              intro km locs h0 h6 h7 h8 h9 h10 h31 h32 h33 h34 h35 h37 h39
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
              by_cases h5 : lvl ≤ 5
              · (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI32, h31]; rw [compareUnsigned_sle']; exact decide_eq_true h5)])
                (conv => lhs; arg 5; simp only [h0, h6, h7, h8, h9, h10, h31, h32, h33, h34, h35, h37, h39])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                (conv => rhs; rw [Algorithm.containsLevel4.eq_1])
                by_cases hcz : childId = 0
                · have hczb : (childId == 0) = true := beq_iff_eq.mpr hcz
                  (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI32, h39]; exact hczb)])
                  (conv => rhs; simp only [h5, hczb, Bool.true_or, ↓reduceIte])
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  simp only [h33]; rfl
                · have hczb : (childId == 0) = false := beq_false_of_ne hcz
                  (conv => lhs; rw [ite_eq_right (by intro h; simp only [JvmVal.asI32, h39] at h; exact Bool.false_ne_true (hczb.symm.trans h))])
                  (conv => rhs; simp only [h5, hczb, Bool.false_or, ↓reduceIte])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  by_cases hcoob : arena.l4Count ≤ childId
                  · have hcoobs : decide (childId ≥ arena.l4Count) = true := decide_eq_true hcoob
                    (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI32, h32, h39]; rw [compareUnsigned_sle']; exact decide_eq_true hcoob)])
                    (conv => rhs; simp only [hcoobs, ↓reduceIte])
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                    rfl
                  · have hcoobs : decide (childId ≥ arena.l4Count) = false := decide_eq_false hcoob
                    (conv => lhs; rw [ite_eq_right (by simp only [JvmVal.asI32, h32, h39]; rw [compareUnsigned_sle', decide_eq_false hcoob]; exact Bool.false_ne_true)])
                    (conv => rhs; simp only [hcoobs, ↓reduceIte])
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                    by_cases hqx8 : rx' ≥ 8
                    · have hqx8s : ((if (8 : Int64).toUInt64 == rx'.toUInt64 then (0 : UInt32)
                          else if (8 : Int64).toUInt64.toBitVec.slt rx'.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = true :=
                        (lcmp_sle_zero_int64 8 rx').mpr hqx8
                      (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI64, h35]; exact hqx8s)])
                      (conv => rhs; simp only [Bool.false_eq_true, ↓reduceIte])
                      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      flat_step_to 365
                      (conv => lhs; arg 5; simp only [h7, h8, h9, h10, h35, h37, h39])
                      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                      rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 45)]; rotate_left; omega
                      refine hjoin365 _ (1 : UInt32) ry'.toUInt64 (rx'.toUInt64 - 8) _
                        (by simp [setLocal, h7]) (by simp [setLocal, h8])
                        (by simp [setLocal, h9]) (by simp [setLocal, h10])
                        rfl rfl rfl rfl rfl rfl ?_ ?_
                      · simp [hqx8]
                      · simp [hqx8]; rfl
                    · have hqx8s : ((if (8 : Int64).toUInt64 == rx'.toUInt64 then (0 : UInt32)
                          else if (8 : Int64).toUInt64.toBitVec.slt rx'.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = false :=
                        Bool.eq_false_iff.mpr (mt (lcmp_sle_zero_int64 8 rx').mp hqx8)
                      (conv => lhs; rw [ite_eq_right (by intro h; simp only [JvmVal.asI64, h35] at h; exact Bool.false_ne_true (hqx8s.symm.trans h))])
                      (conv => rhs; simp only [Bool.false_eq_true, ↓reduceIte])
                      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      flat_step_to 365
                      (conv => lhs; arg 5; simp only [h7, h8, h9, h10, h35, h37, h39])
                      (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                      (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                      rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 45)]; rotate_left; omega
                      refine hjoin365 _ (0 : UInt32) ry'.toUInt64 rx'.toUInt64 _
                        (by simp [setLocal, h7]) (by simp [setLocal, h8])
                        (by simp [setLocal, h9]) (by simp [setLocal, h10])
                        rfl rfl rfl rfl rfl rfl ?_ ?_
                      · simp [hqx8]
                      · simp [hqx8]
              · (conv => lhs; rw [ite_eq_right (by simp only [JvmVal.asI32, h31]; rw [compareUnsigned_sle', decide_eq_false h5]; exact Bool.false_ne_true)])
                (conv => rhs; simp only [h5, ↓reduceIte])
                (conv => lhs; arg 5; simp only [h0, h6, h7, h8, h9, h10, h31, h32, h33, h34, h35, h37, h39])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                (conv => lhs; arg 5; simp only [h0, h6, h7, h8, h9, h10, h31, h32, h33, h34, h35, h37, h39])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                rw [Nat.add_left_comm km ((m + 1) * 330), Nat.add_comm ((m + 1) * 330)]
                exact ih _ arena childId rx' ry' (fuel - 1) hnext _
            have hjoin224 : ∀ km (l46 l49 : UInt32) (l50 : UInt64) (locs : Nat → JvmVal),
                locs 0 = .arenaRef 0 → locs 1 = .i32 nodeId →
                locs 4 = .i64 ry.toUInt64 → locs 6 = .i32 fuel →
                locs 7 = .arenaU64Ref 0 .l4Se → locs 8 = .arenaU64Ref 0 .l4Sw →
                locs 9 = .arenaU64Ref 0 .l4Ne → locs 10 = .arenaU64Ref 0 .l4Nw →
                locs 31 = .i32 lvl → locs 32 = .i32 arena.l4Count →
                locs 40 = .arenaU32Ref 0 .cellSe → locs 41 = .arenaU32Ref 0 .cellSw →
                locs 42 = .arenaU32Ref 0 .cellNe → locs 43 = .arenaU32Ref 0 .cellNw →
                locs 44 = .i32 0 → locs 45 = .i32 1 →
                locs 46 = .i32 l46 → locs 47 = .i64 half.toUInt64 →
                locs 49 = .i32 l49 → locs 50 = .i64 l50 →
                l46 = (if south then 1 else 0) →
                l49 = (if east then 1 else 0) →
                l50 = rx'.toUInt64 →
                runJvmValFast (km + (m + 1) * 330 + 115) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog 224
                  (f_Algorithm_FlatHashLifeArena_containsCellLoop_prog.drop 224)
                  ⟨224, [], locs, [arena], [], []⟩ =
                  some (.i32 (if (if lvl ≤ 5 then Algorithm.containsLevel4 arena childId rx' ry'
                    else arena.containsCellLoop childId rx' ry' (fuel - 1)) then 1 else 0)) := by
              intro km l46 l49 l50 locs h0 h1 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43 h44 h45 h46 h47 h49 h50
                hl46 hl49 hl50
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
              by_cases hs : south = true
              · (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI32, h46, hl46, hs]; decide)])
                (conv => lhs; arg 5; simp only [h0, h1, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43,
                  h44, h45, h46, h47, h49, h50, hl46, hl49, hl50])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                by_cases he : east = true
                · (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI32, h49, hl49, he]; decide)])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  (conv => lhs; simp only [h40, h41, h42, h43])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_to 293
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 80)]; rotate_left; omega
                  rw [Nat.add_right_comm km ((m + 1) * 330)]
                  refine hjoin293 _ _ h0 h6 h7 h8 h9 h10 h31 h32 h44 h45 (h50.trans (congrArg JvmVal.i64 hl50)) ?_ ?_
                  · simp [setLocal, JvmVal.asI64, h4, h47, ry', hs]
                  · simp [setLocal, JvmVal.asI32, getArenaU32, childId, hs, he, h1]
                · (conv => lhs; rw [ite_eq_right (by simp only [JvmVal.asI32, h49, hl49, he]; decide)])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  (conv => lhs; simp only [h40, h41, h42, h43])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_to 293
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 80)]; rotate_left; omega
                  rw [Nat.add_right_comm km ((m + 1) * 330)]
                  refine hjoin293 _ _ h0 h6 h7 h8 h9 h10 h31 h32 h44 h45 (h50.trans (congrArg JvmVal.i64 hl50)) ?_ ?_
                  · simp [setLocal, JvmVal.asI64, h4, h47, ry', hs]
                  · simp [setLocal, JvmVal.asI32, getArenaU32, childId, hs, he, h1]
              · (conv => lhs; rw [ite_eq_right (by simp only [JvmVal.asI32, h46, hl46, hs]; decide)])
                (conv => lhs; arg 5; simp only [h0, h1, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43,
                  h44, h45, h46, h47, h49, h50, hl46, hl49, hl50])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                by_cases he : east = true
                · (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI32, h49, hl49, he]; decide)])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  (conv => lhs; simp only [h40, h41, h42, h43])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_to 293
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 80)]; rotate_left; omega
                  rw [Nat.add_right_comm km ((m + 1) * 330)]
                  refine hjoin293 _ _ h0 h6 h7 h8 h9 h10 h31 h32 h44 h45 (h50.trans (congrArg JvmVal.i64 hl50)) ?_ ?_
                  · simp [setLocal, h4, ry', hs]
                  · simp [setLocal, JvmVal.asI32, getArenaU32, childId, hs, he, h1]
                · (conv => lhs; rw [ite_eq_right (by simp only [JvmVal.asI32, h49, hl49, he]; decide)])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  (conv => lhs; simp only [h40, h41, h42, h43])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_to 293
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 80)]; rotate_left; omega
                  rw [Nat.add_right_comm km ((m + 1) * 330)]
                  refine hjoin293 _ _ h0 h6 h7 h8 h9 h10 h31 h32 h44 h45 (h50.trans (congrArg JvmVal.i64 hl50)) ?_ ?_
                  · simp [setLocal, h4, ry', hs]
                  · simp [setLocal, JvmVal.asI32, getArenaU32, childId, hs, he, h1]
            have hjoin193 : ∀ km (l56 l57 : UInt32) (locs : Nat → JvmVal),
                locs 0 = .arenaRef 0 → locs 1 = .i32 nodeId →
                locs 2 = .i64 rx.toUInt64 → locs 4 = .i64 ry.toUInt64 → locs 6 = .i32 fuel →
                locs 7 = .arenaU64Ref 0 .l4Se → locs 8 = .arenaU64Ref 0 .l4Sw →
                locs 9 = .arenaU64Ref 0 .l4Ne → locs 10 = .arenaU64Ref 0 .l4Nw →
                locs 31 = .i32 lvl → locs 32 = .i32 arena.l4Count →
                locs 40 = .arenaU32Ref 0 .cellSe → locs 41 = .arenaU32Ref 0 .cellSw →
                locs 42 = .arenaU32Ref 0 .cellNe → locs 43 = .arenaU32Ref 0 .cellNw →
                locs 52 = .i32 1 → locs 53 = .i32 0 → locs 54 = .i64 half.toUInt64 →
                locs 56 = .i32 l56 → locs 57 = .i32 l57 →
                l56 = (if east then 1 else 0) →
                l57 = (if south then 1 else 0) →
                runJvmValFast (km + (m + 1) * 330 + 135) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog 193
                  (f_Algorithm_FlatHashLifeArena_containsCellLoop_prog.drop 193)
                  ⟨193, [], locs, [arena], [], []⟩ =
                  some (.i32 (if (if lvl ≤ 5 then Algorithm.containsLevel4 arena childId rx' ry'
                    else arena.containsCellLoop childId rx' ry' (fuel - 1)) then 1 else 0)) := by
              intro km l56 l57 locs h0 h1 h2 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43
                h52 h53 h54 h56 h57 hl56 hl57
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
              by_cases he : east = true
              · (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI32, h56, hl56, he]; decide)])
                (conv => lhs; arg 5; simp only [h0, h1, h2, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43,
                  h52, h53, h54, h56, h57, hl56, hl57])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_to 224
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 115)]; rotate_left; omega
                rw [Nat.add_right_comm km ((m + 1) * 330)]
                refine hjoin224 _ l57 (1 : UInt32) (rx.toUInt64 - half.toUInt64) _
                  h0 h1 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43 h53 h52 h57 h54 rfl
                  (by simp [setLocal, JvmVal.asI64, h2, h54]) hl57 (by simp [he]) (by simp [rx', he])
              · (conv => lhs; rw [ite_eq_right (by simp only [JvmVal.asI32, h56, hl56, he]; decide)])
                (conv => lhs; arg 5; simp only [h0, h1, h2, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43,
                  h52, h53, h54, h56, h57, hl56, hl57])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_to 224
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 115)]; rotate_left; omega
                rw [Nat.add_right_comm km ((m + 1) * 330)]
                refine hjoin224 _ l57 (0 : UInt32) rx.toUInt64 _
                  h0 h1 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43 h53 h52 h57 h54 rfl
                  h2 hl57 (by simp [he]) (by simp [rx', he])
            have hjoin143 : ∀ km (locs : Nat → JvmVal),
                locs 0 = .arenaRef 0 → locs 1 = .i32 nodeId →
                locs 2 = .i64 rx.toUInt64 → locs 4 = .i64 ry.toUInt64 → locs 6 = .i32 fuel →
                locs 7 = .arenaU64Ref 0 .l4Se → locs 8 = .arenaU64Ref 0 .l4Sw →
                locs 9 = .arenaU64Ref 0 .l4Ne → locs 10 = .arenaU64Ref 0 .l4Nw →
                locs 31 = .i32 lvl → locs 32 = .i32 arena.l4Count →
                locs 40 = .arenaU32Ref 0 .cellSe → locs 41 = .arenaU32Ref 0 .cellSw →
                locs 42 = .arenaU32Ref 0 .cellNe → locs 43 = .arenaU32Ref 0 .cellNw →
                locs 58 = .i32 0 →
                (lvl < 63 → ¬ (rx ≥ Algorithm.pow2Int64 lvl) ∧ ¬ (ry ≥ Algorithm.pow2Int64 lvl)) →
                runJvmValFast (km + (m + 1) * 330 + 180) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog 143
                  (f_Algorithm_FlatHashLifeArena_containsCellLoop_prog.drop 143)
                  ⟨143, [], locs, [arena], [], []⟩ =
                  some (.i32 (if arena.containsCellLoop nodeId rx ry fuel then 1 else 0)) := by
              intro km locs h0 h1 h2 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43 h58 hbounds
              have hbnd' : (decide (lvl < 63) && (decide (rx ≥ Algorithm.pow2Int64 lvl) || decide (ry ≥ Algorithm.pow2Int64 lvl))) = false := by
                by_cases h63lt : lvl < 63
                · have ⟨hx, hy⟩ := hbounds h63lt
                  simp [lvl, hx, hy]
                · simp [lvl, h63lt]
              dsimp only [lvl] at hbnd'
              conv =>
                rhs
                rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]
                dsimp only
                simp only [hfz, ↓reduceDIte, hoobb, hrx0, hry0, decide_false, Bool.false_or, hbnd', Bool.false_eq_true, ↓reduceIte]
              change _ = some (JvmVal.i32 (if (if lvl ≤ 5 then Algorithm.containsLevel4 arena childId rx' ry'
                else arena.containsCellLoop childId rx' ry' (fuel - 1)) then 1 else 0))
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
              by_cases h63le : lvl ≤ 63
              · (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI32, h31]; rw [compareUnsigned_sle']; exact decide_eq_true h63le)])
                (conv => lhs; arg 5; simp only [h0, h1, h2, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43, h58])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                have hhalf : ((1 : UInt64) <<< ((lvl - 1) &&& 63).toUInt64) = half.toUInt64 := by
                  simp only [half, Algorithm.pow2Int64.eq_1, lshl_63_mask]; rfl
                rw [hhalf]
                by_cases hrx : rx ≥ half
                · have hrxs : ((0#32).slt (if half.toUInt64 == rx.toUInt64 then (0 : UInt32)
                      else if half.toUInt64.toBitVec.slt rx.toUInt64.toBitVec then 4294967295 else 1).toBitVec) = false :=
                    Bool.eq_false_iff.mpr (mt (lcmp_sgt_zero_int64 half rx).mp (Classical.not_not.mpr hrx))
                  (conv => lhs; rw [ite_eq_right (by intro h; simp only [JvmVal.asI64, h2] at h; exact Bool.false_ne_true (hrxs.symm.trans h))])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  by_cases hry : ry ≥ half
                  · have hrys : ((0#32).slt (if half.toUInt64 == ry.toUInt64 then (0 : UInt32)
                        else if half.toUInt64.toBitVec.slt ry.toUInt64.toBitVec then 4294967295 else 1).toBitVec) = false :=
                      Bool.eq_false_iff.mpr (mt (lcmp_sgt_zero_int64 half ry).mp (Classical.not_not.mpr hry))
                    (conv => lhs; rw [ite_eq_right (by intro h; simp only [JvmVal.asI64, h4] at h; exact Bool.false_ne_true (hrys.symm.trans h))])
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_to 193
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 135)]; rotate_left; omega
                    rw [Nat.add_right_comm km ((m + 1) * 330)]
                    refine hjoin193 _ (1 : UInt32) (1 : UInt32) _ h0 h1 h2 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43 ?_ ?_ ?_ ?_ ?_ ?_ ?_
                    iterate 5 (first | rfl | exact h58)
                    · simp [east, h63le, hrx]
                    · simp [south, h63le, hry]
                  · have hrys : ((0#32).slt (if half.toUInt64 == ry.toUInt64 then (0 : UInt32)
                        else if half.toUInt64.toBitVec.slt ry.toUInt64.toBitVec then 4294967295 else 1).toBitVec) = true :=
                      (lcmp_sgt_zero_int64 half ry).mpr hry
                    (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI64, h4]; exact hrys)])
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_to 193
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 135)]; rotate_left; omega
                    rw [Nat.add_right_comm km ((m + 1) * 330)]
                    refine hjoin193 _ (1 : UInt32) (0 : UInt32) _ h0 h1 h2 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43 ?_ ?_ ?_ ?_ ?_ ?_ ?_
                    iterate 5 (first | rfl | exact h58)
                    · simp [east, h63le, hrx]
                    · simp [south, h63le, hry]
                · have hrxs : ((0#32).slt (if half.toUInt64 == rx.toUInt64 then (0 : UInt32)
                      else if half.toUInt64.toBitVec.slt rx.toUInt64.toBitVec then 4294967295 else 1).toBitVec) = true :=
                    (lcmp_sgt_zero_int64 half rx).mpr hrx
                  (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI64, h2]; exact hrxs)])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  by_cases hry : ry ≥ half
                  · have hrys : ((0#32).slt (if half.toUInt64 == ry.toUInt64 then (0 : UInt32)
                        else if half.toUInt64.toBitVec.slt ry.toUInt64.toBitVec then 4294967295 else 1).toBitVec) = false :=
                      Bool.eq_false_iff.mpr (mt (lcmp_sgt_zero_int64 half ry).mp (Classical.not_not.mpr hry))
                    (conv => lhs; rw [ite_eq_right (by intro h; simp only [JvmVal.asI64, h4] at h; exact Bool.false_ne_true (hrys.symm.trans h))])
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_to 193
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 135)]; rotate_left; omega
                    rw [Nat.add_right_comm km ((m + 1) * 330)]
                    refine hjoin193 _ (0 : UInt32) (1 : UInt32) _ h0 h1 h2 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43 ?_ ?_ ?_ ?_ ?_ ?_ ?_
                    iterate 5 (first | rfl | exact h58)
                    · simp [east, h63le, hrx]
                    · simp [south, h63le, hry]
                  · have hrys : ((0#32).slt (if half.toUInt64 == ry.toUInt64 then (0 : UInt32)
                        else if half.toUInt64.toBitVec.slt ry.toUInt64.toBitVec then 4294967295 else 1).toBitVec) = true :=
                      (lcmp_sgt_zero_int64 half ry).mpr hry
                    (conv => lhs; rw [ite_eq_left (by simp only [JvmVal.asI64, h4]; exact hrys)])
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    flat_step_to 193
                    (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                    (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                    rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 135)]; rotate_left; omega
                    rw [Nat.add_right_comm km ((m + 1) * 330)]
                    refine hjoin193 _ (0 : UInt32) (0 : UInt32) _ h0 h1 h2 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43 ?_ ?_ ?_ ?_ ?_ ?_ ?_
                    iterate 5 (first | rfl | exact h58)
                    · simp [east, h63le, hrx]
                    · simp [south, h63le, hry]
              · (conv => lhs; rw [ite_eq_right (by simp only [JvmVal.asI32, h31]; rw [compareUnsigned_sle', decide_eq_false h63le]; exact Bool.false_ne_true)])
                (conv => lhs; arg 5; simp only [h0, h1, h2, h4, h6, h7, h8, h9, h10, h31, h32, h40, h41, h42, h43, h58])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_to 193
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                rw [← Nat.add_assoc km ((m + 1) * 330), fuel_split1 (C := 135)]; rotate_left; omega
                rw [Nat.add_right_comm km ((m + 1) * 330)]
                refine hjoin193 _ (0 : UInt32) (0 : UInt32) _ h0 h1 h2 h4 h6 h7 h8 h9 h10 h31 h32 h40 h41 h42 h43
                  rfl h58 (congrArg JvmVal.i64 (by simp only [half, Algorithm.pow2Int64.eq_1, lshl_63_mask]; rfl))
                  h58 h58 ?_ ?_
                · simp [east, h63le]
                · simp [south, h63le]
            by_cases h63lt : lvl < 63
            · (conv => lhs; rw [ite_eq_left (by simp only [getArenaU8, u8_sext_band255]; rw [compareUnsigned_slt']; exact decide_eq_true h63lt)])
              (conv => lhs; arg 5; simp only [getArenaU8, u8_sext_band255])
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
              have hsize : ((1 : UInt64) <<< (lvl &&& 63).toUInt64) = (Algorithm.pow2Int64 lvl).toUInt64 := by
                simp only [Algorithm.pow2Int64.eq_1, lshl_63_mask]; rfl
              rw [hsize]
              by_cases hrxs : rx ≥ Algorithm.pow2Int64 lvl
              · have hrxss : ((if (Algorithm.pow2Int64 lvl).toUInt64 == rx.toUInt64 then (0 : UInt32)
                    else if (Algorithm.pow2Int64 lvl).toUInt64.toBitVec.slt rx.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = true :=
                  (lcmp_sle_zero_int64 _ rx).mpr hrxs
                (conv => lhs; rw [ite_eq_left (by exact hrxss)])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                conv =>
                  rhs
                  rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]
                  dsimp only
                  simp [hfz, hoobb, hrx0, lvl, h63lt, hrxs]
              · have hrxss : ((if (Algorithm.pow2Int64 lvl).toUInt64 == rx.toUInt64 then (0 : UInt32)
                    else if (Algorithm.pow2Int64 lvl).toUInt64.toBitVec.slt rx.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = false :=
                  Bool.eq_false_iff.mpr (mt (lcmp_sle_zero_int64 _ rx).mp hrxs)
                (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hrxss.symm.trans h))])
                (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                by_cases hrys : ry ≥ Algorithm.pow2Int64 lvl
                · have hryss : ((if (Algorithm.pow2Int64 lvl).toUInt64 == ry.toUInt64 then (0 : UInt32)
                      else if (Algorithm.pow2Int64 lvl).toUInt64.toBitVec.slt ry.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = true :=
                    (lcmp_sle_zero_int64 _ ry).mpr hrys
                  (conv => lhs; rw [ite_eq_left (by exact hryss)])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_blk f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
                  conv =>
                    rhs
                    rw [Algorithm.FlatHashLifeArena.containsCellLoop.eq_1]
                    dsimp only
                    simp [hfz, hoobb, hrx0, hry0, lvl, h63lt, hrys]
                · have hryss : ((if (Algorithm.pow2Int64 lvl).toUInt64 == ry.toUInt64 then (0 : UInt32)
                      else if (Algorithm.pow2Int64 lvl).toUInt64.toBitVec.slt ry.toUInt64.toBitVec then 4294967295 else 1).toBitVec.sle 0#32) = false :=
                    Bool.eq_false_iff.mpr (mt (lcmp_sle_zero_int64 _ ry).mp hrys)
                  (conv => lhs; rw [ite_eq_right (by intro h; exact Bool.false_ne_true (hryss.symm.trans h))])
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  flat_step_to 143
                  (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
                  (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
                  rw [← Nat.add_assoc k ((m + 1) * 330), fuel_split1 (C := 180)]; rotate_left; omega
                  rw [Nat.add_right_comm k ((m + 1) * 330)]
                  refine hjoin143 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun _ => ⟨hrxs, hrys⟩)
                  all_goals try rfl
            · (conv => lhs; rw [ite_eq_right (by simp only [getArenaU8, u8_sext_band255]; rw [compareUnsigned_slt', decide_eq_false h63lt]; exact Bool.false_ne_true)])
              (conv => lhs; arg 5; simp only [getArenaU8, u8_sext_band255])
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              flat_step_to 143
              (conv => lhs; norm_jvm_locals; norm_flat_run; jvm_whnf_run_args)
              (conv => lhs; arg 1; try simp only [Nat.succ_eq_add_one]; try simp only [nat_add_eq]; simp only [Nat.add_assoc])
              rw [← Nat.add_assoc k ((m + 1) * 330), fuel_split1 (C := 180)]; rotate_left; omega
              rw [Nat.add_right_comm k ((m + 1) * 330)]
              refine hjoin143 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun h => absurd h h63lt)
              all_goals try rfl

theorem containsCellLoop_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) (rx ry : Int64) (fuel : UInt32) :
    runJvm ((fuel.toNat + 1) * 330 + 3) f_Algorithm_FlatHashLifeArena_containsCellLoop_prog
      (initJvmState [(0, .arenaRef 0), (1, .i32 nodeId), (2, .i64 rx.toUInt64), (4, .i64 ry.toUInt64),
        (6, .i32 fuel)] [arena]) =
      some (.i32 (if arena.containsCellLoop nodeId rx ry fuel then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_one_chunk
  rw [runJvmValFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  rw [← Nat.zero_add ((fuel.toNat + 1) * 330)]
  exact containsCellLoop_aux fuel.toNat 0 arena nodeId rx ry fuel (Nat.le_refl _) _

end Batch3

end Algorithm.JvmVerification

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
