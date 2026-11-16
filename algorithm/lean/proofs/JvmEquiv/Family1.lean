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

import JvmBytecode
import proofs.JvmEquiv.Infra
import proofs.JvmEquiv.FlatInfra

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

section Family1

def HasNextGen4x4Lut (jh : Jvm.JvmHeap AlgExt) : Prop :=
  ∃ lutAddr arr,
    jh.getStatic? "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "NEXT_GEN_4X4_LUT" = some (.heapRef lutAddr) ∧
    jh.get? lutAddr = some (.byteArray arr) ∧
    arr.size = 65536 ∧
    ∀ (k : Nat), k < 65536 →
      arr[k]! = (Algorithm.computeNextGen4x4BitwiseUInt (UInt32.ofNat k)).toUInt8

def emptyNodesArray : Array JvmVal :=
  Array.ofFn (n := 33) fun i => .ext (.mc (Algorithm.emptyNode i.val))

def HasEmptyNodes (jh : Jvm.JvmHeap AlgExt) : Prop :=
  ∃ nodesAddr,
    jh.getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_LEVEL_4" = some (.ext (.mc Algorithm.emptyLevel4)) ∧
    jh.getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_NODES" = some (.heapRef nodesAddr) ∧
    jh.get? nodesAddr = some (.objArray "com/alexvanyo/composelife/model/MacroCell" emptyNodesArray)

private theorem lut_byte_signExtend_and15 (x : UInt32) :
    UInt32.ofBitVec (x.toUInt8.toBitVec.signExtend 32) &&& (15 : UInt32) = x &&& (15 : UInt32) := by
  apply UInt32.toBitVec_inj.mp
  ext i hi
  simp only [UInt32.toBitVec_and, BitVec.getElem_and, BitVec.getElem_signExtend]
  by_cases h4 : i < 4
  · simp [show i < 8 by omega, BitVec.getLsbD_eq_getElem hi]
  · have h15 : (15#32 : BitVec 32)[i] = false := by
      have hpow : 15 < 2 ^ i := by
        have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 4 ≤ i)
        omega
      simp [BitVec.getElem_eq_testBit_toNat, Nat.testBit_lt_two_pow hpow]
    simp [h15]

private theorem emptySubnode_eq_emptyNode :
    ∀ {m : Algorithm.MacroCell} {d : Nat}, Algorithm.WFd m d →
      Algorithm.emptySubnode m = Algorithm.emptyNode d
  | .level4Node .., d, h => by
    rw [Algorithm.WFd_level4Node_iff] at h
    subst h
    rfl
  | .cellNode _ nw _ _ _, d, h => by
    rw [Algorithm.WFd_cellNode_iff] at h
    rcases h with ⟨hd, hnw, _⟩
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 5 := ⟨d - 5, by omega⟩
    have ih := emptySubnode_eq_emptyNode hnw
    simp [Algorithm.emptySubnode, Algorithm.emptyNode, ih]

private theorem u32_and_one_ite (x : UInt32) :
    (if (x &&& 1 == (1 : UInt32)) then (1 : UInt32) else 0) = x &&& 1 := by
  have hlt : (x &&& 1).toNat < 2 := by
    rw [UInt32.toNat_and]
    exact Nat.and_lt_two_pow x.toNat (n := 1) (by decide)
  have hcases : (x &&& 1).toNat = 0 ∨ (x &&& 1).toNat = 1 := by omega
  rcases hcases with h0 | h1
  · have hx : x &&& 1 = 0 := UInt32.toNat.inj h0
    simp [hx]
  · have hx : x &&& 1 = 1 := UInt32.toNat.inj h1
    simp [hx]

private theorem bitRuleUInt_ite (c n : UInt32) :
    (if n == 3 then (1 : UInt32) else if n == 2 then (if (c &&& 1 == 1) then 1 else 0) else 0) =
      Algorithm.bitRuleUInt n (c &&& 1) := by
  rw [u32_and_one_ite]
  have hlt : (c &&& 1).toNat < 2 := by
    rw [UInt32.toNat_and]
    exact Nat.and_lt_two_pow c.toNat (n := 1) (by decide)
  have hcases : (c &&& 1).toNat = 0 ∨ (c &&& 1).toNat = 1 := by omega
  unfold Algorithm.bitRuleUInt
  rcases hcases with h0 | h1
  · have hc : c &&& 1 = 0 := UInt32.toNat.inj h0
    by_cases h3 : n = 3 <;> by_cases h2 : n = 2 <;> simp [hc, h3, h2]
  · have hc : c &&& 1 = 1 := UInt32.toNat.inj h1
    by_cases h3 : n = 3 <;> by_cases h2 : n = 2 <;> simp [hc, h3, h2]

theorem getNEXT_GEN_4X4_LUT_equiv (jh : Jvm.JvmHeap AlgExt) (lutAddr : Nat)
    (hlut : jh.getStatic? "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "NEXT_GEN_4X4_LUT" = some (.heapRef lutAddr)) :
    runJvm 10 getNEXT_GEN_4X4_LUT_prog
      (Jvm.initJvmState [] (.i32 0) ⟨[], [], []⟩ jh) = some (.heapRef lutAddr) := by
  apply runJvm_of_runJvmValFast0 10 _ _ _ rfl
  rw [show (10 : Nat) = 9 + 1 from rfl]
  dsimp only [getNEXT_GEN_4X4_LUT_prog, Jvm.initJvmState]
  rw [runJvmValFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  dsimp only [stepInstr, Jvm.stepInstr]
  rw [hlut]
  rfl

theorem getEMPTY_LEVEL_4_equiv (jh : Jvm.JvmHeap AlgExt)
    (hl4 : jh.getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_LEVEL_4" = some (.ext (.mc Algorithm.emptyLevel4))) :
    runJvm 10 getEMPTY_LEVEL_4_prog
      (Jvm.initJvmState [] (.i32 0) ⟨[], [], []⟩ jh) = some (.ext (.mc Algorithm.emptyLevel4)) := by
  apply runJvm_of_runJvmValFast0 10 _ _ _ rfl
  rw [show (10 : Nat) = 9 + 1 from rfl]
  dsimp only [getEMPTY_LEVEL_4_prog, Jvm.initJvmState]
  rw [runJvmValFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  dsimp only [stepInstr, Jvm.stepInstr]
  rw [hl4]
  rfl

theorem getEMPTY_NODES_equiv (jh : Jvm.JvmHeap AlgExt) (nodesAddr : Nat)
    (hnodes : jh.getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_NODES" = some (.heapRef nodesAddr)) :
    runJvm 10 getEMPTY_NODES_prog
      (Jvm.initJvmState [] (.i32 0) ⟨[], [], []⟩ jh) = some (.heapRef nodesAddr) := by
  apply runJvm_of_runJvmValFast0 10 _ _ _ rfl
  rw [show (10 : Nat) = 9 + 1 from rfl]
  dsimp only [getEMPTY_NODES_prog, Jvm.initJvmState]
  rw [runJvmValFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  dsimp only [stepInstr, Jvm.stepInstr]
  rw [hnodes]
  rfl

private theorem u32_and_65535_lt (w : UInt32) :
    (w &&& (65535 : UInt32)).toNat < 65536 := by
  rw [UInt32.toNat_and, show (65535 : UInt32).toNat = 2 ^ 16 - 1 from rfl]
  exact Nat.and_lt_two_pow w.toNat (n := 16) (by decide)

private theorem u32_slt_zero_of_lt {x : UInt32} (hx : x.toNat < 65536) :
    x.toBitVec.slt 0#32 = false := by
  simp [BitVec.slt, BitVec.toInt]
  omega

theorem exportComputeNextGen4x4UInt_equiv (w : UInt32) (jh : Jvm.JvmHeap AlgExt)
    (hlut : HasNextGen4x4Lut jh) :
    runJvm 30 f_Algorithm_exportComputeNextGen4x4UInt_prog
      (Jvm.initJvmState [(0, .i32 w)] (.i32 0) ⟨[], [], []⟩ jh) =
      some (.i32 (Algorithm.computeNextGen4x4UInt w)) := by
  rcases hlut with ⟨lutAddr, arr, hstat, harr, hsz, htbl⟩
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  flat_step_blk f_Algorithm_exportComputeNextGen4x4UInt_prog
  rw [runJvmValFast_invokestatic_step (stepStatic_getNextGen4x4Lut hstat)]
  flat_step_blk f_Algorithm_exportComputeNextGen4x4UInt_prog
  have hmask := u32_and_65535_lt w
  have hslt := u32_slt_zero_of_lt hmask
  rw [runJvmValFast_baload (elems := arr) harr hslt (by omega)]
  flat_step_blk f_Algorithm_exportComputeNextGen4x4UInt_prog
  congr 2
  have heq := htbl (w &&& 65535).toNat hmask
  have hpos : arr[(w &&& 65535).toNat]! = arr[(w &&& 65535).toNat]'(by omega) :=
    getElem!_pos arr _ (by omega)
  rw [hpos] at heq
  have hget : arr[(w &&& 65535).toNat] =
      (Algorithm.computeNextGen4x4BitwiseUInt (w &&& 65535)).toUInt8 := by
    simpa [UInt32.ofNat_toNat] using heq
  rw [hget, lut_byte_signExtend_and15]
  exact (Algorithm.computeNextGen4x4UInt_eq_table w).symm

theorem f1_nat_add_eq_add (a b : Nat) : Nat.add a b = a + b := rfl

private theorem runJvmValFast_split_fuel (m : Nat) {k : Nat}
    (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState)
    (hk : m ≤ k) :
    runJvmValFast k prog pc instrs st = runJvmValFast ((k - m) + m) prog pc instrs st := by
  rw [Nat.sub_add_cancel hk]

private theorem runJvmResFast_split_fuel (m : Nat) {k : Nat}
    (prog : List JvmInstr) (pc : Nat) (instrs : List JvmInstr) (st : JvmState)
    (hk : m ≤ k) :
    runJvmResFast k prog pc instrs st = runJvmResFast ((k - m) + m) prog pc instrs st := by
  rw [Nat.sub_add_cancel hk]

open Lean Elab Tactic in
elab "f1_split_val_fuel " n:term : tactic => do
  evalTactic (← `(tactic| rw [runJvmValFast_split_fuel $n]))
  let g1 :: g2 :: rest ← getGoals | throwError "f1_split_val_fuel: expected fuel side goal"
  setGoals [g2]
  evalTactic (← `(tactic| (try simp only [f1_nat_add_eq_add]); omega))
  let rem ← getGoals
  unless rem.isEmpty do throwError "f1_split_val_fuel: omega failed"
  setGoals (g1 :: rest)

open Lean Elab Tactic in
elab "f1_split_res_fuel " n:term : tactic => do
  evalTactic (← `(tactic| rw [runJvmResFast_split_fuel $n]))
  let g1 :: g2 :: rest ← getGoals | throwError "f1_split_res_fuel: expected fuel side goal"
  setGoals [g2]
  evalTactic (← `(tactic| (try simp only [f1_nat_add_eq_add]); omega))
  let rem ← getGoals
  unless rem.isEmpty do throwError "f1_split_res_fuel: omega failed"
  setGoals (g1 :: rest)

private theorem evalResBranchInstrCons_if_icmpge (f1 : Nat) (prog : List JvmInstr) (pc target : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (b a : UInt32) (s : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes) :
    evalResBranchInstrCons f1 prog pc (.if_icmpge target) rest ⟨pc0, .i32 b :: .i32 a :: s, locs, jh, ⟨ar, u64, asc⟩⟩ =
      if b.toBitVec.sle a.toBitVec then
        runJvmResFast f1 prog target (prog.drop target) ⟨target, s, locs, jh, ⟨ar, u64, asc⟩⟩
      else runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, s, locs, jh, ⟨ar, u64, asc⟩⟩ :=
  Jvm.evalResBranchInstrCons_if_icmpge algHooks f1 prog pc target rest pc0 b a s locs jh ⟨ar, u64, asc⟩

private theorem emptyNodesArray_getElem (d : Nat) (hd : d < emptyNodesArray.size) :
    emptyNodesArray[d]'hd = .ext (.mc (Algorithm.emptyNode d)) := by
  simp only [emptyNodesArray, Array.getElem_ofFn]

private theorem emptyNodesArray_toList_get (d : Nat) (hd : d < emptyNodesArray.toList.length) :
    emptyNodesArray.toList.get ⟨d, hd⟩ = .ext (.mc (Algorithm.emptyNode d)) := by
  rw [List.get_eq_getElem, Array.getElem_toList, emptyNodesArray_getElem]

private theorem runJvmValFast_baload_and65535 {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {x : UInt32} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {h : AlgHeap}
    {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) (hsz : elems.size = 65536) :
    runJvmValFast (f + 1) prog pc (.baload :: rest)
        ⟨pc0, .i32 (x &&& 65535) :: .heapRef addr :: stkRest, locs, jh, h⟩ =
      runJvmValFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofBitVec (BitVec.signExtend 32
          (elems[(x &&& 65535).toNat]'(Nat.lt_of_lt_of_eq (u32_and_65535_lt x) hsz.symm)).toBitVec)) ::
          stkRest, locs, jh, h⟩ :=
  runJvmValFast_baload hget (u32_slt_zero_of_lt (u32_and_65535_lt x))
    (Nat.lt_of_lt_of_eq (u32_and_65535_lt x) hsz.symm)

theorem emptySubnode_equiv (m : Algorithm.MacroCell) {d : Nat} (hm : Algorithm.WFd m d) (hd : d ≤ 32)
    (jh : Jvm.JvmHeap AlgExt) (hn : HasEmptyNodes jh) :
    runJvm 160 f_Algorithm_emptySubnode_prog
      (Jvm.initJvmState [(0, .ext (.mc m))] (.i32 0) ⟨[], [], []⟩ jh) =
      some (.ext (.mc (Algorithm.emptySubnode m))) := by
  rcases hn with ⟨nodesAddr, _he4, hnodes, hobj⟩
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  f1_split_val_fuel 120
  flat_step_blk f_Algorithm_emptySubnode_prog
  f1_split_val_fuel 1
  rw [runJvmValFast_invokestatic_step (stepStatic_getEmptyNodes hnodes)]
  f1_split_val_fuel 120
  flat_step_blk f_Algorithm_emptySubnode_prog
  f1_split_val_fuel 1
  rw [runJvmValFast_invokevirtual_step rfl]
  f1_split_val_fuel 120
  flat_step_blk f_Algorithm_emptySubnode_prog
  have hd4 := Algorithm.WFd_ge_four hm
  have hlev := Algorithm.WFd_level_toNat hm (by omega)
  have hci : coerceInI32 m.level 0 32 = m.level :=
    coerceInI32_of_le m.level 0 32 (Nat.zero_le _) (by simp only [UInt32.reduceToNat]; omega) (by decide)
  rw [hci]
  have hslt : m.level.toBitVec.slt 0#32 = false := by
    simp [BitVec.slt, BitVec.toInt]; omega
  have hlen : m.level.toNat < emptyNodesArray.size := by
    simp [emptyNodesArray]; omega
  f1_split_val_fuel 1
  rw [runJvmValFast_aaload (elems := emptyNodesArray) hobj hslt hlen]
  f1_split_val_fuel 120
  flat_step_blk f_Algorithm_emptySubnode_prog
  rw [emptyNodesArray_toList_get _ hlen, hlev, emptySubnode_eq_emptyNode hm]

theorem expandCentered_equiv (m : Algorithm.MacroCell) {d : Nat} (hm : Algorithm.WFd m d) (hd : d ≤ 33)
    (jh : Jvm.JvmHeap AlgExt) (hn : HasEmptyNodes jh) :
    runJvm 400 f_Algorithm_expandCentered_prog
      (Jvm.initJvmState [(0, .ext (.mc m))] (.i32 0) ⟨[], [], []⟩ jh) =
      some (.ext (.mc (Algorithm.expandCentered m))) := by
  rcases hn with ⟨nodesAddr, he4, hnodes, hobj⟩
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  cases m with
  | level4Node _ nw ne sw se =>
    f1_split_val_fuel 120
    flat_step_blk f_Algorithm_expandCentered_prog
    f1_split_val_fuel 120
    flat_step_blk f_Algorithm_expandCentered_prog
    repeat' (
      first
      | (f1_split_val_fuel 1;
         rw [runJvmValFast_invokestatic_step (stepStatic_getEmptyLevel4 he4)];
         f1_split_val_fuel 120;
         flat_step_blk f_Algorithm_expandCentered_prog)
      | (f1_split_val_fuel 1;
         rw [runJvmValFast_invokevirtual_step rfl];
         f1_split_val_fuel 120;
         flat_step_blk f_Algorithm_expandCentered_prog))
    rfl
  | cellNode _ nw ne sw se =>
    rw [Algorithm.WFd_cellNode_iff] at hm
    rcases hm with ⟨hd5, hnw, _⟩
    f1_split_val_fuel 120
    flat_step_blk f_Algorithm_expandCentered_prog
    f1_split_val_fuel 120
    flat_step_blk f_Algorithm_expandCentered_prog
    f1_split_val_fuel 120
    flat_step_blk f_Algorithm_expandCentered_prog
    repeat' (
      first
      | (f1_split_val_fuel 1;
         rw [runJvmValFast_invokestatic_step (stepStatic_getEmptyNodes hnodes)];
         f1_split_val_fuel 120;
         flat_step_blk f_Algorithm_expandCentered_prog)
      | (f1_split_val_fuel 1;
         rw [runJvmValFast_invokevirtual_step rfl];
         f1_split_val_fuel 120;
         flat_step_blk f_Algorithm_expandCentered_prog))
    have hnw4 := Algorithm.WFd_ge_four hnw
    have hlev := Algorithm.WFd_level_toNat hnw (by omega)
    have hci : coerceInI32 nw.level 0 32 = nw.level :=
      coerceInI32_of_le nw.level 0 32 (Nat.zero_le _) (by simp only [UInt32.reduceToNat]; omega) (by decide)
    rw [hci]
    have hslt : nw.level.toBitVec.slt 0#32 = false := by
      simp [BitVec.slt, BitVec.toInt]; omega
    have hlen : nw.level.toNat < emptyNodesArray.size := by
      simp [emptyNodesArray]; omega
    f1_split_val_fuel 1
    rw [runJvmValFast_aaload (elems := emptyNodesArray) hobj hslt hlen]
    rw [show emptyNodesArray[nw.level.toNat] = .ext (.mc (Algorithm.emptyNode nw.level.toNat)) by
      simp [emptyNodesArray], hlev]
    f1_split_val_fuel 120
    flat_step_blk f_Algorithm_expandCentered_prog
    simp only [Algorithm.expandCentered, emptySubnode_eq_emptyNode hnw]

private theorem clinit_alg_loop :
    ∀ (m k : Nat) (i : UInt32) (arrAddr : Nat) (arr : Array UInt8)
      (jh : Jvm.JvmHeap AlgExt) (locs : Nat → JvmVal),
      65536 - i.toNat ≤ m →
      i.toNat ≤ 65536 →
      jh.get? arrAddr = some (.byteArray arr) →
      arr.size = 65536 →
      (∀ (j : Nat), j < i.toNat → arr[j]! = (Algorithm.computeNextGen4x4BitwiseUInt (UInt32.ofNat j)).toUInt8) →
      jh.getStatic? "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "NEXT_GEN_4X4_LUT" = none →
      locs 0 = .i32 i →
      locs 1 = .heapRef arrAddr →
      ∃ st', runJvmResFast (k + 200 + m * 14) clinit_AlgorithmLeanKt_prog 5
          (clinit_AlgorithmLeanKt_prog.drop 5) ⟨5, [], locs, jh, ⟨[], [], []⟩⟩ = some (.unit, st') ∧
        HasNextGen4x4Lut st'.jvmHeap := by
  intro m
  induction m with
  | zero =>
    intro k i arrAddr arr jh locs hm hi hget hsz htbl hstat hl0 hl1
    have hi_eq : i.toNat = 65536 := by omega
    have hge : (65536#32).sle i.toBitVec = true := by
      simp [BitVec.sle, BitVec.toInt, hi_eq]
    have hrun : runJvmResFast (k + 200 + 0 * 14) clinit_AlgorithmLeanKt_prog 5
        (clinit_AlgorithmLeanKt_prog.drop 5) ⟨5, [], locs, jh, ⟨[], [], []⟩⟩ =
        some (.unit, ⟨21, [], locs,
          jh.setStatic "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "NEXT_GEN_4X4_LUT" (.heapRef arrAddr), ⟨[], [], []⟩⟩) := by
      f1_split_res_fuel 120
      flat_step_blk clinit_AlgorithmLeanKt_prog
      rw [hl0, evalResBranchInstrCons_if_icmpge]
      simp [hge]
      f1_split_res_fuel 120
      flat_step_blk clinit_AlgorithmLeanKt_prog
      rw [hl1]
    refine ⟨_, hrun, ⟨arrAddr, arr, ?_, ?_, hsz, fun j hj => htbl j (by omega)⟩⟩
    · simp [Jvm.JvmHeap.getStatic?, Jvm.JvmHeap.setStatic]
    · simp only [Jvm.JvmHeap.get?, Jvm.JvmHeap.setStatic] at hget ⊢
      exact hget
  | succ m ih =>
    intro k i arrAddr arr jh locs hm hi hget hsz htbl hstat hl0 hl1
    by_cases hi_eq : i.toNat = 65536
    · have hge : (65536#32).sle i.toBitVec = true := by
        simp [BitVec.sle, BitVec.toInt, hi_eq]
      have hrun : runJvmResFast (k + 200 + (m + 1) * 14) clinit_AlgorithmLeanKt_prog 5
          (clinit_AlgorithmLeanKt_prog.drop 5) ⟨5, [], locs, jh, ⟨[], [], []⟩⟩ =
          some (.unit, ⟨21, [], locs,
            jh.setStatic "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "NEXT_GEN_4X4_LUT" (.heapRef arrAddr), ⟨[], [], []⟩⟩) := by
        f1_split_res_fuel 120
        flat_step_blk clinit_AlgorithmLeanKt_prog
        rw [hl0, evalResBranchInstrCons_if_icmpge]
        simp [hge]
        f1_split_res_fuel 120
        flat_step_blk clinit_AlgorithmLeanKt_prog
        rw [hl1]
      refine ⟨_, hrun, ⟨arrAddr, arr, ?_, ?_, hsz, fun j hj => htbl j (by omega)⟩⟩
      · simp [Jvm.JvmHeap.getStatic?, Jvm.JvmHeap.setStatic]
      · simp only [Jvm.JvmHeap.get?, Jvm.JvmHeap.setStatic] at hget ⊢
        exact hget
    · have hi_lt : i.toNat < 65536 := by omega
      have hslt_icmp : (65536#32).sle i.toBitVec = false := by
        simp [BitVec.sle, BitVec.toInt]; omega
      have hslt0 : i.toBitVec.slt 0#32 = false := by
        simp [BitVec.slt, BitVec.toInt]; omega
      have hlt_arr : i.toNat < arr.size := by omega
      have hi1_toNat : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]; simp only [UInt32.reduceToNat]; omega
      let arr' := arr.set i.toNat (Algorithm.computeNextGen4x4BitwiseUInt i).toUInt8 hlt_arr
      let jh' := jh.set arrAddr (.byteArray arr')
      have hget' : jh'.get? arrAddr = some (.byteArray arr') :=
        jvmHeap_get?_set_self hget
      have hsz' : arr'.size = 65536 := by simp [arr', hsz]
      have htbl' : ∀ (j : Nat), j < (i + 1).toNat →
          arr'[j]! = (Algorithm.computeNextGen4x4BitwiseUInt (UInt32.ofNat j)).toUInt8 := by
        intro j hj
        rw [hi1_toNat] at hj
        by_cases hji : j = i.toNat
        · subst hji
          rw [getElem!_pos _ _ (by simp [arr', hsz, hi_lt])]
          simp [arr', UInt32.ofNat_toNat]
        · have hjlt : j < i.toNat := by omega
          have hj_arr : j < arr.size := by omega
          have hj_arr' : j < arr'.size := by simp [arr', hsz]; omega
          rw [getElem!_pos arr' j hj_arr']
          dsimp [arr']
          rw [Array.getElem_set_ne hlt_arr hj_arr (by omega), ← getElem!_pos arr j hj_arr]
          exact htbl j hjlt
      have hstat' : jh'.getStatic? "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "NEXT_GEN_4X4_LUT" = none := by
        dsimp [jh', Jvm.JvmHeap.set, Jvm.JvmHeap.getStatic?]
        split <;> exact hstat
      obtain ⟨st', hrun', hres'⟩ := ih k (i + 1) arrAddr arr' jh'
        (setLocal (setLocal locs 2 (.i32 i)) 0 (.i32 (i + 1)))
        (by omega) (by omega) hget' hsz' htbl' hstat' rfl (by simp [setLocal, hl1])
      refine ⟨st', ?_, hres'⟩
      f1_split_res_fuel 120
      flat_step_blk clinit_AlgorithmLeanKt_prog
      rw [hl0, evalResBranchInstrCons_if_icmpge]
      simp [hslt_icmp]
      f1_split_res_fuel 120
      flat_step_blk clinit_AlgorithmLeanKt_prog
      dsimp only
      rw [hl0, hl1]
      f1_split_res_fuel 120
      flat_step_blk clinit_AlgorithmLeanKt_prog
      f1_split_res_fuel 1
      rw [runJvmResFast_bastore hget hslt0 hlt_arr]
      f1_split_res_fuel 1
      dsimp only [runJvmResFast]
      rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by intro ⟨h, _⟩; cases h)]
      dsimp only [Jvm.stepInstr, setLocal]
      rw [hl0]
      dsimp only [Jvm.JvmVal.asI32?]
      simp only [show (0 = 2) ↔ False by decide, ↓reduceIte]
      rw [← show runJvmResFast = Jvm.runJvmResFast algHooks from rfl]
      f1_split_res_fuel 1
      rw [show (16 + 1 + 1 : Nat) = 18 by rfl]
      dsimp only [runJvmResFast]
      rw [Jvm.runJvmResFast_at_branch_cons algHooks (hbr := rfl)]
      rw [Jvm.evalResBranchInstrCons_goto]
      change runJvmResFast _ clinit_AlgorithmLeanKt_prog 5 (clinit_AlgorithmLeanKt_prog.drop 5) _ = _
      rw [show ((((k + 200 + (m + 1) * 14 - 120 + 116 + 1 - 120).add 113).succ - 120 + 117).add 0).succ - 1 - 1 - 1 =
        k + 200 + m * 14 by simp only [f1_nat_add_eq_add, Nat.succ_eq_add_one]; omega]
      rw [show Int32.toUInt32 1 = 1 from rfl]
      have hbyte_eq : ∀ (x : UInt32),
          { toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 x.toBitVec) : UInt32 }.toUInt8 = x.toUInt8 := by
        intro x
        apply UInt8.eq_of_toBitVec_eq
        apply BitVec.eq_of_getLsbD_eq
        intro b hb
        have hbv : ∀ (y : UInt32), y.toUInt8.toBitVec = BitVec.setWidth 8 y.toBitVec := fun _ => rfl
        rw [hbv, hbv]
        simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hb, decide_true, Bool.true_and,
          ↓reduceIte, show b < 32 by omega]
      rw [hbyte_eq]
      exact hrun'

theorem clinit_AlgorithmLeanKt_equiv :
    ∃ st', runJvmRes 917709 clinit_AlgorithmLeanKt_prog (initJvmState []) = some (.unit, st') ∧
      HasNextGen4x4Lut st'.jvmHeap := by
  let arr0 : Array UInt8 := Array.replicate (65536 : UInt32).toNat 0
  have harr0 : arr0 = Array.replicate 65536 0 := rfl
  have hsz0 : arr0.size = 65536 := by simp [harr0]
  have ⟨st', hrun, hlut⟩ := clinit_alg_loop 65536 0 0 0 arr0
    ⟨#[Jvm.HeapObj.byteArray arr0], []⟩
    (setLocal (setLocal (fun _ => .i32 0) 0 (.i32 0)) 1 (.heapRef 0))
    (by decide) (by decide) (by rfl) hsz0
    (fun j hj => by rw [UInt32.toNat_zero] at hj; omega) (by rfl) rfl rfl
  refine ⟨st', ?_, hlut⟩
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  f1_split_res_fuel 120
  flat_step_blk clinit_AlgorithmLeanKt_prog
  f1_split_res_fuel 1
  rw [runJvmResFast_newarray_byte (by decide)]
  f1_split_res_fuel 1
  rw [runJvmResFast_stepResFlatChunk 1]
  dsimp only [List.foldl, stepResFlatChunk, Jvm.stepResBlockChunkWith, Jvm.isBranchInstr, isFlatStopLeaf, Jvm.stepInstr,
    Jvm.JvmHeap.alloc, Array.size_empty, afterResBlockChunk, Jvm.afterResBlockChunk]
  exact hrun

private theorem clinit_mc_node_step {f : Nat} (pc : Nat) (h : UInt32)
    (prev prevDesc next nextDesc : String) (sub : Algorithm.MacroCell)
    (jh : Jvm.JvmHeap AlgExt) (locs : Nat → JvmVal)
    (hprog : clinit_MacroCellLeanKt_prog.drop pc =
      .newClass "com/alexvanyo/composelife/model/MacroCell$CellNode" :: .dup :: .iconst h ::
      .getstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" prev prevDesc :: .checkcast "com/alexvanyo/composelife/model/MacroCell" ::
      .getstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" prev prevDesc :: .checkcast "com/alexvanyo/composelife/model/MacroCell" ::
      .getstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" prev prevDesc :: .checkcast "com/alexvanyo/composelife/model/MacroCell" ::
      .getstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" prev prevDesc :: .checkcast "com/alexvanyo/composelife/model/MacroCell" ::
      .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/MacroCell$CellNode" "<init>"
        "(ILcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;Lkotlin/jvm/internal/DefaultConstructorMarker;)V" ::
      .putstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" next nextDesc ::
      clinit_MacroCellLeanKt_prog.drop (pc + 14))
    (hget : jh.getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" prev = some (.ext (.mc sub))) :
    runJvmResFast (f + 1 + 14) clinit_MacroCellLeanKt_prog pc (clinit_MacroCellLeanKt_prog.drop pc)
        ⟨pc, [], locs, jh, ⟨[], [], []⟩⟩ =
      runJvmResFast (f + 1) clinit_MacroCellLeanKt_prog (pc + 14) (clinit_MacroCellLeanKt_prog.drop (pc + 14))
        ⟨pc + 14, [], locs,
          jh.setStatic "com/alexvanyo/composelife/model/MacroCellLeanKt" next (.ext (.mc (.cellNode h sub sub sub sub))), ⟨[], [], []⟩⟩ := by
  rw [hprog, show f + 1 + 14 = (f + 3) + 12 by omega, runJvmResFast_stepResFlatChunk 12]
  (conv => lhs; arg 1; dsimp only [stepResFlatChunk, Jvm.stepResBlockChunkWith, Jvm.isBranchInstr, isFlatStopLeaf, Jvm.stepInstr,
    Jvm.evalCheckCast, Jvm.JvmHeap.checkCast, isSubtypeOf,
    algHooks, algResolveStatic, checkCast, Jvm.defaultCheckCast])
  (conv => lhs; arg 1; simp only [
    show ("com/alexvanyo/composelife/model/MacroCell$CellNode" == "java/lang/StringBuilder") = false from rfl,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, hget])
  (conv => lhs; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont,
    show ((f + 2).add 0).succ = f + 2 + 1 from rfl,
    show ((pc + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).add 0).succ = pc + 12 from rfl,
    runJvmResFast_invokespecial_step rfl,
    show f + 2 = (f + 1) + 1 by omega, runJvmResFast_stepResFlatChunk 1]
  (conv => lhs; arg 1; dsimp only [stepResFlatChunk, Jvm.stepResBlockChunkWith, Jvm.isBranchInstr, isFlatStopLeaf, Jvm.stepInstr, setLocal])
  (conv => lhs; arg 1; simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte, ite_true])
  rw [afterResBlockChunk_cont]

private def clinitMcSpecs : List (Nat × UInt32 × String × String × String × String) := [
  (7, 572885659, "EMPTY_LEVEL_4", "Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;", "emptyNode_5", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (21, 2802476370, "emptyNode_5", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_6", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (35, 1707623340, "emptyNode_6", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_7", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (49, 4218611389, "emptyNode_7", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_8", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (63, 2201973367, "emptyNode_8", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_9", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (77, 239121595, "emptyNode_9", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_10", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (91, 3011634316, "emptyNode_10", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_11", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (105, 1722368864, "emptyNode_11", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_12", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (119, 3940829537, "emptyNode_12", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_13", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (133, 2894693595, "emptyNode_13", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_14", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (147, 1654303450, "emptyNode_14", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_15", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (161, 2414827799, "emptyNode_15", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_16", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (175, 3816459313, "emptyNode_16", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_17", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (189, 280834627, "emptyNode_17", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_18", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (203, 2486243748, "emptyNode_18", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_19", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (217, 3514875046, "emptyNode_19", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_20", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (231, 1818352480, "emptyNode_20", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_21", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (245, 3149804332, "emptyNode_21", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_22", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (259, 1572535521, "emptyNode_22", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_23", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (273, 4039701039, "emptyNode_23", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_24", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (287, 1775760851, "emptyNode_24", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_25", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (301, 2567470534, "emptyNode_25", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_26", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (315, 181454591, "emptyNode_26", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_27", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (329, 2683744292, "emptyNode_27", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_28", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (343, 946647544, "emptyNode_28", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_29", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (357, 1135049598, "emptyNode_29", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_30", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (371, 796716940, "emptyNode_30", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_31", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"),
  (385, 350678234, "emptyNode_31", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;", "emptyNode_32", "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;")
]

private theorem makeCellNode_eq_of_eq {nw : Algorithm.MacroCell} {lvl h : UInt32}
    (hlvl : nw.level = lvl) (hh : nw.cellHashCode = h) :
    Algorithm.makeCellNode nw nw nw nw =
      .cellNode (Algorithm.cellNodeHash (lvl + 1) h h h h) nw nw nw nw := by
  simp [Algorithm.makeCellNode, hlvl, hh]

private theorem emptyNode_level_and_hash (k : Nat) :
    (Algorithm.emptyNode k).level = if k ≤ 4 then 4 else UInt32.ofNat k := by
  induction k with
  | zero => decide
  | succ k ih =>
    by_cases hk : k + 1 ≤ 4
    · have : k + 1 = 0 ∨ k + 1 = 1 ∨ k + 1 = 2 ∨ k + 1 = 3 ∨ k + 1 = 4 := by omega
      rcases this with h | h | h | h | h
      · rw [h]; decide
      · rw [h]; decide
      · rw [h]; decide
      · rw [h]; decide
      · rw [h]; decide
    · obtain ⟨m, hm⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
      subst hm
      have ih' : (Algorithm.emptyNode (m + 4)).level = if m + 4 ≤ 4 then 4 else UInt32.ofNat (m + 4) := ih
      simp only [show m + 4 + 1 = m + 5 by omega, Algorithm.emptyNode, Algorithm.makeCellNode,
        Algorithm.MacroCell.level, hk, ↓reduceIte]
      by_cases hle : m + 4 ≤ 4
      · have : m = 0 := by omega
        subst this
        decide
      · simp only [hle, ↓reduceIte] at ih'
        rw [ih']
        apply UInt32.toNat_inj.mp
        simp [UInt32.toNat_add, UInt32.toNat_ofNat]

private def emptyNodeHashSeq : Nat → UInt32
  | 0 => (Algorithm.emptyLevel4).cellHashCode
  | k + 1 =>
    let h := emptyNodeHashSeq k
    Algorithm.cellNodeHash (UInt32.ofNat (k + 5)) h h h h

private theorem cellHashCode_makeCellNode_self (nw ne sw se : Algorithm.MacroCell) :
    (Algorithm.makeCellNode nw ne sw se).cellHashCode =
      Algorithm.cellNodeHash (nw.level + 1) nw.cellHashCode ne.cellHashCode sw.cellHashCode se.cellHashCode :=
  rfl

private theorem emptyNode_cellHashCode (k : Nat) :
    (Algorithm.emptyNode (k + 4)).cellHashCode = emptyNodeHashSeq k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlev : (Algorithm.emptyNode (k + 4)).level = UInt32.ofNat (k + 4) := by
      rw [emptyNode_level_and_hash]
      by_cases h : k + 4 ≤ 4
      · have : k = 0 := by omega
        subst this; decide
      · simp [h]
    have hlev1 : (Algorithm.emptyNode (k + 4)).level + 1 = UInt32.ofNat (k + 5) := by
      rw [hlev]
      apply UInt32.toNat_inj.mp
      simp [UInt32.toNat_add, UInt32.toNat_ofNat]
    rw [show k + 1 + 4 = k + 5 by omega, Algorithm.emptyNode, cellHashCode_makeCellNode_self, hlev1, ih]
    rfl


set_option maxRecDepth 2048 in
private theorem clinitMcSpecs_drop (i : Fin 28) :
    clinit_MacroCellLeanKt_prog.drop (7 + i.val * 14) =
      .newClass "com/alexvanyo/composelife/model/MacroCell$CellNode" :: .dup :: .iconst clinitMcSpecs[i.val].2.1 ::
      .getstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" clinitMcSpecs[i.val].2.2.1 clinitMcSpecs[i.val].2.2.2.1 ::
      .checkcast "com/alexvanyo/composelife/model/MacroCell" ::
      .getstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" clinitMcSpecs[i.val].2.2.1 clinitMcSpecs[i.val].2.2.2.1 ::
      .checkcast "com/alexvanyo/composelife/model/MacroCell" ::
      .getstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" clinitMcSpecs[i.val].2.2.1 clinitMcSpecs[i.val].2.2.2.1 ::
      .checkcast "com/alexvanyo/composelife/model/MacroCell" ::
      .getstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" clinitMcSpecs[i.val].2.2.1 clinitMcSpecs[i.val].2.2.2.1 ::
      .checkcast "com/alexvanyo/composelife/model/MacroCell" ::
      .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/MacroCell$CellNode" "<init>"
        "(ILcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;Lkotlin/jvm/internal/DefaultConstructorMarker;)V" ::
      .putstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" clinitMcSpecs[i.val].2.2.2.2.1 clinitMcSpecs[i.val].2.2.2.2.2 ::
      clinit_MacroCellLeanKt_prog.drop (7 + i.val * 14 + 14) := by
  rcases i with ⟨i, hi⟩
  dsimp only
  match i with
  | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16|17|18|19|20|21|22|23|24|25|26|27 => rfl
  | n + 28 => omega

set_option maxRecDepth 2048 in
private theorem clinit_MacroCellLeanKt_prog_drop_399 :
    clinit_MacroCellLeanKt_prog.drop 399 =
      .iconst 33 :: .anewarray "com/alexvanyo/composelife/model/MacroCell" :: .astore 0 ::
      clinit_MacroCellLeanKt_prog.drop 402 := rfl

set_option maxRecDepth 4096 in
private theorem clinit_MacroCellLeanKt_prog_drop_534 :
    clinit_MacroCellLeanKt_prog.drop 534 =
      .aload 0 :: .putstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_NODES" "[Lcom/alexvanyo/composelife/model/MacroCell;" ::
      .vreturn :: clinit_MacroCellLeanKt_prog.drop 537 := rfl

private def clinitMcArrFieldNames : List String := [
  "EMPTY_LEVEL_4", "EMPTY_LEVEL_4", "EMPTY_LEVEL_4", "EMPTY_LEVEL_4", "EMPTY_LEVEL_4",
  "emptyNode_5", "emptyNode_6", "emptyNode_7", "emptyNode_8", "emptyNode_9",
  "emptyNode_10", "emptyNode_11", "emptyNode_12", "emptyNode_13", "emptyNode_14",
  "emptyNode_15", "emptyNode_16", "emptyNode_17", "emptyNode_18", "emptyNode_19",
  "emptyNode_20", "emptyNode_21", "emptyNode_22", "emptyNode_23", "emptyNode_24",
  "emptyNode_25", "emptyNode_26", "emptyNode_27", "emptyNode_28", "emptyNode_29",
  "emptyNode_30", "emptyNode_31", "emptyNode_32"
]

private theorem clinitMcArrFieldName_eq (k : Fin 33) :
    (if k.val < 5 then "EMPTY_LEVEL_4" else s!"emptyNode_{k.val}") = clinitMcArrFieldNames[k.val] := by
  have hall : (List.finRange 33).all (fun i =>
      decide ((if i.val < 5 then "EMPTY_LEVEL_4" else s!"emptyNode_{i.val}") =
        clinitMcArrFieldNames[i.val])) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hall k (List.mem_finRange k))

set_option maxRecDepth 4096 in
private theorem clinitMcArr_drop (k : Fin 33) :
    clinit_MacroCellLeanKt_prog.drop (402 + k.val * 4) =
      .aload 0 :: .iconst (UInt32.ofNat k.val) ::
      .getstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" (if k.val < 5 then "EMPTY_LEVEL_4" else s!"emptyNode_{k.val}")
        (if k.val < 5 then "Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;"
         else "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;") ::
      .aastore :: clinit_MacroCellLeanKt_prog.drop (402 + k.val * 4 + 4) := by
  rw [clinitMcArrFieldName_eq k]
  rcases k with ⟨k, hk⟩
  dsimp only
  match k with
  | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16|17|18|19|20|21|22|23|24|25|26|27|28|29|30|31|32 => rfl
  | n + 33 => omega

private def mkMcJH : Nat → Jvm.JvmHeap AlgExt
  | 0 => ({} : Jvm.JvmHeap AlgExt).setStatic "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_LEVEL_4" (.ext (.mc (Algorithm.emptyNode 4)))
  | k + 1 =>
    (mkMcJH k).setStatic "com/alexvanyo/composelife/model/MacroCellLeanKt" (clinitMcArrFieldNames.getD (k + 5) "") (.ext (.mc (Algorithm.emptyNode (k + 5))))

private theorem jvHeap_alloc_set0_eq {jh : Jvm.JvmHeap AlgExt} (h0 : jh.objects = #[])
    (a b : Jvm.HeapObj AlgExt) :
    ((jh.alloc a).2).set 0 b = (jh.alloc b).2 := by
  cases jh
  simp only at h0
  subst h0
  rfl

private theorem jvHeap_alloc_get0_eq {jh : Jvm.JvmHeap AlgExt} (h0 : jh.objects = #[])
    (a : Jvm.HeapObj AlgExt) :
    ((jh.alloc a).2).get? 0 = some a := by
  cases jh
  simp only at h0
  subst h0
  rfl

private theorem list_find?_filter_of_imp {α : Type} {p q : α → Bool}
    (himp : ∀ x, p x = true → q x = true) (l : List α) :
    (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases hqa : q a = true
    · simp only [List.filter_cons, hqa, ↓reduceIte, List.find?_cons]
      by_cases hpa : p a = true <;> simp [hpa, ih]
    · have hpa : p a = false := by
        cases h : p a with
        | true => exact False.elim (hqa (himp a h))
        | false => rfl
      simp [hqa, hpa, ih]

private theorem jvmHeap_getStatic?_setStatic_ne {Ext : Type} (jh : Jvm.JvmHeap Ext)
    (c1 f1 c2 f2 : String) (v : Jvm.JvmVal Ext) (hne : c1 ≠ c2 ∨ f1 ≠ f2) :
    (jh.setStatic c1 f1 v).getStatic? c2 f2 = jh.getStatic? c2 f2 := by
  dsimp only [Jvm.JvmHeap.setStatic, Jvm.JvmHeap.getStatic?]
  have hhead : (c1 == c2 && f1 == f2) = false := by
    cases h : c1 == c2 && f1 == f2
    · rfl
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      rcases hne with hne | hne <;> exact False.elim (hne (by first | exact h.1 | exact h.2))
  simp only [List.find?_cons, hhead]
  rw [list_find?_filter_of_imp]
  rintro ⟨c, f, val⟩ hmatch
  simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
  simp only [Bool.not_eq_true']
  by_cases hc : c = c1 <;> by_cases hf : f = f1 <;> simp_all

theorem clinit_MacroCellLeanKt_equiv :
    ∃ st', runJvmRes 550 clinit_MacroCellLeanKt_prog (initJvmState []) = some (.unit, st') ∧
      HasEmptyNodes st'.jvmHeap := by
  have hhashes : ∀ (i : Fin 28),
      clinitMcSpecs[i.val].2.1 = emptyNodeHashSeq (i.val + 1) := by
    have hall : (List.finRange 28).all (fun i => decide (clinitMcSpecs[i.val].2.1 = emptyNodeHashSeq (i.val + 1))) = true := by
      decide
    intro i
    exact of_decide_eq_true (List.all_eq_true.mp hall i (List.mem_finRange i))
  have hnodes := clinitMcSpecs_drop
  have hbuild_cell : ∀ (k : Nat) (h : UInt32), h = emptyNodeHashSeq (k + 1) →
      .cellNode h (Algorithm.emptyNode (k + 4)) (Algorithm.emptyNode (k + 4))
        (Algorithm.emptyNode (k + 4)) (Algorithm.emptyNode (k + 4)) =
      Algorithm.emptyNode (k + 5) := by
    intro k h hh
    have hlev : (Algorithm.emptyNode (k + 4)).level = UInt32.ofNat (k + 4) := by
      rw [emptyNode_level_and_hash]
      by_cases hk : k + 4 ≤ 4
      · have : k = 0 := by omega
        subst this; decide
      · simp [hk]
    have hlev1 : (Algorithm.emptyNode (k + 4)).level + 1 = UInt32.ofNat (k + 5) := by
      rw [hlev]
      apply UInt32.toNat_inj.mp
      simp [UInt32.toNat_add, UInt32.toNat_ofNat]
    have hch := emptyNode_cellHashCode k
    subst hh
    simp only [Algorithm.emptyNode, Algorithm.makeCellNode, hlev1, hch, emptyNodeHashSeq]
  let mkJH := mkMcJH
  have hstep_init : ∀ locs,
      runJvmResFast 550 clinit_MacroCellLeanKt_prog 0 (clinit_MacroCellLeanKt_prog.drop 0)
        ⟨0, [], locs, {}, ⟨[], [], []⟩⟩ =
      runJvmResFast 543 clinit_MacroCellLeanKt_prog 7 (clinit_MacroCellLeanKt_prog.drop 7)
        ⟨7, [], locs, mkJH 0, ⟨[], [], []⟩⟩ := by
    intro locs
    have hp0 : clinit_MacroCellLeanKt_prog.drop 0 =
        .getstatic "com/alexvanyo/composelife/model/MacroCell$Level4Node" "Companion"
          "Lcom/alexvanyo/composelife/model/MacroCell$Level4Node$Companion;" ::
        .lconst 0 :: .lconst 0 :: .lconst 0 :: .lconst 0 ::
        .invokevirtual "com/alexvanyo/composelife/model/MacroCell$Level4Node$Companion"
          "invoke-2jIhpxI" "(JJJJ)Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;" ::
        .putstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_LEVEL_4"
          "Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;" ::
        clinit_MacroCellLeanKt_prog.drop 7 := rfl
    rw [hp0, show (550 : Nat) = 545 + 5 by decide, runJvmResFast_stepResFlatChunk 5]
    (conv => lhs; arg 1; dsimp only [stepResFlatChunk, Jvm.stepResBlockChunkWith, Jvm.isBranchInstr, isFlatStopLeaf, Jvm.stepInstr,
      algHooks, algResolveStatic])
    (conv => lhs; arg 1; simp only [
      show ({} : Jvm.JvmHeap AlgExt).getStatic? "com/alexvanyo/composelife/model/MacroCell$Level4Node" "Companion" =
        none from rfl,
      Bool.or_false, Bool.false_eq_true, ↓reduceIte, ite_true])
    rw [afterResBlockChunk_cont,
      runJvmResFast_invokevirtual_step rfl, runJvmResFast_stepResFlatChunk 1]
    (conv => lhs; arg 1; jvm_whnf_blk)
    rw [afterResBlockChunk_cont]
    rfl
  -- Now chain k = 0..27 in a loop using clinit_mc_node_step and mkJH
  have hmk_get : ∀ (k : Fin 29),
      (mkJH k.val).getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" (clinitMcArrFieldNames.getD (k.val + 4) "") =
        some (.ext (.mc (Algorithm.emptyNode (k.val + 4)))) := by
    intro k
    rcases k with ⟨k, hk⟩
    match k with
    | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16|17|18|19|20|21|22|23|24|25|26|27|28 => rfl
    | n + 29 => omega
  have hchain : ∀ (d : Nat) (hd : d ≤ 28) (f : Nat) (locs : Nat → JvmVal),
      runJvmResFast (f + 1 + d * 14) clinit_MacroCellLeanKt_prog (7 + (28 - d) * 14)
        (clinit_MacroCellLeanKt_prog.drop (7 + (28 - d) * 14))
        ⟨7 + (28 - d) * 14, [], locs, mkJH (28 - d), ⟨[], [], []⟩⟩ =
      runJvmResFast (f + 1) clinit_MacroCellLeanKt_prog 399 (clinit_MacroCellLeanKt_prog.drop 399)
        ⟨399, [], locs, mkJH 28, ⟨[], [], []⟩⟩ := by
    intro d
    induction d with
    | zero =>
      intro _ f locs
      rfl
    | succ d ih =>
      intro hd f locs
      let i : Nat := 28 - (d + 1)
      have hi28 : i < 28 := by omega
      let idx : Fin 28 := ⟨i, hi28⟩
      have hspec := hnodes idx
      have hspecPrev : clinitMcSpecs[idx.val].2.2.1 = clinitMcArrFieldNames.getD (idx.val + 4) "" := by
        have hall : (List.finRange 28).all (fun j =>
            decide (clinitMcSpecs[j.val].2.2.1 = clinitMcArrFieldNames.getD (j.val + 4) "")) = true := by
          decide
        exact of_decide_eq_true (List.all_eq_true.mp hall idx (List.mem_finRange idx))
      have hspecNext : clinitMcSpecs[idx.val].2.2.2.2.1 = clinitMcArrFieldNames.getD (idx.val + 5) "" := by
        have hall : (List.finRange 28).all (fun j =>
            decide (clinitMcSpecs[j.val].2.2.2.2.1 = clinitMcArrFieldNames.getD (j.val + 5) "")) = true := by
          decide
        exact of_decide_eq_true (List.all_eq_true.mp hall idx (List.mem_finRange idx))
      have hhash_i := hhashes idx
      dsimp only [idx] at hspec hspecPrev hspecNext hhash_i
      have hgetPrev : (mkJH i).getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" clinitMcSpecs[i].2.2.1 =
          some (.ext (.mc (Algorithm.emptyNode (i + 4)))) := by
        rw [hspecPrev]; exact hmk_get ⟨i, by omega⟩
      have hstep := clinit_mc_node_step (f := f + d * 14) (7 + i * 14)
        clinitMcSpecs[i].2.1 clinitMcSpecs[i].2.2.1 clinitMcSpecs[i].2.2.2.1
        clinitMcSpecs[i].2.2.2.2.1 clinitMcSpecs[i].2.2.2.2.2 (Algorithm.emptyNode (i + 4))
        (mkJH i) locs hspec hgetPrev
      rw [hbuild_cell i _ (by exact hhash_i), hspecNext] at hstep
      have hmkSucc : (mkJH i).setStatic "com/alexvanyo/composelife/model/MacroCellLeanKt" (clinitMcArrFieldNames.getD (i + 5) "")
          (.ext (.mc (Algorithm.emptyNode (i + 5)))) = mkJH (i + 1) := rfl
      rw [hmkSucc] at hstep
      rw [show f + 1 + (d + 1) * 14 = (f + d * 14) + 1 + 14 by omega]
      change runJvmResFast ((f + d * 14) + 1 + 14) clinit_MacroCellLeanKt_prog (7 + i * 14)
        (clinit_MacroCellLeanKt_prog.drop (7 + i * 14)) ⟨7 + i * 14, [], locs, mkJH i, ⟨[], [], []⟩⟩ = _
      rw [hstep]
      have hpc1 : 7 + i * 14 + 14 = 7 + (28 - d) * 14 := by omega
      have hi1 : i + 1 = 28 - d := by omega
      have hfuel : f + d * 14 + 1 = f + 1 + d * 14 := by omega
      rw [hpc1, hi1, hfuel]
      exact ih (by omega) f locs
  have hmk_get_all : ∀ (j : Fin 33),
      (mkJH 28).getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" (if j.val < 5 then "EMPTY_LEVEL_4" else s!"emptyNode_{j.val}") =
        some (.ext (.mc (Algorithm.emptyNode j.val))) := by
    intro j
    rw [clinitMcArrFieldName_eq j]
    rcases j with ⟨j, hj⟩
    match j with
    | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16|17|18|19|20|21|22|23|24|25|26|27|28|29|30|31|32 => rfl
    | n + 33 => omega
  let arrAt (k : Nat) : Array JvmVal :=
    Array.ofFn (n := 33) fun i => if i.val < k then .ext (.mc (Algorithm.emptyNode i.val)) else .null
  have harr0 : Array.replicate (33 : UInt32).toNat (.null : JvmVal) = arrAt 0 := by
    apply Array.ext
    · simp [arrAt]
    · intro i hi1 hi2
      simp [arrAt]
  have harrSet : ∀ (k : Nat) (hk : k < 33) (hlen : (arrAt k).size = 33),
      (arrAt k).set k (.ext (.mc (Algorithm.emptyNode k))) (by omega) = arrAt (k + 1) := by
    intro k hk hlen
    apply Array.ext
    · simp [arrAt]
    · intro i hi1 hi2
      simp only [Array.getElem_set, arrAt, Array.getElem_ofFn]
      by_cases hki : k = i
      · subst hki; simp
      · have : (i < k + 1) = (i < k) := propext ⟨fun h => by omega, fun h => by omega⟩
        simp [hki, this]
  have harr33 : arrAt 33 = emptyNodesArray := by
    apply Array.ext
    · simp [arrAt, emptyNodesArray]
    · intro i hi1 hi2
      simp only [arrAt, emptyNodesArray, Array.getElem_ofFn]
      have : i < 33 := by simp [arrAt] at hi1; exact hi1
      simp [this]
  have harr_step : ∀ (f pc : Nat) (idx : Nat) (name desc : String)
      (elems : Array JvmVal) (jh : Jvm.JvmHeap AlgExt) (locs : Nat → JvmVal) (val : Algorithm.MacroCell)
      (hlt33 : idx < 33) (hsz : elems.size = 33),
      clinit_MacroCellLeanKt_prog.drop pc =
        .aload 0 :: .iconst (UInt32.ofNat idx) :: .getstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" name desc :: .aastore ::
        clinit_MacroCellLeanKt_prog.drop (pc + 4) →
      jh.getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" name = some (.ext (.mc val)) →
      locs 0 = .heapRef 0 →
      jh.get? 0 = some (.objArray "com/alexvanyo/composelife/model/MacroCell" elems) →
      runJvmResFast (f + 4) clinit_MacroCellLeanKt_prog pc (clinit_MacroCellLeanKt_prog.drop pc)
          ⟨pc, [], locs, jh, ⟨[], [], []⟩⟩ =
        runJvmResFast f clinit_MacroCellLeanKt_prog (pc + 4) (clinit_MacroCellLeanKt_prog.drop (pc + 4))
          ⟨pc + 4, [], locs,
            jh.set 0 (.objArray "com/alexvanyo/composelife/model/MacroCell"
              (elems.set idx (.ext (.mc val)) (by omega))), ⟨[], [], []⟩⟩ := by
    intro f pc idx name desc elems jh locs val hlt33 hsz hp hjg hl0 hj0
    have hidxNat : (UInt32.ofNat idx).toNat = idx := Nat.mod_eq_of_lt (by omega)
    have hslt : (UInt32.ofNat idx).toBitVec.slt 0#32 = false := by
      simp [BitVec.slt, BitVec.toInt]; omega
    have hlt_elems : (UInt32.ofNat idx).toNat < elems.size := by omega
    rw [hp, show f + 4 = (f + 1) + 3 by omega, runJvmResFast_stepResFlatChunk 3]
    (conv => lhs; arg 1; dsimp only [stepResFlatChunk, Jvm.stepResBlockChunkWith, Jvm.isBranchInstr, isFlatStopLeaf, Jvm.stepInstr,
      Jvm.JvmVal.asI32?])
    (conv => lhs; arg 1; simp only [hl0, hjg, Bool.or_false, Bool.false_eq_true, ↓reduceIte])
    rw [afterResBlockChunk_cont, show pc + 1 + 1 + 1 = pc + 3 by omega]
    have hstep := Jvm.stepInstr_aastore algHooks (pc := pc + 3) (v := .ext (.mc val))
      (idx := UInt32.ofNat idx) (addr := 0) (stkRest := []) (locs := locs) (hp := ⟨[], [], []⟩)
      rfl hj0 hslt hlt_elems
    dsimp only [runJvmResFast]
    rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by intro ⟨h, _⟩; cases h)]
    simp only [hstep, ↓reduceIte]
    have heqSet : elems.set (UInt32.ofNat idx).toNat (.ext (.mc val)) hlt_elems =
        elems.set idx (.ext (.mc val)) (by omega) := by
      congr 1
    rw [heqSet, show pc + 3 + 1 = pc + 4 by omega]
  have harr_chain : ∀ (d : Nat) (hd : d ≤ 33) (f : Nat) (locs : Nat → JvmVal),
      locs 0 = .heapRef 0 →
      runJvmResFast (f + d * 4) clinit_MacroCellLeanKt_prog (402 + (33 - d) * 4)
        (clinit_MacroCellLeanKt_prog.drop (402 + (33 - d) * 4))
        ⟨402 + (33 - d) * 4, [], locs,
          (mkJH 28).alloc (.objArray "com/alexvanyo/composelife/model/MacroCell" (arrAt (33 - d))) |>.2,
          ⟨[], [], []⟩⟩ =
      runJvmResFast f clinit_MacroCellLeanKt_prog 534 (clinit_MacroCellLeanKt_prog.drop 534)
        ⟨534, [], locs,
          (mkJH 28).alloc (.objArray "com/alexvanyo/composelife/model/MacroCell" (arrAt 33)) |>.2,
          ⟨[], [], []⟩⟩ := by
    intro d
    induction d with
    | zero =>
      intro _ f locs _; rfl
    | succ d ih =>
      intro hd f locs hl0
      let j : Nat := 33 - (d + 1)
      have hj33 : j < 33 := by omega
      let name := if j < 5 then "EMPTY_LEVEL_4" else s!"emptyNode_{j}"
      let desc := if j < 5 then "Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;"
        else "Lcom/alexvanyo/composelife/model/MacroCell$CellNode;"
      have hp_j : clinit_MacroCellLeanKt_prog.drop (402 + j * 4) =
          .aload 0 :: .iconst (UInt32.ofNat j) :: .getstatic "com/alexvanyo/composelife/model/MacroCellLeanKt" name desc :: .aastore ::
          clinit_MacroCellLeanKt_prog.drop (402 + j * 4 + 4) :=
        clinitMcArr_drop ⟨j, hj33⟩
      let jh_j := ((mkJH 28).alloc (.objArray "com/alexvanyo/composelife/model/MacroCell" (arrAt j))).2
      have hstatic_j : jh_j.getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" name = some (.ext (.mc (Algorithm.emptyNode j))) := by
        dsimp only [jh_j, Jvm.JvmHeap.alloc, Jvm.JvmHeap.getStatic?, name]
        exact hmk_get_all ⟨j, hj33⟩
      have hget0_j : jh_j.get? 0 = some (.objArray "com/alexvanyo/composelife/model/MacroCell" (arrAt j)) :=
        jvHeap_alloc_get0_eq (by rfl : (mkJH 28).objects = #[]) _
      have hsz_j : (arrAt j).size = 33 := by simp [arrAt]
      have hstep := harr_step (f + d * 4) (402 + j * 4) j name desc (arrAt j) jh_j locs
        (Algorithm.emptyNode j) hj33 hsz_j hp_j hstatic_j hl0 hget0_j
      have hjh_eq : jh_j.set 0 (.objArray "com/alexvanyo/composelife/model/MacroCell"
          ((arrAt j).set j (.ext (.mc (Algorithm.emptyNode j))) (by omega))) =
          ((mkJH 28).alloc (.objArray "com/alexvanyo/composelife/model/MacroCell" (arrAt (j + 1)))).2 := by
        dsimp only [jh_j]
        rw [jvHeap_alloc_set0_eq (by rfl : (mkJH 28).objects = #[])]
        exact congrArg
          (fun arr => ((mkJH 28).alloc (.objArray "com/alexvanyo/composelife/model/MacroCell" arr)).2)
          (harrSet j hj33 hsz_j)
      rw [hjh_eq] at hstep
      rw [show f + (d + 1) * 4 = (f + d * 4) + 4 by omega]
      change runJvmResFast ((f + d * 4) + 4) clinit_MacroCellLeanKt_prog (402 + j * 4)
        (clinit_MacroCellLeanKt_prog.drop (402 + j * 4)) ⟨402 + j * 4, [], locs, jh_j, ⟨[], [], []⟩⟩ = _
      rw [hstep]
      have hpc1 : 402 + j * 4 + 4 = 402 + (33 - d) * 4 := by omega
      have hj1 : j + 1 = 33 - d := by omega
      rw [hpc1, hj1]
      exact ih (by omega) f locs hl0
  let stFinal : JvmState :=
    ⟨536, [], setLocal (fun _ => .i32 0) 0 (.heapRef 0),
      (((mkJH 28).alloc (.objArray "com/alexvanyo/composelife/model/MacroCell" emptyNodesArray)).2).setStatic
        "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_NODES" (.heapRef 0),
      ⟨[], [], []⟩⟩
  refine ⟨stFinal, ?_, ?_⟩
  · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    change runJvmResFast 550 clinit_MacroCellLeanKt_prog 0 (clinit_MacroCellLeanKt_prog.drop 0)
      ⟨0, [], fun _ => .i32 0, {}, ⟨[], [], []⟩⟩ = some (.unit, stFinal)
    rw [hstep_init (fun _ => .i32 0)]
    rw [show (543 : Nat) = 150 + 1 + 28 * 14 by decide]
    change runJvmResFast (150 + 1 + 28 * 14) clinit_MacroCellLeanKt_prog (7 + (28 - 28) * 14)
      (clinit_MacroCellLeanKt_prog.drop (7 + (28 - 28) * 14))
      ⟨7 + (28 - 28) * 14, [], fun _ => .i32 0, mkJH (28 - 28), ⟨[], [], []⟩⟩ = _
    rw [hchain 28 (by decide) 150 (fun _ => .i32 0)]
    change runJvmResFast 151 _ _ _ _ = _
    have hp399 := clinit_MacroCellLeanKt_prog_drop_399
    have hmk0 : (mkJH 28).objects = #[] := by rfl
    have hrepl : Array.replicate 33 (.null : JvmVal) = arrAt 0 := by simpa using harr0
    have harr0' : (mkJH 28).alloc (.objArray "com/alexvanyo/composelife/model/MacroCell"
        (Array.replicate 33 (.null : JvmVal))) =
        (0, ((mkJH 28).alloc (.objArray "com/alexvanyo/composelife/model/MacroCell" (arrAt 0))).2) := by
      rw [hrepl]
      simp [Jvm.JvmHeap.alloc, hmk0]
    rw [hp399, show (151 : Nat) = 148 + 3 by decide, runJvmResFast_stepResFlatChunk 3]
    (conv => lhs; arg 1; dsimp only [stepResFlatChunk, Jvm.stepResBlockChunkWith, Jvm.isBranchInstr, isFlatStopLeaf, Jvm.stepInstr,
      Jvm.JvmVal.asI32?])
    (conv => lhs; arg 1; simp only [show ((33 : UInt32).toBitVec.slt 0#32) = false from rfl,
      show (33 : UInt32).toNat = 33 from rfl, harr0', Bool.or_false, Bool.false_eq_true, ↓reduceIte])
    rw [afterResBlockChunk_cont]
    change runJvmResFast (16 + 33 * 4) clinit_MacroCellLeanKt_prog (402 + (33 - 33) * 4)
      (clinit_MacroCellLeanKt_prog.drop (402 + (33 - 33) * 4))
      ⟨402 + (33 - 33) * 4, [], setLocal (fun _ => .i32 0) 0 (.heapRef 0),
        ((mkJH 28).alloc (.objArray "com/alexvanyo/composelife/model/MacroCell" (arrAt (33 - 33)))).2,
        ⟨[], [], []⟩⟩ = _
    rw [harr_chain 33 (by decide) 16 (setLocal (fun _ => .i32 0) 0 (.heapRef 0)) rfl, harr33]
    have hp534 := clinit_MacroCellLeanKt_prog_drop_534
    rw [hp534, show (16 : Nat) = 13 + 3 by decide, runJvmResFast_stepResFlatChunk 3]
    (conv => lhs; arg 1; jvm_whnf_blk)
    dsimp only [afterResBlockChunk]
    rfl
  · refine ⟨0, ?_, ?_, ?_⟩
    · have h0 := hmk_get_all ⟨0, by decide⟩
      simp only [show (0 : Nat) < 5 by decide, ↓reduceIte, Algorithm.emptyNode] at h0
      dsimp only [stFinal]
      rw [jvmHeap_getStatic?_setStatic_ne _ _ _ _ _ _ (Or.inr (by decide))]
      exact h0
    · simp [stFinal, Jvm.JvmHeap.getStatic?, Jvm.JvmHeap.setStatic]
    · have hmk0 : (mkJH 28).objects = #[] := by rfl
      simp [stFinal, Jvm.JvmHeap.setStatic, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?, hmk0]

private theorem lut_entry_and15 (arr : Array UInt8) (hsz : arr.size = 65536)
    (htbl : ∀ (k : Nat), k < 65536 → arr[k]! = (Algorithm.computeNextGen4x4BitwiseUInt (UInt32.ofNat k)).toUInt8)
    (x : UInt32) :
    UInt32.ofBitVec (BitVec.signExtend 32 (arr[(x &&& 65535).toNat]'(by have := u32_and_65535_lt x; omega)).toBitVec) &&&
        (15 : UInt32) =
      Algorithm.computeNextGen4x4UInt x := by
  have hmask := u32_and_65535_lt x
  have hget : arr[(x &&& 65535).toNat] =
      (Algorithm.computeNextGen4x4BitwiseUInt (x &&& 65535)).toUInt8 := by
    have heq := htbl (x &&& 65535).toNat hmask
    have hpos : arr[(x &&& 65535).toNat]! = arr[(x &&& 65535).toNat]'(by omega) :=
      getElem!_pos arr _ (by omega)
    rw [hpos] at heq
    simpa [UInt32.ofNat_toNat] using heq
  rw [hget, lut_byte_signExtend_and15]
  exact (Algorithm.computeNextGen4x4UInt_eq_table x).symm

theorem computeLeafNextGen8x8FastUInt_equiv (w : UInt64) (jh : Jvm.JvmHeap AlgExt)
    (hlut : HasNextGen4x4Lut jh) :
    runJvm 1200 AlgorithmLeanKt_f_Algorithm_computeLeafNextGen8x8FastUInt_prog
      (Jvm.initJvmState [(0, .i64 w)] (.i32 0) ⟨[], [], []⟩ jh) =
      some (.i32 (Algorithm.computeLeafNextGen8x8FastUInt w)) := by
  rcases hlut with ⟨lutAddr, arr, hstat, harr, hsz, htbl⟩
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  f1_split_val_fuel 120
  flat_step_blk AlgorithmLeanKt_f_Algorithm_computeLeafNextGen8x8FastUInt_prog
  repeat' (
    first
    | (f1_split_val_fuel 1; rw [runJvmValFast_invokestatic_step (stepStatic_getNextGen4x4Lut hstat)];
       f1_split_val_fuel 120; flat_step_blk AlgorithmLeanKt_f_Algorithm_computeLeafNextGen8x8FastUInt_prog)
    | (f1_split_val_fuel 1; rw [runJvmValFast_invokestatic_step (stepStatic_getNextGen4x4LutPkg hstat)];
       f1_split_val_fuel 120; flat_step_blk AlgorithmLeanKt_f_Algorithm_computeLeafNextGen8x8FastUInt_prog)
    | (f1_split_val_fuel 1; rw [runJvmValFast_baload_and65535 harr hsz];
       f1_split_val_fuel 120; flat_step_blk AlgorithmLeanKt_f_Algorithm_computeLeafNextGen8x8FastUInt_prog))
  repeat rw [lut_entry_and15 arr hsz htbl]
  rfl

theorem computeLeafNextGen8x8FastUInt_1_equiv (w : UInt64) (jh : Jvm.JvmHeap AlgExt)
    (hlut : HasNextGen4x4Lut jh) :
    runJvm 1200 FlatHashLifeLeanKt_f_Algorithm_computeLeafNextGen8x8FastUInt_prog
      (Jvm.initJvmState [(0, .i64 w)] (.i32 0) ⟨[], [], []⟩ jh) =
      some (.i32 (Algorithm.computeLeafNextGen8x8FastUInt w)) := by
  rcases hlut with ⟨lutAddr, arr, hstat, harr, hsz, htbl⟩
  apply runJvm_of_runJvmValFast0 _ _ _ _ rfl
  f1_split_val_fuel 120
  flat_step_blk FlatHashLifeLeanKt_f_Algorithm_computeLeafNextGen8x8FastUInt_prog
  repeat' (
    first
    | (f1_split_val_fuel 1; rw [runJvmValFast_invokestatic_step (stepStatic_getNextGen4x4LutPkg hstat)];
       f1_split_val_fuel 120; flat_step_blk FlatHashLifeLeanKt_f_Algorithm_computeLeafNextGen8x8FastUInt_prog)
    | (f1_split_val_fuel 1; rw [runJvmValFast_baload_and65535 harr hsz];
       f1_split_val_fuel 120; flat_step_blk FlatHashLifeLeanKt_f_Algorithm_computeLeafNextGen8x8FastUInt_prog))
  repeat rw [lut_entry_and15 arr hsz htbl]
  rfl

theorem computeLeafNextGen8x8FastUInt_2_equiv (w : UInt64) (jh : Jvm.JvmHeap AlgExt)
    (hlut : HasNextGen4x4Lut jh) :
    runJvm 1200 MacroCellLeanKt_f_Algorithm_computeLeafNextGen8x8FastUInt_prog
      (Jvm.initJvmState [(0, .i64 w)] (.i32 0) ⟨[], [], []⟩ jh) =
      some (.i32 (Algorithm.computeLeafNextGen8x8FastUInt w)) :=
  computeLeafNextGen8x8FastUInt_1_equiv w jh hlut

end Family1

end Algorithm.JvmVerification
