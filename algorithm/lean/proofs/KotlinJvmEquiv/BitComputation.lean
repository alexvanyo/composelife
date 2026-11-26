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

import KotlinJvmBytecode
import models.BitComputationModel
import theorems.BitComputationModelTheorems
import proofs.JvmEquiv.Infra
import proofs.JvmEquiv.FlatInfra
import proofs.JvmEquiv.Family1

local notation "ℤ" => Int

namespace Algorithm.KotlinJvmVerification
open Algorithm.JvmVerification
open Algorithm.KotlinJvmBytecode
open Algorithm.KotlinModel

/-- Heap invariant stating `BitComputationKt.QUAD_INFO_LUT` holds the 65536-entry `computeQuadInfoModel` table. -/
def HasQuadInfoLut (jh : Jvm.JvmHeap AlgExt) : Prop :=
  ∃ lutAddr arr,
    jh.getStatic? "com/alexvanyo/composelife/algorithm/BitComputationKt" "QUAD_INFO_LUT" = some (.heapRef lutAddr) ∧
    jh.get? lutAddr = some (.intArray arr) ∧
    arr.size = 65536 ∧
    ∀ (k : Nat), k < 65536 → arr[k]! = computeQuadInfoModel (UInt32.ofNat k)

private def isKcStopLeaf : JvmInstr → Bool
  | .invokestatic _ _ _ => true
  | .getstatic _ _ _ => true
  | .putstatic _ _ _ => true
  | .iaload => true
  | .baload => true
  | .iastore => true
  | .newarray _ => true
  | _ => false

private def stepKcChunk : Nat → Nat → Nat → List JvmInstr → JvmState → Jvm.BlockResChunkRes AlgExt AlgHeap :=
  Jvm.stepResBlockChunkWith algHooks isKcStopLeaf

private theorem runJvmResFast_stepKcChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmResFast fuel prog pc instrs st = afterResBlockChunk (stepKcChunk maxSteps fuel pc instrs st) prog :=
  Jvm.runJvmResFast_stepBlockChunkWith algHooks isKcStopLeaf maxSteps fuel prog pc instrs st

private theorem runJvmResFast_getstatic_some {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls fld desc : String} {rest : List JvmInstr} {pc0 : Nat} {v : JvmVal}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hgs : jh.getStatic? cls fld = some v) (hf : 1 ≤ f := by decide) :
    runJvmResFast f prog pc (.getstatic cls fld desc :: rest)
        ⟨pc0, stkRest, locs, jh, hp⟩ =
      runJvmResFast (f - 1) prog (pc + 1) rest ⟨pc + 1, v :: stkRest, locs, jh, hp⟩ := by
  cases f with
  | zero => simp at hf
  | succ f' =>
    simp only [Nat.succ_sub_one, runJvmResFast]
    exact Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp)
      (by dsimp only [Jvm.stepInstr]; rw [hgs]) rfl

private theorem runJvmResFast_setStatic {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls fld desc : String} {rest : List JvmInstr} {pc0 : Nat} {v : JvmVal}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.putstatic cls fld desc :: rest)
        ⟨pc0, v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stkRest, locs, jh.setStatic cls fld v, hp⟩ := by
  dsimp only [runJvmResFast]
  exact Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_if_icmpge_branch {f1 pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : b.toBitVec.sle a.toBitVec = true) :
    runJvmResFast (f1 + 1) prog pc (.if_icmpge target :: rest)
        ⟨pc, .i32 b :: .i32 a :: srest, locs, jh, hp⟩ =
      runJvmResFast f1 prog target (prog.drop target) ⟨target, srest, locs, jh, hp⟩ := by
  dsimp only [runJvmResFast]
  rw [Jvm.runJvmResFast_at_branch_cons algHooks (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpge]
  simp [h]

private theorem runJvmResFast_if_icmpge_fallthrough {f1 pc target : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : b.toBitVec.sle a.toBitVec = false) :
    runJvmResFast (f1 + 1) prog pc (.if_icmpge target :: rest)
        ⟨pc, .i32 b :: .i32 a :: srest, locs, jh, hp⟩ =
      runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  dsimp only [runJvmResFast]
  rw [Jvm.runJvmResFast_at_branch_cons algHooks (hbr := rfl), Jvm.evalResBranchInstrCons_if_icmpge]
  simp [h]

private theorem runJvmResFast_iaload {f : Nat} {prog : List JvmInstr} {pc : Nat} {rest : List JvmInstr}
    {pc0 : Nat} {idx : UInt32} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array UInt32}
    (hget : jh.get? addr = some (.intArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) (hf : 1 ≤ f := by decide) :
    runJvmResFast f prog pc (.iaload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast (f - 1) prog (pc + 1) rest
        ⟨pc + 1, .i32 elems[idx.toNat] :: stkRest, locs, jh, hp⟩ := by
  cases f with
  | zero => simp at hf
  | succ f' =>
    simp only [Nat.succ_sub_one]
    exact Jvm.runJvmResFast_iaload algHooks hget hslt hlt

private theorem runJvmResFast_baload {f : Nat} {prog : List JvmInstr} {pc : Nat} {rest : List JvmInstr}
    {pc0 : Nat} {idx : UInt32} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) (hf : 1 ≤ f := by decide) :
    runJvmResFast f prog pc (.baload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast (f - 1) prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofBitVec (elems[idx.toNat].toBitVec.signExtend 32)) :: stkRest, locs, jh, hp⟩ := by
  cases f with
  | zero => simp at hf
  | succ f' =>
    simp only [Nat.succ_sub_one]
    exact Jvm.runJvmResFast_baload algHooks hget hslt hlt

private theorem runJvmResFast_iastore {f : Nat} {prog : List JvmInstr} {pc : Nat} {rest : List JvmInstr}
    {pc0 : Nat} {v idx : UInt32} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array UInt32}
    (hget : jh.get? addr = some (.intArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    runJvmResFast (f + 1) prog pc (.iastore :: rest)
        ⟨pc0, .i32 v :: .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, stkRest, locs, jh.set addr (.intArray (elems.set idx.toNat v hlt)), hp⟩ :=
  Jvm.runJvmResFast_iastore algHooks hget hslt hlt

private theorem runJvmResFast_newarray_int {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {n : UInt32} {stkRest : List JvmVal} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    runJvmResFast (f + 1) prog pc (.newarray "int" :: rest) ⟨pc0, .i32 n :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
        (jh.alloc (.intArray (Array.replicate n.toNat 0))).2, hp⟩ :=
  Jvm.runJvmResFast_newarray_int algHooks hslt

private theorem runJvmResFast_ifne_branch {f1 pc target : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : (x == 0) = false) (hf : 1 ≤ f1 := by decide) :
    runJvmResFast f1 prog pc (.ifne target :: rest)
        ⟨pc, .i32 x :: srest, locs, jh, hp⟩ =
      runJvmResFast (f1 - 1) prog target (prog.drop target) ⟨target, srest, locs, jh, hp⟩ := by
  cases f1 with
  | zero => simp at hf
  | succ f' =>
    simp only [Nat.succ_sub_one, runJvmResFast]
    letI : Jvm.HasDefaultIsZero algHooks := ⟨rfl⟩
    exact Jvm.runJvmResFast_ifne_branch algHooks h

private theorem runJvmResFast_ifne_fallthrough {f1 pc target : Nat} {prog rest : List JvmInstr}
    {x : UInt32} {srest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : x = 0) (hf : 1 ≤ f1 := by decide) :
    runJvmResFast f1 prog pc (.ifne target :: rest)
        ⟨pc, .i32 x :: srest, locs, jh, hp⟩ =
      runJvmResFast (f1 - 1) prog (pc + 1) rest ⟨pc + 1, srest, locs, jh, hp⟩ := by
  cases f1 with
  | zero => simp at hf
  | succ f' =>
    simp only [Nat.succ_sub_one, runJvmResFast]
    letI : Jvm.HasDefaultIsZero algHooks := ⟨rfl⟩
    exact Jvm.runJvmResFast_ifne_fallthrough algHooks h

private theorem runJvmResFast_uintCtor {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 1 ≤ f := by decide) :
    runJvmResFast f prog pc
        (.invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast (f - 1) prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  cases f with
  | zero => simp at hf
  | succ f' =>
    simp only [Nat.succ_sub_one]
    rw [runJvmResFast_invokestatic_step (hs := rfl)]

private theorem runJvmResFast_invokestatic_step_n {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {cls m desc : String}
    {stk stk' : List JvmVal} {locs : Nat → JvmVal} {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hs : stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩ cls m desc = .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩))
    (hf : 1 ≤ f := by decide) :
    runJvmResFast f prog pc (.invokestatic cls m desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast (f - 1) prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ := by
  cases f with
  | zero => simp at hf
  | succ f' =>
    simp only [Nat.succ_sub_one]
    exact runJvmResFast_invokestatic_step (hs := hs)

private theorem val_of_map_fast0 {fuel : Nat} {prog : List JvmInstr} {st0 : JvmState}
    {v : JvmVal} (hpc : st0.pc = 0)
    (hmap : (runJvmResFast fuel prog 0 prog st0).map Prod.fst = some v) :
    runJvm fuel prog st0 = some v := by
  rw [runJvm_eq_runJvmRes]
  exact Jvm.runJvmRes_map_of_runJvmResFast0 algHooks Prod.fst fuel prog st0 v hpc hmap

private theorem exists_st_of_map_fast0 {fuel : Nat} {prog : List JvmInstr} {st0 : JvmState}
    {v : JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hpc : st0.pc = 0)
    (hmap : (runJvmResFast fuel prog 0 prog st0).map (fun p => (p.1, p.2.jvmHeap, p.2.heap)) =
      some (v, jh, hp)) :
    ∃ st', runJvmRes fuel prog st0 = some (v, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp := by
  have h1 := Jvm.runJvmRes_map_of_runJvmResFast0 algHooks (fun p => (p.1, p.2.jvmHeap, p.2.heap))
    fuel prog st0 (v, jh, hp) hpc hmap
  cases hr : runJvmRes fuel prog st0 with
  | none => simp [hr] at h1
  | some p =>
    simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    exact ⟨p.2, congrArg some (Prod.ext h1.1 rfl), h1.2.1, h1.2.2⟩

private theorem ui32_toNat_of_lt {n : Nat} (hn : n < 2 ^ 32) :
    (UInt32.ofNat n).toNat = n := by
  change (UInt32.ofBitVec (BitVec.ofNat 32 n)).toNat = n
  rw [UInt32.toNat_ofBitVec, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hn

private theorem ui32_toNat_of_lt_65536 {n : Nat} (hn : n < 65536) :
    (UInt32.ofNat n).toNat = n :=
  ui32_toNat_of_lt (by omega)

private theorem u32_slt_zero_of_lt {x : UInt32} (hx : x.toNat < 65536) :
    x.toBitVec.slt 0#32 = false := by
  rw [BitVec.slt]
  have h1 : x.toBitVec.toInt = (x.toNat : ℤ) := by
    rw [BitVec.toInt]
    have hlt : 2 * x.toNat < 2 ^ 32 := by omega
    rw [UInt32.toNat_toBitVec]
    simp [hlt]
  have h0 : (0#32 : BitVec 32).toInt = 0 := by decide
  rw [h1, h0]
  simp

private theorem slt_zero_false_of_lt_65536 {n : Nat} (hn : n < 65536) :
    (UInt32.ofNat n).toBitVec.slt 0#32 = false :=
  u32_slt_zero_of_lt (by rw [ui32_toNat_of_lt_65536 hn]; exact hn)

private theorem u32_and_65535_lt (x : UInt32) : (x &&& (65535 : UInt32)).toNat < 65536 := by
  have h1 : (x &&& (65535 : UInt32)).toNat ≤ 65535 := by
    rw [UInt32.toNat_and]
    exact Nat.le_trans Nat.and_le_right (by decide)
  omega

private theorem u64_ushr48_lt (w : UInt64) : (w >>> 48).toUInt32.toNat < 65536 := by
  have h : (w >>> 48).toNat < 65536 := by
    rw [UInt64.toNat_shiftRight]
    have : w.toNat < 2 ^ 64 := w.toBitVec.isLt
    change w.toNat >>> (48 % 64) < 65536
    rw [Nat.shiftRight_eq_div_pow]
    have hpow : 2 ^ (48 % 64) = 281474976710656 := by decide
    rw [hpow]
    omega
  rw [UInt64.toNat_toUInt32]
  have : (w >>> 48).toNat % 2 ^ 32 = (w >>> 48).toNat := Nat.mod_eq_of_lt (by omega)
  omega

private theorem u64_quad_and16_lt (w : UInt64) (s : UInt64) :
    ((w >>> s) &&& (65535 : UInt64)).toUInt32.toNat < 65536 := by
  have h : ((w >>> s) &&& (65535 : UInt64)).toNat ≤ 65535 := by
    rw [UInt64.toNat_and]
    exact Nat.le_trans Nat.and_le_right (by decide)
  rw [UInt64.toNat_toUInt32]
  have : ((w >>> s) &&& (65535 : UInt64)).toNat % 2 ^ 32 = ((w >>> s) &&& (65535 : UInt64)).toNat :=
    Nat.mod_eq_of_lt (by omega)
  omega

private theorem u64_and16_lt (w : UInt64) :
    (w &&& (65535 : UInt64)).toUInt32.toNat < 65536 := by
  have h : (w &&& (65535 : UInt64)).toNat ≤ 65535 := by
    rw [UInt64.toNat_and]
    exact Nat.le_trans Nat.and_le_right (by decide)
  rw [UInt64.toNat_toUInt32]
  have : (w &&& (65535 : UInt64)).toNat % 2 ^ 32 = (w &&& (65535 : UInt64)).toNat :=
    Nat.mod_eq_of_lt (by omega)
  omega

private theorem u32_slt_zero_of_lt' {x : UInt32} (hx : x.toNat < 65536) :
    x.toBitVec.slt 0#32 = false :=
  u32_slt_zero_of_lt hx

private theorem pack4x4_idx_lt (a b c d : UInt32) :
    (((a &&& (0xF : UInt32)) ||| ((b &&& (0xF : UInt32)) <<< 4) |||
      ((c &&& (0xF : UInt32)) <<< 8) ||| ((d &&& (0xF : UInt32)) <<< 12)) < (65536 : UInt32)) := by
  have ha : (a &&& (0xF : UInt32)) < 16 := by
    show (a &&& (0xF : UInt32)).toNat < 16
    rw [UInt32.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hb : (b &&& (0xF : UInt32)) < 16 := by
    show (b &&& (0xF : UInt32)).toNat < 16
    rw [UInt32.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hc : (c &&& (0xF : UInt32)) < 16 := by
    show (c &&& (0xF : UInt32)).toNat < 16
    rw [UInt32.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hd : (d &&& (0xF : UInt32)) < 16 := by
    show (d &&& (0xF : UInt32)).toNat < 16
    rw [UInt32.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  exact pk_lt_65536 _ _ _ _ ha hb hc hd

private theorem ng_lut_signExtend_eq (x : UInt32) :
    UInt32.ofBitVec ((Algorithm.computeNextGen4x4BitwiseUInt x).toUInt8.toBitVec.signExtend 32) =
      Algorithm.computeNextGen4x4BitwiseUInt x := by
  have hlt : (Algorithm.computeNextGen4x4BitwiseUInt x).toNat < 16 :=
    Algorithm.computeNextGen4x4UInt_lt_16 x
  apply UInt32.toBitVec_inj.mp
  ext i hi
  simp only [BitVec.getElem_signExtend]
  by_cases h8 : i < 8
  · simp [h8, BitVec.getLsbD_eq_getElem hi]
  · have hmsb : ((Algorithm.computeNextGen4x4BitwiseUInt x).toUInt8.toBitVec).msb = false := by
      rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_eq_getElem (by omega : 7 < 8),
        BitVec.getElem_eq_testBit_toNat, UInt8.toNat_toBitVec, UInt32.toNat_toUInt8]
      exact Nat.testBit_lt_two_pow (by omega : (Algorithm.computeNextGen4x4BitwiseUInt x).toNat % 256 < 2 ^ 7)
    have hhi : (Algorithm.computeNextGen4x4BitwiseUInt x).toBitVec[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, UInt32.toNat_toBitVec]
      have hpow : 16 ≤ 2 ^ i := by
        have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 8 ≤ i)
        omega
      exact Nat.testBit_lt_two_pow (by omega : (Algorithm.computeNextGen4x4BitwiseUInt x).toNat < 2 ^ i)
    simp only [h8, ↓reduceDIte, hmsb]
    exact hhi.symm

private theorem evalPureKotlinFromHeap_eq_model (jh : Jvm.JvmHeap AlgExt) (w : UInt64)
    (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
    evalPureKotlinFromHeap jh w = some (computeNextGenerationPureKotlinModel w) := by
  by_cases hw : w = 0
  · subst hw; rfl
  · rcases hqi with ⟨qiAddr, qiArr, hqiStatic, hqiObj, hqiSz, hqiSpec⟩
    rcases hng with ⟨ngAddr, ngArr, hngStatic, hngObj, hngSz, hngSpec⟩
    have hbeq : (w == 0) = false := beq_false_of_ne hw
    have hq0 : (w &&& (0xFFFF : UInt64)).toUInt32.toNat < qiArr.size := by
      have := u64_and16_lt w; omega
    have hq1 : ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32.toNat < qiArr.size := by
      have := u64_quad_and16_lt w 16; omega
    have hq2 : ((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32.toNat < qiArr.size := by
      have := u64_quad_and16_lt w 32; omega
    have hq3 : (w >>> 48).toUInt32.toNat < qiArr.size := by
      have := u64_ushr48_lt w; omega
    have hinfo0 : qiArr[(w &&& (0xFFFF : UInt64)).toUInt32.toNat] =
        computeQuadInfoModel (w &&& (0xFFFF : UInt64)).toUInt32 := by
      have h := hqiSpec _ (by rw [← hqiSz]; exact hq0)
      rw [getElem!_pos qiArr _ hq0, UInt32.ofNat_toNat] at h
      exact h
    have hinfo1 : qiArr[((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32.toNat] =
        computeQuadInfoModel ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32 := by
      have h := hqiSpec _ (by rw [← hqiSz]; exact hq1)
      rw [getElem!_pos qiArr _ hq1, UInt32.ofNat_toNat] at h
      exact h
    have hinfo2 : qiArr[((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32.toNat] =
        computeQuadInfoModel ((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32 := by
      have h := hqiSpec _ (by rw [← hqiSz]; exact hq2)
      rw [getElem!_pos qiArr _ hq2, UInt32.ofNat_toNat] at h
      exact h
    have hinfo3 : qiArr[(w >>> 48).toUInt32.toNat] =
        computeQuadInfoModel (w >>> 48).toUInt32 := by
      have h := hqiSpec _ (by rw [← hqiSz]; exact hq3)
      rw [getElem!_pos qiArr _ hq3, UInt32.ofNat_toNat] at h
      exact h
    unfold evalPureKotlinFromHeap
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, hqiStatic, hngStatic, hqiObj, hngObj]
    simp only [hq0, hq1, hq2, hq3, ↓reduceDIte, hinfo0, hinfo1, hinfo2, hinfo3]
    let info0 := computeQuadInfoModel (w &&& (0xFFFF : UInt64)).toUInt32
    let info1 := computeQuadInfoModel ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32
    let info2 := computeQuadInfoModel ((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32
    let info3 := computeQuadInfoModel (w >>> 48).toUInt32
    let n00 := info0 &&& (0xF : UInt32)
    let n02 := info1 &&& (0xF : UInt32)
    let n20 := info2 &&& (0xF : UInt32)
    let n22 := info3 &&& (0xF : UInt32)
    let n01 := ((info0 >>> 4) &&& (0x5 : UInt32)) ||| ((info1 >>> 8) &&& (0xA : UInt32))
    let n21 := ((info2 >>> 4) &&& (0x5 : UInt32)) ||| ((info3 >>> 8) &&& (0xA : UInt32))
    let n10 := ((info0 >>> 12) &&& (0x3 : UInt32)) ||| ((info2 >>> 16) &&& (0xC : UInt32))
    let n12 := ((info1 >>> 12) &&& (0x3 : UInt32)) ||| ((info3 >>> 16) &&& (0xC : UInt32))
    let n11 := ((info0 >>> 20) &&& (1 : UInt32)) ||| ((info1 >>> 20) &&& (2 : UInt32)) |||
      ((info2 >>> 20) &&& (4 : UInt32)) ||| ((info3 >>> 20) &&& (8 : UInt32))
    have hlt_sub : ∀ (a b c d : UInt32),
        a < 16 → b < 16 → c < 16 → d < 16 →
        (a ||| (b <<< 4) ||| (c <<< 8) ||| (d <<< 12)).toNat < ngArr.size := by
      intro a b c d ha hb hc hd
      have h : (a ||| (b <<< 4) ||| (c <<< 8) ||| (d <<< 12)) < (65536 : UInt32) :=
        pk_lt_65536 a b c d ha hb hc hd
      change (a ||| (b <<< 4) ||| (c <<< 8) ||| (d <<< 12)).toNat < (65536 : UInt32).toNat at h
      have h65 : (65536 : UInt32).toNat = 65536 := by decide
      rw [h65] at h
      omega
    have hm16 : ∀ (x m : UInt32), m ≤ 15 → (x &&& m) < 16 := by
      intro x m hm
      change (x &&& m).toNat < 16
      rw [UInt32.toNat_and]
      exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_succ_of_le hm)
    have hmo16 : ∀ (x m1 y m2 : UInt32), m1 ≤ 15 → m2 ≤ 15 → ((x &&& m1) ||| (y &&& m2)) < 16 := by
      intro x m1 y m2 hm1 hm2
      change ((x &&& m1) ||| (y &&& m2)).toNat < 2 ^ 4
      rw [UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_and]
      have h1 : x.toNat &&& m1.toNat < 2 ^ 4 := Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_succ_of_le hm1)
      have h2 : y.toNat &&& m2.toNat < 2 ^ 4 := Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_succ_of_le hm2)
      exact Nat.or_lt_two_pow h1 h2
    have hn00 : n00 < 16 := hm16 _ _ (by decide)
    have hn02 : n02 < 16 := hm16 _ _ (by decide)
    have hn20 : n20 < 16 := hm16 _ _ (by decide)
    have hn22 : n22 < 16 := hm16 _ _ (by decide)
    have hn01 : n01 < 16 := hmo16 _ _ _ _ (by decide) (by decide)
    have hn21 : n21 < 16 := hmo16 _ _ _ _ (by decide) (by decide)
    have hn10 : n10 < 16 := hmo16 _ _ _ _ (by decide) (by decide)
    have hn12 : n12 < 16 := hmo16 _ _ _ _ (by decide) (by decide)
    have hn11 : n11 < 16 := by
      have h12 := hmo16 (info0 >>> 20) 1 (info1 >>> 20) 2 (by decide) (by decide)
      change (((info0 >>> 20) &&& (1 : UInt32)) ||| ((info1 >>> 20) &&& (2 : UInt32))).toNat < 2 ^ 4 at h12
      have h123 : ((((info0 >>> 20) &&& (1 : UInt32)) ||| ((info1 >>> 20) &&& (2 : UInt32))) |||
          ((info2 >>> 20) &&& (4 : UInt32))).toNat < 2 ^ 4 := by
        rw [UInt32.toNat_or, UInt32.toNat_and]
        exact Nat.or_lt_two_pow h12 (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))
      change n11.toNat < 2 ^ 4
      dsimp only [n11]
      rw [UInt32.toNat_or, UInt32.toNat_and]
      exact Nat.or_lt_two_pow h123 (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))
    have hnw : (n00 ||| (n01 <<< 4) ||| (n10 <<< 8) ||| (n11 <<< 12)).toNat < ngArr.size :=
      hlt_sub _ _ _ _ hn00 hn01 hn10 hn11
    have hne : (n01 ||| (n02 <<< 4) ||| (n11 <<< 8) ||| (n12 <<< 12)).toNat < ngArr.size :=
      hlt_sub _ _ _ _ hn01 hn02 hn11 hn12
    have hsw : (n10 ||| (n11 <<< 4) ||| (n20 <<< 8) ||| (n21 <<< 12)).toNat < ngArr.size :=
      hlt_sub _ _ _ _ hn10 hn11 hn20 hn21
    have hse : (n11 ||| (n12 <<< 4) ||| (n21 <<< 8) ||| (n22 <<< 12)).toNat < ngArr.size :=
      hlt_sub _ _ _ _ hn11 hn12 hn21 hn22
    have hget_ng : ∀ (x : UInt32) (hx : x.toNat < ngArr.size),
        UInt32.ofBitVec (ngArr[x.toNat].toBitVec.signExtend 32) =
          Algorithm.computeNextGen4x4BitwiseUInt x := by
      intro x hx
      have hs := hngSpec x.toNat (by rw [← hngSz]; exact hx)
      rw [getElem!_pos ngArr _ hx, UInt32.ofNat_toNat] at hs
      rw [hs]
      exact ng_lut_signExtend_eq x
    rw [dite_eq_left_of_eq_true (eq_true hnw), dite_eq_left_of_eq_true (eq_true hne),
      dite_eq_left_of_eq_true (eq_true hsw), dite_eq_left_of_eq_true (eq_true hse)]
    rw [hget_ng _ hnw, hget_ng _ hne, hget_ng _ hsw, hget_ng _ hse]
    simp only [computeNextGenerationPureKotlinModel, computeNextGenerationPureKotlinModelWith, hbeq,
      Bool.false_eq_true, ↓reduceIte]
    rfl

/-- Equivalence theorem for `BitComputationKt.computeQuadInfo`. -/
theorem computeQuadInfo_res_equiv (q : UInt32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ st',
      runJvmRes 150 BitComputationKt_computeQuadInfo_prog (Jvm.initJvmState [(0, .i32 q)] (.i32 0) hp jh) =
        some (.i32 (computeQuadInfoModel q), st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  apply exists_st_of_map_fast0 rfl
  conv =>
    lhs
    arg 2
    rw [runJvmResFast_stepKcChunk 35]
    arg 1
    jvm_whnf_blk
  conv =>
    lhs
    arg 2
    rw [afterResBlockChunk_cont, runJvmResFast_stepKcChunk 35]
    arg 1
    jvm_whnf_blk
  conv =>
    lhs
    arg 2
    rw [afterResBlockChunk_cont, runJvmResFast_stepKcChunk 35]
    arg 1
    jvm_whnf_blk
  conv =>
    lhs
    arg 2
    rw [afterResBlockChunk_cont, runJvmResFast_stepKcChunk 35]
    arg 1
    jvm_whnf_blk
  rw [afterResBlockChunk_done]
  rfl

theorem computeQuadInfo_equiv (q : UInt32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    runJvm 150 BitComputationKt_computeQuadInfo_prog (Jvm.initJvmState [(0, .i32 q)] (.i32 0) hp jh) =
      some (.i32 (computeQuadInfoModel q)) := by
  rw [runJvm_eq_runJvmRes]
  rcases computeQuadInfo_res_equiv q jh hp with ⟨st', hrun, _⟩
  rw [hrun]
  rfl

/-- Equivalence theorem for `BitComputationKt.computeNextGen4x4`. -/
theorem computeNextGen4x4_equiv (w : UInt32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hlut : HasNextGen4x4Lut jh) :
    runJvm 30 BitComputationKt_computeNextGen4x4_prog (Jvm.initJvmState [(0, .i32 w)] (.i32 0) hp jh) =
      some (.i32 (Algorithm.computeNextGen4x4BitwiseUInt (w &&& 0xFFFF) &&& 0xF)) := by
  rcases hlut with ⟨lutAddr, lutArr, hstat, hobj, hsz, hspec⟩
  have hlt65536 : (w &&& (65535 : UInt32)).toNat < 65536 := u32_and_65535_lt w
  have hlt : (w &&& (65535 : UInt32)).toNat < lutArr.size := by omega
  have hslt : (w &&& (65535 : UInt32)).toBitVec.slt 0#32 = false := u32_slt_zero_of_lt hlt65536
  have helem : lutArr[(w &&& (65535 : UInt32)).toNat] =
      (Algorithm.computeNextGen4x4BitwiseUInt (w &&& (65535 : UInt32))).toUInt8 := by
    have h := hspec _ hlt65536
    rw [getElem!_pos lutArr _ hlt, UInt32.ofNat_toNat] at h
    exact h
  apply val_of_map_fast0 rfl
  dsimp only [Jvm.initJvmState, List.foldl]
  conv =>
    lhs
    arg 2
    rw [runJvmResFast_stepKcChunk 10]
    arg 1
    jvm_whnf_blk
  conv =>
    lhs
    arg 2
    rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step_n
      (hs := stepStatic_getNextGen4x4LutPkg hstat)]
    rw [runJvmResFast_stepKcChunk 10]
    arg 1
    jvm_whnf_blk
  conv =>
    lhs
    arg 2
    rw [afterResBlockChunk_cont]
    norm_jvm_locals
    jvm_whnf_run_args
    rw [runJvmResFast_uintCtor, runJvmResFast_baload hobj hslt hlt,
      runJvmResFast_uintCtor]
    rw [runJvmResFast_stepKcChunk 10]
    arg 1
    jvm_whnf_blk
  conv =>
    lhs
    arg 2
    rw [afterResBlockChunk_cont, runJvmResFast_uintCtor]
    rw [runJvmResFast_stepKcChunk 10]
    arg 1
    jvm_whnf_blk
  rw [afterResBlockChunk_done, helem, ng_lut_signExtend_eq]
  rfl

/-- Equivalence theorem for `Long.computeNextGenerationPureKotlin`. -/
theorem computeNextGenerationPureKotlin_res_equiv (w : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
    ∃ st',
      runJvmRes 250 BitComputationKt_computeNextGenerationPureKotlin_prog (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
        some (.i32 (computeNextGenerationPureKotlinModel w), st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  by_cases hw : w = 0
  · subst hw
    apply exists_st_of_map_fast0 rfl
    dsimp only [Jvm.initJvmState, List.foldl]
    conv =>
      lhs
      arg 2
      rw [runJvmResFast_stepKcChunk 10]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      change runJvmResFast 247 BitComputationKt_computeNextGenerationPureKotlin_prog 3
        (.ifne 6 :: BitComputationKt_computeNextGenerationPureKotlin_prog.drop 4)
        ⟨3, [.i32 0], Jvm.setLocal (fun _ => .i32 0) 0 (.i64 0), jh, hp⟩
      rw [runJvmResFast_ifne_fallthrough rfl]
      rw [runJvmResFast_stepKcChunk 10]
      arg 1
      jvm_whnf_blk
    rw [afterResBlockChunk_done]
    rfl
  · rcases hqi with ⟨qiAddr, qiArr, hqiStatic, hqiObj, hqiSz, hqiSpec⟩
    rcases hng with ⟨ngAddr, ngArr, hngStatic, hngObj, hngSz, hngSpec⟩
    have hq0_lt := u64_and16_lt w
    have hq1_lt := u64_quad_and16_lt w 16
    have hq2_lt := u64_quad_and16_lt w 32
    have hq3_lt := u64_ushr48_lt w
    have hq0_sz : (w &&& (65535 : UInt64)).toUInt32.toNat < qiArr.size := by omega
    have hq1_sz : ((w >>> 16) &&& (65535 : UInt64)).toUInt32.toNat < qiArr.size := by omega
    have hq2_sz : ((w >>> 32) &&& (65535 : UInt64)).toUInt32.toNat < qiArr.size := by omega
    have hq3_sz : (w >>> 48).toUInt32.toNat < qiArr.size := by omega
    have hq0_slt := u32_slt_zero_of_lt hq0_lt
    have hq1_slt := u32_slt_zero_of_lt hq1_lt
    have hq2_slt := u32_slt_zero_of_lt hq2_lt
    have hq3_slt := u32_slt_zero_of_lt hq3_lt
    have hi0 : qiArr[(w &&& (65535 : UInt64)).toUInt32.toNat] =
        computeQuadInfoModel (w &&& (0xFFFF : UInt64)).toUInt32 := by
      have h := hqiSpec _ hq0_lt
      rw [getElem!_pos qiArr _ hq0_sz, UInt32.ofNat_toNat] at h
      exact h
    have hi1 : qiArr[((w >>> 16) &&& (65535 : UInt64)).toUInt32.toNat] =
        computeQuadInfoModel ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32 := by
      have h := hqiSpec _ hq1_lt
      rw [getElem!_pos qiArr _ hq1_sz, UInt32.ofNat_toNat] at h
      exact h
    have hi2 : qiArr[((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32.toNat] =
        computeQuadInfoModel ((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32 := by
      have h := hqiSpec _ hq2_lt
      rw [getElem!_pos qiArr _ hq2_sz, UInt32.ofNat_toNat] at h
      exact h
    have hi3 : qiArr[(w >>> 48).toUInt32.toNat] =
        computeQuadInfoModel (w >>> 48).toUInt32 := by
      have h := hqiSpec _ hq3_lt
      rw [getElem!_pos qiArr _ hq3_sz, UInt32.ofNat_toNat] at h
      exact h
    have hlcmp : ((if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0) = false := by
      have hb : (w == 0) = false := beq_false_of_ne hw
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      cases w.toBitVec.slt 0#64 <;> decide
    let info0 := computeQuadInfoModel (w &&& (0xFFFF : UInt64)).toUInt32
    let info1 := computeQuadInfoModel ((w >>> 16) &&& (0xFFFF : UInt64)).toUInt32
    let info2 := computeQuadInfoModel ((w >>> 32) &&& (0xFFFF : UInt64)).toUInt32
    let info3 := computeQuadInfoModel (w >>> 48).toUInt32
    let n00 := info0 &&& (15 : UInt32)
    let n02 := info1 &&& (15 : UInt32)
    let n20 := info2 &&& (15 : UInt32)
    let n22 := info3 &&& (15 : UInt32)
    let n01 := ((info0 >>> 4) &&& (5 : UInt32)) ||| ((info1 >>> 8) &&& (10 : UInt32))
    let n21 := ((info2 >>> 4) &&& (5 : UInt32)) ||| ((info3 >>> 8) &&& (10 : UInt32))
    let n10 := ((info0 >>> 12) &&& (3 : UInt32)) ||| ((info2 >>> 16) &&& (12 : UInt32))
    let n12 := ((info1 >>> 12) &&& (3 : UInt32)) ||| ((info3 >>> 16) &&& (12 : UInt32))
    let n11 := ((info0 >>> 20) &&& (1 : UInt32)) ||| ((info1 >>> 20) &&& (2 : UInt32)) |||
      ((info2 >>> 20) &&& (4 : UInt32)) ||| ((info3 >>> 20) &&& (8 : UInt32))
    have hidx_lt : ∀ (a b c d : UInt32),
        a < 16 → b < 16 → c < 16 → d < 16 →
        (a ||| (b <<< 4) ||| (c <<< 8) ||| (d <<< 12)).toNat < 65536 := by
      intro a b c d ha hb hc hd
      exact pk_lt_65536 a b c d ha hb hc hd
    have hm : ∀ (x m : UInt32), m ≤ 15 → (x &&& m) < 16 := by
      intro x m hm
      change (x &&& m).toNat < 16
      rw [UInt32.toNat_and]
      exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_succ_of_le hm)
    have hmo : ∀ (x m1 y m2 : UInt32), m1 ≤ 15 → m2 ≤ 15 → ((x &&& m1) ||| (y &&& m2)) < 16 := by
      intro x m1 y m2 hm1 hm2
      change ((x &&& m1) ||| (y &&& m2)).toNat < 2 ^ 4
      rw [UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_and]
      exact Nat.or_lt_two_pow
        (Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_succ_of_le hm1))
        (Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_succ_of_le hm2))
    have hn00 : n00 < 16 := hm _ _ (by decide)
    have hn02 : n02 < 16 := hm _ _ (by decide)
    have hn20 : n20 < 16 := hm _ _ (by decide)
    have hn22 : n22 < 16 := hm _ _ (by decide)
    have hn01 : n01 < 16 := hmo _ _ _ _ (by decide) (by decide)
    have hn21 : n21 < 16 := hmo _ _ _ _ (by decide) (by decide)
    have hn10 : n10 < 16 := hmo _ _ _ _ (by decide) (by decide)
    have hn12 : n12 < 16 := hmo _ _ _ _ (by decide) (by decide)
    have hn11 : n11 < 16 := by
      have h12 : (((info0 >>> 20) &&& (1 : UInt32)) ||| ((info1 >>> 20) &&& (2 : UInt32))).toNat < 2 ^ 4 :=
        hmo (info0 >>> 20) 1 (info1 >>> 20) 2 (by decide) (by decide)
      have h123 : ((((info0 >>> 20) &&& (1 : UInt32)) ||| ((info1 >>> 20) &&& (2 : UInt32))) |||
          ((info2 >>> 20) &&& (4 : UInt32))).toNat < 2 ^ 4 := by
        rw [UInt32.toNat_or, UInt32.toNat_and]
        exact Nat.or_lt_two_pow h12 (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))
      show n11.toNat < 2 ^ 4
      dsimp only [n11]
      rw [UInt32.toNat_or, UInt32.toNat_and]
      exact Nat.or_lt_two_pow h123 (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))
    have hnw65 := hidx_lt _ _ _ _ hn00 hn01 hn10 hn11
    have hne65 := hidx_lt _ _ _ _ hn01 hn02 hn11 hn12
    have hsw65 := hidx_lt _ _ _ _ hn10 hn11 hn20 hn21
    have hse65 := hidx_lt _ _ _ _ hn11 hn12 hn21 hn22
    have hnw_sz : (n00 ||| (n01 <<< 4) ||| (n10 <<< 8) ||| (n11 <<< 12)).toNat < ngArr.size :=
      Nat.lt_of_lt_of_eq hnw65 hngSz.symm
    have hne_sz : (n01 ||| (n02 <<< 4) ||| (n11 <<< 8) ||| (n12 <<< 12)).toNat < ngArr.size :=
      Nat.lt_of_lt_of_eq hne65 hngSz.symm
    have hsw_sz : (n10 ||| (n11 <<< 4) ||| (n20 <<< 8) ||| (n21 <<< 12)).toNat < ngArr.size :=
      Nat.lt_of_lt_of_eq hsw65 hngSz.symm
    have hse_sz : (n11 ||| (n12 <<< 4) ||| (n21 <<< 8) ||| (n22 <<< 12)).toNat < ngArr.size :=
      Nat.lt_of_lt_of_eq hse65 hngSz.symm
    have hnw_slt := u32_slt_zero_of_lt hnw65
    have hne_slt := u32_slt_zero_of_lt hne65
    have hsw_slt := u32_slt_zero_of_lt hsw65
    have hse_slt := u32_slt_zero_of_lt hse65
    have hng_elem : ∀ (x : UInt32) (hx : x.toNat < 65536) (hsz : x.toNat < ngArr.size),
        UInt32.ofBitVec (ngArr[x.toNat].toBitVec.signExtend 32) =
          Algorithm.computeNextGen4x4BitwiseUInt x := by
      intro x hx hsz
      have h := hngSpec x.toNat hx
      rw [getElem!_pos ngArr _ hsz, UInt32.ofNat_toNat] at h
      rw [h]
      exact ng_lut_signExtend_eq x
    have hsh16_64 : ((16 : UInt32) &&& 63).toUInt64 = 16 := by decide
    have hsh32_64 : ((32 : UInt32) &&& 63).toUInt64 = 32 := by decide
    have hsh48_64 : ((48 : UInt32) &&& 63).toUInt64 = 48 := by decide
    have hsh4_32 : (4 : UInt32) &&& 31 = 4 := by decide
    have hsh8_32 : (8 : UInt32) &&& 31 = 8 := by decide
    have hsh12_32 : (12 : UInt32) &&& 31 = 12 := by decide
    have hsh16_32 : (16 : UInt32) &&& 31 = 16 := by decide
    have hsh20_32 : (20 : UInt32) &&& 31 = 20 := by decide
    apply exists_st_of_map_fast0 rfl
    dsimp only [Jvm.initJvmState, List.foldl]
    conv =>
      lhs
      arg 2
      rw [runJvmResFast_stepKcChunk 10]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      change runJvmResFast 247 BitComputationKt_computeNextGenerationPureKotlin_prog 3
        (.ifne 6 :: BitComputationKt_computeNextGenerationPureKotlin_prog.drop 4)
        ⟨3, [.i32 (if (w == 0) = true then 0 else if w.toBitVec.slt 0#64 = true then 4294967295 else 1)],
          Jvm.setLocal (fun _ => .i32 0) 0 (.i64 w), jh, hp⟩
      rw [runJvmResFast_ifne_branch hlcmp]
      rw [runJvmResFast_stepKcChunk 30]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      norm_jvm_locals
      jvm_whnf_run_args
      rw [runJvmResFast_getstatic_some hqiStatic]
      rw [runJvmResFast_stepKcChunk 10]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      norm_jvm_locals
      jvm_whnf_run_args
      rw [runJvmResFast_iaload hqiObj hq0_slt hq0_sz]
      rw [runJvmResFast_stepKcChunk 10]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      norm_jvm_locals
      jvm_whnf_run_args
      simp only [hsh16_64]
      rw [runJvmResFast_iaload hqiObj hq1_slt hq1_sz]
      rw [runJvmResFast_stepKcChunk 10]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      norm_jvm_locals
      jvm_whnf_run_args
      simp only [hsh16_64, hsh32_64]
      rw [runJvmResFast_iaload hqiObj hq2_slt hq2_sz]
      rw [runJvmResFast_stepKcChunk 10]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      norm_jvm_locals
      jvm_whnf_run_args
      simp only [hsh16_64, hsh32_64, hsh48_64]
      rw [runJvmResFast_iaload hqiObj hq3_slt hq3_sz]
      rw [hi0, hi1, hi2, hi3]
      rw [runJvmResFast_stepKcChunk 30]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      norm_jvm_locals
      jvm_whnf_run_args
      rw [runJvmResFast_stepKcChunk 30]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      norm_jvm_locals
      jvm_whnf_run_args
      rw [runJvmResFast_stepKcChunk 35]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      norm_jvm_locals
      jvm_whnf_run_args
      rw [runJvmResFast_invokestatic_step_n
        (hs := stepStatic_getNextGen4x4LutPkg hngStatic)]
      rw [runJvmResFast_stepKcChunk 20]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      norm_jvm_locals
      jvm_whnf_run_args
      simp only [hsh4_32, hsh8_32, hsh12_32, hsh16_32, hsh20_32]
      rw [runJvmResFast_baload hngObj hnw_slt hnw_sz]
      rw [runJvmResFast_stepKcChunk 20]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      norm_jvm_locals
      jvm_whnf_run_args
      simp only [hsh4_32, hsh8_32, hsh12_32, hsh16_32, hsh20_32]
      rw [runJvmResFast_baload hngObj hne_slt hne_sz]
      rw [runJvmResFast_stepKcChunk 20]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      norm_jvm_locals
      jvm_whnf_run_args
      simp only [hsh4_32, hsh8_32, hsh12_32, hsh16_32, hsh20_32]
      rw [runJvmResFast_baload hngObj hsw_slt hsw_sz]
      rw [runJvmResFast_stepKcChunk 20]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_cont]
      norm_jvm_locals
      jvm_whnf_run_args
      simp only [hsh4_32, hsh8_32, hsh12_32, hsh16_32, hsh20_32]
      rw [runJvmResFast_baload hngObj hse_slt hse_sz]
      rw [runJvmResFast_stepKcChunk 20]
      arg 1
      jvm_whnf_blk
    conv =>
      lhs
      arg 2
      rw [afterResBlockChunk_done]
      norm_jvm_locals
      jvm_whnf_run_args
    rw [hng_elem _ hnw65 hnw_sz, hng_elem _ hne65 hne_sz,
      hng_elem _ hsw65 hsw_sz, hng_elem _ hse65 hse_sz]
    simp only [hsh4_32, hsh8_32, hsh12_32,
      computeNextGenerationPureKotlinModel, computeNextGenerationPureKotlinModelWith,
      beq_false_of_ne hw, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem computeNextGenerationPureKotlin_equiv (w : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
    runJvm 250 BitComputationKt_computeNextGenerationPureKotlin_prog (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
      some (.i32 (computeNextGenerationPureKotlinModel w)) := by
  rw [runJvm_eq_runJvmRes]
  rcases computeNextGenerationPureKotlin_res_equiv w jh hp hqi hng with ⟨st', hrun, _⟩
  rw [hrun]
  rfl

/-- Equivalence theorem for `ULong.computeNextGenerationPureKotlin` (`-VKZWuLQ` bridge). -/
theorem computeNextGenerationPureKotlin_1_equiv (w : UInt64) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh) :
    runJvm 10 BitComputationKt_computeNextGenerationPureKotlin_1_prog (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) =
      some (.i32 (computeNextGenerationPureKotlinModel w)) := by
  have hev := evalPureKotlinFromHeap_eq_model jh w hqi hng
  have hs : stepInvokeStatic ⟨1, [.i64 w], Jvm.setLocal (fun _ => .i32 0) 0 (.i64 w), jh, hp⟩
      "com/alexvanyo/composelife/algorithm/BitComputationKt" "computeNextGenerationPureKotlin" "(J)I" =
      .inl (some ⟨2, [.i32 (computeNextGenerationPureKotlinModel w)],
        Jvm.setLocal (fun _ => .i32 0) 0 (.i64 w), jh, hp⟩) := by
    have hfn : stepInvokeStatic ⟨1, [.i64 w], Jvm.setLocal (fun _ => .i32 0) 0 (.i64 w), jh, hp⟩
        "com/alexvanyo/composelife/algorithm/BitComputationKt" "computeNextGenerationPureKotlin" "(J)I" =
        match evalPureKotlinFromHeap jh w with
        | some r => .inl (some ⟨2, [.i32 r], Jvm.setLocal (fun _ => .i32 0) 0 (.i64 w), jh, hp⟩)
        | none => .inr none := rfl
    rw [hfn, hev]
  apply val_of_map_fast0 rfl
  dsimp only [Jvm.initJvmState, List.foldl]
  conv =>
    lhs
    arg 2
    rw [runJvmResFast_stepKcChunk 5]
    arg 1
    jvm_whnf_blk
  conv =>
    lhs
    arg 2
    rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step_n (hs := hs)]
    rw [runJvmResFast_stepKcChunk 5]
    arg 1
    jvm_whnf_blk
  rw [afterResBlockChunk_done]
  rfl

private def clinitArrAt (k : Nat) : Array UInt32 :=
  Array.ofFn (n := 65536) fun i => if i.val < k then computeQuadInfoModel (UInt32.ofNat i.val) else 0

private def clinitJH (k : Nat) : Jvm.JvmHeap AlgExt :=
  (({} : Jvm.JvmHeap AlgExt).alloc (.intArray (clinitArrAt k))).2

private theorem clinitArr_sz (k : Nat) : (clinitArrAt k).size = 65536 := by
  simp [clinitArrAt]

private theorem clinitArr_set (k : Nat) (hk : k < 65536) :
    (clinitArrAt k).set k (computeQuadInfoModel (UInt32.ofNat k)) (by rw [clinitArr_sz]; exact hk) =
      clinitArrAt (k + 1) := by
  apply Array.ext
  · simp only [Array.size_set, clinitArrAt, Array.size_ofFn]
  · intro i hi1 hi2
    simp only [Array.getElem_set, clinitArrAt, Array.getElem_ofFn]
    by_cases hki : k = i
    · subst hki; simp
    · have : (i < k + 1) = (i < k) := propext ⟨fun h => by omega, fun h => by omega⟩
      simp [hki, this]

private theorem clinitJH_get0 (k : Nat) : (clinitJH k).get? 0 = some (.intArray (clinitArrAt k)) := by
  simp [clinitJH, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]

private theorem clinitArr_zero : Array.replicate 65536 (0 : UInt32) = clinitArrAt 0 := by
  apply Array.ext
  · simp [clinitArrAt]
  · intro i hi1 hi2
    simp [clinitArrAt, Array.getElem_replicate]

private theorem clinitJH_zero :
    (({} : Jvm.JvmHeap AlgExt).alloc (.intArray (Array.replicate 65536 0))).2 = clinitJH 0 := by
  rw [clinitArr_zero]
  rfl

/-- Class initializer equivalence for `BitComputationKt.<clinit>`: populates `QUAD_INFO_LUT` with `computeQuadInfoModel`. -/
theorem clinit_BitComputationKt_equiv :
    ∃ st',
      runJvmRes 800000 BitComputationKt_clinit_prog ⟨0, [], fun _ => .i32 0, {}, ⟨[], [], []⟩⟩ =
        some (.unit, st') ∧
      HasQuadInfoLut st'.jvmHeap := by
  have hloop : ∀ (d : Nat) (hd : d ≤ 65536) (f : Nat) (locs : Nat → JvmVal),
      locs 0 = .i32 (UInt32.ofNat (65536 - d)) →
      locs 1 = .heapRef 0 →
      ∃ st',
        runJvmResFast (f + 6 + d * 12) BitComputationKt_clinit_prog 5
            (BitComputationKt_clinit_prog.drop 5)
            ⟨5, [], locs, clinitJH (65536 - d), ⟨[], [], []⟩⟩ =
          some (.unit, st') ∧
        HasQuadInfoLut st'.jvmHeap := by
    intro d hd
    induction d with
    | zero =>
      intro f locs hl0 hl1
      simp only [Nat.sub_zero, Nat.zero_mul, Nat.add_zero] at hl0 ⊢
      refine ⟨⟨19, [], locs, (clinitJH 65536).setStatic "com/alexvanyo/composelife/algorithm/BitComputationKt" "QUAD_INFO_LUT" (.heapRef 0),
          ⟨[], [], []⟩⟩, ?_, ?_⟩
      · rw [show f + 6 = f + 4 + 2 by omega, runJvmResFast_stepKcChunk 2]
        (conv => lhs; arg 1; jvm_whnf_blk)
        simp only [hl0]
        rw [afterResBlockChunk_cont, runJvmResFast_if_icmpge_branch (by decide)]
        rw [show f + 3 = f + 2 + 1 by omega, runJvmResFast_stepKcChunk 1]
        (conv => lhs; arg 1; jvm_whnf_blk)
        simp only [hl1]
        rw [afterResBlockChunk_cont, runJvmResFast_setStatic]
        rw [runJvmResFast_stepKcChunk 1]
        (conv => lhs; arg 1; jvm_whnf_blk)
        rfl
      · refine ⟨0, clinitArrAt 65536, ?_, ?_, clinitArr_sz 65536, ?_⟩
        · simp [Jvm.JvmHeap.setStatic, Jvm.JvmHeap.getStatic?]
        · simp only [Jvm.JvmHeap.setStatic]; exact clinitJH_get0 65536
        · intro k hk
          rw [getElem!_pos (clinitArrAt 65536) k (by rw [clinitArr_sz]; exact hk)]
          simp only [clinitArrAt, Array.getElem_ofFn, hk, ↓reduceIte]
    | succ d ih =>
      intro f locs hl0 hl1
      have hkd : 65536 - (d + 1) < 65536 := by omega
      have hsle_cmp : ((65536 : UInt32).toBitVec.sle (UInt32.ofNat (65536 - (d + 1))).toBitVec) = false := by
        rw [BitVec.sle]
        have h1 : (UInt32.ofNat (65536 - (d + 1))).toBitVec.toInt = ((65536 - (d + 1) : Nat) : ℤ) := by
          have hn1 := ui32_toNat_of_lt_65536 hkd
          dsimp only [BitVec.toInt]
          rw [UInt32.toNat_toBitVec, hn1]
          split
          · rfl
          · omega
        have h2 : (65536 : UInt32).toBitVec.toInt = (65536 : ℤ) := by decide
        rw [h1, h2]
        simp only [decide_eq_false_iff_not]
        omega
      have hslt_idx := slt_zero_false_of_lt_65536 hkd
      have hsz_idx : (UInt32.ofNat (65536 - (d + 1))).toNat < (clinitArrAt (65536 - (d + 1))).size := by
        rw [clinitArr_sz (65536 - (d + 1)), ui32_toNat_of_lt_65536 hkd]; exact hkd
      have hs_inv : stepInvokeStatic
          ⟨13, [.i32 (UInt32.ofNat (65536 - (d + 1))), .i32 (UInt32.ofNat (65536 - (d + 1))), .heapRef 0],
            Jvm.setLocal locs 2 (.i32 (UInt32.ofNat (65536 - (d + 1)))),
            clinitJH (65536 - (d + 1)), ⟨[], [], []⟩⟩
          "com/alexvanyo/composelife/algorithm/BitComputationKt" "computeQuadInfo" "(I)I" =
          .inl (some ⟨14,
            [.i32 (computeQuadInfoModel (UInt32.ofNat (65536 - (d + 1)))),
              .i32 (UInt32.ofNat (65536 - (d + 1))), .heapRef 0],
            Jvm.setLocal locs 2 (.i32 (UInt32.ofNat (65536 - (d + 1)))),
            clinitJH (65536 - (d + 1)), ⟨[], [], []⟩⟩) := rfl
      have hset : (clinitJH (65536 - (d + 1))).set 0
          (.intArray ((clinitArrAt (65536 - (d + 1))).set (UInt32.ofNat (65536 - (d + 1))).toNat
            (computeQuadInfoModel (UInt32.ofNat (65536 - (d + 1)))) hsz_idx)) =
          clinitJH (65536 - d) := by
        have hk1 : 65536 - (d + 1) + 1 = 65536 - d := by omega
        have hidx_eq : (UInt32.ofNat (65536 - (d + 1))).toNat = 65536 - (d + 1) :=
          ui32_toNat_of_lt_65536 hkd
        simp only [hidx_eq]
        rw [clinitArr_set (65536 - (d + 1)) hkd, hk1]
        simp [clinitJH, Jvm.JvmHeap.alloc, Jvm.JvmHeap.set]
      have hinc : UInt32.ofNat (65536 - (d + 1)) + 1 = UInt32.ofNat (65536 - d) := by
        have hk1 : 65536 - (d + 1) + 1 = 65536 - d := by omega
        apply UInt32.toNat.inj
        have h1 : (1 : UInt32).toNat = 1 := rfl
        rw [UInt32.toNat_add, ui32_toNat_of_lt (by omega), h1, ui32_toNat_of_lt (by omega)]
        rw [Nat.mod_eq_of_lt (by omega)]
        exact hk1
      let locs' := Jvm.setLocal (Jvm.setLocal locs 2 (.i32 (UInt32.ofNat (65536 - (d + 1)))))
        0 (.i32 (UInt32.ofNat (65536 - d)))
      have hl0' : locs' 0 = .i32 (UInt32.ofNat (65536 - d)) := rfl
      have hl1' : locs' 1 = .heapRef 0 := by simp [locs', Jvm.setLocal, hl1]
      rcases ih (by omega) f locs' hl0' hl1' with ⟨st', hrun', hqi'⟩
      refine ⟨st', ?_, hqi'⟩
      rw [show f + 6 + (d + 1) * 12 = (f + 6 + d * 12 + 10) + 2 by omega, runJvmResFast_stepKcChunk 2]
      (conv => lhs; arg 1; jvm_whnf_blk)
      simp only [hl0]
      rw [afterResBlockChunk_cont, runJvmResFast_if_icmpge_fallthrough hsle_cmp]
      rw [show f + 6 + d * 12 + 9 = (f + 6 + d * 12 + 4) + 5 by omega, runJvmResFast_stepKcChunk 5]
      (conv => lhs; arg 1; jvm_whnf_blk)
      simp only [hl0, hl1]
      rw [afterResBlockChunk_cont, runJvmResFast_invokestatic_step (hs := hs_inv)]
      rw [show f + 6 + d * 12 + 3 = (f + 6 + d * 12 + 2) + 1 by omega,
        runJvmResFast_iastore (clinitJH_get0 (65536 - (d + 1))) hslt_idx hsz_idx]
      rw [hset]
      have hl0_2 : Jvm.setLocal locs 2 (.i32 (UInt32.ofNat (65536 - (d + 1)))) 0 =
          .i32 (UInt32.ofNat (65536 - (d + 1))) := by simp [Jvm.setLocal, hl0]
      dsimp only [runJvmResFast]
      rw [Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp)
        (by
          have hsub : Jvm.stepInstr algHooks (.iinc 0 1)
              ⟨13 + 1 + 1, [], Jvm.setLocal locs 2 (.i32 (UInt32.ofNat (65536 - (d + 1)))),
                clinitJH (65536 - d), ⟨[], [], []⟩⟩ =
              match (Jvm.setLocal locs 2 (.i32 (UInt32.ofNat (65536 - (d + 1)))) 0).asI32? with
              | some cur => Sum.inl (some ⟨13 + 1 + 1 + 1, [],
                  Jvm.setLocal (Jvm.setLocal locs 2 (.i32 (UInt32.ofNat (65536 - (d + 1))))) 0
                    (.i32 (cur + (1 : Int32).toUInt32)),
                  clinitJH (65536 - d), ⟨[], [], []⟩⟩)
              | none => Sum.inr none := rfl
          rw [hsub, hl0_2]; rfl) rfl]
      rw [Jvm.runJvmResFast_goto algHooks]
      have h1u : (1 : Int32).toUInt32 = (1 : UInt32) := rfl
      simp only [h1u, hinc] at hrun' ⊢
      exact hrun'
  rcases hloop 65536 (by omega) 13557
      (Jvm.setLocal (Jvm.setLocal (fun _ => .i32 0) 0 (.i32 0)) 1 (.heapRef 0))
      (by rfl) (by rfl) with ⟨st', hrun, hqi⟩
  rw [show (65536 - 65536 : Nat) = 0 by decide] at hrun
  refine ⟨st', ?_, hqi⟩
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  rw [runJvmResFast_stepKcChunk 3]
  (conv => lhs; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont, runJvmResFast_newarray_int (by decide)]
  rw [show (65536 : UInt32).toNat = 65536 from by decide, clinitJH_zero]
  rw [runJvmResFast_stepKcChunk 1]
  (conv => lhs; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont]
  have hzero_sz : ({ } : Jvm.JvmHeap AlgExt).objects.size = 0 := rfl
  rw [hzero_sz]
  have hfuel : 13557 + 6 + 65536 * 12 = 799995 := by decide
  rw [hfuel] at hrun
  exact hrun

/-- End-to-end JVM bytecode correctness theorem directly connecting `BitComputationKt.class` execution to Conway's Game of Life. -/
theorem computeNextGenerationPureKotlin_bytecode_correct (w : UInt64)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hqi : HasQuadInfoLut jh) (hng : HasNextGen4x4Lut jh)
    (x y : ℤ) (hx : 2 ≤ x ∧ x < 6) (hy : 2 ≤ y ∧ y < 6) :
    ∃ r : UInt32,
      runJvm 250 BitComputationKt_computeNextGenerationPureKotlin_prog (Jvm.initJvmState [(0, .i64 w)] (.i32 0) hp jh) = some (.i32 r) ∧
      r.toBitVec.getLsbD (Algorithm.mortonIndex4 (x - 2).toNat (y - 2).toNat) =
        Algorithm.nextGenAt (Algorithm.leafAt w) x y := by
  refine ⟨computeNextGenerationPureKotlinModel w, ?_, ?_⟩
  · exact computeNextGenerationPureKotlin_equiv w jh hp hqi hng
  · exact computeNextGenerationPureKotlinModel_correct w x y hx hy

end Algorithm.KotlinJvmVerification
