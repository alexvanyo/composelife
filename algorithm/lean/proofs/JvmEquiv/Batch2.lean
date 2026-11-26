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

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

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
    runJvm 15 AlgorithmLeanKt_f_Algorithm_computeLeafNextGen8x8BranchUInt_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (Algorithm.computeLeafNextGen8x8BranchUInt w)) := by
  apply runJvm_of_runJvmValFast0 15 _ _ _ rfl
  have heval : runJvmValFast 15 AlgorithmLeanKt_f_Algorithm_computeLeafNextGen8x8BranchUInt_prog 0
      AlgorithmLeanKt_f_Algorithm_computeLeafNextGen8x8BranchUInt_prog (initJvmState [(0, .i64 w)]) =
      (if ((if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0) = true then
        some (.i32 0) else some (.i32 (Algorithm.computeLeafNextGen8x8FastUInt w))) := rfl
  rw [heval, lcmp_bv_eq_zero]; unfold Algorithm.computeLeafNextGen8x8BranchUInt
  by_cases hw : w == 0 <;> simp [hw]

theorem computeLeafNextGen8x8BranchUInt_1_equiv (w : UInt64) :
    runJvm 15 FlatHashLifeLeanKt_f_Algorithm_computeLeafNextGen8x8BranchUInt_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (Algorithm.computeLeafNextGen8x8BranchUInt w)) := by
  apply runJvm_of_runJvmValFast0 15 _ _ _ rfl
  have heval : runJvmValFast 15 FlatHashLifeLeanKt_f_Algorithm_computeLeafNextGen8x8BranchUInt_prog 0
      FlatHashLifeLeanKt_f_Algorithm_computeLeafNextGen8x8BranchUInt_prog (initJvmState [(0, .i64 w)]) =
      (if ((if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0) = true then
        some (.i32 0) else some (.i32 (Algorithm.computeLeafNextGen8x8FastUInt w))) := rfl
  rw [heval, lcmp_bv_eq_zero]; unfold Algorithm.computeLeafNextGen8x8BranchUInt
  by_cases hw : w == 0 <;> simp [hw]

theorem computeLeafNextGen8x8BranchUInt_2_equiv (w : UInt64) :
    runJvm 15 MacroCellLeanKt_f_Algorithm_computeLeafNextGen8x8BranchUInt_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (Algorithm.computeLeafNextGen8x8BranchUInt w)) := by
  apply runJvm_of_runJvmValFast0 15 _ _ _ rfl
  have heval : runJvmValFast 15 MacroCellLeanKt_f_Algorithm_computeLeafNextGen8x8BranchUInt_prog 0
      MacroCellLeanKt_f_Algorithm_computeLeafNextGen8x8BranchUInt_prog (initJvmState [(0, .i64 w)]) =
      (if ((if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0) = true then
        some (.i32 0) else some (.i32 (Algorithm.computeLeafNextGen8x8FastUInt w))) := rfl
  rw [heval, lcmp_bv_eq_zero]; unfold Algorithm.computeLeafNextGen8x8BranchUInt
  by_cases hw : w == 0 <;> simp [hw]

theorem leafContains_1_equiv (leaf : UInt64) (x y : UInt32) :
    runJvm 25 MacroCellLeanKt_f_Algorithm_leafContains_prog (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y)]) =
      some (.i32 (if Algorithm.leafContains leaf x y then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 25 _ _ _ rfl
  have heval : runJvmValFast 25 MacroCellLeanKt_f_Algorithm_leafContains_prog 0 MacroCellLeanKt_f_Algorithm_leafContains_prog
      (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y)]) =
      (if ((if (leaf >>> (Algorithm.cellToLeafBitUInt x y &&& 63).toUInt64) &&& 1 == 1 then (0 : UInt32)
        else if ((leaf >>> (Algorithm.cellToLeafBitUInt x y &&& 63).toUInt64) &&& 1).toBitVec.slt 1#64 then 4294967295 else 1) == 0) then
        some (.i32 1) else some (.i32 0)) := rfl
  rw [heval, cellToLeafBitUInt_and_63, lcmp_bv_eq_zero]
  unfold Algorithm.leafContains
  by_cases h : (((leaf >>> (Algorithm.cellToLeafBitUInt x y).toUInt64) &&& 1) == 1) = true <;> simp [h]

theorem leafWithCell_1_equiv (leaf : UInt64) (x y : UInt32) (isAlive : Bool) :
    runJvm 35 MacroCellLeanKt_f_Algorithm_leafWithCell_prog
      (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y), (4, .i32 (if isAlive then 1 else 0))]) =
      some (.i64 (Algorithm.leafWithCell leaf x y isAlive)) := by
  apply runJvm_of_runJvmValFast0 35 _ _ _ rfl
  unfold Algorithm.leafWithCell
  cases isAlive <;> dsimp
  · have heval : runJvmValFast 35 MacroCellLeanKt_f_Algorithm_leafWithCell_prog 0 MacroCellLeanKt_f_Algorithm_leafWithCell_prog
        (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y), (4, .i32 0)]) =
        some (.i64 (leaf &&& ((1 <<< (Algorithm.cellToLeafBitUInt x y &&& 63).toUInt64) ^^^ 18446744073709551615))) := rfl
    rw [heval, cellToLeafBitUInt_and_63, xor_allOnes_eq_not]
  · have heval : runJvmValFast 35 MacroCellLeanKt_f_Algorithm_leafWithCell_prog 0 MacroCellLeanKt_f_Algorithm_leafWithCell_prog
        (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y), (4, .i32 1)]) =
        some (.i64 (leaf ||| (1 <<< (Algorithm.cellToLeafBitUInt x y &&& 63).toUInt64))) := rfl
    rw [heval, cellToLeafBitUInt_and_63]

theorem leanUnboxULong_equiv (v : UInt64) :
    runJvm 25 FlatHashLifeLeanKt_leanUnboxULong_prog (initJvmState [(0, .boxedULong v)]) = some (.i64 v) := by rfl

theorem leanUnboxULong_1_equiv (v : UInt64) :
    runJvm 25 MacroCellLeanKt_leanUnboxULong_prog (initJvmState [(0, .boxedULong v)]) = some (.i64 v) := by rfl

theorem leanUnboxInt_equiv (v : UInt32) :
    runJvm 25 Life105LeanKt_leanUnboxInt_prog (initJvmState [(0, .boxedInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxInt_1_equiv (v : UInt32) :
    runJvm 25 Life106LeanKt_leanUnboxInt_prog (initJvmState [(0, .boxedInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxInt_2_equiv (v : UInt32) :
    runJvm 25 RleLeanKt_leanUnboxInt_prog (initJvmState [(0, .boxedInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxUInt_equiv (v : UInt32) :
    runJvm 25 Life105LeanKt_leanUnboxUInt_prog (initJvmState [(0, .boxedUInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxUInt_1_equiv (v : UInt32) :
    runJvm 25 Life106LeanKt_leanUnboxUInt_prog (initJvmState [(0, .boxedUInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxUInt_2_equiv (v : UInt32) :
    runJvm 25 MacroCellLeanKt_leanUnboxUInt_prog (initJvmState [(0, .boxedUInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxUInt_3_equiv (v : UInt32) :
    runJvm 25 PlaintextLeanKt_leanUnboxUInt_prog (initJvmState [(0, .boxedUInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxUInt_4_equiv (v : UInt32) :
    runJvm 25 RleLeanKt_leanUnboxUInt_prog (initJvmState [(0, .boxedUInt v)]) = some (.i32 v) := by rfl

theorem leanUnboxUByte_equiv (v : UInt32) :
    runJvm 25 leanUnboxUByte_prog (initJvmState [(0, .boxedUByte v)]) =
      some (.i32 (UInt32.ofBitVec ((v.toBitVec.setWidth 8).signExtend 32))) := by rfl

theorem macrocellSingleLeaf_lam0_equiv (w : UInt64) :
    runJvm 15 f_Algorithm_macrocellSingleLeaf___lam__0_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (if w == 0 then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 15 _ _ _ rfl
  have heval : runJvmValFast 15 f_Algorithm_macrocellSingleLeaf___lam__0_prog 0
      f_Algorithm_macrocellSingleLeaf___lam__0_prog (initJvmState [(0, .i64 w)]) =
      (if (if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0 then
        some (.i32 1) else some (.i32 0)) := rfl
  rw [heval, lcmp_bv_eq_zero]
  by_cases hw : w == 0 <;> simp [hw]

theorem macrocellSingleLeaf_lam1_equiv (w : UInt64) :
    runJvm 15 f_Algorithm_macrocellSingleLeaf___lam__1_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (if w == 0 then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 15 _ _ _ rfl
  have heval : runJvmValFast 15 f_Algorithm_macrocellSingleLeaf___lam__1_prog 0
      f_Algorithm_macrocellSingleLeaf___lam__1_prog (initJvmState [(0, .i64 w)]) =
      (if (if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0 then
        some (.i32 1) else some (.i32 0)) := rfl
  rw [heval, lcmp_bv_eq_zero]
  by_cases hw : w == 0 <;> simp [hw]

theorem macrocellSingleLeaf_lam2_equiv (w : UInt64) :
    runJvm 15 f_Algorithm_macrocellSingleLeaf___lam__2_prog (initJvmState [(0, .i64 w)]) =
      some (.i32 (if w == 0 then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 15 _ _ _ rfl
  have heval : runJvmValFast 15 f_Algorithm_macrocellSingleLeaf___lam__2_prog 0
      f_Algorithm_macrocellSingleLeaf___lam__2_prog (initJvmState [(0, .i64 w)]) =
      (if (if w == 0 then (0 : UInt32) else if w.toBitVec.slt 0#64 then 4294967295 else 1) == 0 then
        some (.i32 1) else some (.i32 0)) := rfl
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
    runJvm 60 PlaintextLeanKt_f_Algorithm_cellBox_prog (initJvmState [(0, (.ext (.u64Ref 0)))] [] [cells]) =
      some (jvmBoxCellBox (Algorithm.cellBox cells)) := by
  apply runJvm_of_runJvmValFast0 60 _ _ _ rfl
  have heval : runJvmValFast 60 PlaintextLeanKt_f_Algorithm_cellBox_prog 0 PlaintextLeanKt_f_Algorithm_cellBox_prog
      (initJvmState [(0, (.ext (.u64Ref 0)))] [] [cells]) =
      (if cells.size.toUInt32 == 0 then some (jvmBoxCellBox (0, 0, 0, 0))
       else
         let k := cells[0]!
         let x := (k >>> 32).toUInt32.toInt32
         let y := k.toUInt32.toInt32
         some (jvmBoxCellBox (Algorithm.cellBounds cells 1 cells.size.toUInt32 x x y y))) := rfl
  rw [heval]; unfold Algorithm.cellBox Algorithm.cellKeyX Algorithm.cellKeyY
  by_cases h0 : cells.size.toUInt32 == 0 <;> simp [h0]

theorem cellBox_1_equiv (cells : Array UInt64) :
    runJvm 60 RleLeanKt_f_Algorithm_cellBox_prog (initJvmState [(0, (.ext (.u64Ref 0)))] [] [cells]) =
      some (jvmBoxCellBox (Algorithm.cellBox cells)) := by
  apply runJvm_of_runJvmValFast0 60 _ _ _ rfl
  have heval : runJvmValFast 60 RleLeanKt_f_Algorithm_cellBox_prog 0 RleLeanKt_f_Algorithm_cellBox_prog
      (initJvmState [(0, (.ext (.u64Ref 0)))] [] [cells]) =
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
      some ((.ext (.mc (Algorithm.emptyAtHeight h)))) := by
  apply runJvm_of_runJvmValFast0 30 _ _ _ rfl
  have heval : runJvmValFast 30 f_Algorithm_emptyAtHeight_prog 0 f_Algorithm_emptyAtHeight_prog
      (initJvmState [(0, .i32 h)]) =
      (if h == 0 then some ((.ext (.mc Algorithm.emptyLevel4)))
      else let e := Algorithm.emptyAtHeight (h - 1); some ((.ext (.mc (Algorithm.makeCellNode e e e e))))) := rfl
  rw [heval]
  by_cases hh : h = 0
  · subst hh; simp [Algorithm.emptyAtHeight]
  · have hb : (h == 0) = false := beq_false_of_ne hh
    simp only [hb, Bool.false_eq_true, ite_false]
    conv => rhs; rw [Algorithm.emptyAtHeight]
    simp [hh]

theorem serializePlaintext_equiv (cells : Array UInt64) (minX maxX minY maxY : Int32) :
    runJvm 70 f_Algorithm_serializePlaintext_prog
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 minX.toUInt32), (2, .i32 maxX.toUInt32),
        (3, .i32 minY.toUInt32), (4, .i32 maxY.toUInt32)] [] [cells]) =
      some (.strArr (Algorithm.serializePlaintext cells minX maxX minY maxY)) := by
  apply runJvm_of_runJvmValFast0 70 _ _ _ rfl
  jvm_step_blk0 f_Algorithm_serializePlaintext_prog
  unfold Algorithm.serializePlaintext
  by_cases h0 : cells.size.toUInt32 == 0
  · simp only [h0, ↓reduceIte]
    jvm_step_blk f_Algorithm_serializePlaintext_prog
  · simp only [h0, Bool.false_eq_true, ↓reduceIte]
    jvm_step_blk f_Algorithm_serializePlaintext_prog
    rw [show (1 : UInt32) = Int32.toUInt32 1 from rfl, Int32.toUInt32_add, Int32.toUInt32_sub]
    rfl

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
  unfold Algorithm.findLastLeafX
  jvm_step_blk0 f_Algorithm_findLastLeafX_prog
  cases Algorithm.leafContains leaf 7 y <;> simp <;> try rfl
  jvm_step_blk f_Algorithm_findLastLeafX_prog
  cases Algorithm.leafContains leaf 6 y <;> simp <;> try rfl
  jvm_step_blk f_Algorithm_findLastLeafX_prog
  cases Algorithm.leafContains leaf 5 y <;> simp <;> try rfl
  jvm_step_blk f_Algorithm_findLastLeafX_prog
  cases Algorithm.leafContains leaf 4 y <;> simp <;> try rfl
  jvm_step_blk f_Algorithm_findLastLeafX_prog
  cases Algorithm.leafContains leaf 3 y <;> simp <;> try rfl
  jvm_step_blk f_Algorithm_findLastLeafX_prog
  cases Algorithm.leafContains leaf 2 y <;> simp <;> try rfl
  jvm_step_blk f_Algorithm_findLastLeafX_prog
  cases Algorithm.leafContains leaf 1 y <;> simp <;> try rfl
  jvm_step_blk f_Algorithm_findLastLeafX_prog
  cases Algorithm.leafContains leaf 0 y <;> simp <;> rfl

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

elab "jvm_step_branch_tail_mc" : tactic => do
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
        (conv => lhs; arg 2; arg 6; jvm_whnf_blk)
        (try (conv => {
          lhs; arg 2; arg 6; arg 2
          simp only [evalInstanceOf_algHooks_ext, checkInstanceOf_level4_level4,
            checkInstanceOf_level4_cell, checkInstanceOf_cell_level4, checkInstanceOf_cell_cell,
            eq_self_iff_true, Bool.false_eq_true, ite_true, ite_false]
        })))))
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
        (conv => lhs; arg 6; jvm_whnf_blk)
        (try (conv => {
          lhs; arg 6; arg 2
          simp only [evalInstanceOf_algHooks_ext, checkInstanceOf_level4_level4,
            checkInstanceOf_level4_cell, checkInstanceOf_cell_level4, checkInstanceOf_cell_cell,
            eq_self_iff_true, Bool.false_eq_true, ite_true, ite_false]
        })))))
      let tgt2 := (← Lean.Elab.Tactic.getMainTarget).consumeMData
      let some (_, lhs2, _) := tgt2.eq? | return ()
      rwEvalBranchByInstr isRes (lhs2.getArg! 3)
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
        (conv => lhs; norm_jvm_locals)
        reduce_top_mc_ite
        (conv => lhs; jvm_whnf_run_args))))

elab "jvm_step_blk_mc" _prog:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_nonbranch_chunks))
  if !(← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then
    Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_branch_tail_mc))

theorem dagWriter_addEntry_equiv (w : Algorithm.DagWriter) (m : Algorithm.MacroCell) (c1 c2 c3 c4 : UInt32) :
    runJvm 150 f_Algorithm_DagWriter_addEntry_prog
      (initJvmState [(0, (.ext (.dagWriter w))), (1, (.ext (.mc m))), (2, .i32 c1), (3, .i32 c2), (4, .i32 c3), (5, .i32 c4)]) =
      let r := w.addEntry m c1 c2 c3 c4
      some (.pair (.boxedUInt r.1) ((.ext (.dagWriter r.2)))) := by
  apply runJvm_of_runJvmValFast0 150 _ _ _ rfl
  rcases m with ⟨h, nw, ne, sw, se⟩ | ⟨h, nw, ne, sw, se⟩
  · jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
    jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
    rw [lcmp_bv_eq_zero]
    by_cases hnw : nw = 0
    · simp only [hnw, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false]
      jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
      rw [lcmp_bv_eq_zero]
      by_cases hne : ne = 0
      · simp only [hne, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false]
        jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
        rw [lcmp_bv_eq_zero]
        by_cases hsw : sw = 0
        · simp only [hsw, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false]
          jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
          rw [lcmp_bv_eq_zero]
          by_cases hse : se = 0
          · simp only [hse, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false]
            jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
            simp [Algorithm.DagWriter.addEntry]
          · simp only [beq_eq_false_iff_ne.mpr hse, Bool.not_false, ite_true]
            jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
            simp [Algorithm.DagWriter.addEntry, hse]
        · simp only [beq_eq_false_iff_ne.mpr hsw, Bool.not_false, ite_true]
          jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
          simp [Algorithm.DagWriter.addEntry, hsw]
      · simp only [beq_eq_false_iff_ne.mpr hne, Bool.not_false, ite_true]
        jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
        simp [Algorithm.DagWriter.addEntry, hne]
    · simp only [beq_eq_false_iff_ne.mpr hnw, Bool.not_false, ite_true]
      jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
      simp [Algorithm.DagWriter.addEntry, hnw]
  · jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
    jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
    jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
    by_cases h1 : c1 == 0
    · simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
      by_cases h2 : c2 == 0
      · simp only [h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
        by_cases h3 : c3 == 0
        · simp only [h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
          by_cases h4 : c4 == 0
          · simp only [h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
            simp [Algorithm.DagWriter.addEntry, h1, h2, h3, h4]
          · simp only [h4, Bool.not_false, ↓reduceIte]
            jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
            simp [Algorithm.DagWriter.addEntry, h1, h2, h3, h4]
        · simp only [h3, Bool.not_false, ↓reduceIte]
          jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
          simp [Algorithm.DagWriter.addEntry, h1, h2, h3]
      · simp only [h2, Bool.not_false, ↓reduceIte]
        jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
        simp [Algorithm.DagWriter.addEntry, h1, h2]
    · simp only [h1, Bool.not_false, ↓reduceIte]
      jvm_step_blk_mc f_Algorithm_DagWriter_addEntry_prog
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

private theorem u32_double_add1_slt_zero {n : Nat} (hn : n < 2 ^ 30) :
    ((n.toUInt32 <<< 1 + 1).toBitVec.slt 0#32) = false := by
  have h1 : n.toUInt32.toNat = n := Nat.mod_eq_of_lt (by omega)
  have h2 : (n.toUInt32 <<< 1 + 1).toNat = 2 * n + 1 := by
    rw [UInt32.toNat_add, UInt32.toNat_shiftLeft, h1]
    have hmod : UInt32.toNat 1 % 32 = 1 := rfl
    have h1n : UInt32.toNat 1 = 1 := rfl
    rw [hmod, h1n, Nat.shiftLeft_eq]
    omega
  change decide ((n.toUInt32 <<< 1 + 1).toBitVec.toInt < (0#32).toInt) = false
  rw [decide_eq_false_iff_not]
  have hbv : (n.toUInt32 <<< 1 + 1).toBitVec.toNat = 2 * n + 1 := h2
  rw [BitVec.toInt_eq_toNat_cond, hbv]
  have h0 : (0#32 : BitVec 32).toInt = 0 := rfl
  rw [h0]
  split <;> omega

private theorem uint32_shl_one' (x : UInt32) : x <<< (1 &&& 31) = x <<< 1 := rfl

private theorem runJvmResFast_ulongArrayNew (fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (rest : List JvmInstr) (pc0 : Nat) (sz : UInt32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hsz : sz.toBitVec.slt 0#32 = false) :
    runJvmResFast (fuel + 1) prog pc
      (.invokestatic "kotlin/ULongArray" "constructor-impl" "(I)[J" :: rest)
      ⟨pc0, .i32 sz :: stk, locs, jh, hp⟩ =
      runJvmResFast fuel prog (pc + 1) rest
        ⟨pc + 1, .ext (.u64Ref hp.u64Arrays.length) :: stk, locs, jh,
          { hp with u64Arrays := hp.u64Arrays ++ [Array.replicate sz.toNat 0] }⟩ := by
  dsimp only [runJvmResFast, Jvm.runJvmResFast]
  have hnbr : (isBranchInstr (.invokestatic "kotlin/ULongArray" "constructor-impl" "(I)[J") = true) = False := by
    decide
  rw [ite_eq_right (fun h => by rw [hnbr] at h; exact h.elim)]
  have hstep : Jvm.stepInstr algHooks (.invokestatic "kotlin/ULongArray" "constructor-impl" "(I)[J")
      ⟨pc, .i32 sz :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.u64Ref hp.u64Arrays.length) :: stk, locs, jh,
        { hp with u64Arrays := hp.u64Arrays ++ [Array.replicate sz.toNat 0] }⟩) := by
    change (if sz.toBitVec.slt 0#32 = true then _ else _) = _
    rw [hsz]
    rfl
  rw [hstep]
  dsimp only
  simp only [↓reduceIte]

macro "prove_u64Buf_push" prog:ident arr:ident hsz:ident : tactic =>
  `(tactic| (
    apply runJvmRes_map_of_runJvmResFast0 _ 65 _ _ _ rfl
    jvm_step_blk0 $prog
    rw [show UInt32.toNat 0 = 0 from rfl, compareUnsigned_slt']
    by_cases hlt : ($arr)[0]!.toUInt32 + 1 < ($arr).size.toUInt32
    · simp only [hlt, decide_true, ite_true]
      jvm_step_blk $prog
      simp [Algorithm.U64Buf.push, hlt]
    · simp only [hlt, decide_false, Bool.false_eq_true, ite_false]
      rw [runJvmResFast_stepBlockChunk 7]
      (conv => lhs; arg 2; arg 1; jvm_whnf_blk)
      rw [afterResBlockChunk_cont]
      (conv => lhs; arg 2; norm_jvm_locals; jvm_whnf_run_args)
      (conv => lhs; arg 2; arg 5; arg 2; rw [uint32_shl_one'])
      rw [runJvmResFast_ulongArrayNew (hsz := u32_double_add1_slt_zero $hsz)]
      (conv => lhs; arg 2; norm_jvm_locals; jvm_whnf_run_args)
      jvm_step_blk $prog
      have hnat : ((($arr).size % 4294967296) <<< 1 + 1) % 4294967296 =
          (2 * ($arr).size + 1) % 4294967296 := by
        rw [Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
        omega
      simp [Algorithm.U64Buf.push, hlt, hnat]))

theorem u64Buf_push_equiv (arr : Array UInt64) (x : UInt64) (hsz : arr.size < 2 ^ 30) :
    (runJvmRes 65 Life105LeanKt_f_Algorithm_U64Buf_push_prog (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i64 x)] [] [arr])).map
      (fun p => (p.1, p.2.heap.u64Arrays)) =
      some (if arr[0]!.toUInt32 + 1 < arr.size.toUInt32 then ((.ext (.u64Ref 0)), [Algorithm.U64Buf.push arr x])
            else ((.ext (.u64Ref 1)), [arr, Algorithm.U64Buf.push arr x])) := by
  prove_u64Buf_push Life105LeanKt_f_Algorithm_U64Buf_push_prog arr hsz

theorem u64Buf_push_1_equiv (arr : Array UInt64) (x : UInt64) (hsz : arr.size < 2 ^ 30) :
    (runJvmRes 65 Life106LeanKt_f_Algorithm_U64Buf_push_prog (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i64 x)] [] [arr])).map
      (fun p => (p.1, p.2.heap.u64Arrays)) =
      some (if arr[0]!.toUInt32 + 1 < arr.size.toUInt32 then ((.ext (.u64Ref 0)), [Algorithm.U64Buf.push arr x])
            else ((.ext (.u64Ref 1)), [arr, Algorithm.U64Buf.push arr x])) := by
  prove_u64Buf_push Life106LeanKt_f_Algorithm_U64Buf_push_prog arr hsz

theorem u64Buf_push_2_equiv (arr : Array UInt64) (x : UInt64) (hsz : arr.size < 2 ^ 30) :
    (runJvmRes 65 MacroCellLeanKt_f_Algorithm_U64Buf_push_prog (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i64 x)] [] [arr])).map
      (fun p => (p.1, p.2.heap.u64Arrays)) =
      some (if arr[0]!.toUInt32 + 1 < arr.size.toUInt32 then ((.ext (.u64Ref 0)), [Algorithm.U64Buf.push arr x])
            else ((.ext (.u64Ref 1)), [arr, Algorithm.U64Buf.push arr x])) := by
  prove_u64Buf_push MacroCellLeanKt_f_Algorithm_U64Buf_push_prog arr hsz

theorem u64Buf_push_3_equiv (arr : Array UInt64) (x : UInt64) (hsz : arr.size < 2 ^ 30) :
    (runJvmRes 65 PlaintextLeanKt_f_Algorithm_U64Buf_push_prog (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i64 x)] [] [arr])).map
      (fun p => (p.1, p.2.heap.u64Arrays)) =
      some (if arr[0]!.toUInt32 + 1 < arr.size.toUInt32 then ((.ext (.u64Ref 0)), [Algorithm.U64Buf.push arr x])
            else ((.ext (.u64Ref 1)), [arr, Algorithm.U64Buf.push arr x])) := by
  prove_u64Buf_push PlaintextLeanKt_f_Algorithm_U64Buf_push_prog arr hsz

theorem u64Buf_push_4_equiv (arr : Array UInt64) (x : UInt64) (hsz : arr.size < 2 ^ 30) :
    (runJvmRes 65 RleLeanKt_f_Algorithm_U64Buf_push_prog (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i64 x)] [] [arr])).map
      (fun p => (p.1, p.2.heap.u64Arrays)) =
      some (if arr[0]!.toUInt32 + 1 < arr.size.toUInt32 then ((.ext (.u64Ref 0)), [Algorithm.U64Buf.push arr x])
            else ((.ext (.u64Ref 1)), [arr, Algorithm.U64Buf.push arr x])) := by
  prove_u64Buf_push RleLeanKt_f_Algorithm_U64Buf_push_prog arr hsz

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

private def extractMcInstanceOfFVar? (sub : Lean.Expr) : Option Lean.FVarId := do
  let val ←
    if sub.isAppOfArity ``checkInstanceOf 2 then some (sub.getArg! 1)
    else if sub.isAppOfArity ``Jvm.JvmHooks.checkInstanceOf 5 then some (sub.getArg! 4)
    else if sub.isAppOfArity ``Jvm.evalInstanceOf 6 then some (sub.getArg! 5)
    else none
  guard (val.isAppOfArity ``Jvm.JvmVal.ext 2)
  let extVal := val.getArg! 1
  guard (extVal.isAppOfArity ``AlgExt.mc 1)
  let fv := extVal.getArg! 0
  guard fv.isFVar
  return fv.fvarId!

private def findMcInstanceOfFVar? (e : Lean.Expr) : Option Lean.FVarId :=
  (e.find? fun sub => (extractMcInstanceOfFVar? sub).isSome).bind extractMcInstanceOfFVar?

private def isUnbranchedRunLhs (e : Lean.Expr) : Bool :=
  let (inner, _) := unwrapRunLhs e
  inner.isAppOfArity ``runJvmValFast 5 || inner.isAppOfArity ``runJvmResFast 5

elab "split_next_mc_instanceof" : tactic => Lean.Elab.Tactic.withMainContext do
  let tgt ← Lean.Elab.Tactic.getMainTarget
  let some (_, lhs, _) := tgt.eq? | throwError "split_next_mc_instanceof: not an eq"
  let some fv := findMcInstanceOfFVar? lhs
    | throwError "split_next_mc_instanceof: no checkInstanceOf ((.ext (.mc fvar)))"
  Lean.Elab.Tactic.liftMetaTactic fun mvarId => do
    let subgoals ← mvarId.cases fv
    return subgoals.toList.map (·.mvarId)
  Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals reduce_top_mc_ite))

elab "step_mc_tree" prog:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| jvm_step_blk_mc $prog))
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
        Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals (try jvm_step_blk_mc $prog)))
        madeProgress := true
      else if isUnbranched then
        Lean.Elab.Tactic.evalTactic (← `(tactic| try jvm_step_blk_mc $prog))
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
    runJvm 45 f_Algorithm_needToExpand_prog (initJvmState [(0, (.ext (.mc m)))]) =
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
    runJvm 45 f_Algorithm_stepLevel4Node_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some (.i64 (Algorithm.stepLevel4Node m)) := by
  apply runJvm_of_runJvmValFast0 45 _ _ _ rfl
  step_mc_tree f_Algorithm_stepLevel4Node_prog
  all_goals simp [Algorithm.stepLevel4Node]

theorem stepLevel4NodeWith_equiv (m : Algorithm.MacroCell) (computeLeaf : UInt64 → UInt32) :
    runJvm 45 f_Algorithm_stepLevel4NodeWith_prog
      (initJvmState [(0, (.ext (.mc m))), (1, (.ext (.fnU64ToU32 computeLeaf)))]) =
      some (.i64 (Algorithm.stepLevel4NodeWith m computeLeaf)) := by
  apply runJvm_of_runJvmValFast0 45 _ _ _ rfl
  step_mc_tree f_Algorithm_stepLevel4NodeWith_prog
  all_goals simp [Algorithm.stepLevel4NodeWith]

theorem importsAsEmpty_equiv (m : Algorithm.MacroCell) :
    runJvm 55 f_Algorithm_importsAsEmpty_prog (initJvmState [(0, (.ext (.mc m)))]) =
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
    runJvm 55 f_Algorithm_importNeedsChildren_prog (initJvmState [(0, (.ext (.mc m)))]) =
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
      some ((.ext (.pruneThresh (Algorithm.computePruneThresholds computedGenerations
        generationsToCacheInMacroCellMaps generationsToCacheInLeafNodeMap)))) := by
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
    runJvm 75 f_Algorithm_prepareStep_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some ((.ext (.stepPrep (Algorithm.prepareStep m)))) := by
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
    runJvm 110 f_Algorithm_Level4Node_cellEquals_prog (initJvmState [(0, (.ext (.mc m))), (1, (.ext (.mc other)))]) =
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
    runJvm 110 f_Algorithm_CellNode_cellEquals_prog (initJvmState [(0, (.ext (.mc m))), (1, (.ext (.mc other)))]) =
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
    runJvm 195 f_Algorithm_MacroCell_cellEquals_prog (initJvmState [(0, (.ext (.mc m))), (1, (.ext (.mc other)))]) =
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
      (initJvmState [(0, (.ext (.mc m))), (1, (.ext (.fnMcToMc internLevel4))), (2, (.ext (.fnMcToOptMc findExistingCell))),
        (3, (.ext (.fnMcToMc canonicalizeSubnode))), (4, (.ext (.fnMcToMc internCell)))]) =
      some ((.ext (.mc (Algorithm.canonicalizeMacroCellWith m internLevel4 findExistingCell
        canonicalizeSubnode internCell)))) := by
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
    runJvm 200 f_Algorithm_centeredHorizontalSubnode_prog (initJvmState [(0, (.ext (.mc w))), (1, (.ext (.mc e)))]) =
      some ((.ext (.mc (Algorithm.centeredHorizontalSubnode w e)))) := by
  apply runJvm_of_runJvmValFast0 200 _ _ _ rfl
  step_mc_tree f_Algorithm_centeredHorizontalSubnode_prog
  all_goals simp [Algorithm.centeredHorizontalSubnode]

theorem centeredVerticalSubnode_equiv (n s : Algorithm.MacroCell) :
    runJvm 200 f_Algorithm_centeredVerticalSubnode_prog (initJvmState [(0, (.ext (.mc n))), (1, (.ext (.mc s)))]) =
      some ((.ext (.mc (Algorithm.centeredVerticalSubnode n s)))) := by
  apply runJvm_of_runJvmValFast0 200 _ _ _ rfl
  step_mc_tree f_Algorithm_centeredVerticalSubnode_prog
  all_goals simp [Algorithm.centeredVerticalSubnode]

theorem centeredSubnode_equiv (m : Algorithm.MacroCell) :
    runJvm 240 f_Algorithm_centeredSubnode_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some ((.ext (.mc (Algorithm.centeredSubnode m)))) := by
  apply runJvm_of_runJvmValFast0 240 _ _ _ rfl
  step_mc_tree f_Algorithm_centeredSubnode_prog
  all_goals simp only [Algorithm.centeredSubnode, Algorithm.centeredSubnodeLevel4]
  all_goals rfl

theorem f_centeredSubSubnodeFast_equiv (m : Algorithm.MacroCell) :
    runJvm 340 f_Algorithm_centeredSubSubnodeFast_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some ((.ext (.mc (Algorithm.centeredSubSubnodeFast m)))) := by
  apply runJvm_of_runJvmValFast0 340 _ _ _ rfl
  step_mc_tree f_Algorithm_centeredSubSubnodeFast_prog
  all_goals rfl

set_option maxRecDepth 10000 in
theorem f_centeredSubSubnodeSizeFast_equiv (m : Algorithm.MacroCell) :
    runJvm 600 f_Algorithm_centeredSubSubnodeSizeFast_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some (.i64 (Algorithm.centeredSubSubnodeSizeFast m)) := by
  apply runJvm_of_runJvmValFast0 600 _ _ _ rfl
  step_mc_tree f_Algorithm_centeredSubSubnodeSizeFast_prog
  all_goals rfl

private theorem shift_and_63_16 : ((16 : UInt32) &&& 63).toUInt64 = 16 := rfl
private theorem shift_and_63_32 : ((32 : UInt32) &&& 63).toUInt64 = 32 := rfl
private theorem shift_and_63_48 : ((48 : UInt32) &&& 63).toUInt64 = 48 := rfl

set_option maxRecDepth 4096 in
theorem stepQuadrants_equiv (m : Algorithm.MacroCell) (d : Nat) (hm : Algorithm.WFd m d) :
    runJvm 880 f_Algorithm_stepQuadrants_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some ((.ext (.stepQuad (Algorithm.stepQuadrants m)))) := by
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

set_option maxRecDepth 4096 in
theorem stepCellNodeWith_equiv (m : Algorithm.MacroCell) (d : Nat) (hm : Algorithm.WFd m d)
    (stepLevel4 : Algorithm.MacroCell → UInt64) (stepCell : Algorithm.MacroCell → Algorithm.MacroCell) :
    runJvm 920 f_Algorithm_stepCellNodeWith_prog
      (initJvmState [(0, (.ext (.mc m))), (1, (.ext (.fnMcToU64 stepLevel4))), (2, (.ext (.fnMcToMc stepCell)))]) =
      some ((.ext (.mc (Algorithm.stepCellNodeWith m stepLevel4 stepCell)))) := by
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


end Algorithm.JvmVerification
