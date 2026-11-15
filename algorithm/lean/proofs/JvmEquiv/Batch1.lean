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

import Std.Tactic.BVDecide
import JvmBytecode
import proofs.JvmEquiv.Infra

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
  dsimp [Jvm.JvmVal.asI32, Jvm.JvmVal.asI64, setLocal, initJvmState, Jvm.initJvmState, List.foldl,
    Algorithm.centeredSubnodeLevel4]
  bv_check "../lrat/JvmEquiv.Algorithm.JvmVerification.centeredSubnodeLevel4_equiv.lrat"

theorem centeredHorizontalSubnodeLevel4_equiv (qnw qne qsw qse : UInt64) :
    runJvm 80 f_Algorithm_centeredHorizontalSubnodeLevel4_prog
      (initJvmState [(0, .i64 qnw), (2, .i64 qne), (4, .i64 qsw), (6, .i64 qse)]) =
      some (.i64 (Algorithm.centeredHorizontalSubnodeLevel4 qnw qne qsw qse)) := by
  change some (JvmVal.i64 _) = some (JvmVal.i64 _)
  congr 2
  dsimp [Jvm.JvmVal.asI32, Jvm.JvmVal.asI64, setLocal, initJvmState, Jvm.initJvmState, List.foldl,
    Algorithm.centeredHorizontalSubnodeLevel4, Algorithm.centeredSubnodeLevel4]
  bv_check "../lrat/JvmEquiv.Algorithm.JvmVerification.centeredHorizontalSubnodeLevel4_equiv.lrat"

theorem centeredVerticalSubnodeLevel4_equiv (qnw qne qsw qse : UInt64) :
    runJvm 80 f_Algorithm_centeredVerticalSubnodeLevel4_prog
      (initJvmState [(0, .i64 qnw), (2, .i64 qne), (4, .i64 qsw), (6, .i64 qse)]) =
      some (.i64 (Algorithm.centeredVerticalSubnodeLevel4 qnw qne qsw qse)) := by
  change some (JvmVal.i64 _) = some (JvmVal.i64 _)
  congr 2
  dsimp [Jvm.JvmVal.asI32, Jvm.JvmVal.asI64, setLocal, initJvmState, Jvm.initJvmState, List.foldl,
    Algorithm.centeredVerticalSubnodeLevel4, Algorithm.centeredSubnodeLevel4]
  bv_check "../lrat/JvmEquiv.Algorithm.JvmVerification.centeredVerticalSubnodeLevel4_equiv.lrat"

theorem packLeafFrom4x4s_equiv (q0 q1 q2 q3 : UInt32) :
    runJvm 60 f_Algorithm_packLeafFrom4x4sUInt_prog
      (initJvmState [(0, .i32 q0), (1, .i32 q1), (2, .i32 q2), (3, .i32 q3)]) =
      some (.i64 (Algorithm.packLeafFrom4x4sUInt q0 q1 q2 q3)) := by
  change some (JvmVal.i64 _) = some (JvmVal.i64 _)
  congr 2
  dsimp [Jvm.JvmVal.asI32, Jvm.JvmVal.asI64, setLocal, initJvmState, Jvm.initJvmState, List.foldl,
    Algorithm.packLeafFrom4x4sUInt]
  bv_check "../lrat/JvmEquiv.Algorithm.JvmVerification.packLeafFrom4x4s_equiv.lrat"

theorem expandOffsetDelta_equiv (lvl : UInt32) (h1 : 1 ≤ lvl) (h2 : lvl ≤ 30) :
    runJvm 20 f_Algorithm_expandOffsetDeltaUInt_prog (initJvmState [(0, .i32 lvl)]) =
      some (.i32 (Algorithm.expandOffsetDeltaUInt lvl).toUInt32) := by
  change some (JvmVal.i32 _) = some (JvmVal.i32 _)
  congr 2
  dsimp [Jvm.JvmVal.asI32, Jvm.JvmVal.asI64, setLocal, initJvmState, Jvm.initJvmState, List.foldl,
    Algorithm.expandOffsetDeltaUInt]
  bv_check "../lrat/JvmEquiv.Algorithm.JvmVerification.expandOffsetDelta_equiv.lrat"

theorem stepOffsetDelta_equiv (lvl : UInt32) (h1 : 2 ≤ lvl) (h2 : lvl ≤ 30) :
    runJvm 20 f_Algorithm_stepOffsetDeltaUInt_prog (initJvmState [(0, .i32 lvl)]) =
      some (.i32 (Algorithm.stepOffsetDeltaUInt lvl).toUInt32) := by
  change some (JvmVal.i32 _) = some (JvmVal.i32 _)
  congr 2
  dsimp [Jvm.JvmVal.asI32, Jvm.JvmVal.asI64, setLocal, initJvmState, Jvm.initJvmState, List.foldl,
    Algorithm.stepOffsetDeltaUInt]
  bv_check "../lrat/JvmEquiv.Algorithm.JvmVerification.stepOffsetDelta_equiv.lrat"

theorem leafContains_equiv (leaf : UInt64) (x y : UInt32) :
    runJvm 25 f_Algorithm_leafContains_prog (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y)]) =
      some (.i32 (if Algorithm.leafContains leaf x y then 1 else 0)) := by
  change some (JvmVal.i32 _) = some (JvmVal.i32 _)
  congr 2
  dsimp [Jvm.JvmVal.asI32, Jvm.JvmVal.asI64, setLocal, initJvmState, Jvm.initJvmState, List.foldl,
    Algorithm.leafContains, Algorithm.cellToLeafBitUInt]
  bv_check "../lrat/JvmEquiv.Algorithm.JvmVerification.leafContains_equiv.lrat"

theorem leafWithCell_equiv (leaf : UInt64) (x y : UInt32) (isAlive : Bool) :
    runJvm 35 f_Algorithm_leafWithCell_prog
      (initJvmState [(0, .i64 leaf), (2, .i32 x), (3, .i32 y), (4, .i32 (if isAlive then 1 else 0))]) =
      some (.i64 (Algorithm.leafWithCell leaf x y isAlive)) := by
  change some (JvmVal.i64 _) = some (JvmVal.i64 _)
  congr 2
  dsimp [Jvm.JvmVal.asI32, Jvm.JvmVal.asI64, setLocal, initJvmState, Jvm.initJvmState, List.foldl,
    Algorithm.leafWithCell, Algorithm.cellToLeafBitUInt]
  bv_check "../lrat/JvmEquiv.Algorithm.JvmVerification.leafWithCell_equiv.lrat"


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
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 idx), (2, .i32 val)] [arena]) =
      some (.unit, { (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 idx), (2, .i32 val)] [arena]) with
        pc := 10, heap := { arenas := [arena.setRemapL4 idx val] },
        locals := setLocal (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 idx), (2, .i32 val)] [arena]).locals 3 ((.ext (.arenaU32Ref 0 .remapL4))) }) := by rfl

theorem flatHashLifeArena_setRemapCell_equiv (arena : Algorithm.FlatHashLifeArena) (idx val : UInt32) :
    runJvmRes 15 f_Algorithm_FlatHashLifeArena_setRemapCell_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 idx), (2, .i32 val)] [arena]) =
      some (.unit, { (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 idx), (2, .i32 val)] [arena]) with
        pc := 10, heap := { arenas := [arena.setRemapCell idx val] },
        locals := setLocal (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 idx), (2, .i32 val)] [arena]).locals 3 ((.ext (.arenaU32Ref 0 .remapCell))) }) := by rfl

theorem flatHashLifeArena_setCellStepRes_equiv (arena : Algorithm.FlatHashLifeArena) (idx val : UInt32) :
    runJvmRes 15 f_Algorithm_FlatHashLifeArena_setCellStepRes_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 idx), (2, .i32 val)] [arena]) =
      some (.unit, { (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 idx), (2, .i32 val)] [arena]) with
        pc := 10, heap := { arenas := [arena.setCellStepRes idx val] },
        locals := setLocal (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 idx), (2, .i32 val)] [arena]).locals 3 ((.ext (.arenaU32Ref 0 .cellStepRes))) }) := by rfl

theorem flatHashLifeArena_setL4StepRes_equiv (arena : Algorithm.FlatHashLifeArena) (idx : UInt32) (val : UInt64) :
    runJvmRes 25 f_Algorithm_FlatHashLifeArena_setL4StepRes_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 idx), (2, .i64 val)] [arena]) =
      some (.unit, { (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 idx), (2, .i64 val)] [arena]) with
        pc := 17, heap := { arenas := [arena.setL4StepRes idx val] },
        locals := setLocal (setLocal (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 idx), (2, .i64 val)] [arena]).locals 4 ((.ext (.arenaU64Ref 0 .l4StepRes)))) 5 ((.ext (.arenaU8Ref 0 .l4HasRes))) }) := by rfl

theorem flatHashLifeArena_setOverflow_equiv (arena : Algorithm.FlatHashLifeArena) :
    runJvmRes 15 f_Algorithm_FlatHashLifeArena_setOverflow_prog (initJvmState [(0, (.ext (.arenaRef 0)))] [arena]) =
      some (.unit, { (initJvmState [(0, (.ext (.arenaRef 0)))] [arena]) with pc := 6, heap := { arenas := [arena.setOverflow] }}) := by rfl

theorem flatHashLifeArena_clearOverflow_equiv (arena : Algorithm.FlatHashLifeArena) :
    runJvmRes 15 f_Algorithm_FlatHashLifeArena_clearOverflow_prog (initJvmState [(0, (.ext (.arenaRef 0)))] [arena]) =
      some (.unit, { (initJvmState [(0, (.ext (.arenaRef 0)))] [arena]) with pc := 6, heap := { arenas := [arena.clearOverflow] }}) := by rfl

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
    runJvm 10 f_Algorithm_cellCursorDone_prog (initJvmState [(0, (.ext (.cellFrames fs)))]) =
      some (.i32 (if Algorithm.cellCursorDone fs then 1 else 0)) := by rfl

theorem cellsToMacroCell_closed0_equiv :
    runJvm 10 f_Algorithm_cellsToMacroCell___closed__0_prog (initJvmState []) =
      some ((.ext (.mc (Algorithm.emptyAtHeight 1)))) := by rfl

theorem cellsToMacroCell_closed1_equiv :
    runJvm 15 f_Algorithm_cellsToMacroCell___closed__1_prog (initJvmState []) =
      some (.pair (.boxedULong 2147483648) ((.ext (.mc (Algorithm.emptyAtHeight 1))))) := by rfl

theorem cellsToMacroCell_closed2_equiv :
    runJvm 15 f_Algorithm_cellsToMacroCell___closed__2_prog (initJvmState []) =
      some (.pair (.boxedULong 2147483648) (.pair (.boxedULong 2147483648) ((.ext (.mc (Algorithm.emptyAtHeight 1)))))) := by rfl

theorem makeLevel4Node_equiv (nw ne sw se : UInt64) :
    runJvm 25 f_Algorithm_makeLevel4Node_prog
      (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)]) =
      some ((.ext (.mc (Algorithm.makeLevel4Node nw ne sw se)))) := by rfl

theorem makeCellNode_equiv (nw ne sw se : Algorithm.MacroCell) :
    runJvm 60 f_Algorithm_makeCellNode_prog
      (initJvmState [(0, (.ext (.mc nw))), (1, (.ext (.mc ne))), (2, (.ext (.mc sw))), (3, (.ext (.mc se)))]) =
      some ((.ext (.mc (Algorithm.makeCellNode nw ne sw se)))) := by rfl

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
      (initJvmState [(0, (.ext (.u64Ref 0))), (1, .i32 minX.toUInt32), (2, .i32 minY.toUInt32), (3, .i32 maxY.toUInt32)] [] [cells]) =
      some (.strArr (Algorithm.serializeLife105Block cells minX minY maxY)) := by rfl

theorem serializeLife105_equiv (cells : Array UInt64) :
    runJvm 50 f_Algorithm_serializeLife105_prog
      (initJvmState [(0, (.ext (.u64Ref 0)))] [] [cells]) =
      some (.strArr (Algorithm.serializeLife105 cells)) := by rfl

private theorem stepStatic_arraysCopyOfRange_u64
    {pc : Nat} {id : Nat} {s e : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {arr : Array UInt64} (hget : u64[id]? = some arr)
    (hs : s < 0x80000000) (he : e < 0x80000000) (hse : s ≤ e) (heb : e.toNat ≤ arr.size) :
    stepInvokeStatic ⟨pc, .i32 e :: .i32 s :: (.ext (.u64Ref id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/collections/ArraysKt" "copyOfRange" "([JII)[J" =
      .inl (some ⟨pc + 1, (.ext (.u64Ref u64.length)) :: rest, locs, jh, ⟨ar, u64 ++ [arr.extract s.toNat e.toNat], asc⟩⟩) := by
  have h1 : stepInvokeStatic ⟨pc, .i32 e :: .i32 s :: (.ext (.u64Ref id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/collections/ArraysKt" "copyOfRange" "([JII)[J" =
      match u64[id]? with
      | some a =>
        if s < 0x80000000 && e < 0x80000000 && s ≤ e && e.toNat ≤ a.size then
          .inl (some ⟨pc + 1, (.ext (.u64Ref u64.length)) :: rest, locs, jh, ⟨ar, u64 ++ [a.extract s.toNat e.toNat], asc⟩⟩)
        else .inr none
      | none => .inr none := rfl
  rw [h1, hget]
  dsimp only
  have hcond : (s < 0x80000000 && e < 0x80000000 && s ≤ e && e.toNat ≤ arr.size) = true := by
    simp [hs, he, hse, heb]
  rw [hcond]
  rfl

private theorem u64buf_toArray_of_prog (prog : List JvmInstr)
    (hprog : prog = f_Algorithm_U64Buf_toArray_prog)
    (arr : Array UInt64) (h1 : 1 ≤ arr.size) (h2 : arr.size < 2 ^ 31)
    (h3 : arr[0]!.toUInt32.toNat + 1 ≤ arr.size) :
    runJvmRes 35 prog (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]) =
      some ((.ext (.u64Ref 1)), { (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]) with
        pc := 24, stack := [(.ext (.u64Ref 1))], heap := { u64Arrays := [arr, Algorithm.U64Buf.toArray arr] } }) := by
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
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  have heval1 : runJvmResFast 35 f_Algorithm_U64Buf_toArray_prog 0 f_Algorithm_U64Buf_toArray_prog
      (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]) =
    runJvmResFast 13 f_Algorithm_U64Buf_toArray_prog 22 (f_Algorithm_U64Buf_toArray_prog.drop 22)
      { (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]) with
        pc := 22,
        stack := [.i32 (coerceInI32 (arr[0]!.toUInt32 + 1) (coerceInI32 1 0 arr.size.toUInt32) arr.size.toUInt32),
          .i32 (coerceInI32 1 0 arr.size.toUInt32), .ext (.u64Ref 0)] } := rfl
  rw [heval1, hc1, hc2]
  have hs_lt : (1 : UInt32) < 0x80000000 := by decide
  have he_lt : arr[0]!.toUInt32 + 1 < 0x80000000 := by
    change (arr[0]!.toUInt32 + 1).toNat < 2147483648; omega
  have hse : (1 : UInt32) ≤ arr[0]!.toUInt32 + 1 := by
    change (1 : UInt32).toNat ≤ (arr[0]!.toUInt32 + 1).toNat
    simp only [UInt32.toNat_one]; omega
  have heb : (arr[0]!.toUInt32 + 1).toNat ≤ arr.size := by omega
  have hdrop22 : f_Algorithm_U64Buf_toArray_prog.drop 22 =
      [.invokestatic "kotlin/collections/ArraysKt" "copyOfRange" "([JII)[J",
       .invokestatic "kotlin/ULongArray" "constructor-impl" "([J)[J", .areturn] := rfl
  rw [hdrop22, show (13 : Nat) = 12 + 1 by decide]
  dsimp only [runJvmResFast, Jvm.runJvmResFast, Jvm.isBranchInstr]
  have hcopy : Jvm.stepInstr algHooks (.invokestatic "kotlin/collections/ArraysKt" "copyOfRange" "([JII)[J")
      { pc := 22, stack := [.i32 (arr[0]!.toUInt32 + 1), .i32 1, .ext (.u64Ref 0)],
        locals := (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]).locals,
        jvmHeap := (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]).jvmHeap,
        heap := (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]).heap } =
      stepInvokeStatic
        { pc := 22, stack := [.i32 (arr[0]!.toUInt32 + 1), .i32 1, .ext (.u64Ref 0)],
          locals := (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]).locals,
          jvmHeap := (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]).jvmHeap,
          heap := (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]).heap }
        "kotlin/collections/ArraysKt" "copyOfRange" "([JII)[J" := rfl
  rw [hcopy, stepStatic_arraysCopyOfRange_u64 (by rfl) hs_lt he_lt hse heb]
  dsimp only [Option.map]
  rw [UInt32.toNat_one]
  rfl

theorem u64Buf_toArray_equiv (arr : Array UInt64) (h1 : 1 ≤ arr.size) (h2 : arr.size < 2 ^ 31)
    (h3 : arr[0]!.toUInt32.toNat + 1 ≤ arr.size) :
    runJvmRes 35 f_Algorithm_U64Buf_toArray_prog (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]) =
      some ((.ext (.u64Ref 1)), { (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]) with
        pc := 24, stack := [(.ext (.u64Ref 1))], heap := { u64Arrays := [arr, Algorithm.U64Buf.toArray arr] } }) :=
  u64buf_toArray_of_prog f_Algorithm_U64Buf_toArray_prog rfl arr h1 h2 h3

theorem u64Buf_toArray_1_equiv (arr : Array UInt64) (h1 : 1 ≤ arr.size) (h2 : arr.size < 2 ^ 31)
    (h3 : arr[0]!.toUInt32.toNat + 1 ≤ arr.size) :
    runJvmRes 35 f_Algorithm_U64Buf_toArray_1_prog (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]) =
      some ((.ext (.u64Ref 1)), { (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]) with
        pc := 24, stack := [(.ext (.u64Ref 1))], heap := { u64Arrays := [arr, Algorithm.U64Buf.toArray arr] } }) :=
  u64buf_toArray_of_prog f_Algorithm_U64Buf_toArray_1_prog rfl arr h1 h2 h3

theorem u64Buf_toArray_2_equiv (arr : Array UInt64) (h1 : 1 ≤ arr.size) (h2 : arr.size < 2 ^ 31)
    (h3 : arr[0]!.toUInt32.toNat + 1 ≤ arr.size) :
    runJvmRes 35 f_Algorithm_U64Buf_toArray_2_prog (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]) =
      some ((.ext (.u64Ref 1)), { (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]) with
        pc := 24, stack := [(.ext (.u64Ref 1))], heap := { u64Arrays := [arr, Algorithm.U64Buf.toArray arr] } }) :=
  u64buf_toArray_of_prog f_Algorithm_U64Buf_toArray_2_prog rfl arr h1 h2 h3

theorem u64Buf_toArray_3_equiv (arr : Array UInt64) (h1 : 1 ≤ arr.size) (h2 : arr.size < 2 ^ 31)
    (h3 : arr[0]!.toUInt32.toNat + 1 ≤ arr.size) :
    runJvmRes 35 f_Algorithm_U64Buf_toArray_3_prog (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]) =
      some ((.ext (.u64Ref 1)), { (initJvmState [(0, (.ext (.u64Ref 0)))] [] [arr]) with
        pc := 24, stack := [(.ext (.u64Ref 1))], heap := { u64Arrays := [arr, Algorithm.U64Buf.toArray arr] } }) :=
  u64buf_toArray_of_prog f_Algorithm_U64Buf_toArray_3_prog rfl arr h1 h2 h3

theorem noCells_equiv :
    runJvmRes 10 f_Algorithm_noCells_prog (initJvmState []) =
      some ((.ext (.u64Ref 0)), { (initJvmState []) with pc := 2, stack := [(.ext (.u64Ref 0))], heap := { u64Arrays := [Algorithm.noCells] } }) := by rfl

theorem noCells_1_equiv :
    runJvmRes 10 f_Algorithm_noCells_1_prog (initJvmState []) =
      some ((.ext (.u64Ref 0)), { (initJvmState []) with pc := 2, stack := [(.ext (.u64Ref 0))], heap := { u64Arrays := [Algorithm.noCells] } }) := by rfl

theorem noCells_2_equiv :
    runJvmRes 10 f_Algorithm_noCells_2_prog (initJvmState []) =
      some ((.ext (.u64Ref 0)), { (initJvmState []) with pc := 2, stack := [(.ext (.u64Ref 0))], heap := { u64Arrays := [Algorithm.noCells] } }) := by rfl

theorem u64Buf_empty_equiv :
    runJvmRes 10 f_Algorithm_U64Buf_empty_prog (initJvmState []) =
      some ((.ext (.u64Ref 0)), { (initJvmState []) with pc := 2, stack := [(.ext (.u64Ref 0))], heap := { u64Arrays := [Algorithm.U64Buf.empty] } }) := by rfl

theorem u64Buf_empty_1_equiv :
    runJvmRes 10 f_Algorithm_U64Buf_empty_1_prog (initJvmState []) =
      some ((.ext (.u64Ref 0)), { (initJvmState []) with pc := 2, stack := [(.ext (.u64Ref 0))], heap := { u64Arrays := [Algorithm.U64Buf.empty] } }) := by rfl

theorem u64Buf_empty_2_equiv :
    runJvmRes 10 f_Algorithm_U64Buf_empty_2_prog (initJvmState []) =
      some ((.ext (.u64Ref 0)), { (initJvmState []) with pc := 2, stack := [(.ext (.u64Ref 0))], heap := { u64Arrays := [Algorithm.U64Buf.empty] } }) := by rfl

theorem u64Buf_empty_3_equiv :
    runJvmRes 10 f_Algorithm_U64Buf_empty_3_prog (initJvmState []) =
      some ((.ext (.u64Ref 0)), { (initJvmState []) with pc := 2, stack := [(.ext (.u64Ref 0))], heap := { u64Arrays := [Algorithm.U64Buf.empty] } }) := by rfl

theorem u64Buf_empty_4_equiv :
    runJvmRes 10 f_Algorithm_U64Buf_empty_4_prog (initJvmState []) =
      some ((.ext (.u64Ref 0)), { (initJvmState []) with pc := 2, stack := [(.ext (.u64Ref 0))], heap := { u64Arrays := [Algorithm.U64Buf.empty] } }) := by rfl

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
    runJvm 40 f_Algorithm_serializeLife106_prog (initJvmState [(0, (.ext (.u64Ref 0)))] [] [cells]) =
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
    runJvm 15 f_Algorithm_MacroCell_level_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some (.i32 m.level) := by rfl

theorem macroCell_cellHashCode_equiv (m : Algorithm.MacroCell) :
    runJvm 15 f_Algorithm_MacroCell_cellHashCode_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some (.i32 m.cellHashCode) := by rfl

theorem makeLevel4Node_1_equiv (nw ne sw se : UInt64) :
    runJvm 25 f_Algorithm_makeLevel4Node_1_prog
      (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se)]) =
      some ((.ext (.mc (Algorithm.makeLevel4Node nw ne sw se)))) := by rfl

theorem makeCellNode_1_equiv (nw ne sw se : Algorithm.MacroCell) :
    runJvm 70 f_Algorithm_makeCellNode_1_prog
      (initJvmState [(0, (.ext (.mc nw))), (1, (.ext (.mc ne))), (2, (.ext (.mc sw))), (3, (.ext (.mc se)))]) =
      some ((.ext (.mc (Algorithm.makeCellNode nw ne sw se)))) := by rfl

theorem macroCell_size_equiv (m : Algorithm.MacroCell) :
    runJvm 15 f_Algorithm_MacroCell_size_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some (.i64 m.size) := by rfl

theorem macroCell_hashCode_equiv (m : Algorithm.MacroCell) :
    runJvm 15 f_Algorithm_MacroCell_hashCode_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some (.i32 m.cellHashCode) := by rfl

theorem emptyLevel4_closed0_equiv :
    runJvm 15 f_Algorithm_emptyLevel4___closed__0_prog (initJvmState []) =
      some ((.ext (.mc Algorithm.emptyLevel4))) := by rfl

theorem emptyLevel4_equiv :
    runJvm 15 f_Algorithm_emptyLevel4_prog (initJvmState []) =
      some ((.ext (.mc Algorithm.emptyLevel4))) := by rfl

theorem centeredSubSubnodeFast_equiv (m : Algorithm.MacroCell) :
    runJvm 15 f_Algorithm_centeredSubSubnode_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some ((.ext (.mc (Algorithm.centeredSubSubnodeFast m)))) := by rfl

theorem centeredSubSubnode_equiv (m : Algorithm.MacroCell) (d : Nat) (hm : Algorithm.WFd m d) (h5 : 5 ≤ d) :
    runJvm 15 f_Algorithm_centeredSubSubnode_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some ((.ext (.mc (Algorithm.centeredSubSubnode m)))) := by
  rw [centeredSubSubnodeFast_equiv m, Algorithm.centeredSubSubnodeFast_eq_centeredSubSubnode_Impl hm h5]

theorem centeredSubSubnodeSizeFast_equiv (m : Algorithm.MacroCell) :
    runJvm 15 f_Algorithm_centeredSubSubnodeSize_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some (.i64 (Algorithm.centeredSubSubnodeSizeFast m)) := by rfl

theorem centeredSubSubnodeSize_equiv (m : Algorithm.MacroCell) (d : Nat) (hm : Algorithm.WFd m d) (h5 : 5 ≤ d) :
    runJvm 15 f_Algorithm_centeredSubSubnodeSize_prog (initJvmState [(0, (.ext (.mc m)))]) =
      some (.i64 (Algorithm.centeredSubSubnodeSize m)) := by
  rw [centeredSubSubnodeSizeFast_equiv m, Algorithm.centeredSubSubnodeSizeFast_eq_centeredSubSubnodeSize_Impl hm h5]

theorem stepHashLifeStateWith_equiv (st : Algorithm.HashLifeStepState) (f : Algorithm.MacroCell → Algorithm.MacroCell) :
    runJvm 50 f_Algorithm_stepHashLifeStateWith_prog
      (initJvmState [(0, (.ext (.hlState st))), (1, (.ext (.fnMcToMc f)))]) =
      some ((.ext (.hlState (Algorithm.stepHashLifeStateWith st f)))) := by rfl

theorem computeGenerationStep_equiv (step : UInt32) (st : Algorithm.HashLifeStepState)
    (computedGenerations : UInt64) (macroKeep leafKeep : UInt32)
    (stepOneGen : Algorithm.HashLifeStepState → Algorithm.HashLifeStepState) :
    runJvm 45 f_Algorithm_computeGenerationStep_prog
      (initJvmState [(0, .i32 step), (1, (.ext (.hlState st))), (2, .i64 computedGenerations),
        (4, .i32 macroKeep), (5, .i32 leafKeep), (6, (.ext (.fnHlToHl stepOneGen)))]) =
      some ((.ext (.stepBatch (Algorithm.computeGenerationStep step st computedGenerations macroKeep leafKeep stepOneGen)))) := by
  change some (JvmVal.ext (AlgExt.stepBatch _)) = some (JvmVal.ext (AlgExt.stepBatch _))
  congr 4
  dsimp [Jvm.JvmVal.asI32, Jvm.JvmVal.asI64, setLocal, initJvmState, Jvm.initJvmState, List.foldl]
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
      some ((.ext (.mc (Algorithm.emptyMacroCellUInt32 level)))) := by rfl

theorem macrocellLeafChild_closed0_equiv :
    runJvm 10 f_Algorithm_macrocellLeafChild___closed__0_prog (initJvmState []) = some (.boxedULong 0) := by rfl

theorem serializePlaintextCells_equiv (cells : Array UInt64) :
    runJvm 45 f_Algorithm_serializePlaintextCells_prog (initJvmState [(0, (.ext (.u64Ref 0)))] [] [cells]) =
      some (.strArr (Algorithm.serializePlaintextCells cells)) := by rfl

theorem asciiStringLossy_equiv (bytes : ByteArray) (s e : UInt32) :
    runJvm 35 f_Algorithm_asciiStringLossy_prog
      (initJvmState [(0, (.ext (.byteArr bytes))), (1, .i32 s), (2, .i32 e)]) =
      some (.str (Algorithm.asciiStringLossy bytes s e)) := by rfl

theorem expandRuns_closed0_equiv :
    runJvm 15 f_Algorithm_expandRuns___closed__0_prog (initJvmState []) =
      some (.pair (.boxedUInt 0) (.boxedUInt 0)) := by rfl

theorem parseRLEData_closed0_equiv :
    runJvm 15 f_Algorithm_parseRLEData___closed__0_prog (initJvmState []) =
      some (.pair (.boxedUInt 0) (.boxedUInt 1)) := by rfl

theorem parseRLEComments_closed1_equiv :
    runJvm 15 f_Algorithm_parseRLEComments___closed__1_prog (initJvmState []) =
      some ((.ext (.rleStatus (.invalidHeader "none")))) := by rfl

theorem wrapRLEItems_closed0_equiv :
    runJvm 15 f_Algorithm_wrapRLEItems___closed__0_prog (initJvmState []) =
      some (.pair (.boxedUByte 0) (.boxedUInt 0)) := by rfl

theorem serializeRLE_closed0_equiv :
    runJvm 15 f_Algorithm_serializeRLE___closed__0_prog (initJvmState []) =
      some (.pair (.boxedUByte 33) (.boxedUInt 1)) := by rfl

theorem serializeRLECells_equiv (cells : Array UInt64) :
    runJvm 45 f_Algorithm_serializeRLECells_prog (initJvmState [(0, (.ext (.u64Ref 0)))] [] [cells]) =
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
      (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se), (8, (.ext (.fnU64ToU32 fn)))]) =
      some (.i64 (Algorithm.computeLevel4NextGen16x16WithUInt nw ne sw se fn)) := by
  apply runJvm_of_stepListAtClean _ f_Algorithm_computeLevel4NextGen16x16WithUInt_prog _ _ _ rfl (by decide)
  change stepListAtClean 0 f_Algorithm_computeLevel4NextGen16x16WithUInt_prog
    (initJvmState [(0, .i64 nw), (2, .i64 ne), (4, .i64 sw), (6, .i64 se), (8, (.ext (.fnU64ToU32 fn)))]) =
    some (.i64 (Algorithm.computeLevel4NextGen16x16WithUInt nw ne sw se fn))
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem stepLevel4NodeWith_spec0_equiv (nw ne sw se : UInt64) (fn : UInt64 → UInt32) :
    runJvm 800 f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_stepLevel4NodeWith_spec__0_prog
      (initJvmState [(0, (.ext (.fnU64ToU32 fn))), (1, .i64 nw), (3, .i64 ne), (5, .i64 sw), (7, .i64 se)]) =
      some (.i64 (Algorithm.computeLevel4NextGen16x16WithUInt nw ne sw se fn)) := by
  apply runJvm_of_stepListAtClean _ f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_stepLevel4NodeWith_spec__0_prog _ _ _ rfl (by decide)
  change stepListAtClean 0 f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_stepLevel4NodeWith_spec__0_prog
    (initJvmState [(0, (.ext (.fnU64ToU32 fn))), (1, .i64 nw), (3, .i64 ne), (5, .i64 sw), (7, .i64 se)]) =
    some (.i64 (Algorithm.computeLevel4NextGen16x16WithUInt nw ne sw se fn))
  rfl


end Algorithm.JvmVerification
