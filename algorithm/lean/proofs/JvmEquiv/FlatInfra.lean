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
import proofs.JvmEquiv.Batch2

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

private theorem lcmp_eq_zero (a b : UInt64) (c : Bool) :
    ((if (a == b) = true then (0 : UInt32) else if c = true then 4294967295 else 1) = 0) ↔ a = b :=
  Jvm.lcmp_eq_zero a b c

private theorem u8_sext_eq_zero (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 0) ↔ b = 0 :=
  Jvm.u8_sext_eq_zero b

private theorem u8_sext_eq_one (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 1) ↔ b = 1 :=
  Jvm.u8_sext_eq_one b

private theorem u8_sext_eq_five (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 5) ↔ b = 5 :=
  Jvm.u8_sext_eq_five b

private theorem u8_sext_eq_six (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 6) ↔ b = 6 :=
  Jvm.u8_sext_eq_six b

private theorem u8_sext_eq_seven (b : UInt8) : (b.toInt8.toInt32.toUInt32 = 7) ↔ b = 7 :=
  Jvm.u8_sext_eq_seven b

theorem u8_sub1_u32_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((BitVec.setWidth 32 b.toBitVec &&& 255#32) - 1#32))) } : UInt8) = b - 1 :=
  Jvm.u8_sub1_u32_jvm b

private theorem u8_sub1_sext_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 1#32))) } : UInt8) = b - 1 :=
  Jvm.u8_sub1_sext_jvm b

private theorem u8_sub2_sext_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 2#32))) } : UInt8) = b - 2 :=
  Jvm.u8_sub2_sext_jvm b

private theorem u8_add1_sext_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) + 1#32))) } : UInt8) = b + 1 :=
  Jvm.u8_add1_sext_jvm b

private theorem u8_add2_sext_jvm (b : UInt8) :
    ({ toBitVec := BitVec.setWidth 8 (BitVec.signExtend 32
        (BitVec.setWidth 8 ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) + 2#32))) } : UInt8) = b + 2 :=
  Jvm.u8_add2_sext_jvm b

private theorem u8_and255_sext_jvm (b : UInt8) :
    (b.toInt8.toInt32.toUInt32 &&& 255) = b.toUInt32 :=
  Jvm.u8_and255_sext_jvm b

private theorem u8_sub1_and255_u32 (b : UInt8) :
    UInt32.ofBitVec ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 1#32) = b.toUInt32 - 1 :=
  Jvm.u8_sub1_and255_u32 b

private theorem u8_sub5_and255_u32 (b : UInt8) :
    UInt32.ofBitVec ((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 5#32) = b.toUInt32 - 5 :=
  Jvm.u8_sub5_and255_u32 b

private theorem u8_sub1_sub5_and255_u32 (b : UInt8) :
    UInt32.ofBitVec (((b.toInt8.toInt32.toUInt32.toBitVec &&& 255#32) - 1#32) - 5#32) = (b.toUInt32 - 1) - 5 :=
  Jvm.u8_sub1_sub5_and255_u32 b

private theorem u8_ext_u32 (b : UInt8) :
    UInt32.ofBitVec (BitVec.setWidth 32 b.toBitVec) = b.toUInt32 :=
  Jvm.u8_ext_u32 b

private theorem u8_sext_toUInt8 (b : UInt8) :
    b.toInt8.toInt32.toUInt32.toUInt8 = b :=
  Jvm.u8_sext_toUInt8 b

private theorem u8_sub1_u32_exact (b : UInt8) :
    ({ toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 (b.toUInt32 - 1).toBitVec) } : UInt32).toUInt8 = b - 1 :=
  Jvm.u8_sub1_u32_exact b

private theorem u8_sub2_u32_exact (b : UInt8) :
    ({ toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 (b.toUInt32 - 2).toBitVec) } : UInt32).toUInt8 = b - 2 :=
  Jvm.u8_sub2_u32_exact b

private theorem u8_add1_u32_exact (b : UInt8) :
    ({ toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 (b.toUInt32 + 1).toBitVec) } : UInt32).toUInt8 = b + 1 :=
  Jvm.u8_add1_u32_exact b

private theorem u8_add2_u32_exact (b : UInt8) :
    ({ toBitVec := BitVec.signExtend 32 (BitVec.setWidth 8 (b.toUInt32 + 2).toBitVec) } : UInt32).toUInt8 = b + 2 :=
  Jvm.u8_add2_u32_exact b

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
  Jvm.ui32_toNat_add_1 a

private theorem ui32_toNat_add_2 (a : UInt32) : (a + 2).toNat = (a.toNat + 2) % 4294967296 :=
  Jvm.ui32_toNat_add_2 a

private theorem ui32_toNat_add_3 (a : UInt32) : (a + 3).toNat = (a.toNat + 3) % 4294967296 :=
  Jvm.ui32_toNat_add_3 a

private theorem ui32_toNat_add_4 (a : UInt32) : (a + 4).toNat = (a.toNat + 4) % 4294967296 :=
  Jvm.ui32_toNat_add_4 a

private theorem beq_false_of_ne' {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) : (a == b) = false :=
  Jvm.beq_false_of_ne' h

private theorem bne_true_of_ne' {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) : (a != b) = true :=
  Jvm.bne_true_of_ne' h

export Jvm (eq_of_ite_branches)

private theorem compareUnsigned_eq_zero (a b : UInt32) :
    ((if a == b then (0 : UInt32) else if a < b then 4294967295 else 1) = 0) ↔ a = b :=
  Jvm.compareUnsigned_eq_zero a b

private theorem compareUnsigned64_sge' (a b : UInt64) :
    (0#32).sle (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec = decide (b ≤ a) :=
  Jvm.compareUnsigned64_sge' a b

def isFlatStopLeaf : JvmInstr → Bool
  | .invokestatic _ _ _ => true
  | .invokevirtual _ _ _ => true
  | .invokespecial _ _ _ => true
  | .invokeinterface _ _ _ => true
  | .baload => true
  | .aaload => true
  | .bastore => true
  | .newarray _ => true
  | _ => false

def isFlatStop (i : JvmInstr) : Bool :=
  isBranchInstr i || isFlatStopLeaf i

def stepFlatChunk : Nat → Nat → Nat → List JvmInstr → JvmState → BlockChunkRes AlgExt AlgHeap :=
  Jvm.stepBlockChunkWith algHooks isFlatStopLeaf

theorem runJvmValFast_stepFlatChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmValFast fuel prog pc instrs st = afterBlockChunk (stepFlatChunk maxSteps fuel pc instrs st) prog :=
  Jvm.runJvmValFast_stepBlockChunkWith algHooks isFlatStopLeaf maxSteps fuel prog pc instrs st

def stepResFlatChunk : Nat → Nat → Nat → List JvmInstr → JvmState → BlockResChunkRes AlgExt AlgHeap :=
  Jvm.stepResBlockChunkWith algHooks isFlatStopLeaf

theorem runJvmResFast_stepResFlatChunk (maxSteps fuel : Nat) (prog : List JvmInstr) (pc : Nat)
    (instrs : List JvmInstr) (st : JvmState) :
    runJvmResFast fuel prog pc instrs st = afterResBlockChunk (stepResFlatChunk maxSteps fuel pc instrs st) prog :=
  Jvm.runJvmResFast_stepBlockChunkWith algHooks isFlatStopLeaf maxSteps fuel prog pc instrs st

theorem runJvmValFast_invokestatic_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hs : stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmValFast (f1 + 1) prog pc (.invokestatic cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  Jvm.runJvmValFast_invokestatic_step algHooks hs

theorem runJvmResFast_invokestatic_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hs : stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmResFast (f1 + 1) prog pc (.invokestatic cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  Jvm.runJvmResFast_invokestatic_step algHooks hs

theorem runJvmValFast_baload {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {idx : UInt32} {addr : Nat} {stkRest : List JvmVal} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    runJvmValFast (f1 + 1) prog pc (.baload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmValFast f1 prog (pc + 1) rest
        ⟨pc + 1, .i32 (UInt32.ofBitVec (BitVec.signExtend 32 elems[idx.toNat].toBitVec)) :: stkRest,
          locs, jh, hp⟩ :=
  Jvm.runJvmValFast_baload algHooks hget hslt hlt

theorem runJvmValFast_aaload {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {idx : UInt32} {addr : Nat} {stkRest : List JvmVal} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cls : String} {elems : Array JvmVal}
    (hget : jh.get? addr = some (.objArray cls elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    runJvmValFast (f1 + 1) prog pc (.aaload :: rest)
        ⟨pc0, .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmValFast f1 prog (pc + 1) rest
        ⟨pc + 1, elems[idx.toNat] :: stkRest, locs, jh, hp⟩ :=
  Jvm.runJvmValFast_aaload algHooks hget hslt hlt

theorem runJvmResFast_bastore {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {v idx : UInt32} {addr : Nat} {stkRest : List JvmVal} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems))
    (hslt : idx.toBitVec.slt 0#32 = false)
    (hlt : idx.toNat < elems.size) :
    runJvmResFast (f1 + 1) prog pc (.bastore :: rest)
        ⟨pc0, .i32 v :: .i32 idx :: .heapRef addr :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f1 prog (pc + 1) rest
        ⟨pc + 1, stkRest, locs, jh.set addr (.byteArray (elems.set idx.toNat v.toUInt8 hlt)), hp⟩ :=
  Jvm.runJvmResFast_bastore algHooks hget hslt hlt

export Jvm (jvmHeap_get?_set_self)

theorem runJvmResFast_newarray_byte {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {n : UInt32} {stkRest : List JvmVal} {rest : List JvmInstr} {pc0 : Nat}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hslt : n.toBitVec.slt 0#32 = false) :
    runJvmResFast (f1 + 1) prog pc (.newarray "byte" :: rest)
        ⟨pc0, .i32 n :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f1 prog (pc + 1) rest
        ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
          (jh.alloc (.byteArray (Array.replicate n.toNat 0))).2, hp⟩ :=
  Jvm.runJvmResFast_newarray_byte algHooks hslt

theorem runJvmValFast_invokevirtual_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hs : stepInvokeVirtual ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmValFast (f1 + 1) prog pc (.invokevirtual cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  Jvm.runJvmValFast_invokevirtual_step algHooks hs

theorem runJvmResFast_invokevirtual_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hs : stepInvokeVirtual ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmResFast (f1 + 1) prog pc (.invokevirtual cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  Jvm.runJvmResFast_invokevirtual_step algHooks hs

private theorem runJvmValFast_invokespecial_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hs : stepInvokeSpecial ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmValFast (f1 + 1) prog pc (.invokespecial cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  Jvm.runJvmValFast_invokespecial_step algHooks hs

theorem runJvmResFast_invokespecial_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hs : stepInvokeSpecial ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmResFast (f1 + 1) prog pc (.invokespecial cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  Jvm.runJvmResFast_invokespecial_step algHooks hs

private theorem runJvmResFast_invokespecial_pred {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hf : 0 < f)
    (hs : stepInvokeSpecial ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmResFast f prog pc (.invokespecial cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast (f - 1) prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  Jvm.runJvmResFast_invokespecial_pred algHooks hf hs

private theorem runJvmValFast_invokeinterface_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hs : stepInvokeInterface ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmValFast (f1 + 1) prog pc (.invokeinterface cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmValFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  Jvm.runJvmValFast_invokeinterface_step algHooks hs

private theorem runJvmResFast_invokeinterface_step {f1 : Nat} {prog : List JvmInstr} {pc : Nat}
    {cls method desc : String} {rest : List JvmInstr} {pc0 : Nat} {stk stk' : List JvmVal}
    {locs : Nat → JvmVal} {jh jh' : Jvm.JvmHeap AlgExt} {hp hp' : AlgHeap}
    (hs : stepInvokeInterface ⟨pc, stk, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, stk', locs, jh', hp'⟩)) :
    runJvmResFast (f1 + 1) prog pc (.invokeinterface cls method desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f1 prog (pc + 1) rest ⟨pc + 1, stk', locs, jh', hp'⟩ :=
  Jvm.runJvmResFast_invokeinterface_step algHooks hs

private theorem updateArena_eq_some {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {id : Nat} {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a)
    (f : Algorithm.FlatHashLifeArena → Algorithm.FlatHashLifeArena) :
    updateArena ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩ id f =
      some ⟨pc + 1, stk, locs, jh, ⟨ar.set id (f a), u64, asc⟩⟩ := by
  simp only [updateArena, har]

theorem stepStatic_checkNotNullParameter
    {pc : Nat} {msg obj : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hnull : obj.isNull = false) :
    stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar, u64, asc⟩⟩) :=
  Jvm.stepInvokeStatic_intrinsics_checkNotNullParam algHooks hnull

private theorem stepStatic_uintCtor
    {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UInt" "constructor-impl" "(I)I" =
      .inl (some ⟨pc + 1, stk, locs, jh, ⟨ar, u64, asc⟩⟩) :=
  Jvm.stepInvokeStatic_uint_ctor algHooks

private theorem stepStatic_ulongCtor
    {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULong" "constructor-impl" "(J)J" =
      .inl (some ⟨pc + 1, stk, locs, jh, ⟨ar, u64, asc⟩⟩) :=
  Jvm.stepInvokeStatic_ulong_ctor algHooks

private theorem stepStatic_ubyteCtor
    {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UByte" "constructor-impl" "(B)B" =
      .inl (some ⟨pc + 1, stk, locs, jh, ⟨ar, u64, asc⟩⟩) :=
  Jvm.stepInvokeStatic_ubyte_ctor algHooks

private theorem stepStatic_intCompareUnsigned
    {pc : Nat} {b a : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "java/lang/Integer" "compareUnsigned" "(II)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩) :=
  Jvm.stepInvokeStatic_integer_compareUnsigned algHooks

private theorem stepStatic_intDivideUnsigned
    {pc : Nat} {a : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i32 5 :: .i32 a :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "java/lang/Integer" "divideUnsigned" "(II)I" =
      .inl (some ⟨pc + 1, .i32 (a / 5) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) :=
  Jvm.stepInvokeStatic_integer_divideUnsigned algHooks (b := 5) (by decide)

private theorem stepStatic_uintArrGet
    {pc : Nat} {idx : UInt32} {id : Nat} {f : ArenaU32Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 idx :: (.ext (.arenaU32Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UIntArray" "get-pVg5ArA" "([II)I" =
      .inl (some ⟨pc + 1, .i32 ((getArenaU32 a f)[idx.toNat]!) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 idx :: (.ext (.arenaU32Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UIntArray" "get-pVg5ArA" "([II)I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 ((getArenaU32 a f)[idx.toNat]!) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_uintArrGetSize
    {pc : Nat} {id : Nat} {f : ArenaU32Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, (.ext (.arenaU32Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UIntArray" "getSize-impl" "([I)I" =
      .inl (some ⟨pc + 1, .i32 (getArenaU32 a f).size.toUInt32 :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, (.ext (.arenaU32Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UIntArray" "getSize-impl" "([I)I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 (getArenaU32 a f).size.toUInt32 :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_ubyteArrGet
    {pc : Nat} {idx : UInt32} {id : Nat} {f : ArenaU8Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 idx :: (.ext (.arenaU8Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UByteArray" "get-w2LRezQ" "([BI)B" =
      .inl (some ⟨pc + 1, .i32 ((getArenaU8 a f)[idx.toNat]!).toInt8.toInt32.toUInt32 :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 idx :: (.ext (.arenaU8Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UByteArray" "get-w2LRezQ" "([BI)B" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 ((getArenaU8 a f)[idx.toNat]!).toInt8.toInt32.toUInt32 :: rest,
          locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_ulongArrGetArena
    {pc : Nat} {idx : UInt32} {id : Nat} {f : ArenaU64Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 idx :: (.ext (.arenaU64Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" =
      .inl (some ⟨pc + 1, .i64 ((getArenaU64 a f)[idx.toNat]!) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 idx :: (.ext (.arenaU64Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i64 ((getArenaU64 a f)[idx.toNat]!) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

theorem stepStatic_ulongArrGetU64
    {pc : Nat} {idx : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {arr : Array UInt64} (hu : u64[id]? = some arr) :
    stepInvokeStatic ⟨pc, .i32 idx :: (.ext (.u64Ref id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" =
      .inl (some ⟨pc + 1, .i64 (arr[idx.toNat]!) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 idx :: (.ext (.u64Ref id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" =
      match u64[id]? with
      | some arr => .inl (some ⟨pc + 1, .i64 (arr[idx.toNat]!) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, hu]

private theorem stepStatic_ulongArrSetU64
    {pc : Nat} {val : UInt64} {idx : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {arr : Array UInt64} (hu : u64[id]? = some arr) :
    stepInvokeStatic ⟨pc, .i64 val :: .i32 idx :: (.ext (.u64Ref id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULongArray" "set-k8EXiF4" "([JIJ)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar, u64.set id (arr.set! idx.toNat val), asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i64 val :: .i32 idx :: (.ext (.u64Ref id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULongArray" "set-k8EXiF4" "([JIJ)V" =
      match u64[id]? with
      | some arr => .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar, u64.set id (arr.set! idx.toNat val), asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, hu]

private theorem stepStatic_ulongArrSetArena
    {pc : Nat} {val : UInt64} {idx : UInt32} {id : Nat} {f : ArenaU64Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i64 val :: .i32 idx :: (.ext (.arenaU64Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULongArray" "set-k8EXiF4" "([JIJ)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id (setArenaU64 a f ((getArenaU64 a f).set! idx.toNat val)), u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i64 val :: .i32 idx :: (.ext (.arenaU64Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULongArray" "set-k8EXiF4" "([JIJ)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => setArenaU64 a f ((getArenaU64 a f).set! idx.toNat val))) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_uintArrSet
    {pc : Nat} {val idx : UInt32} {id : Nat} {f : ArenaU32Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 val :: .i32 idx :: (.ext (.arenaU32Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UIntArray" "set-VXSXFK8" "([III)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id (setArenaU32 a f ((getArenaU32 a f).set! idx.toNat val)), u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 val :: .i32 idx :: (.ext (.arenaU32Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UIntArray" "set-VXSXFK8" "([III)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => setArenaU32 a f ((getArenaU32 a f).set! idx.toNat val))) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_ubyteArrSet
    {pc : Nat} {val idx : UInt32} {id : Nat} {f : ArenaU8Field} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 val :: .i32 idx :: (.ext (.arenaU8Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UByteArray" "set-VurrAj0" "([BIB)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id (setArenaU8 a f ((getArenaU8 a f).set! idx.toNat val.toUInt8)), u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 val :: .i32 idx :: (.ext (.arenaU8Ref id f)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UByteArray" "set-VurrAj0" "([BIB)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => setArenaU8 a f ((getArenaU8 a f).set! idx.toNat val.toUInt8))) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_checkNotNull
    {pc : Nat} {msg obj : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hnull : obj.isNull = false) :
    stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar, u64, asc⟩⟩) :=
  Jvm.stepInvokeStatic_intrinsics_checkNotNull algHooks hnull

private theorem stepStatic_intrinsicsCompare
    {pc : Nat} {b a : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/jvm/internal/Intrinsics" "compare" "(II)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a == b then 0 else if a.toBitVec.slt b.toBitVec then 4294967295 else 1) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩) :=
  Jvm.stepInvokeStatic_intrinsics_compare algHooks

private theorem stepStatic_longCompareUnsigned
    {pc : Nat} {b a : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i64 b :: .i64 a :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "java/lang/Long" "compareUnsigned" "(JJ)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩) :=
  Jvm.stepInvokeStatic_long_compareUnsigned algHooks

private theorem stepStatic_intValueOf
    {pc : Nat} {v : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i32 v :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" =
      .inl (some ⟨pc + 1, .boxedInt v :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) :=
  Jvm.stepInvokeStatic_integer_valueOf algHooks

private theorem stepStatic_ulongBox
    {pc : Nat} {v : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i64 v :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULong" "box-impl" "(J)Lkotlin/ULong;" =
      .inl (some ⟨pc + 1, .boxedULong v :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) :=
  Jvm.stepInvokeStatic_ulong_box algHooks

private theorem stepStatic_flat_getRemapCell
    {pc : Nat} {nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_getRemapCell-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.getRemapCell a nodeId) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_getRemapCell-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 (Algorithm.getRemapCell a nodeId) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_getCellStepRes
    {pc : Nat} {nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_getCellStepRes-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.getCellStepRes a nodeId) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_getCellStepRes-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 (Algorithm.getCellStepRes a nodeId) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_centeredSubSubnodeSizeCell
    {pc : Nat} {nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_centeredSubSubnodeSizeCell-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)J" =
      .inl (some ⟨pc + 1, .i64 (Algorithm.centeredSubSubnodeSizeCell a nodeId) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_centeredSubSubnodeSizeCell-Qn1smSk" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)J" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i64 (Algorithm.centeredSubSubnodeSizeCell a nodeId) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_computeLevel4NextGen
    {pc : Nat} {se sw ne nw : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i64 se :: .i64 sw :: .i64 ne :: .i64 nw :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0-2jIhpxI"
      "(JJJJ)J" =
      .inl (some ⟨pc + 1,
        .i64 (Algorithm.computeLevel4NextGen16x16UInt nw ne sw se) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepStatic_flat_centeredHorizontal
    {pc : Nat} {eId wId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 eId :: .i32 wId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredHorizontal-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.centeredHorizontal wId eId).1 :: rest, locs, jh, ⟨ar.set id (a.centeredHorizontal wId eId).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 eId :: .i32 wId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredHorizontal-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.centeredHorizontal wId eId
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_centeredVertical
    {pc : Nat} {sId nId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 sId :: .i32 nId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredVertical-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.centeredVertical nId sId).1 :: rest, locs, jh, ⟨ar.set id (a.centeredVertical nId sId).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 sId :: .i32 nId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredVertical-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.centeredVertical nId sId
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_centeredSubnode
    {pc : Nat} {nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredSubnode-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.centeredSubnode nodeId).1 :: rest, locs, jh, ⟨ar.set id (a.centeredSubnode nodeId).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredSubnode-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.centeredSubnode nodeId
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_centeredSubSubnode
    {pc : Nat} {nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredSubSubnode-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.centeredSubSubnode nodeId).1 :: rest, locs, jh, ⟨ar.set id (a.centeredSubSubnode nodeId).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_centeredSubSubnode-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.centeredSubSubnode nodeId
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_quadrantNW
    {pc : Nat} {nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantNW-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.quadrantNW nodeId).1 :: rest, locs, jh, ⟨ar.set id (a.quadrantNW nodeId).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantNW-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.quadrantNW nodeId
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_quadrantNE
    {pc : Nat} {nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantNE-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.quadrantNE nodeId).1 :: rest, locs, jh, ⟨ar.set id (a.quadrantNE nodeId).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantNE-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.quadrantNE nodeId
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_quadrantSW
    {pc : Nat} {nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantSW-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.quadrantSW nodeId).1 :: rest, locs, jh, ⟨ar.set id (a.quadrantSW nodeId).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantSW-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.quadrantSW nodeId
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_quadrantSE
    {pc : Nat} {nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantSE-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.quadrantSE nodeId).1 :: rest, locs, jh, ⟨ar.set id (a.quadrantSE nodeId).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_quadrantSE-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.quadrantSE nodeId
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_stepLevel4
    {pc : Nat} {l4Id : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 l4Id :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_stepLevel4-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)J" =
      .inl (some ⟨pc + 1,
        .i64 (a.stepLevel4 l4Id).1 :: rest, locs, jh, ⟨ar.set id (a.stepLevel4 l4Id).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 l4Id :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_stepLevel4-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)J" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.stepLevel4 l4Id
        .inl (some ⟨pc + 1, .i64 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_stepLevel5
    {pc : Nat} {nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_stepLevel5-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.stepLevel5 nodeId).1 :: rest, locs, jh, ⟨ar.set id (a.stepLevel5 nodeId).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_stepLevel5-Qn1smSk"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;I)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.stepLevel5 nodeId
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_setRemapL4
    {pc : Nat} {val idx : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 val :: .i32 idx :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setRemapL4-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id (a.setRemapL4 idx val), u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 val :: .i32 idx :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setRemapL4-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => a.setRemapL4 idx val)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_setRemapCell
    {pc : Nat} {val idx : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 val :: .i32 idx :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setRemapCell-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id (a.setRemapCell idx val), u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 val :: .i32 idx :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setRemapCell-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => a.setRemapCell idx val)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_setCellStepRes
    {pc : Nat} {val idx : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 val :: .i32 idx :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setCellStepRes-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id (a.setCellStepRes idx val), u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 val :: .i32 idx :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setCellStepRes-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => a.setCellStepRes idx val)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_setL4StepRes
    {pc : Nat} {val : UInt64} {idx : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i64 val :: .i32 idx :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setL4StepRes-c82oGLE"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IJ)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id (a.setL4StepRes idx val), u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i64 val :: .i32 idx :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setL4StepRes-c82oGLE"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IJ)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => a.setL4StepRes idx val)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_setOverflow
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setOverflow"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id a.setOverflow, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_setOverflow"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => a.setOverflow)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_expandFrame
    {pc : Nat} {base nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 base :: .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_expandFrame-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id (a.expandFrame nodeId base), u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 base :: .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_expandFrame-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => a.expandFrame nodeId base)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_initRemapL4Loop
    {pc : Nat} {limit i : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 limit :: .i32 i :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_initRemapL4Loop-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id (a.initRemapL4Loop i limit), u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 limit :: .i32 i :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_initRemapL4Loop-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => a.initRemapL4Loop i limit)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_initRemapCellLoop
    {pc : Nat} {limit i : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 limit :: .i32 i :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_initRemapCellLoop-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id (a.initRemapCellLoop i limit), u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 limit :: .i32 i :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_initRemapCellLoop-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => a.initRemapCellLoop i limit)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_stepCellSerialLoop
    {pc : Nat} {fuel limit sp : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 fuel :: .i32 limit :: .i32 sp :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_stepCellSerialLoop-7IvYBaQ"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;III)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id (a.stepCellSerialLoop sp limit fuel), u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 fuel :: .i32 limit :: .i32 sp :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_stepCellSerialLoop-7IvYBaQ"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;III)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => a.stepCellSerialLoop sp limit fuel)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_copyL4From
    {pc : Nat} {copyMemos l4Id : UInt32} {srcId dstId : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {dst src : Algorithm.FlatHashLifeArena} (hdst : ar[dstId]? = some dst) (hsrc : ar[srcId]? = some src) :
    stepInvokeStatic ⟨pc, .i32 copyMemos :: .i32 l4Id :: (.ext (.arenaRef srcId)) :: (.ext (.arenaRef dstId)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_copyL4From-BzPDsQc"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IZ)I" =
      .inl (some ⟨pc + 1,
        .i32 (dst.copyL4From src l4Id (copyMemos != 0)).1 :: rest, locs, jh, ⟨ar.set dstId (dst.copyL4From src l4Id (copyMemos != 0)).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 copyMemos :: .i32 l4Id :: (.ext (.arenaRef srcId)) :: (.ext (.arenaRef dstId)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_copyL4From-BzPDsQc"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IZ)I" =
      match ar[dstId]?, ar[srcId]? with
      | some dst, some src =>
        let (r, dst') := dst.copyL4From src l4Id (copyMemos != 0)
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set dstId dst', u64, asc⟩⟩)
      | _, _ => .inr none := rfl
  rw [hfn, hdst, hsrc]

private theorem stepStatic_flat_copyCellFromLoop
    {pc : Nat} {fuel sp stackBase copyMemos : UInt32} {srcId dstId : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)}
    {asc : List Algorithm.AsciiBytes} {dst src : Algorithm.FlatHashLifeArena}
    (hdst : ar[dstId]? = some dst) (hsrc : ar[srcId]? = some src) :
    stepInvokeStatic ⟨pc, .i32 fuel :: .i32 sp :: .i32 stackBase :: .i32 copyMemos :: (.ext (.arenaRef srcId)) :: (.ext (.arenaRef dstId)) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_copyCellFromLoop-sA3nruY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;ZIII)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set dstId (dst.copyCellFromLoop src (copyMemos != 0) stackBase sp fuel),
        u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 fuel :: .i32 sp :: .i32 stackBase :: .i32 copyMemos :: (.ext (.arenaRef srcId)) :: (.ext (.arenaRef dstId)) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_copyCellFromLoop-sA3nruY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;ZIII)V" =
      match ar[dstId]?, ar[srcId]? with
      | some dst, some src =>
        .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set dstId (dst.copyCellFromLoop src (copyMemos != 0) stackBase sp fuel),
          u64, asc⟩⟩)
      | _, _ => .inr none := rfl
  rw [hfn, hdst, hsrc]

private theorem stepVirtual_arena_canCopySubgraphFrom
    {pc : Nat} {srcId dstId : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {dst src : Algorithm.FlatHashLifeArena} (hdst : ar[dstId]? = some dst) (hsrc : ar[srcId]? = some src) :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef srcId)) :: (.ext (.arenaRef dstId)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena"
      "canCopySubgraphFrom" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;)Z" =
      .inl (some ⟨pc + 1, .i32 (if dst.canCopySubgraphFrom src then 1 else 0) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, (.ext (.arenaRef srcId)) :: (.ext (.arenaRef dstId)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena"
      "canCopySubgraphFrom" "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;)Z" =
      match ar[dstId]?, ar[srcId]? with
      | some dst, some src =>
        .inl (some ⟨pc + 1, .i32 (if dst.canCopySubgraphFrom src then 1 else 0) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | _, _ => .inr none := rfl
  rw [hfn, hdst, hsrc]

private theorem stepVirtual_arena_getCellCount
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellCount-pVg5ArA" "()I" =
      .inl (some ⟨pc + 1, .i32 a.cellCount :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellCount-pVg5ArA" "()I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 a.cellCount :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepVirtual_arena_getCellMask
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellMask-pVg5ArA" "()I" =
      .inl (some ⟨pc + 1, .i32 a.cellMask :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellMask-pVg5ArA" "()I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 a.cellMask :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepVirtual_arena_getL4Count
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Count-pVg5ArA" "()I" =
      .inl (some ⟨pc + 1, .i32 a.l4Count :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Count-pVg5ArA" "()I" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 a.l4Count :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepVirtual_arena_getOverflow
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getOverflow-w2LRezQ" "()B" =
      .inl (some ⟨pc + 1, .i32 a.overflow.toInt8.toInt32.toUInt32 :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getOverflow-w2LRezQ" "()B" =
      match ar[id]? with
      | some a => .inl (some ⟨pc + 1, .i32 a.overflow.toInt8.toInt32.toUInt32 :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepVirtual_arena_getCellLevel
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellLevel-TcUX1vc" "()[B" =
      .inl (some ⟨pc + 1, (.ext (.arenaU8Ref id .cellLevel)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getL4HasRes
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4HasRes-TcUX1vc" "()[B" =
      .inl (some ⟨pc + 1, (.ext (.arenaU8Ref id .l4HasRes)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getCellNe
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellNe--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, (.ext (.arenaU32Ref id .cellNe)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getCellNw
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellNw--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, (.ext (.arenaU32Ref id .cellNw)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getCellSw
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellSw--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, (.ext (.arenaU32Ref id .cellSw)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getCellSe
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellSe--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, (.ext (.arenaU32Ref id .cellSe)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getCellStepRes
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellStepRes--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, (.ext (.arenaU32Ref id .cellStepRes)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getRemapCell
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getRemapCell--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, (.ext (.arenaU32Ref id .remapCell)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getRemapL4
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getRemapL4--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, (.ext (.arenaU32Ref id .remapL4)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getCellPop
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellPop-Y2RjT0g" "()[J" =
      .inl (some ⟨pc + 1, (.ext (.arenaU64Ref id .cellPop)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getL4Nw
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Nw-Y2RjT0g" "()[J" =
      .inl (some ⟨pc + 1, (.ext (.arenaU64Ref id .l4Nw)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getL4Ne
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Ne-Y2RjT0g" "()[J" =
      .inl (some ⟨pc + 1, (.ext (.arenaU64Ref id .l4Ne)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getL4Sw
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Sw-Y2RjT0g" "()[J" =
      .inl (some ⟨pc + 1, (.ext (.arenaU64Ref id .l4Sw)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getL4Se
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Se-Y2RjT0g" "()[J" =
      .inl (some ⟨pc + 1, (.ext (.arenaU64Ref id .l4Se)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getL4StepRes
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4StepRes-Y2RjT0g" "()[J" =
      .inl (some ⟨pc + 1, (.ext (.arenaU64Ref id .l4StepRes)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_internCellNode
    {pc : Nat} {se sw ne nw lvl : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeVirtual ⟨pc, .i32 se :: .i32 sw :: .i32 ne :: .i32 nw :: .i32 lvl :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "internCellNode-gt5aIGQ" "(BIIII)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.internCellNode lvl.toUInt8 nw ne sw se).1 :: rest, locs, jh, ⟨ar.set id (a.internCellNode lvl.toUInt8 nw ne sw se).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, .i32 se :: .i32 sw :: .i32 ne :: .i32 nw :: .i32 lvl :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "internCellNode-gt5aIGQ" "(BIIII)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.internCellNode lvl.toUInt8 nw ne sw se
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepVirtual_arena_internLevel4
    {pc : Nat} {se sw ne nw : UInt64} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeVirtual ⟨pc, .i64 se :: .i64 sw :: .i64 ne :: .i64 nw :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "internLevel4-PT-fW9Q" "(JJJJ)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.internLevel4 nw ne sw se).1 :: rest, locs, jh, ⟨ar.set id (a.internLevel4 nw ne sw se).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeVirtual ⟨pc, .i64 se :: .i64 sw :: .i64 ne :: .i64 nw :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "internLevel4-PT-fW9Q" "(JJJJ)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.internLevel4 nw ne sw se
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_expandFrameIfNeeded
    {pc : Nat} {base nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 base :: .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar.set id (a.expandFrameIfNeeded nodeId base), u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 base :: .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded-BltQuoY"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;II)V" =
      .inl (updateArena ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ id (fun a => a.expandFrameIfNeeded nodeId base)) := rfl
  rw [hfn, updateArena_eq_some har]

private theorem stepStatic_flat_combineQuadrants
    {pc : Nat} {se sw ne nw lvl nodeId : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {a : Algorithm.FlatHashLifeArena} (har : ar[id]? = some a) :
    stepInvokeStatic ⟨pc, .i32 se :: .i32 sw :: .i32 ne :: .i32 nw :: .i32 lvl :: .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_combineQuadrants-t447iZE"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IBIIII)I" =
      .inl (some ⟨pc + 1,
        .i32 (a.combineQuadrants nodeId lvl.toUInt8 nw ne sw se).1 :: rest, locs, jh, ⟨ar.set id (a.combineQuadrants nodeId lvl.toUInt8 nw ne sw se).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 se :: .i32 sw :: .i32 ne :: .i32 nw :: .i32 lvl :: .i32 nodeId :: (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_FlatHashLifeArena_combineQuadrants-t447iZE"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IBIIII)I" =
      match ar[id]? with
      | some a =>
        let (r, a') := a.combineQuadrants nodeId lvl.toUInt8 nw ne sw se
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set id a', u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, har]

private theorem stepStatic_flat_copyCellTryStep
    {pc : Nat} {copyMemos cellId : UInt32} {srcId dstId : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {dst src : Algorithm.FlatHashLifeArena} (hdst : ar[dstId]? = some dst) (hsrc : ar[srcId]? = some src) :
    stepInvokeStatic ⟨pc, .i32 copyMemos :: .i32 cellId :: (.ext (.arenaRef srcId)) :: (.ext (.arenaRef dstId)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_copyCellTryStep-BzPDsQc"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IZ)I" =
      .inl (some ⟨pc + 1,
        .i32 (Algorithm.copyCellTryStep dst src cellId (copyMemos != 0)).1 :: rest, locs, jh, ⟨ar.set dstId (Algorithm.copyCellTryStep dst src cellId (copyMemos != 0)).2, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 copyMemos :: .i32 cellId :: (.ext (.arenaRef srcId)) :: (.ext (.arenaRef dstId)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_copyCellTryStep-BzPDsQc"
      "(Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;Lcom/alexvanyo/composelife/algorithm/FlatHashLifeArena;IZ)I" =
      match ar[dstId]?, ar[srcId]? with
      | some dst, some src =>
        let (r, dst') := Algorithm.copyCellTryStep dst src cellId (copyMemos != 0)
        .inl (some ⟨pc + 1, .i32 r :: rest, locs, jh, ⟨ar.set dstId dst', u64, asc⟩⟩)
      | _, _ => .inr none := rfl
  rw [hfn, hdst, hsrc]

private theorem stepStatic_flat_leafContains
    {pc : Nat} {y x : UInt32} {leaf : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i32 y :: .i32 x :: .i64 leaf :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt"
      "f_Algorithm_leafContains-fMEO4hA" "(JII)Z" =
      .inl (some ⟨pc + 1, .i32 (if Algorithm.leafContains leaf x y then 1 else 0) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepStatic_makeCellNode
    {pc : Nat} {se sw ne nw : Algorithm.MacroCell} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, (.ext (.mc se)) :: (.ext (.mc sw)) :: (.ext (.mc ne)) :: (.ext (.mc nw)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt"
      "f_Algorithm_makeCellNode"
      "(Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;)Lcom/alexvanyo/composelife/model/MacroCell;" =
      .inl (some ⟨pc + 1, (.ext (.mc (Algorithm.makeCellNode nw ne sw se))) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepStatic_decodeCharAt
    {pc : Nat} {limit p : UInt32} {bytes : ByteArray} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i32 limit :: .i32 p :: (.ext (.byteArr bytes)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/PlaintextLeanKt"
      "f_Algorithm_decodeCharAt-BltQuoY" "([BII)Lkotlin/Pair;" =
      .inl (some ⟨pc + 1,
        .pair (.boxedUInt (Algorithm.decodeCharAt bytes p limit).1)
          (.boxedUInt (Algorithm.decodeCharAt bytes p limit).2) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepStatic_formatCoordLine
    {pc : Nat} {y x : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i32 y :: .i32 x :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/Life106LeanKt"
      "f_Algorithm_formatCoordLine-feOb9K0" "(II)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (Algorithm.formatCoordLine x y) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepStatic_growBufPush_105
    {pc : Nat} {s : String} {b : Algorithm.GrowBuf String} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .str s :: (.ext (.strGrowBuf b)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_GrowBuf_push___redArg" "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, (.ext (.strGrowBuf (b.push s))) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepStatic_growBufPush_106
    {pc : Nat} {s : String} {b : Algorithm.GrowBuf String} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .str s :: (.ext (.strGrowBuf b)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/Life106LeanKt"
      "f_Algorithm_GrowBuf_push___redArg" "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, (.ext (.strGrowBuf (b.push s))) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepStatic_growBufPush_plain
    {pc : Nat} {s : String} {b : Algorithm.GrowBuf String} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .str s :: (.ext (.strGrowBuf b)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/PlaintextLeanKt"
      "f_Algorithm_GrowBuf_push___redArg" "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, (.ext (.strGrowBuf (b.push s))) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

theorem stepStatic_u64BufPush_105
    {pc : Nat} {x : UInt64} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {arr : Array UInt64} (hu : u64[id]? = some arr) :
    stepInvokeStatic ⟨pc, .i64 x :: (.ext (.u64Ref id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_U64Buf_push-3yFGk1Y" "([JJ)[J" =
      .inl (some ⟨pc + 1, (.ext (.u64Ref u64.length)) :: rest, locs, jh, ⟨ar,
        u64 ++ [Algorithm.U64Buf.push arr x], asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i64 x :: (.ext (.u64Ref id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_U64Buf_push-3yFGk1Y" "([JJ)[J" =
      match u64[id]? with
      | some arr => .inl (some ⟨pc + 1, (.ext (.u64Ref u64.length)) :: rest, locs, jh, ⟨ar,
          u64 ++ [Algorithm.U64Buf.push arr x], asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, hu]

private theorem stepStatic_asciiToStringRange_105
    {pc : Nat} {e s : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {g : Algorithm.AsciiBytes} (hasc : asc[id]? = some g) :
    stepInvokeStatic ⟨pc, .i32 e :: .i32 s :: (.ext (.asciiRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_AsciiBytes_toStringRange-BltQuoY" "([BII)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (g.toStringRange s e) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 e :: .i32 s :: (.ext (.asciiRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_AsciiBytes_toStringRange-BltQuoY" "([BII)Ljava/lang/String;" =
      match asc[id]? with
      | some g => .inl (some ⟨pc + 1, .str (g.toStringRange s e) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, hasc]

private theorem stepStatic_asciiToStringRange_plain
    {pc : Nat} {e s : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {g : Algorithm.AsciiBytes} (hasc : asc[id]? = some g) :
    stepInvokeStatic ⟨pc, .i32 e :: .i32 s :: (.ext (.asciiRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/PlaintextLeanKt"
      "f_Algorithm_AsciiBytes_toStringRange-BltQuoY" "([BII)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (g.toStringRange s e) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 e :: .i32 s :: (.ext (.asciiRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/PlaintextLeanKt"
      "f_Algorithm_AsciiBytes_toStringRange-BltQuoY" "([BII)Ljava/lang/String;" =
      match asc[id]? with
      | some g => .inl (some ⟨pc + 1, .str (g.toStringRange s e) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, hasc]

theorem stepStatic_asciiSet_105
    {pc : Nat} {v i : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {g : Algorithm.AsciiBytes} (hasc : asc[id]? = some g) (hb : v.toUInt8 < 128) :
    stepInvokeStatic ⟨pc, .i32 v :: .i32 i :: (.ext (.asciiRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar, u64, asc.set id (g.set i v.toUInt8 hb)⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 v :: .i32 i :: (.ext (.asciiRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/Life105LeanKt"
      "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" =
      match asc[id]? with
      | some g =>
        if hb' : v.toUInt8 < 128 then
          .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar, u64, asc.set id (g.set i v.toUInt8 hb')⟩⟩)
        else .inr none
      | none => .inr none := rfl
  rw [hfn, hasc]; simp only [hb, ↓reduceDIte]

theorem stepStatic_asciiSet_plain
    {pc : Nat} {v i : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {g : Algorithm.AsciiBytes} (hasc : asc[id]? = some g) (hb : v.toUInt8 < 128) :
    stepInvokeStatic ⟨pc, .i32 v :: .i32 i :: (.ext (.asciiRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/PlaintextLeanKt"
      "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar, u64, asc.set id (g.set i v.toUInt8 hb)⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 v :: .i32 i :: (.ext (.asciiRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/PlaintextLeanKt"
      "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" =
      match asc[id]? with
      | some g =>
        if hb' : v.toUInt8 < 128 then
          .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar, u64, asc.set id (g.set i v.toUInt8 hb')⟩⟩)
        else .inr none
      | none => .inr none := rfl
  rw [hfn, hasc]; simp only [hb, ↓reduceDIte]

theorem stepStatic_asciiSet_rle
    {pc : Nat} {v i : UInt32} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {g : Algorithm.AsciiBytes} (hasc : asc[id]? = some g) (hb : v.toUInt8 < 128) :
    stepInvokeStatic ⟨pc, .i32 v :: .i32 i :: (.ext (.asciiRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/RleLeanKt"
      "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar, u64, asc.set id (g.set i v.toUInt8 hb)⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 v :: .i32 i :: (.ext (.asciiRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/RleLeanKt"
      "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" =
      match asc[id]? with
      | some g =>
        if hb' : v.toUInt8 < 128 then
          .inl (some ⟨pc + 1, rest, locs, jh, ⟨ar, u64, asc.set id (g.set i v.toUInt8 hb')⟩⟩)
        else .inr none
      | none => .inr none := rfl
  rw [hfn, hasc]; simp only [hb, ↓reduceDIte]

private theorem stepStatic_coerceIn
    {pc : Nat} {hi lo v : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i32 hi :: .i32 lo :: .i32 v :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ranges/RangesKt" "coerceIn" "(III)I" =
      .inl (some ⟨pc + 1, .i32 (coerceInI32 v lo hi) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepStatic_makeLevel4Node
    {pc : Nat} {se sw ne nw : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i64 se :: .i64 sw :: .i64 ne :: .i64 nw :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "f_Algorithm_makeLevel4Node-2jIhpxI" "(JJJJ)Lcom/alexvanyo/composelife/model/MacroCell;" =
      .inl (some ⟨pc + 1, .ext (.mc (Algorithm.makeLevel4Node nw ne sw se)) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepStatic_computeNextGen4x4BitwiseUInt
    {pc : Nat} {w : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, .i32 w :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "f_Algorithm_computeNextGen4x4BitwiseUInt-WZ4Q5Ns" "(I)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.computeNextGen4x4BitwiseUInt w) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

theorem stepStatic_getNextGen4x4Lut
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} {lutAddr : Nat}
    (hlut : jh.getStatic? "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "NEXT_GEN_4X4_LUT" = some (.heapRef lutAddr)) :
    stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "getNEXT_GEN_4X4_LUT" "()[B" =
      .inl (some ⟨pc + 1, .heapRef lutAddr :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "getNEXT_GEN_4X4_LUT" "()[B" =
      match jh.getStatic? "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "NEXT_GEN_4X4_LUT" with
      | some v => .inl (some ⟨pc + 1, v :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, hlut]

theorem stepStatic_getNextGen4x4LutPkg
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} {lutAddr : Nat}
    (hlut : jh.getStatic? "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "NEXT_GEN_4X4_LUT" = some (.heapRef lutAddr)) :
    stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "getNEXT_GEN_4X4_LUT" "()[B" =
      .inl (some ⟨pc + 1, .heapRef lutAddr :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "getNEXT_GEN_4X4_LUT" "()[B" =
      match jh.getStatic? "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt" "NEXT_GEN_4X4_LUT" with
      | some v => .inl (some ⟨pc + 1, v :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, hlut]

theorem stepStatic_getEmptyLevel4
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hl4 : jh.getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_LEVEL_4" = some (.ext (.mc Algorithm.emptyLevel4))) :
    stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "getEMPTY_LEVEL_4" "()Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;" =
      .inl (some ⟨pc + 1, .ext (.mc Algorithm.emptyLevel4) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "getEMPTY_LEVEL_4" "()Lcom/alexvanyo/composelife/model/MacroCell$Level4Node;" =
      .inl (some ⟨pc + 1,
        ((jh.getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_LEVEL_4").getD (.ext (.mc Algorithm.emptyLevel4))) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩) := rfl
  rw [hfn, hl4]; rfl

theorem stepStatic_getEmptyNodes
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} {nodesAddr : Nat}
    (hnodes : jh.getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_NODES" = some (.heapRef nodesAddr)) :
    stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "getEMPTY_NODES" "()[Lcom/alexvanyo/composelife/model/MacroCell;" =
      .inl (some ⟨pc + 1, .heapRef nodesAddr :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have hfn : stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/model/MacroCellLeanKt" "getEMPTY_NODES" "()[Lcom/alexvanyo/composelife/model/MacroCell;" =
      match jh.getStatic? "com/alexvanyo/composelife/model/MacroCellLeanKt" "EMPTY_NODES" with
      | some v => .inl (some ⟨pc + 1, v :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [hfn, hnodes]

private theorem stepVirtual_arena_getCellNext
    {pc id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getCellNext--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, (.ext (.arenaU32Ref id .cellNext)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_arena_getL4Next
    {pc id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, (.ext (.arenaRef id)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "com/alexvanyo/composelife/algorithm/FlatHashLifeArena" "getL4Next--hP7Qyg" "()[I" =
      .inl (some ⟨pc + 1, (.ext (.arenaU32Ref id .l4Next)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_pair_getSecond
    {pc : Nat} {a b : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .pair a b :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/Pair" "getSecond" "()Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, b :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepVirtual_uint_unbox
    {pc : Nat} {v : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeVirtual ⟨pc, .boxedUInt v :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/UInt" "unbox-impl" "()I" =
      .inl (some ⟨pc + 1, .i32 v :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepSpecial_pair_init
    {pc : Nat} {a b : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeSpecial ⟨pc, b :: a :: .allocRef "kotlin/Pair" :: .allocRef "kotlin/Pair" :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V" =
      .inl (some ⟨pc + 1, .pair a b :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepInterface_fn1_hlToHl
    {pc : Nat} {fn : Algorithm.HashLifeStepState → Algorithm.HashLifeStepState}
    {hs : Algorithm.HashLifeStepState} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeInterface ⟨pc, (.ext (.hlState hs)) :: (.ext (.fnHlToHl fn)) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/jvm/functions/Function1" "invoke" "(Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, (.ext (.hlState (fn hs))) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

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

private partial def normNatExpr (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let e ← reduceStateProj e
  let ew ← Lean.Meta.whnf e
  if let some n := ew.rawNatLit? then
    return Lean.mkNatLit n
  if ew.isConstOf ``Nat.zero then
    return Lean.mkNatLit 0
  if ew.isAppOfArity ``Nat.succ 1 then
    let a ← normNatExpr ew.appArg!
    if let some n := a.rawNatLit? then
      return Lean.mkNatLit (n + 1)
    return Lean.mkApp ew.getAppFn a
  return ew

private def normFlatStateExpr (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let sw ← Lean.Meta.whnf e
  if sw.isAppOfArity ``Jvm.JvmState.mk 7 then
    let args := sw.getAppArgs
    let pc' ← normNatExpr args[2]!
    let stk' ← normListSpine args[3]!
    let locs' ← reduceStateProj args[4]!
    let jh' ← reduceStateProj args[5]!
    let hw ← Lean.Meta.whnf args[6]!
    let heap' ←
      if hw.isAppOfArity ``AlgHeap.mk 3 then
        let hargs := hw.getAppArgs
        let ar' ← normListSpine hargs[0]!
        let u64' ← normListSpine hargs[1]!
        let asc' ← normListSpine hargs[2]!
        pure (Lean.mkAppN hw.getAppFn #[ar', u64', asc'])
      else
        pure hw
    return Lean.mkAppN sw.getAppFn #[args[0]!, args[1]!, pc', stk', locs', jh', heap']
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
  | ``Jvm.JvmInstr.invokestatic, "kotlin/jvm/internal/Intrinsics", "checkNotNullParameter", _ =>
    [(``stepStatic_checkNotNullParameter, 1)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/UInt", "constructor-impl", "(I)I" =>
    [(``stepStatic_uintCtor, 0)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/ULong", "constructor-impl", "(J)J" =>
    [(``stepStatic_ulongCtor, 0)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/UByte", "constructor-impl", "(B)B" =>
    [(``stepStatic_ubyteCtor, 0)]
  | ``Jvm.JvmInstr.invokestatic, "java/lang/Integer", "compareUnsigned", "(II)I" =>
    [(``stepStatic_intCompareUnsigned, 0)]
  | ``Jvm.JvmInstr.invokestatic, "java/lang/Integer", "divideUnsigned", "(II)I" =>
    [(``stepStatic_intDivideUnsigned, 0)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/UIntArray", "get-pVg5ArA", "([II)I" =>
    [(``stepStatic_uintArrGet, 1)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/UIntArray", "getSize-impl", "([I)I" =>
    [(``stepStatic_uintArrGetSize, 1)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/UByteArray", "get-w2LRezQ", "([BI)B" =>
    [(``stepStatic_ubyteArrGet, 1)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/ULongArray", "get-s-VKNKU", "([JI)J" =>
    [(``stepStatic_ulongArrGetArena, 1), (``stepStatic_ulongArrGetU64, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_getRemapCell-Qn1smSk", _ =>
    [(``stepStatic_flat_getRemapCell, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_getCellStepRes-Qn1smSk", _ =>
    [(``stepStatic_flat_getCellStepRes, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_centeredSubSubnodeSizeCell-Qn1smSk", _ =>
    [(``stepStatic_flat_centeredSubSubnodeSizeCell, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_computeLevel4NextGen16x16WithUInt___at___00Algorithm_computeLevel4NextGen16x16UInt_spec__0-2jIhpxI", _ =>
    [(``stepStatic_flat_computeLevel4NextGen, 0)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_centeredHorizontal-BltQuoY", _ =>
    [(``stepStatic_flat_centeredHorizontal, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_centeredVertical-BltQuoY", _ =>
    [(``stepStatic_flat_centeredVertical, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_centeredSubnode-Qn1smSk", _ =>
    [(``stepStatic_flat_centeredSubnode, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_centeredSubSubnode-Qn1smSk", _ =>
    [(``stepStatic_flat_centeredSubSubnode, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_quadrantNW-Qn1smSk", _ =>
    [(``stepStatic_flat_quadrantNW, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_quadrantNE-Qn1smSk", _ =>
    [(``stepStatic_flat_quadrantNE, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_quadrantSW-Qn1smSk", _ =>
    [(``stepStatic_flat_quadrantSW, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_quadrantSE-Qn1smSk", _ =>
    [(``stepStatic_flat_quadrantSE, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_stepLevel4-Qn1smSk", _ =>
    [(``stepStatic_flat_stepLevel4, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_stepLevel5-Qn1smSk", _ =>
    [(``stepStatic_flat_stepLevel5, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_setRemapL4-BltQuoY", _ =>
    [(``stepStatic_flat_setRemapL4, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_setRemapCell-BltQuoY", _ =>
    [(``stepStatic_flat_setRemapCell, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_setCellStepRes-BltQuoY", _ =>
    [(``stepStatic_flat_setCellStepRes, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_setL4StepRes-c82oGLE", _ =>
    [(``stepStatic_flat_setL4StepRes, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_setOverflow", _ =>
    [(``stepStatic_flat_setOverflow, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_expandFrame-BltQuoY", _ =>
    [(``stepStatic_flat_expandFrame, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_initRemapL4Loop-BltQuoY", _ =>
    [(``stepStatic_flat_initRemapL4Loop, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_initRemapCellLoop-BltQuoY", _ =>
    [(``stepStatic_flat_initRemapCellLoop, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_stepCellSerialLoop-7IvYBaQ", _ =>
    [(``stepStatic_flat_stepCellSerialLoop, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_copyL4From-BzPDsQc", _ =>
    [(``stepStatic_flat_copyL4From, 2)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_copyCellFromLoop-sA3nruY", _ =>
    [(``stepStatic_flat_copyCellFromLoop, 2)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "canCopySubgraphFrom", _ =>
    [(``stepVirtual_arena_canCopySubgraphFrom, 2)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellCount-pVg5ArA", _ =>
    [(``stepVirtual_arena_getCellCount, 1)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellMask-pVg5ArA", _ =>
    [(``stepVirtual_arena_getCellMask, 1)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Count-pVg5ArA", _ =>
    [(``stepVirtual_arena_getL4Count, 1)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getOverflow-w2LRezQ", _ =>
    [(``stepVirtual_arena_getOverflow, 1)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellLevel-TcUX1vc", _ =>
    [(``stepVirtual_arena_getCellLevel, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4HasRes-TcUX1vc", _ =>
    [(``stepVirtual_arena_getL4HasRes, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellNe--hP7Qyg", _ =>
    [(``stepVirtual_arena_getCellNe, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellNw--hP7Qyg", _ =>
    [(``stepVirtual_arena_getCellNw, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellSw--hP7Qyg", _ =>
    [(``stepVirtual_arena_getCellSw, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellSe--hP7Qyg", _ =>
    [(``stepVirtual_arena_getCellSe, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellStepRes--hP7Qyg", _ =>
    [(``stepVirtual_arena_getCellStepRes, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getRemapCell--hP7Qyg", _ =>
    [(``stepVirtual_arena_getRemapCell, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getRemapL4--hP7Qyg", _ =>
    [(``stepVirtual_arena_getRemapL4, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellPop-Y2RjT0g", _ =>
    [(``stepVirtual_arena_getCellPop, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Nw-Y2RjT0g", _ =>
    [(``stepVirtual_arena_getL4Nw, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Ne-Y2RjT0g", _ =>
    [(``stepVirtual_arena_getL4Ne, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Sw-Y2RjT0g", _ =>
    [(``stepVirtual_arena_getL4Sw, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Se-Y2RjT0g", _ =>
    [(``stepVirtual_arena_getL4Se, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4StepRes-Y2RjT0g", _ =>
    [(``stepVirtual_arena_getL4StepRes, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "internCellNode-gt5aIGQ", _ =>
    [(``stepVirtual_arena_internCellNode, 1)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "internLevel4-PT-fW9Q", _ =>
    [(``stepVirtual_arena_internLevel4, 1)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getCellNext--hP7Qyg", _ =>
    [(``stepVirtual_arena_getCellNext, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "com/alexvanyo/composelife/algorithm/FlatHashLifeArena", "getL4Next--hP7Qyg", _ =>
    [(``stepVirtual_arena_getL4Next, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "kotlin/Pair", "getSecond", _ =>
    [(``stepVirtual_pair_getSecond, 0)]
  | ``Jvm.JvmInstr.invokevirtual, "kotlin/UInt", "unbox-impl", _ =>
    [(``stepVirtual_uint_unbox, 0)]
  | ``Jvm.JvmInstr.invokespecial, "kotlin/Pair", "<init>", _ =>
    [(``stepSpecial_pair_init, 0)]
  | ``Jvm.JvmInstr.invokeinterface, "kotlin/jvm/functions/Function1", "invoke", _ =>
    [(``stepInterface_fn1_hlToHl, 0)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/jvm/internal/Intrinsics", "checkNotNull", _ =>
    [(``stepStatic_checkNotNull, 1)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/jvm/internal/Intrinsics", "compare", "(II)I" =>
    [(``stepStatic_intrinsicsCompare, 0)]
  | ``Jvm.JvmInstr.invokestatic, "java/lang/Long", "compareUnsigned", "(JJ)I" =>
    [(``stepStatic_longCompareUnsigned, 0)]
  | ``Jvm.JvmInstr.invokestatic, "java/lang/Integer", "valueOf", _ =>
    [(``stepStatic_intValueOf, 0)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/ULong", "box-impl", _ =>
    [(``stepStatic_ulongBox, 0)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/ULongArray", "set-k8EXiF4", "([JIJ)V" =>
    [(``stepStatic_ulongArrSetU64, 1), (``stepStatic_ulongArrSetArena, 1)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/UIntArray", "set-VXSXFK8", "([III)V" =>
    [(``stepStatic_uintArrSet, 1)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/UByteArray", "set-VurrAj0", "([BIB)V" =>
    [(``stepStatic_ubyteArrSet, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded-BltQuoY", _ =>
    [(``stepStatic_flat_expandFrameIfNeeded, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_FlatHashLifeArena_combineQuadrants-t447iZE", _ =>
    [(``stepStatic_flat_combineQuadrants, 1)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_copyCellTryStep-BzPDsQc", _ =>
    [(``stepStatic_flat_copyCellTryStep, 2)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_leafContains-fMEO4hA", _ =>
    [(``stepStatic_flat_leafContains, 0)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_makeCellNode", _ =>
    [(``stepStatic_makeCellNode, 0)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_makeLevel4Node-2jIhpxI", _ =>
    [(``stepStatic_makeLevel4Node, 0)]
  | ``Jvm.JvmInstr.invokestatic, "kotlin/ranges/RangesKt", "coerceIn", _ =>
    [(``stepStatic_coerceIn, 0)]
  | ``Jvm.JvmInstr.invokestatic, "com/alexvanyo/composelife/algorithm/AlgorithmLeanKt", "f_Algorithm_computeNextGen4x4BitwiseUInt-WZ4Q5Ns", _ =>
    [(``stepStatic_computeNextGen4x4BitwiseUInt, 0)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_decodeCharAt-BltQuoY", _ =>
    [(``stepStatic_decodeCharAt, 0)]
  | ``Jvm.JvmInstr.invokestatic, _, "f_Algorithm_formatCoordLine-feOb9K0", _ =>
    [(``stepStatic_formatCoordLine, 0)]
  | ``Jvm.JvmInstr.invokestatic, "com/alexvanyo/composelife/model/Life105LeanKt", "f_Algorithm_U64Buf_push-3yFGk1Y", _ =>
    [(``stepStatic_u64BufPush_105, 1)]
  | ``Jvm.JvmInstr.invokestatic, "com/alexvanyo/composelife/model/Life105LeanKt", "f_Algorithm_AsciiBytes_toStringRange-BltQuoY", _ =>
    [(``stepStatic_asciiToStringRange_105, 1)]
  | ``Jvm.JvmInstr.invokestatic, "com/alexvanyo/composelife/model/PlaintextLeanKt", "f_Algorithm_AsciiBytes_toStringRange-BltQuoY", _ =>
    [(``stepStatic_asciiToStringRange_plain, 1)]
  | ``Jvm.JvmInstr.invokestatic, "com/alexvanyo/composelife/model/Life105LeanKt", "f_Algorithm_GrowBuf_push___redArg", _ =>
    [(``stepStatic_growBufPush_105, 0)]
  | ``Jvm.JvmInstr.invokestatic, "com/alexvanyo/composelife/model/Life106LeanKt", "f_Algorithm_GrowBuf_push___redArg", _ =>
    [(``stepStatic_growBufPush_106, 0)]
  | ``Jvm.JvmInstr.invokestatic, "com/alexvanyo/composelife/model/PlaintextLeanKt", "f_Algorithm_GrowBuf_push___redArg", _ =>
    [(``stepStatic_growBufPush_plain, 0)]
  | _, _, _, _ => []

def tryStepFlatInvoke : Lean.Elab.Tactic.TacticM Bool := do
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
  if opName != ``Jvm.JvmInstr.invokestatic && opName != ``Jvm.JvmInstr.invokevirtual &&
     opName != ``Jvm.JvmInstr.invokespecial && opName != ``Jvm.JvmInstr.invokeinterface then
    return false
  let args := instr.getAppArgs
  if args.size < 3 then return false
  let (some cls, some method, some desc) :=
    (← extractStrLit? args[0]!, ← extractStrLit? args[1]!, ← extractStrLit? args[2]!) | return false
  let bridgeName :=
    if !isRes then
      if opName == ``Jvm.JvmInstr.invokestatic then ``runJvmValFast_invokestatic_step
      else if opName == ``Jvm.JvmInstr.invokevirtual then ``runJvmValFast_invokevirtual_step
      else if opName == ``Jvm.JvmInstr.invokespecial then ``runJvmValFast_invokespecial_step
      else ``runJvmValFast_invokeinterface_step
    else
      if opName == ``Jvm.JvmInstr.invokestatic then ``runJvmResFast_invokestatic_step
      else if opName == ``Jvm.JvmInstr.invokevirtual then ``runJvmResFast_invokevirtual_step
      else if opName == ``Jvm.JvmInstr.invokespecial then ``runJvmResFast_invokespecial_step
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

def isRunJvmAtFlatNonStop : Lean.Elab.Tactic.TacticM Bool := do
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
        if cn == ``Jvm.BlockChunkRes.cont then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_cont]))
        else if cn == ``Jvm.BlockChunkRes.jump then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_jump]))
        else if cn == ``Jvm.BlockChunkRes.done then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterBlockChunk_done]))
      else
        if cn == ``Jvm.BlockResChunkRes.cont then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_cont]))
        else if cn == ``Jvm.BlockResChunkRes.jump then
          Lean.Elab.Tactic.evalTactic (← `(tactic| rw [afterResBlockChunk_jump]))
        else if cn == ``Jvm.BlockResChunkRes.done then
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

theorem lcmp_beq_eq_zero (a b : UInt64) (c : Bool) :
    ((if a == b then (0 : UInt32) else if c then 4294967295 else 1) == 0) = (a == b) := by
  by_cases h : a = b <;> cases c <;> simp [h]

private theorem lcmp_eq_zero' (a b : UInt64) [d : Decidable (a = b)] (c : Bool) [dc : Decidable (c = true)] :
    ((@ite _ (a = b) d (0 : UInt32) (@ite _ (c = true) dc 4294967295 1)) = 0) ↔ a = b := by
  by_cases h : a = b <;> cases c <;> simp [h]

theorem u8_sext_beq_zero (b : UInt8) : (b.toInt8.toInt32.toUInt32 == 0) = (b == 0) := by
  revert b; decide

private theorem u8_sext_beq_one (b : UInt8) : (b.toInt8.toInt32.toUInt32 == 1) = (b == 1) := by
  revert b; decide

theorem u8_sext_beq_five (b : UInt8) : (b.toInt8.toInt32.toUInt32 == 5) = (b == 5) := by
  revert b; decide

theorem u8_sext_beq_six (b : UInt8) : (b.toInt8.toInt32.toUInt32 == 6) = (b == 6) := by
  revert b; decide

theorem u8_sext_beq_seven (b : UInt8) : (b.toInt8.toInt32.toUInt32 == 7) = (b == 7) := by
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


end Algorithm.JvmVerification
