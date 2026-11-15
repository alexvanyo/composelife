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
import proofs.JvmEquiv.HeapInfra
import proofs.JvmEquiv.SharedStep
import proofs.JvmEquiv.StepExt

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

/-! ### Sub-batch 2B: Life106 (`formatCoordLine`, `deserializeLife106*`) -/

private theorem cellKey_bits_eq (x y : Int32) :
    ((UInt64.ofBitVec (x.toUInt32.toBitVec.signExtend 64) &&& 4294967295) <<<
        ((32 : UInt32).toUInt64 &&& 63)) +
      ((UInt64.ofBitVec (y.toUInt32.toBitVec.signExtend 64) &&& 4294967295) &&& 4294967295) =
      Algorithm.cellBits (x, y) := by
  have hmask : ∀ v : UInt32,
      ({ toBitVec := v.toBitVec.signExtend 64 } : UInt64) &&& 4294967295 = v.toUInt64 := by
    intro v
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i hlt64
    simp only [UInt64.toBitVec_and, BitVec.getLsbD_and, BitVec.getLsbD_signExtend, hlt64,
      decide_true, Bool.true_and]
    rw [show UInt64.toBitVec 4294967295 = 4294967295#64 from rfl]
    by_cases hi32 : i < 32
    · have h64 : (4294967295#64).getLsbD i = true := by
        rw [BitVec.getLsbD_eq_getElem hlt64]; revert i hlt64 hi32; decide
      have hv64 : v.toUInt64.toBitVec.getLsbD i = v.toBitVec.getLsbD i := by
        simp only [UInt32.toBitVec_toUInt64, BitVec.getLsbD_setWidth, hlt64, decide_true, Bool.true_and]
      simp only [hi32, ↓reduceIte, h64, hv64, Bool.and_true]
    · have h64 : (4294967295#64).getLsbD i = false := by
        rw [BitVec.getLsbD_eq_getElem hlt64]; revert i hlt64 hi32; decide
      have hv64 : v.toUInt64.toBitVec.getLsbD i = false := by
        simp only [UInt32.toBitVec_toUInt64, BitVec.getLsbD_setWidth, hlt64, decide_true, Bool.true_and]
        exact @BitVec.getLsbD_of_ge 32 v.toBitVec i (Nat.le_of_not_lt hi32)
      rw [h64, Bool.and_false, hv64]
  have hsh : ((32 : UInt32).toUInt64 &&& 63) = 32 := rfl
  change ({ toBitVec := x.toUInt32.toBitVec.signExtend 64 } &&& 4294967295) <<< ((32 : UInt32).toUInt64 &&& 63) +
      (({ toBitVec := y.toUInt32.toBitVec.signExtend 64 } &&& 4294967295) &&& 4294967295) = _
  rw [hmask x.toUInt32, hmask y.toUInt32, hsh]
  rfl

theorem formatCoordLine_equiv (x y : UInt32) :
    runJvm 20 f_Algorithm_formatCoordLine_prog (initJvmState [(0, .i32 x), (1, .i32 y)]) =
      some (.str (Algorithm.formatCoordLine x y)) := by
  apply runJvm_of_runJvmValFast0 20 _ _ _ rfl
  have hconcat : @Jvm.evalMakeConcatWithConstants AlgExt "\x01\x01\x01"
      "(Ljava/lang/String;Ljava/lang/String;I)Ljava/lang/String;"
      [.i32 y, .str " ", .str (Jvm.i32ToDecimalString x)] =
      some (Jvm.i32ToDecimalString x ++ (" " ++ (Jvm.i32ToDecimalString y ++ "")), []) := rfl
  have hstep1 : runJvmValFast 20 f_Algorithm_formatCoordLine_prog 0 f_Algorithm_formatCoordLine_prog
      (initJvmState [(0, .i32 x), (1, .i32 y)]) =
      runJvmValFast 12 f_Algorithm_formatCoordLine_prog 8
        (f_Algorithm_formatCoordLine_prog.drop 8)
        ⟨8, [.i32 y, .str " ", .str (Jvm.i32ToDecimalString x)],
          setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.i32 x)) 1 (.i32 y))
            2 (.str (Jvm.i32ToDecimalString x))) 3 (.str " "), {}, {}⟩ := by
    split_val_fuel 12
    dsimp only [f_Algorithm_formatCoordLine_prog, List.drop]
    heap_step_blk f_Algorithm_formatCoordLine_prog
    norm_res_fuel
    rfl
  rw [hstep1]
  have hstep2 : runJvmValFast 12 f_Algorithm_formatCoordLine_prog 8
      (f_Algorithm_formatCoordLine_prog.drop 8)
      ⟨8, [.i32 y, .str " ", .str (Jvm.i32ToDecimalString x)],
        setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.i32 x)) 1 (.i32 y))
          2 (.str (Jvm.i32ToDecimalString x))) 3 (.str " "), {}, {}⟩ =
      some (.str (Jvm.i32ToDecimalString x ++ (" " ++ (Jvm.i32ToDecimalString y ++ "")))) := by
    dsimp only [f_Algorithm_formatCoordLine_prog, List.drop]
    rw [runJvmValFast_step_nonbranch (hbr := rfl) (hno := by simp)]
    have hdyn : stepInstr
        (.invokedynamic "makeConcatWithConstants" "\x01\x01\x01"
          "(Ljava/lang/String;Ljava/lang/String;I)Ljava/lang/String;")
        ⟨8, [.i32 y, .str " ", .str (Jvm.i32ToDecimalString x)],
          setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.i32 x)) 1 (.i32 y))
            2 (.str (Jvm.i32ToDecimalString x))) 3 (.str " "), {}, {}⟩ =
        .inl (some ⟨9, [.str (Jvm.i32ToDecimalString x ++ (" " ++ (Jvm.i32ToDecimalString y ++ "")))],
          setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.i32 x)) 1 (.i32 y))
            2 (.str (Jvm.i32ToDecimalString x))) 3 (.str " "), {}, {}⟩) := by
      simp only [stepInstr, Jvm.stepInstr, hconcat]; rfl
    dsimp only
    rw [hdyn]
    rfl
  rw [hstep2, i32ToDecimalString_eq_toString x, i32ToDecimalString_eq_toString y]
  simp only [Algorithm.formatCoordLine, String.append_empty, String.append_assoc]
  rfl

theorem deserializeLife106___closed__1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = []) :
    ∃ v st', runJvmRes 20 f_Algorithm_deserializeLife106___closed__1_prog
        ⟨0, [], fun _ => .null, jh, hp⟩ = some (v, st') ∧
      decodeLife106Result st' v = some ⟨.emptyFile, #[]⟩ := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  refine ⟨.heapRef objs.size, ?_, ?_, ?_⟩
  · exact ⟨9, [.heapRef objs.size], setLocal (fun _ => .null) 0 (.ext (.u64Ref hp.u64Arrays.length)),
      (({ objects := objs, statics := [] } : Jvm.JvmHeap AlgExt).alloc
        (.instance "com/alexvanyo/composelife/model/Life106Result"
          [("status", .allocRef "com/alexvanyo/composelife/model/Life106Status$EmptyFile"),
           ("cells", .ext (.u64Ref hp.u64Arrays.length))])).2,
      { hp with u64Arrays := hp.u64Arrays ++ [#[]] }⟩
  · apply runJvmRes_of_runJvmResFast0 20 _ _ _ rfl
    rcases hp with ⟨ar, u64, asc⟩
    split_res_fuel 20
    dsimp only [f_Algorithm_deserializeLife106___closed__1_prog, List.drop]
    rw [runJvmResFast_invokestatic_step (stepStatic_noCells_heap (Or.inr rfl))]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
    dsimp only [f_Algorithm_deserializeLife106___closed__1_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
    rw [runJvmResFast_invokespecial_step rfl]; norm_res_fuel
    dsimp only [f_Algorithm_deserializeLife106___closed__1_prog, List.drop]
    heap_step_nonbranch_chunks
    dsimp only [Jvm.JvmHeap.alloc]
  · dsimp [decodeLife106Result, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    rw [Array.getElem?_push_size]
    simp [List.lookup, decodeLife106Status]

private theorem deserializeLife106_loop_base
    (f : Nat) (lines : Array String) (i limit : UInt32) (accId : Nat)
    (acc : Array UInt64) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hstat : jh.statics = [])
    (hnot : ¬(i < limit)) (hf : 30 ≤ f) (hu : u64[accId]? = some acc)
    (h1 : locs 1 = .i32 i) (h2 : locs 2 = .i32 limit) (h3 : locs 3 = .ext (AlgExt.u64Ref accId)) :
    ∃ v st', runJvmResFast f f_Algorithm_deserializeLife106_loop_prog 6
        (f_Algorithm_deserializeLife106_loop_prog.drop 6)
        ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
      decodeLife106Result st' v = some (Algorithm.deserializeLife106.loop lines i limit acc) := by
  have hrun : runJvmResFast f f_Algorithm_deserializeLife106_loop_prog 6
      (f_Algorithm_deserializeLife106_loop_prog.drop 6)
      ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      some (.heapRef jh.objects.size,
        ⟨22, [.heapRef jh.objects.size],
          setLocal (setLocal locs 4 (.allocRef "com/alexvanyo/composelife/model/Life106Status$Ok"))
            5 (.ext (AlgExt.u64Ref u64.length)),
          (jh.alloc (.instance "com/alexvanyo/composelife/model/Life106Result"
            [("status", .allocRef "com/alexvanyo/composelife/model/Life106Status$Ok"),
             ("cells", .ext (AlgExt.u64Ref u64.length))])).2,
          ⟨ar, u64 ++ [Algorithm.U64Buf.toArray acc], asc⟩⟩) := by
    split_res_fuel 30
    dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h1, h2]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hnot)]
    norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
    conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
    rw [runJvmResFast_getstatic_step hstat rfl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
    rw [h3]
    rw [runJvmResFast_invokestatic_step (stepStatic_u64BufToArray_heap (Or.inr (Or.inl rfl)) hu)]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
    rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
    rw [runJvmResFast_invokespecial_step rfl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
    heap_step_nonbranch_chunks
    dsimp only [Jvm.JvmHeap.alloc]
  refine ⟨_, _, hrun, ?_⟩
  rw [Algorithm.deserializeLife106.loop]; simp only [hnot, ↓reduceDIte]
  dsimp [decodeLife106Result, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  rw [Array.getElem?_push_size]
  simp [List.lookup, decodeLife106Status]

private theorem deserializeLife106_loop_pre
    (f : Nat) (lines : Array String) (i limit : UInt32) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hf : 70 ≤ f) (hlt : i < limit) (hilen : i.toNat < lines.size)
    (hislt : i.toBitVec.slt 0#32 = false)
    (h0 : locs 0 = .strArr lines) (h1 : locs 1 = .i32 i) (h2 : locs 2 = .i32 limit) :
    runJvmResFast f f_Algorithm_deserializeLife106_loop_prog 6
      (f_Algorithm_deserializeLife106_loop_prog.drop 6)
      ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 70 + 54) f_Algorithm_deserializeLife106_loop_prog 35
        (f_Algorithm_deserializeLife106_loop_prog.drop 35)
        ⟨35, [match Algorithm.parseCoordLine lines[i.toNat] with
              | some (x, y) => .pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32)
              | none => .null],
          setLocal (setLocal locs 4 (.str lines[i.toNat])) 5
            (match Algorithm.parseCoordLine lines[i.toNat] with
              | some (x, y) => .pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32)
              | none => .null),
          jh, ⟨ar, u64, asc⟩⟩ := by
  split_res_fuel 70
  dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [h1, h2]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt)]
  norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [h0, h1]
  rw [runJvmResFast_aaload_strArr hislt hilen]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  rfl

private theorem deserializeLife106_loop_none
    (f : Nat) (lines : Array String) (i : UInt32) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hilen : i.toNat < lines.size) (h1 : locs 1 = .i32 i) :
    runJvmResFast (f - 70 + 54) f_Algorithm_deserializeLife106_loop_prog 35
      (f_Algorithm_deserializeLife106_loop_prog.drop 35)
      ⟨35, [.null],
        setLocal (setLocal locs 4 (.str lines[i.toNat])) 5 .null, jh, ⟨ar, u64, asc⟩⟩ =
      some (.heapRef (jh.objects.size + 1),
        ⟨56, [.heapRef (jh.objects.size + 1)],
          setLocal (setLocal (setLocal (setLocal locs 4 (.str lines[i.toNat])) 5 .null)
            6 (.heapRef jh.objects.size))
            7 (.ext (AlgExt.u64Ref u64.length)),
          ((jh.alloc (.instance "com/alexvanyo/composelife/model/Life106Status$InvalidLine"
              [("lineIndex", .i32 (i + 1)), ("line", .str lines[i.toNat])])).2.alloc
            (.instance "com/alexvanyo/composelife/model/Life106Result"
              [("status", .heapRef jh.objects.size),
               ("cells", .ext (AlgExt.u64Ref u64.length))])).2,
          ⟨ar, u64 ++ [#[]], asc⟩⟩) := by
  rw [show f - 70 + 54 = (f - 70 + 53) + 1 from rfl]
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  rw [runJvmResFast_ifnonnull_fallthrough]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
  conv => lhs; arg 5; dsimp only [Jvm.JvmVal.asI32]
  rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
  rw [runJvmResFast_invokespecial_step rfl]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
  rw [runJvmResFast_invokestatic_step (stepStatic_noCells_heap (Or.inr rfl))]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
  conv => lhs; arg 5; dsimp only
  rw [runJvmResFast_checkcast_instance
    (cls := "com/alexvanyo/composelife/model/Life106Status$InvalidLine") _ (by decide)]
  · norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
    rw [runJvmResFast_invokespecial_step rfl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
    heap_step_nonbranch_chunks
    rw [h1]
    dsimp only [Jvm.JvmHeap.alloc, Jvm.JvmVal.asI32]
    rw [Array.size_push]
  · simp [Jvm.JvmHeap.get?]

private theorem deserializeLife106_loop_some
    (f : Nat) (lines : Array String) (i limit : UInt32) (accId : Nat)
    (acc : Array UInt64) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (c : Int32 × Int32) (hilen : i.toNat < lines.size) (hu : u64[accId]? = some acc)
    (h0 : locs 0 = .strArr lines) (h1 : locs 1 = .i32 i)
    (h2 : locs 2 = .i32 limit) (h3 : locs 3 = .ext (.u64Ref accId)) :
    runJvmResFast (f - 70 + 54) f_Algorithm_deserializeLife106_loop_prog 35
      (f_Algorithm_deserializeLife106_loop_prog.drop 35)
      ⟨35, [.pair (.boxedInt c.1.toUInt32) (.boxedInt c.2.toUInt32)],
        setLocal (setLocal locs 4 (.str lines[i.toNat])) 5
          (.pair (.boxedInt c.1.toUInt32) (.boxedInt c.2.toUInt32)), jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 70) f_Algorithm_deserializeLife106_loop_prog 6
        (f_Algorithm_deserializeLife106_loop_prog.drop 6)
        ⟨6, [],
          setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 4 (.str lines[i.toNat])) 5 (.pair (.boxedInt c.1.toUInt32) (.boxedInt c.2.toUInt32))) 6 (.i32 (i + 1))) 7 (.i32 c.1.toUInt32)) 8 (.i32 c.2.toUInt32)) 9 (.ext (AlgExt.u64Ref u64.length))) 10 (.strArr lines)) 11 (.i32 limit)) 0 (.strArr lines)) 1 (.i32 (i + 1))) 2 (.i32 limit)) 3 (.ext (AlgExt.u64Ref u64.length)),
          jh, ⟨ar, u64 ++ [Algorithm.U64Buf.push acc (Algorithm.cellBits c)], asc⟩⟩ := by
  have hcb := cellKey_bits_eq c.1 c.2
  rw [show f - 70 + 54 = (f - 70 + 53) + 1 from rfl]
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  rw [runJvmResFast_ifnonnull_branch (v := .pair (.boxedInt c.1.toUInt32) (.boxedInt c.2.toUInt32)) rfl]
  norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
  simp only [h1]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
  rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
  simp only [h3]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.add_eq, Nat.succ_eq_add_one]
  rw [runJvmResFast_invokestatic_step (stepStatic_u64BufPush_heap (Or.inr (Or.inl rfl)) hu)]
  norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_goto]
  norm_res_fuel
  conv => lhs; arg 5; simp only [h0, h2, hcb]
  rfl

private theorem deserializeLife106_loop_tail
    (m : Nat) (f : Nat) (lines : Array String) (i limit : UInt32) (accId : Nat)
    (acc : Array UInt64) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hstat : jh.statics = [])
    (hm : limit.toNat - i.toNat ≤ m) (hf : m * 70 + 30 ≤ f)
    (hlim31 : limit.toNat < 2 ^ 31) (hlen : limit.toNat ≤ lines.size)
    (hu : u64[accId]? = some acc)
    (h0 : locs 0 = .strArr lines) (h1 : locs 1 = .i32 i)
    (h2 : locs 2 = .i32 limit) (h3 : locs 3 = .ext (.u64Ref accId)) :
    ∃ v st', runJvmResFast f f_Algorithm_deserializeLife106_loop_prog 6
        (f_Algorithm_deserializeLife106_loop_prog.drop 6)
        ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
      decodeLife106Result st' v = some (Algorithm.deserializeLife106.loop lines i limit acc) := by
  induction m generalizing f i accId acc locs jh u64 with
  | zero =>
    have hnot : ¬(i < limit) := by
      intro hlt; have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    exact deserializeLife106_loop_base f lines i limit accId acc locs jh ar u64 asc hstat hnot
      (by omega) hu h1 h2 h3
  | succ m ih =>
    by_cases hlt : i < limit
    · have hltNat : i.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hlt
      have hi31 : i.toNat < 2 ^ 31 := by omega
      have hilen : i.toNat < lines.size := by omega
      have hislt : i.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 hi31
      have hi1_nat : (i + 1).toNat = i.toNat + 1 := ui32_add1_toNat hlt
      have hlin : lines[i.toNat]! = lines[i.toNat] := by simp [getElem!_pos, hilen]
      have hpre := deserializeLife106_loop_pre f lines i limit locs jh ar u64 asc
        (by omega) hlt hilen hislt h0 h1 h2
      rw [hpre]
      cases hpc : Algorithm.parseCoordLine lines[i.toNat] with
      | none =>
        have hrun := deserializeLife106_loop_none f lines i locs jh ar u64 asc hilen h1
        refine ⟨_, _, hrun, ?_⟩
        rw [Algorithm.deserializeLife106.loop]; simp only [hlt, ↓reduceDIte, hlin, hpc]
        dsimp only [decodeLife106Result, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
        let obj1 : Jvm.HeapObj AlgExt := .instance "com/alexvanyo/composelife/model/Life106Status$InvalidLine"
          [("lineIndex", .i32 (i + 1)), ("line", .str lines[i.toNat])]
        have hsz1 : jh.objects.size + 1 = (jh.objects.push obj1).size := (Array.size_push obj1).symm
        have hget1 : ((jh.objects.push obj1).push (.instance "com/alexvanyo/composelife/model/Life106Result"
            [("status", .heapRef jh.objects.size), ("cells", .ext (AlgExt.u64Ref u64.length))]))[jh.objects.size]? =
            some obj1 := by
          have hlt1 : jh.objects.size < (jh.objects.push obj1).size := by rw [← hsz1]; exact Nat.lt_succ_self _
          rw [Array.getElem?_push_lt hlt1]
          simp
        rw [hsz1, Array.getElem?_push_size]
        simp only [List.lookup, decodeLife106Status, Jvm.JvmHeap.get?]
        rw [show ("status" == "status") = true from rfl,
          show ("cells" == "status") = false from rfl,
          show ("cells" == "cells") = true from rfl]
        dsimp only
        rw [hget1]
        simp [obj1, List.lookup, Jvm.JvmVal.asI32]
      | some c =>
        have hstep := deserializeLife106_loop_some f lines i limit accId acc locs jh ar u64 asc c
          hilen hu h0 h1 h2 h3
        rcases ih (f := f - 70) (i := i + 1) (accId := u64.length)
            (acc := Algorithm.U64Buf.push acc (Algorithm.cellBits c))
            (locs := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 4 (.str lines[i.toNat])) 5 (.pair (.boxedInt c.1.toUInt32) (.boxedInt c.2.toUInt32))) 6 (.i32 (i + 1))) 7 (.i32 c.1.toUInt32)) 8 (.i32 c.2.toUInt32)) 9 (.ext (AlgExt.u64Ref u64.length))) 10 (.strArr lines)) 11 (.i32 limit)) 0 (.strArr lines)) 1 (.i32 (i + 1))) 2 (.i32 limit)) 3 (.ext (AlgExt.u64Ref u64.length)))
            (jh := jh) (u64 := u64 ++ [Algorithm.U64Buf.push acc (Algorithm.cellBits c)])
            hstat (by omega) (by omega)
            (by simp)
            (by simp [setLocal]) (by simp [setLocal])
            (by simp [setLocal]) (by simp [setLocal]) with ⟨v, st', htail, hdec⟩
        refine ⟨v, st', ?_, ?_⟩
        · rw [hstep]; exact htail
        · rw [Algorithm.deserializeLife106.loop]; simp only [hlt, ↓reduceDIte, hlin, hpc]
          exact hdec
    · exact deserializeLife106_loop_base f lines i limit accId acc locs jh ar u64 asc hstat hlt
        (by omega) hu h1 h2 h3

theorem deserializeLife106_loop_equiv (lines : Array String) (i limit : UInt32) (acc : Algorithm.U64Buf)
    (hlim31 : limit.toNat < 2 ^ 31) (hlen : limit.toNat ≤ lines.size) :
    ∃ v st', runJvmRes ((limit.toNat - i.toNat) * 70 + 40) f_Algorithm_deserializeLife106_loop_prog
        (initJvmState [(0, .strArr lines), (1, .i32 i), (2, .i32 limit), (3, .ext (AlgExt.u64Ref 0))] [] [acc]) =
        some (v, st') ∧
      decodeLife106Result st' v = some (Algorithm.deserializeLife106.loop lines i limit acc) := by
  let locs0 := setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.strArr lines))
    1 (.i32 i)) 2 (.i32 limit)) 3 (.ext (AlgExt.u64Ref 0))
  obtain ⟨v, st', htail, hdec⟩ := deserializeLife106_loop_tail
    (m := limit.toNat - i.toNat) (f := (limit.toNat - i.toNat) * 70 + 34)
    lines i limit 0 acc locs0 {} [] [acc] [] rfl
    (Nat.le_refl _) (by omega) hlim31 hlen rfl
    (by simp [locs0, setLocal]) (by simp [locs0, setLocal])
    (by simp [locs0, setLocal]) (by simp [locs0, setLocal])
  refine ⟨v, st', ?_, hdec⟩
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  have hpre0 : runJvmResFast ((limit.toNat - i.toNat) * 70 + 40) f_Algorithm_deserializeLife106_loop_prog 0
      f_Algorithm_deserializeLife106_loop_prog
      (initJvmState [(0, .strArr lines), (1, .i32 i), (2, .i32 limit), (3, .ext (AlgExt.u64Ref 0))] [] [acc]) =
      runJvmResFast ((limit.toNat - i.toNat) * 70 + 34) f_Algorithm_deserializeLife106_loop_prog 6
        (f_Algorithm_deserializeLife106_loop_prog.drop 6)
        ⟨6, [], locs0, {}, ⟨[], [acc], []⟩⟩ := by
    rw [show (limit.toNat - i.toNat) * 70 + 40 = ((limit.toNat - i.toNat) * 70 + 34) + 6 from rfl]
    dsimp only [f_Algorithm_deserializeLife106_loop_prog, initJvmState, Jvm.initJvmState, List.foldl]
    rw [runJvmResFast_stepResHeapChunk 2]
    conv => lhs; arg 1; jvm_whnf_blk
    rw [afterResBlockChunk_cont]; norm_res_fuel
    conv => lhs; arg 5; dsimp only
    rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
    rw [runJvmResFast_stepResHeapChunk 2]
    conv => lhs; arg 1; jvm_whnf_blk
    rw [afterResBlockChunk_cont]; norm_res_fuel
    conv => lhs; arg 5; dsimp only
    rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_loop_prog, List.drop]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
    rfl
  rw [hpre0]
  exact htail

theorem deserializeLife106_equiv (lines : Array String) (hlen31 : lines.size < 2 ^ 31) :
    ∃ v st', runJvmRes 50 f_Algorithm_deserializeLife106_prog
        (initJvmState [(0, .strArr lines)]) = some (v, st') ∧
      decodeLife106Result st' v = some (Algorithm.deserializeLife106 lines) := by
  by_cases h0 : lines.size = 0
  · let enc := encodeLife106Result ({} : Jvm.JvmHeap AlgExt) ([] : List (Array UInt64)) ⟨.emptyFile, #[]⟩
    refine ⟨enc.1, ⟨46, [enc.1], setLocal (setLocal (fun _ => .i32 0) 0 (.strArr lines)) 1 (.i32 0),
        enc.2.1, ⟨[], enc.2.2, []⟩⟩, ?_, ?_⟩
    · apply runJvmRes_of_runJvmResFast0 50 _ _ _ rfl
      dsimp only [f_Algorithm_deserializeLife106_prog, initJvmState, Jvm.initJvmState, List.foldl]
      heap_step_nonbranch_chunks; norm_res_fuel
      conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
      rw [runJvmResFast_arraylength_strArr]; norm_res_fuel
      conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
      heap_step_nonbranch_chunks; norm_res_fuel
      conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
      rw [h0, show UInt32.ofNat 0 = (0 : UInt32) from rfl]
      split_res_fuel 1
      conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
      rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
      conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
      rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
      conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
      heap_step_nonbranch_chunks
      dsimp only [enc, encodeLife106Result, Jvm.JvmHeap.alloc]
    · have hempty : lines = #[] := Array.eq_empty_of_size_eq_zero h0
      subst hempty
      dsimp only [enc, encodeLife106Result, decodeLife106Result, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
      rfl
  · have hpos : 0 < lines.size := Nat.pos_of_ne_zero h0
    have hlimNe : UInt32.ofNat lines.size ≠ 0 := by
      intro heq
      have := congrArg UInt32.toNat heq
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega : lines.size < 2 ^ 32)] at this
      exact h0 this
    have hlimB : (lines.size.toUInt32 == 0) = false := beq_false_of_ne hlimNe
    have hlin0 : lines[0]! = lines[0] := by simp [getElem!_pos, hpos]
    by_cases hhdr : lines[0]! = "#Life 1.06"
    · have hhdrB : (lines[0]! != "#Life 1.06") = false := by simp [hhdr]
      let loopRes := Algorithm.deserializeLife106.loop lines 1 lines.size.toUInt32 Algorithm.U64Buf.empty
      let enc := encodeLife106Result ({} : Jvm.JvmHeap AlgExt) [Algorithm.U64Buf.empty] loopRes
      refine ⟨enc.1, ⟨44, [enc.1],
          setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.strArr lines))
            1 (.i32 lines.size.toUInt32)) 2 (.str lines[0])) 3 (.str "#Life 1.06"))
            4 (.ext (.u64Ref 0)),
          enc.2.1, ⟨[], enc.2.2, []⟩⟩, ?_, ?_⟩
      · apply runJvmRes_of_runJvmResFast0 50 _ _ _ rfl
        dsimp only [f_Algorithm_deserializeLife106_prog, initJvmState, Jvm.initJvmState, List.foldl]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        rw [runJvmResFast_arraylength_strArr]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        split_res_fuel 1
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        rw [runJvmResFast_ifeq_fallthrough hlimB]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        rw [runJvmResFast_aaload_strArr (idx := 0) (by decide) hpos]; norm_res_fuel
        simp only [UInt32.toNat_zero]
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; dsimp only [Nat.add, Nat.succ_eq_add_one]; simp only [Nat.reduceAdd]
        rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
        have hbeq : Jvm.JvmVal.beqVal algHooks.beqExt (.str lines[0]) (.str "#Life 1.06") = true := by
          rw [hlin0] at hhdr; simp [Jvm.JvmVal.beqVal, hhdr]
        rw [hbeq]
        split_res_fuel 1
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        rw [runJvmResFast_ifne_bool_branch]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        rw [runJvmResFast_invokestatic_step (stepStatic_u64BufEmpty_heap (Or.inr (Or.inl rfl)))]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        heap_step_nonbranch_chunks
        dsimp only [enc, encodeLife106Result, loopRes, Jvm.JvmHeap.alloc]
        rfl
      · simp only [Algorithm.deserializeLife106, hlimB, hhdrB, Bool.false_eq_true, ↓reduceIte]
        have hdec := decodeLife106Result_encode {} ⟨[], [Algorithm.U64Buf.empty], []⟩ loopRes
        dsimp only [decodeLife106Result] at hdec ⊢
        exact hdec
    · have hhdrB : (lines[0] != "#Life 1.06") = true := by rw [← hlin0]; simp [hhdr]
      let enc := encodeLife106Result ({} : Jvm.JvmHeap AlgExt) [] ⟨.invalidHeader lines[0], #[]⟩
      refine ⟨enc.1, ⟨36, [enc.1],
          setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
            0 (.strArr lines)) 1 (.i32 lines.size.toUInt32)) 2 (.str lines[0]))
            3 (.str "#Life 1.06")) 4 (.heapRef 0)) 5 (.ext (.u64Ref 0)),
          enc.2.1, ⟨[], enc.2.2, []⟩⟩, ?_, ?_⟩
      · apply runJvmRes_of_runJvmResFast0 50 _ _ _ rfl
        dsimp only [f_Algorithm_deserializeLife106_prog, initJvmState, Jvm.initJvmState, List.foldl]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        rw [runJvmResFast_arraylength_strArr]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        split_res_fuel 1
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        rw [runJvmResFast_ifeq_fallthrough hlimB]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        rw [runJvmResFast_aaload_strArr (idx := 0) (by decide) hpos]; norm_res_fuel
        simp only [UInt32.toNat_zero]
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; dsimp only [Nat.add, Nat.succ_eq_add_one]; simp only [Nat.reduceAdd]
        rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
        have hbeq : Jvm.JvmVal.beqVal algHooks.beqExt (.str lines[0]) (.str "#Life 1.06") = false := by
          rw [hlin0] at hhdr; simp [Jvm.JvmVal.beqVal, hhdr]
        rw [hbeq]
        split_res_fuel 1
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        rw [runJvmResFast_ifne_bool_fallthrough]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        rw [runJvmResFast_invokespecial_step rfl]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        rw [runJvmResFast_invokestatic_step (stepStatic_noCells_heap (Or.inr rfl))]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        conv => lhs; arg 5; dsimp only [Jvm.JvmHeap.alloc]
        rw [runJvmResFast_checkcast_instance
          (cls := "com/alexvanyo/composelife/model/Life106Status$InvalidHeader") _ (by decide)]
        · norm_res_fuel
          conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
          heap_step_nonbranch_chunks; norm_res_fuel
          conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
          rw [runJvmResFast_invokespecial_step rfl]; norm_res_fuel
          conv => lhs; arg 4; dsimp only [f_Algorithm_deserializeLife106_prog, List.drop]
          heap_step_nonbranch_chunks
          dsimp only [enc, encodeLife106Result, Jvm.JvmHeap.alloc]
          rfl
        · simp [Jvm.JvmHeap.get?]
      · simp only [Algorithm.deserializeLife106, hlimB, hlin0, hhdrB, Bool.false_eq_true, ↓reduceIte]
        have hdec := decodeLife106Result_encode {} ⟨[], [], []⟩ ⟨.invalidHeader lines[0], #[]⟩
        dsimp only [decodeLife106Result, enc] at hdec ⊢
        exact hdec

private theorem runJvmResFast_tableswitch_pcl {f pc dflt : Nat} {low : Int32} {targets : List Nat}
    {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.tableswitch low targets dflt :: rest)
        ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      let tgt := Jvm.tableswitchTarget v low targets dflt
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32]

private theorem runJvmResFast_instanceof_boxedInt_uint {f : Nat} {prog : List JvmInstr}
    {pc : Nat} {rest : List JvmInstr} {pc0 : Nat} {v : UInt32} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.instanceof "kotlin/UInt" :: rest)
        ⟨pc0, .boxedInt v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 0 :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.instanceof "kotlin/UInt")
      ⟨pc, .boxedInt v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 0 :: stkRest, locs, jh, hp⟩) := rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

private theorem stepVirtual_uint_unbox_pcl
    {pc : Nat} {v : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .boxedUInt v :: rest, locs, jh, hp⟩
      "kotlin/UInt" "unbox-impl" "()I" =
      .inl (some ⟨pc + 1, .i32 v :: rest, locs, jh, hp⟩) := rfl

private theorem runJvmResFast_aaload1_len1_none_rfl {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {o0 o1 o2 : Jvm.HeapObj AlgExt} {x0 : JvmVal}
    {stats : List (String × String × JvmVal)} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.aaload :: rest)
        ⟨pc0, .i32 1 :: .heapRef 3 :: stkRest, locs,
          ⟨#[o0, o1, o2, .objArray "java/lang/Object" #[x0]], stats⟩, hp⟩ =
      none := by
  have hstep : Jvm.stepInstr algHooks .aaload
      ⟨pc, .i32 1 :: .heapRef 3 :: stkRest, locs,
        ⟨#[o0, o1, o2, .objArray "java/lang/Object" #[x0]], stats⟩, hp⟩ = .inr none := rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep]

private theorem u8_signExtend_beq_32 (b : UInt8) :
    (UInt32.ofBitVec (b.toBitVec.signExtend 32) == (32 : UInt32)) = (b == 32) := by
  revert b; decide

private theorem u8_signExtend_beq_9 (b : UInt8) :
    (UInt32.ofBitVec (b.toBitVec.signExtend 32) == (9 : UInt32)) = (b == 9) := by
  revert b; decide

private theorem u8_signExtend_beq_13 (b : UInt8) :
    (UInt32.ofBitVec (b.toBitVec.signExtend 32) == (13 : UInt32)) = (b == 13) := by
  revert b; decide

private theorem jvm_runJvmRes_mono {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap) :
    ∀ (f g : Nat) (prog : List JvmInstr) (st : Jvm.JvmState Ext Heap)
      (res : Jvm.JvmVal Ext × Jvm.JvmState Ext Heap),
      f ≤ g → Jvm.runJvmRes hooks f prog st = some res → Jvm.runJvmRes hooks g prog st = some res := by
  intro f
  induction f with
  | zero => intro g _ _ _ _ h; simp [Jvm.runJvmRes] at h
  | succ f ih =>
    intro g prog st res hfg hrun
    cases g with
    | zero => omega
    | succ g =>
      have hle : f ≤ g := Nat.le_of_succ_le_succ hfg
      cases hg : prog[st.pc]? with
      | none =>
        unfold Jvm.runJvmRes at hrun
        simp [hg] at hrun
      | some instr =>
        cases hbr : Jvm.isBranchInstr instr
        · rw [Jvm.runJvmRes_nonbranch hooks f prog st instr hg hbr] at hrun
          rw [Jvm.runJvmRes_nonbranch hooks g prog st instr hg hbr]
          cases hs : Jvm.stepInstr hooks instr st with
          | inr r =>
            cases r with
            | none => simp [hs] at hrun
            | some v => simp only [hs] at hrun ⊢; exact hrun
          | inl opt =>
            cases opt with
            | none => simp [hs] at hrun
            | some st' => simp only [hs] at hrun ⊢; exact ih _ _ _ _ hle hrun
        · unfold Jvm.runJvmRes at hrun ⊢
          simp only [hg] at hrun ⊢
          cases instr <;> simp [Jvm.isBranchInstr] at hbr <;> dsimp only at hrun ⊢ <;>
            first
            | exact ih _ _ _ _ hle hrun
            | (rcases hstk : st.stack with _ | ⟨v, rest⟩
               · simp [hstk] at hrun
               · first
                 | (simp only [hstk] at hrun ⊢; split at hrun <;> simp_all only [] <;>
                     exact ih _ _ _ _ hle hrun)
                 | (rcases rest with _ | ⟨v2, rest2⟩
                    · simp [hstk] at hrun
                    · simp only [hstk] at hrun ⊢; split at hrun <;> simp_all only [] <;>
                        exact ih _ _ _ _ hle hrun)
                 | (simp only [hstk] at hrun ⊢; exact ih _ _ _ _ hle hrun))

private theorem runJvmRes_eq_runJvmResFast_no_i2l {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    (prog : List JvmInstr) (hnoi2l : ∀ i ∈ prog, i ≠ .i2l) :
    ∀ fuel pc instrs (st : Jvm.JvmState Ext Heap),
      st.pc = pc → prog.drop pc = instrs →
      Jvm.runJvmResFast hooks fuel prog pc instrs st = Jvm.runJvmRes hooks fuel prog st := by
  intro fuel
  refine Nat.strongRecOn (motive := fun f => ∀ pc instrs st,
      st.pc = pc → prog.drop pc = instrs →
      Jvm.runJvmResFast hooks f prog pc instrs st = Jvm.runJvmRes hooks f prog st) fuel ?_
  intro fuel ih pc instrs st hpc hdrop
  cases fuel with
  | zero => simp [Jvm.runJvmResFast, Jvm.runJvmRes]
  | succ f1 =>
    rcases instrs with _ | ⟨instr, rest⟩
    · have hnone : prog[st.pc]? = none := by
        have hdrop0 : (prog.drop pc)[0]? = prog[pc]? := by simp [List.getElem?_drop]
        rw [hpc, ← hdrop0, hdrop]; rfl
      simp [Jvm.runJvmResFast, Jvm.runJvmRes, hnone]
    · have hg0 : prog[st.pc]? = some instr := by
        have hdrop0 : (prog.drop pc)[0]? = prog[pc]? := by simp [List.getElem?_drop]
        rw [hpc, ← hdrop0, hdrop]; rfl
      have hne : instr ≠ .i2l := hnoi2l instr (List.mem_of_getElem? hg0)
      have hst_eq : { st with pc := pc } = st := by cases st; cases hpc; rfl
      have hdrop_succ : prog.drop (pc + 1) = rest := by rw [← List.drop_drop, hdrop]; rfl
      cases hbr : Jvm.isBranchInstr instr
      · rw [Jvm.runJvmResFast_step_nonbranch hooks f1 prog pc instr rest st hbr (fun ⟨hi, _⟩ => hne hi)]
        rw [hst_eq, Jvm.runJvmRes_nonbranch hooks f1 prog st instr hg0 hbr]
        cases Jvm.stepInstr hooks instr st with
        | inr opt => cases opt <;> rfl
        | inl opt =>
          cases opt with
          | none => rfl
          | some st' =>
            dsimp only
            split
            · next hpc' => exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest st' hpc' hdrop_succ
            · exact ih f1 (Nat.lt_succ_self f1) st'.pc (prog.drop st'.pc) st' rfl rfl
      · cases instr <;> simp [Jvm.isBranchInstr] at hbr <;>
          (unfold Jvm.runJvmResFast Jvm.runJvmRes; rw [hg0]
           first
           | (dsimp only; exact ih f1 (Nat.lt_succ_self f1) _ (prog.drop _) _ rfl rfl)
           | (rcases hstk : st.stack with _ | ⟨v, s⟩
              · simp
              · first
                | (dsimp only; (try rw [hpc]); exact ih f1 (Nat.lt_succ_self f1) _ (prog.drop _) _ rfl rfl)
                | (dsimp only; (try rw [hpc]); split <;>
                    first
                    | exact ih f1 (Nat.lt_succ_self f1) _ (prog.drop _) _ rfl rfl
                    | exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl hdrop_succ)
                | (rcases s with _ | ⟨v2, s2⟩
                   · simp
                   · dsimp only; (try rw [hpc]); split <;>
                       first
                       | exact ih f1 (Nat.lt_succ_self f1) _ (prog.drop _) _ rfl rfl
                       | exact ih f1 (Nat.lt_succ_self f1) (pc + 1) rest _ rfl hdrop_succ)))

def ParseCoordLineSupported (line : String) : Prop :=
  let bytes := line.toByteArray
  let limit := bytes.size.toUInt32
  let p0 := Algorithm.skipSpaces bytes 0 limit
  match Algorithm.parseInt32At bytes p0 limit with
  | none => True
  | some r1 =>
    if r1.next < limit && Algorithm.isSpaceByte (bytes.get! r1.next.toNat) then
      (Algorithm.parseInt32At bytes (Algorithm.skipSpaces bytes r1.next limit) limit).isSome
    else True

private theorem parseCoordLine_prefix (f : Nat) (line : String)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hf : 20 ≤ f) :
    let bytes := line.toByteArray
    let limit := bytes.size.toUInt32
    let p0 := Algorithm.skipSpaces bytes 0 limit
    let jh1 := (jh.alloc (.byteArray bytes.data)).2
    let opt1 := (Algorithm.parseInt32At bytes p0 limit).map fun r =>
      (JvmVal.boxedInt r.val.toUInt32, JvmVal.boxedUInt r.next)
    let (v4, jh2) := encodeOptScalarPair jh1 opt1
    runJvmResFast f f_Algorithm_parseCoordLine_prog 0 f_Algorithm_parseCoordLine_prog
        ⟨0, [], setLocal (fun _ => .i32 0) 0 (.str line), jh, hp⟩ =
      runJvmResFast (f - 20) f_Algorithm_parseCoordLine_prog 20
        (f_Algorithm_parseCoordLine_prog.drop 20)
        ⟨20, [],
          setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.str line))
            1 (.heapRef jh.objects.size)) 2 (.i32 limit)) 3 (.i32 p0)) 4 v4,
          jh2, hp⟩ := by
  have hf' : 20 ≤ f := hf
  rw [show f = (f - 20) + 20 from (Nat.sub_add_cancel hf').symm, Nat.add_sub_cancel]
  dsimp only [f_Algorithm_parseCoordLine_prog]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
  rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
  have hgetb : (jh.alloc (.byteArray line.toUTF8.data)).2.get? jh.objects.size =
      some (.byteArray line.toUTF8.data) := jvmHeap_get?_alloc_self _ _
  dsimp only [Jvm.JvmHeap.alloc] at *
  rw [runJvmResFast_arraylength_byte hgetb]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
  rw [runJvmResFast_invokestatic_step (stepStatic_skipSpaces_heap (Or.inr (Or.inl rfl)) hgetb)]
  norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
  rw [runJvmResFast_invokestatic_step (stepStatic_parseInt32At_heap (Or.inr (Or.inl rfl)) hgetb)]
  norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  dsimp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  dsimp only [Jvm.stepInstr]
  have hutf8 : (⟨line.toUTF8.data⟩ : ByteArray) = line.toByteArray := rfl
  have hlim_eq : UInt32.ofNat line.toUTF8.data.size = line.toByteArray.size.toUInt32 := rfl
  simp only [Nat.reduceAdd, hutf8, hlim_eq, Jvm.JvmHeap.alloc]
  rfl

private theorem parseCoordLine_pc109 (fuel : Nat) (hf : 70 ≤ fuel)
    (bytes : ByteArray) (limit : UInt32) (r1 : Algorithm.ParsedInt32)
    (bAddr : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hb : jh.get? bAddr = some (.byteArray bytes.data))
    (hl1 : locs 1 = .heapRef bAddr) (hl2 : locs 2 = .i32 limit)
    (hl6 : locs 6 = .i32 r1.val.toUInt32) (hl7 : locs 7 = .i32 r1.next)
    (r2 : Algorithm.ParsedInt32)
    (h2 : Algorithm.parseInt32At bytes (Algorithm.skipSpaces bytes r1.next limit) limit = some r2) :
    let p2 := Algorithm.skipSpaces bytes r2.next limit
    let inner2 : Array JvmVal := #[JvmVal.boxedInt 0, .boxedInt r2.val.toUInt32, .null, .null, .null, .boxedUInt r2.next]
    let innerAddr2 := jh.objects.size
    let jh3 := ((jh.alloc (.objArray "java/lang/Object" inner2)).2.alloc
      (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr2])).2
    ∃ st',
      runJvmResFast fuel f_Algorithm_parseCoordLine_prog 109
          (f_Algorithm_parseCoordLine_prog.drop 109) ⟨109, [], locs, jh, hp⟩ =
        some ((if p2 = limit then .pair (.boxedInt r1.val.toUInt32) (.boxedInt r2.val.toUInt32) else .null),
          st') ∧
      st'.jvmHeap = jh3 := by
  let p1 := Algorithm.skipSpaces bytes r1.next limit
  let p2 := Algorithm.skipSpaces bytes r2.next limit
  let inner2 : Array JvmVal := #[JvmVal.boxedInt 0, .boxedInt r2.val.toUInt32, .null, .null, .null, .boxedUInt r2.next]
  let innerAddr2 := jh.objects.size
  let jha := (jh.alloc (.objArray "java/lang/Object" inner2)).2
  let outerAddr2 := jha.objects.size
  let jh3 := (jha.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr2])).2
  have hget_inner2 : jh3.get? innerAddr2 = some (.objArray "java/lang/Object" inner2) := by
    have hlt : innerAddr2 < jha.objects.size := by
      simp [jha, innerAddr2, Jvm.JvmHeap.alloc, Array.size_push]
    rw [jvmHeap_get?_alloc_lt _ _ hlt]
    exact jvmHeap_get?_alloc_self _ _
  have hget_outer2 : jh3.get? outerAddr2 =
      some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr2]) :=
    jvmHeap_get?_alloc_self _ _
  have hget_b3 : jh3.get? bAddr = some (.byteArray bytes.data) := by
    have hbd : bAddr < jh.objects.size := by
      simp only [Jvm.JvmHeap.get?] at hb
      cases Nat.lt_or_ge bAddr jh.objects.size with
      | inl h => exact h
      | inr h =>
        have : jh.objects[bAddr]? = none := Array.getElem?_eq_none h
        simp [this] at hb
    have hlt2 : bAddr < jha.objects.size := by
      simp [jha, Jvm.JvmHeap.alloc, Array.size_push]; omega
    rw [jvmHeap_get?_alloc_lt _ _ hlt2, jvmHeap_get?_alloc_lt _ _ hbd]
    exact hb
  let locs179 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
    (setLocal locs 8 (.i32 p1)) 9 (.heapRef outerAddr2)) 10 (.heapRef innerAddr2))
    12 (.boxedInt r2.val.toUInt32)) 13 (.i32 0)) 11 (.i32 r2.val.toUInt32))
    13 (.boxedUInt r2.next)) 14 (.i32 0)) 12 (.i32 p2)
  have hpre : runJvmResFast fuel f_Algorithm_parseCoordLine_prog 109
      (f_Algorithm_parseCoordLine_prog.drop 109) ⟨109, [], locs, jh, hp⟩ =
      runJvmResFast (fuel - 59) f_Algorithm_parseCoordLine_prog 179
        (f_Algorithm_parseCoordLine_prog.drop 179)
        ⟨179, [.i32 limit, .i32 p2], locs179, jh3, hp⟩ := by
    rw [show fuel = (fuel - 59) + 59 from (Nat.sub_add_cancel (by omega)).symm, Nat.add_sub_cancel]
    dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
    rw [hl1, hl7, hl2]
    rw [runJvmResFast_invokestatic_step (stepStatic_skipSpaces_heap (Or.inr (Or.inl rfl)) hb)]
    norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
    rw [hl1, hl2]
    rw [runJvmResFast_invokestatic_step (stepStatic_parseInt32At_heap (Or.inr (Or.inl rfl)) hb)]
    norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    have hbytes_eta : (⟨bytes.data⟩ : ByteArray) = bytes := rfl
    dsimp only [encodeOptScalarPair, Jvm.JvmVal.asI32]
    rw [hbytes_eta, h2]
    dsimp only [Option.map_some]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    rw [runJvmResFast_ifnonnull_branch rfl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    have hget_outer2' :
        ({ objects := (jh.objects.push (Jvm.HeapObj.objArray "java/lang/Object" inner2)).push
            (Jvm.HeapObj.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr2]),
           statics := jh.statics : Jvm.JvmHeap AlgExt }).get?
          (jh.objects.push (Jvm.HeapObj.objArray "java/lang/Object" inner2)).size =
          some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr2]) := by
      simpa [jh3, outerAddr2, jha, innerAddr2, Jvm.JvmHeap.alloc] using hget_outer2
    have hget_inner2' :
        ({ objects := (jh.objects.push (Jvm.HeapObj.objArray "java/lang/Object" inner2)).push
            (Jvm.HeapObj.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr2]),
           statics := jh.statics : Jvm.JvmHeap AlgExt }).get?
          jh.objects.size =
          some (.objArray "java/lang/Object" inner2) := by
      simpa [jh3, innerAddr2, jha, Jvm.JvmHeap.alloc] using hget_inner2
    have hget_b3' :
        ({ objects := (jh.objects.push (Jvm.HeapObj.objArray "java/lang/Object" inner2)).push
            (Jvm.HeapObj.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr2]),
           statics := jh.statics : Jvm.JvmHeap AlgExt }).get?
          bAddr =
          some (.byteArray bytes.data) := by
      simpa [jh3, jha, innerAddr2, Jvm.JvmHeap.alloc] using hget_b3
    conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    conv => lhs; arg 5; dsimp only [Jvm.JvmHeap.alloc]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    rw [runJvmResFast_checkcast_objArray hget_outer2' (Or.inl rfl)]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    rw [runJvmResFast_aaload hget_outer2' (by decide) (by simp)]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    rw [runJvmResFast_checkcast_objArray hget_inner2' (Or.inl rfl)]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    rw [runJvmResFast_aaload hget_inner2' (by decide) (by simp [inner2])]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    rw [runJvmResFast_instanceof_boxedInt_uint]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    rw [hl1]
    rw [runJvmResFast_checkcast_objArray hget_inner2' (Or.inl rfl)]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    rw [runJvmResFast_aaload hget_inner2' (by decide) (by simp [inner2])]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox_pcl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
    rw [hl2]
    rw [runJvmResFast_invokestatic_step (stepStatic_skipSpaces_heap (Or.inr (Or.inl rfl)) hget_b3')]
    norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    rw [show fuel - 59 + 3 = (fuel - 60) + 4 from by omega]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [show fuel - 60 + 1 = fuel - 59 from by omega]
    cases hp
    rw [hl2, show ({ data := bytes.data } : ByteArray) = bytes from rfl]
    have ha10 : (#[JvmVal.boxedInt 1, Jvm.JvmVal.heapRef innerAddr2] : Array JvmVal)[(1 : UInt32).toNat] =
        Jvm.JvmVal.heapRef innerAddr2 := rfl
    have ha12 : (#[JvmVal.boxedInt 0, JvmVal.boxedInt r2.val.toUInt32, JvmVal.null, JvmVal.null, JvmVal.null,
        JvmVal.boxedUInt r2.next] : Array JvmVal)[(1 : UInt32).toNat] = .boxedInt r2.val.toUInt32 := rfl
    have ha13 : (#[JvmVal.boxedInt 0, JvmVal.boxedInt r2.val.toUInt32, JvmVal.null, JvmVal.null, JvmVal.null,
        JvmVal.boxedUInt r2.next] : Array JvmVal)[(5 : UInt32).toNat] = .boxedUInt r2.next := rfl
    dsimp only [innerAddr2] at ha10
    rw [ha10, ha12, ha13]
    dsimp only [locs179, jh3, outerAddr2, jha, innerAddr2, Jvm.JvmHeap.alloc]
  rw [hpre]
  dsimp only
  by_cases hp2 : Algorithm.skipSpaces bytes r2.next limit = limit
  · refine ⟨⟨189, [.pair (.boxedInt r1.val.toUInt32) (.boxedInt r2.val.toUInt32)], locs179, jh3, hp⟩, ?_, ?_⟩
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hp2)]
      rw [show fuel - 59 = (fuel - 68) + 8 + 1 from by omega, show p2 = limit from hp2]
      dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      rw [runJvmResFast_if_icmpeq_branch rfl]; norm_res_fuel
      conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      rw [show fuel - 68 + 8 = (fuel - 68 + 5) + 3 from by omega]
      heap_step_nonbranch_chunks
      rw [hl6]
      cases hp
      dsimp only [locs179, Jvm.JvmVal.asI32]
    · rfl
  · refine ⟨⟨181, [.null], locs179, jh3, hp⟩, ?_, rfl⟩
    rw [show fuel - 59 = (fuel - 62) + 2 + 1 from by omega]
    dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hp2)]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
    heap_step_nonbranch_chunks
    cases hp
    dsimp only [locs179]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hp2)]

private theorem parseCoordLine_pc20_to_89 (fuel : Nat) (hf : 70 ≤ fuel)
    (line : String) (limit p0 : UInt32) (r1 : Algorithm.ParsedInt32)
    (jh jh2 : Jvm.JvmHeap AlgExt) (outerAddr1 innerAddr1 : Nat) (hp : AlgHeap)
    (hget_inner1 : jh2.get? innerAddr1 =
      some (.objArray "java/lang/Object"
        #[JvmVal.boxedInt 0, .boxedInt r1.val.toUInt32, .null, .null, .null, .boxedUInt r1.next]))
    (hget_outer1 : jh2.get? outerAddr1 =
      some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr1])) :
    runJvmResFast fuel f_Algorithm_parseCoordLine_prog 20
      (f_Algorithm_parseCoordLine_prog.drop 20)
      ⟨20, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.str line))
        1 (.heapRef jh.objects.size)) 2 (.i32 limit)) 3 (.i32 p0)) 4 (.heapRef outerAddr1),
        jh2, hp⟩ =
    runJvmResFast (fuel - 58) f_Algorithm_parseCoordLine_prog 89
      (f_Algorithm_parseCoordLine_prog.drop 89)
      ⟨89, [.i32 (if r1.next == limit then 0 else if r1.next < limit then 4294967295 else 1)],
        setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          (setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
            0 (.str line)) 1 (.heapRef jh.objects.size)) 2 (.i32 limit)) 3 (.i32 p0))
            4 (.heapRef outerAddr1)) 5 (.heapRef innerAddr1))
          7 (.boxedInt r1.val.toUInt32)) 8 (.i32 0)) 6 (.i32 r1.val.toUInt32))
          8 (.boxedUInt r1.next)) 9 (.i32 0)) 7 (.i32 r1.next),
        jh2, hp⟩ := by
  rw [show fuel = (fuel - 58) + 58 from (Nat.sub_add_cancel (by omega)).symm, Nat.add_sub_cancel]
  dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_checkcast_objArray hget_outer1 (Or.inl rfl)]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_aaload hget_outer1 (by decide) (by simp)]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  rw [runJvmResFast_tableswitch_pcl]
  rw [show Jvm.tableswitchTarget 1 0 [33, 35] 190 = 35 from by decide]
  dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_checkcast_objArray hget_outer1 (Or.inl rfl)]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_aaload hget_outer1 (by decide) (by simp)]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_checkcast_objArray hget_inner1 (Or.inl rfl)]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_aaload hget_inner1 (by decide) (by simp)]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_instanceof_boxedInt_uint]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_checkcast_objArray hget_inner1 (Or.inl rfl)]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_aaload hget_inner1 (by decide) (by simp)]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  rw [runJvmResFast_invokevirtual_step stepVirtual_uint_unbox_pcl]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  rfl

theorem parseCoordLine_equiv_cond (line : String)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hsz : line.toByteArray.size < 2 ^ 31)
    (hsupp : ParseCoordLineSupported line) :
    ∃ v st',
      runJvmRes 200 f_Algorithm_parseCoordLine_prog
        ⟨0, [], setLocal (fun _ => .i32 0) 0 (.str line), jh, hp⟩ = some (v, st') ∧
      v = match Algorithm.parseCoordLine line with
        | some (x, y) => .pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32)
        | none => .null := by
  let bytes := line.toByteArray
  let limit := bytes.size.toUInt32
  let p0 := Algorithm.skipSpaces bytes 0 limit
  let jh1 := (jh.alloc (.byteArray bytes.data)).2
  have hgetb : jh1.get? jh.objects.size = some (.byteArray bytes.data) :=
    jvmHeap_get?_alloc_self _ _
  have hb_lt_j1 : jh.objects.size < jh1.objects.size := by
    simp [jh1, Jvm.JvmHeap.alloc, Array.size_push]
  have hlim_nat : limit.toNat = bytes.size := by
    dsimp only [limit, bytes]
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega : line.toByteArray.size < 2 ^ 32)]
  cases h1 : Algorithm.parseInt32At bytes p0 limit with
  | none =>
    let jh2 := (jh1.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
    have hget4 : jh2.get? jh1.objects.size =
        some (.objArray "java/lang/Object" #[.boxedInt 0]) := jvmHeap_get?_alloc_self _ _
    have hnone_res : Algorithm.parseCoordLine line = none := by
      unfold Algorithm.parseCoordLine
      change (match Algorithm.parseInt32At bytes p0 limit with | none => none | some _ => _) = none
      rw [h1]
    have hfast : ∃ st',
        runJvmResFast 200 f_Algorithm_parseCoordLine_prog 0 f_Algorithm_parseCoordLine_prog
          ⟨0, [], setLocal (fun _ => .i32 0) 0 (.str line), jh, hp⟩ = some (.null, st') := by
      let st34 : JvmState :=
        ⟨34, [.null],
          setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.str line))
            1 (.heapRef jh.objects.size)) 2 (.i32 limit)) 3 (.i32 p0))
            4 (.heapRef jh1.objects.size),
          jh2, hp⟩
      refine ⟨st34, ?_⟩
      rw [parseCoordLine_prefix 200 line jh hp (by decide)]
      have h1' : Algorithm.parseInt32At line.toByteArray
          (Algorithm.skipSpaces line.toByteArray 0 line.toByteArray.size.toUInt32)
          line.toByteArray.size.toUInt32 = none := h1
      dsimp only [encodeOptScalarPair]
      rw [h1']
      dsimp only [Option.map_none]
      norm_res_fuel
      conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      heap_step_nonbranch_chunks; norm_res_fuel
      have hget4' :
          ({ objects := (jh.objects.push (Jvm.HeapObj.byteArray line.toByteArray.data)).push
              (Jvm.HeapObj.objArray "java/lang/Object" #[JvmVal.boxedInt 0]),
             statics := jh.statics : Jvm.JvmHeap AlgExt }).get?
            (jh.objects.push (Jvm.HeapObj.byteArray line.toByteArray.data)).size =
            some (Jvm.HeapObj.objArray "java/lang/Object" #[JvmVal.boxedInt 0]) := by
        simpa [jh2, jh1, bytes, Jvm.JvmHeap.alloc] using hget4
      conv => lhs; arg 5; dsimp only [Jvm.JvmHeap.alloc]
      conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
      conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
      rw [runJvmResFast_checkcast_objArray hget4' (Or.inl rfl)]; norm_res_fuel
      conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      heap_step_nonbranch_chunks; norm_res_fuel
      conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
      conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
      rw [runJvmResFast_aaload hget4' (by decide) (by simp)]; norm_res_fuel
      conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      heap_step_nonbranch_chunks; norm_res_fuel
      conv => lhs; arg 3; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
      conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd, Nat.succ_eq_add_one]
      rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
      conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]; norm_res_fuel
      conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      rw [runJvmResFast_tableswitch_pcl]
      rw [show Jvm.tableswitchTarget 0 0 [33, 35] 190 = 33 from by decide]
      dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      heap_step_nonbranch_chunks
      cases hp
      dsimp only [st34, jh2, jh1, bytes, limit, p0, Jvm.JvmHeap.alloc]
    obtain ⟨st', hst'⟩ := hfast
    exact ⟨.null, st', runJvmRes_of_runJvmResFast0 200 _ _ _ rfl hst', by rw [hnone_res]⟩
  | some r1 =>
    let inner1 : Array JvmVal :=
      #[JvmVal.boxedInt 0, .boxedInt r1.val.toUInt32, .null, .null, .null, .boxedUInt r1.next]
    let innerAddr1 := jh1.objects.size
    let jh1a := (jh1.alloc (.objArray "java/lang/Object" inner1)).2
    let outerAddr1 := jh1a.objects.size
    let jh2 := (jh1a.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr1])).2
    have hget_inner1 : jh2.get? innerAddr1 =
        some (.objArray "java/lang/Object"
          #[JvmVal.boxedInt 0, .boxedInt r1.val.toUInt32, .null, .null, .null, .boxedUInt r1.next]) := by
      have hlt : innerAddr1 < jh1a.objects.size := by
        simp [innerAddr1, jh1a, Jvm.JvmHeap.alloc, Array.size_push]
      rw [jvmHeap_get?_alloc_lt _ _ hlt]
      exact jvmHeap_get?_alloc_self _ _
    have hget_outer1 : jh2.get? outerAddr1 =
        some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr1]) :=
      jvmHeap_get?_alloc_self _ _
    have hget_b2 : jh2.get? jh.objects.size = some (.byteArray bytes.data) := by
      have hlt1 : jh.objects.size < jh1a.objects.size := by
        simp [jh1a, Jvm.JvmHeap.alloc, Array.size_push]; omega
      rw [jvmHeap_get?_alloc_lt _ _ hlt1, jvmHeap_get?_alloc_lt _ _ hb_lt_j1]
      exact hgetb
    have hpre89 :
        runJvmResFast 200 f_Algorithm_parseCoordLine_prog 0 f_Algorithm_parseCoordLine_prog
          ⟨0, [], setLocal (fun _ => .i32 0) 0 (.str line), jh, hp⟩ =
        runJvmResFast 122 f_Algorithm_parseCoordLine_prog 89
          (f_Algorithm_parseCoordLine_prog.drop 89)
          ⟨89, [.i32 (if r1.next == limit then 0 else if r1.next < limit then 4294967295 else 1)],
            setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
              (setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
                0 (.str line)) 1 (.heapRef jh.objects.size)) 2 (.i32 limit)) 3 (.i32 p0))
                4 (.heapRef outerAddr1)) 5 (.heapRef innerAddr1))
              7 (.boxedInt r1.val.toUInt32)) 8 (.i32 0)) 6 (.i32 r1.val.toUInt32))
              8 (.boxedUInt r1.next)) 9 (.i32 0)) 7 (.i32 r1.next),
            jh2, hp⟩ := by
      rw [parseCoordLine_prefix 200 line jh hp (by decide)]
      have h1' : Algorithm.parseInt32At line.toByteArray
          (Algorithm.skipSpaces line.toByteArray 0 line.toByteArray.size.toUInt32)
          line.toByteArray.size.toUInt32 = some r1 := h1
      dsimp only [encodeOptScalarPair]
      rw [h1']
      dsimp only [Option.map_some]
      norm_res_fuel
      have h20 := parseCoordLine_pc20_to_89 180 (by decide) line limit p0 r1
        jh jh2 outerAddr1 innerAddr1 hp hget_inner1 hget_outer1
      dsimp only [jh2, outerAddr1, jh1a, innerAddr1, inner1, jh1, bytes, limit, p0, Jvm.JvmHeap.alloc] at h20 ⊢
      exact h20
    have hpc89_res :
        (match Algorithm.parseCoordLine line with
          | some (x, y) => .pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32)
          | none => .null : JvmVal) =
        (if hr1lt : r1.next < limit then
          if hsp : Algorithm.isSpaceByte (bytes.get! r1.next.toNat) then
            match Algorithm.parseInt32At bytes (Algorithm.skipSpaces bytes r1.next limit) limit with
            | some r2 =>
              if Algorithm.skipSpaces bytes r2.next limit = limit then
                .pair (.boxedInt r1.val.toUInt32) (.boxedInt r2.val.toUInt32)
              else .null
            | none => .null
          else .null
        else .null) := by
      unfold Algorithm.parseCoordLine
      dsimp only [bytes, limit]
      have h1' : Algorithm.parseInt32At line.toByteArray
          (Algorithm.skipSpaces line.toByteArray 0 line.toByteArray.size.toUInt32)
          line.toByteArray.size.toUInt32 = some r1 := h1
      rw [h1']
      dsimp only
      by_cases hlt : r1.next < line.toByteArray.size.toUInt32
      · rw [dite_eq_left_of_eq_true (eq_true hlt)]
        by_cases hsp : Algorithm.isSpaceByte (line.toByteArray.get! r1.next.toNat)
        · have hcond : (decide (r1.next < line.toByteArray.size.toUInt32) &&
              Algorithm.isSpaceByte (line.toByteArray.get! r1.next.toNat)) = true := by
            rw [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hlt, hsp⟩
          rw [dite_eq_left_of_eq_true (eq_true hsp), hcond, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
          cases h2 : Algorithm.parseInt32At line.toByteArray
              (Algorithm.skipSpaces line.toByteArray r1.next line.toByteArray.size.toUInt32)
              line.toByteArray.size.toUInt32 with
          | none => rfl
          | some r2 =>
            dsimp only
            by_cases heq : Algorithm.skipSpaces line.toByteArray r2.next line.toByteArray.size.toUInt32 =
                line.toByteArray.size.toUInt32
            · rw [ite_eq_left_of_eq_true _ _ (eq_true heq),
                ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr heq))]
            · have hne : (Algorithm.skipSpaces line.toByteArray r2.next line.toByteArray.size.toUInt32 ==
                  line.toByteArray.size.toUInt32) = false := beq_false_of_ne heq
              rw [ite_eq_right_of_eq_false _ _ (eq_false heq), hne,
                ite_eq_right_of_eq_false _ _ (eq_false Bool.false_ne_true)]
        · have hcond : (decide (r1.next < line.toByteArray.size.toUInt32) &&
              Algorithm.isSpaceByte (line.toByteArray.get! r1.next.toNat)) = false := by
            rw [Bool.and_eq_false_iff]; exact Or.inr (Bool.eq_false_iff.mpr hsp)
          rw [dite_eq_right_of_eq_false (eq_false hsp), hcond,
            ite_eq_right_of_eq_false _ _ (eq_false Bool.false_ne_true)]
      · have hcond : (decide (r1.next < line.toByteArray.size.toUInt32) &&
            Algorithm.isSpaceByte (line.toByteArray.get! r1.next.toNat)) = false := by
          rw [Bool.and_eq_false_iff, decide_eq_false_iff_not]; exact Or.inl hlt
        rw [dite_eq_right_of_eq_false (eq_false hlt), hcond,
          ite_eq_right_of_eq_false _ _ (eq_false Bool.false_ne_true)]
    suffices hsuf : ∃ st',
        runJvmResFast 200 f_Algorithm_parseCoordLine_prog 0 f_Algorithm_parseCoordLine_prog
          ⟨0, [], setLocal (fun _ => .i32 0) 0 (.str line), jh, hp⟩ =
        some (match Algorithm.parseCoordLine line with
          | some (x, y) => .pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32)
          | none => .null, st') by
      obtain ⟨st', hst'⟩ := hsuf
      exact ⟨_, st', runJvmRes_of_runJvmResFast0 200 _ _ _ rfl hst', rfl⟩
    rw [hpc89_res]
    by_cases hr1lt : r1.next < limit
    · simp only [hr1lt, ↓reduceDIte]
      have hslt : (if r1.next == limit then (0 : UInt32)
          else if r1.next < limit then 4294967295 else 1).toBitVec.slt 0#32 = true := by
        rw [compareUnsigned_slt_zero]
        exact decide_eq_true hr1lt
      have hr1_slt0 : r1.next.toBitVec.slt 0#32 = false := by
        have : r1.next.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hr1lt
        rw [hlim_nat] at this; dsimp only [bytes] at this
        exact u32_slt_zero_of_lt_2_31 (by omega)
      have hr1_lt_sz : r1.next.toNat < bytes.data.size := by
        have : r1.next.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hr1lt
        rw [hlim_nat] at this; exact this
      have hgetb_eq : bytes.data[r1.next.toNat] = bytes.get! r1.next.toNat := by
        simp only [ByteArray.get!]
        exact (getElem!_pos bytes.data r1.next.toNat hr1_lt_sz).symm
      let locs89 : Nat → JvmVal :=
        setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          (setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
            0 (.str line)) 1 (.heapRef jh.objects.size)) 2 (.i32 limit)) 3 (.i32 p0))
            4 (.heapRef outerAddr1)) 5 (.heapRef innerAddr1))
          7 (.boxedInt r1.val.toUInt32)) 8 (.i32 0)) 6 (.i32 r1.val.toUInt32))
          8 (.boxedUInt r1.next)) 9 (.i32 0)) 7 (.i32 r1.next)
      have h89_to_100 :
          runJvmResFast 200 f_Algorithm_parseCoordLine_prog 0 f_Algorithm_parseCoordLine_prog
            ⟨0, [], setLocal (fun _ => .i32 0) 0 (.str line), jh, hp⟩ =
          runJvmResFast 113 f_Algorithm_parseCoordLine_prog 100
            (.if_icmpeq 109 :: f_Algorithm_parseCoordLine_prog.drop 101)
            ⟨100, [.i32 32, .i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))],
              setLocal locs89 8 (.i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))),
              jh2, hp⟩ := by
        rw [hpre89]
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        rw [show (122 : Nat) = 121 + 1 from rfl, runJvmResFast_iflt_branch hslt]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        rw [show (118 : Nat) = 117 + 1 from rfl, runJvmResFast_baload hget_b2 hr1_slt0 hr1_lt_sz]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        rw [show (117 : Nat) = 116 + 1 from rfl, runJvmResFast_invokestatic_step rfl]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        dsimp only [Jvm.JvmVal.asI32]
        rw [hgetb_eq]
        conv => rhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      rw [h89_to_100]
      by_cases hsp : Algorithm.isSpaceByte (bytes.get! r1.next.toNat)
      · simp only [hsp, ↓reduceDIte]
        have hsupp' : (Algorithm.parseInt32At bytes (Algorithm.skipSpaces bytes r1.next limit) limit).isSome = true := by
          unfold ParseCoordLineSupported at hsupp
          dsimp only at hsupp
          have h1' : Algorithm.parseInt32At line.toByteArray
              (Algorithm.skipSpaces line.toByteArray 0 line.toByteArray.size.toUInt32)
              line.toByteArray.size.toUInt32 = some r1 := h1
          have hcond : (decide (r1.next < line.toByteArray.size.toUInt32) &&
              Algorithm.isSpaceByte (line.toByteArray.get! r1.next.toNat)) = true := by
            rw [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hr1lt, hsp⟩
          rw [h1'] at hsupp
          dsimp only at hsupp
          rw [hcond] at hsupp
          exact hsupp
        rcases Option.isSome_iff_exists.mp hsupp' with ⟨r2, h2⟩
        simp only [h2]
        have hstep_pc109 : ∀ k, 70 ≤ k →
            ∃ st', runJvmResFast k f_Algorithm_parseCoordLine_prog 109
                (f_Algorithm_parseCoordLine_prog.drop 109)
                ⟨109, [], setLocal locs89 8 (.i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))), jh2, hp⟩ =
              some (if Algorithm.skipSpaces bytes r2.next limit = limit then
                .pair (.boxedInt r1.val.toUInt32) (.boxedInt r2.val.toUInt32) else .null, st') := by
          intro k hk
          have hcall := parseCoordLine_pc109 k hk bytes limit r1 jh.objects.size
            (setLocal locs89 8 (.i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))))
            jh2 hp hget_b2 rfl rfl rfl rfl r2 h2
          exact ⟨hcall.choose, hcall.choose_spec.1⟩
        have hb_cases : bytes.get! r1.next.toNat = 32 ∨ bytes.get! r1.next.toNat = 9 ∨
            bytes.get! r1.next.toNat = 13 := by
          unfold Algorithm.isSpaceByte at hsp
          simp only [Bool.or_eq_true, beq_iff_eq] at hsp
          rcases hsp with (h | h) | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        rcases hb_cases with hb | hb | hb
        · rw [show (113 : Nat) = 112 + 1 from rfl,
            runJvmResFast_if_icmpeq_branch (by rw [hb]; decide)]
          exact hstep_pc109 112 (by decide)
        · have h100_103 :
              runJvmResFast 113 f_Algorithm_parseCoordLine_prog 100
                (.if_icmpeq 109 :: f_Algorithm_parseCoordLine_prog.drop 101)
                ⟨100, [.i32 32, .i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))],
                  setLocal locs89 8 (.i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))),
                  jh2, hp⟩ =
              runJvmResFast 110 f_Algorithm_parseCoordLine_prog 103
                (.if_icmpeq 109 :: f_Algorithm_parseCoordLine_prog.drop 104)
                ⟨103, [.i32 9, .i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))],
                  setLocal locs89 8 (.i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))),
                  jh2, hp⟩ := by
            rw [show (113 : Nat) = 112 + 1 from rfl,
              runJvmResFast_if_icmpeq_fallthrough (by rw [u8_signExtend_beq_32, hb]; rfl)]; norm_res_fuel
            conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
            heap_step_nonbranch_chunks; norm_res_fuel
            conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
            conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
            conv => rhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
          rw [h100_103, show (110 : Nat) = 109 + 1 from rfl,
            runJvmResFast_if_icmpeq_branch (by rw [hb]; decide)]
          exact hstep_pc109 109 (by decide)
        · have h100_106 :
              runJvmResFast 113 f_Algorithm_parseCoordLine_prog 100
                (.if_icmpeq 109 :: f_Algorithm_parseCoordLine_prog.drop 101)
                ⟨100, [.i32 32, .i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))],
                  setLocal locs89 8 (.i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))),
                  jh2, hp⟩ =
              runJvmResFast 107 f_Algorithm_parseCoordLine_prog 106
                (.if_icmpeq 109 :: f_Algorithm_parseCoordLine_prog.drop 107)
                ⟨106, [.i32 13, .i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))],
                  setLocal locs89 8 (.i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))),
                  jh2, hp⟩ := by
            rw [show (113 : Nat) = 112 + 1 from rfl,
              runJvmResFast_if_icmpeq_fallthrough (by rw [u8_signExtend_beq_32, hb]; rfl)]; norm_res_fuel
            conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
            heap_step_nonbranch_chunks; norm_res_fuel
            conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
            conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
            rw [show (110 : Nat) = 109 + 1 from rfl,
              runJvmResFast_if_icmpeq_fallthrough (by rw [u8_signExtend_beq_9, hb]; rfl)]; norm_res_fuel
            conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
            heap_step_nonbranch_chunks; norm_res_fuel
            conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
            conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
            conv => rhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
          rw [h100_106, show (107 : Nat) = 106 + 1 from rfl,
            runJvmResFast_if_icmpeq_branch (by rw [hb]; decide)]
          exact hstep_pc109 106 (by decide)
      · have hne32 : (bytes.get! r1.next.toNat == 32) = false := by
          unfold Algorithm.isSpaceByte at hsp
          simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hsp
          exact hsp.1.1
        have hne9 : (bytes.get! r1.next.toNat == 9) = false := by
          unfold Algorithm.isSpaceByte at hsp
          simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hsp
          exact hsp.1.2
        have hne13 : (bytes.get! r1.next.toNat == 13) = false := by
          unfold Algorithm.isSpaceByte at hsp
          simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hsp
          exact hsp.2
        refine ⟨⟨108, [.null],
          setLocal locs89 8 (.i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))),
          jh2, hp⟩, ?_⟩
        rw [show (113 : Nat) = 112 + 1 from rfl,
          runJvmResFast_if_icmpeq_fallthrough (by rw [u8_signExtend_beq_32]; exact hne32)]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        rw [show (110 : Nat) = 109 + 1 from rfl,
          runJvmResFast_if_icmpeq_fallthrough (by rw [u8_signExtend_beq_9]; exact hne9)]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
        rw [show (107 : Nat) = 106 + 1 from rfl,
          runJvmResFast_if_icmpeq_fallthrough (by rw [u8_signExtend_beq_13]; exact hne13)]; norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        heap_step_nonbranch_chunks
        rw [dite_eq_right_of_eq_false (eq_false hsp)]
    · have hslt : (if r1.next == limit then (0 : UInt32)
          else if r1.next < limit then 4294967295 else 1).toBitVec.slt 0#32 = false := by
        rw [compareUnsigned_slt_zero]
        exact decide_eq_false hr1lt
      refine ⟨⟨91, [.null],
        setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          (setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
            0 (.str line)) 1 (.heapRef jh.objects.size)) 2 (.i32 limit)) 3 (.i32 p0))
            4 (.heapRef outerAddr1)) 5 (.heapRef innerAddr1))
          7 (.boxedInt r1.val.toUInt32)) 8 (.i32 0)) 6 (.i32 r1.val.toUInt32))
          8 (.boxedUInt r1.next)) 9 (.i32 0)) 7 (.i32 r1.next),
        jh2, hp⟩, ?_⟩
      rw [hpre89]
      conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      rw [show (122 : Nat) = 121 + 1 from rfl, runJvmResFast_iflt_fallthrough hslt]; norm_res_fuel
      conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      heap_step_nonbranch_chunks
      rw [dite_eq_right_of_eq_false (eq_false hr1lt)]

theorem parseCoordLine_second_parseInt32At_none_traps (line : String)
    (hp : AlgHeap) (r1 : Algorithm.ParsedInt32)
    (hsz : line.toByteArray.size < 2 ^ 31)
    (h1 : Algorithm.parseInt32At line.toByteArray
      (Algorithm.skipSpaces line.toByteArray 0 line.toByteArray.size.toUInt32)
      line.toByteArray.size.toUInt32 = some r1)
    (hsp : r1.next < line.toByteArray.size.toUInt32 ∧
      Algorithm.isSpaceByte (line.toByteArray.get! r1.next.toNat) = true)
    (h2 : Algorithm.parseInt32At line.toByteArray
      (Algorithm.skipSpaces line.toByteArray r1.next line.toByteArray.size.toUInt32)
      line.toByteArray.size.toUInt32 = none) :
    ∀ f : Nat,
      runJvmRes f f_Algorithm_parseCoordLine_prog
        ⟨0, [], setLocal (fun _ => .i32 0) 0 (.str line), {}, hp⟩ = none := by
  intro f
  cases hres : runJvmRes f f_Algorithm_parseCoordLine_prog
      ⟨0, [], setLocal (fun _ => .i32 0) 0 (.str line), {}, hp⟩ with
  | none => rfl
  | some res =>
    exfalso
    let jh : Jvm.JvmHeap AlgExt := {}
    have h120 : runJvmRes (f + 120) f_Algorithm_parseCoordLine_prog
        ⟨0, [], setLocal (fun _ => .i32 0) 0 (.str line), jh, hp⟩ = some res :=
      jvm_runJvmRes_mono algHooks f (f + 120) f_Algorithm_parseCoordLine_prog _ res (by omega) hres
    have hall_noi2l : f_Algorithm_parseCoordLine_prog.all (fun | .i2l => false | _ => true) = true := by
      decide
    have hnoi2l : ∀ i ∈ f_Algorithm_parseCoordLine_prog, i ≠ .i2l := by
      intro i hi h
      subst h
      simp only [List.all_eq_true] at hall_noi2l
      exact Bool.false_ne_true (hall_noi2l .i2l hi)
    dsimp only [runJvmRes] at h120
    rw [← runJvmRes_eq_runJvmResFast_no_i2l algHooks f_Algorithm_parseCoordLine_prog hnoi2l
      (f + 120) 0 f_Algorithm_parseCoordLine_prog _ rfl rfl] at h120
    change runJvmResFast (f + 120) f_Algorithm_parseCoordLine_prog 0 f_Algorithm_parseCoordLine_prog
      ⟨0, [], setLocal (fun _ => .i32 0) 0 (.str line), jh, hp⟩ = some res at h120
    let bytes := line.toByteArray
    let limit := bytes.size.toUInt32
    let p0 := Algorithm.skipSpaces bytes 0 limit
    let jh1 := (jh.alloc (.byteArray bytes.data)).2
    have hgetb : jh1.get? jh.objects.size = some (.byteArray bytes.data) :=
      jvmHeap_get?_alloc_self _ _
    have hb_lt_j1 : jh.objects.size < jh1.objects.size := by
      simp [jh1, Jvm.JvmHeap.alloc, Array.size_push]
    have hlim_nat : limit.toNat = bytes.size := by
      dsimp only [limit, bytes]
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega : line.toByteArray.size < 2 ^ 32)]
    let inner1 : Array JvmVal := #[JvmVal.boxedInt 0, .boxedInt r1.val.toUInt32, .null, .null, .null, .boxedUInt r1.next]
    let innerAddr1 := jh1.objects.size
    let jh1a := (jh1.alloc (.objArray "java/lang/Object" inner1)).2
    let outerAddr1 := jh1a.objects.size
    let jh2 := (jh1a.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr1])).2
    have hget_inner1 : jh2.get? innerAddr1 = some (.objArray "java/lang/Object" inner1) := by
      have hlt : innerAddr1 < jh1a.objects.size := by
        simp [jh1a, innerAddr1, Jvm.JvmHeap.alloc, Array.size_push]
      rw [jvmHeap_get?_alloc_lt _ _ hlt]
      exact jvmHeap_get?_alloc_self _ _
    have hget_outer1 : jh2.get? outerAddr1 =
        some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr1]) :=
      jvmHeap_get?_alloc_self _ _
    have hget_b2 : jh2.get? jh.objects.size = some (.byteArray bytes.data) := by
      have hlt1 : jh.objects.size < jh1a.objects.size := by
        simp [jh1a, Jvm.JvmHeap.alloc, Array.size_push]; omega
      rw [jvmHeap_get?_alloc_lt _ _ hlt1, jvmHeap_get?_alloc_lt _ _ hb_lt_j1]
      exact hgetb
    rw [parseCoordLine_prefix (f + 120) line jh hp (by omega)] at h120
    dsimp only [encodeOptScalarPair, h1, Option.map_some] at h120
    have hpc89_none : runJvmResFast (f + 120 - 20) f_Algorithm_parseCoordLine_prog 20
        (f_Algorithm_parseCoordLine_prog.drop 20)
        ⟨20, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.str line))
          1 (.heapRef jh.objects.size)) 2 (.i32 limit)) 3 (.i32 p0)) 4 (.heapRef outerAddr1),
          jh2, hp⟩ = none := by
      rw [parseCoordLine_pc20_to_89 (f + 120 - 20) (by omega) line limit p0 r1
        jh jh2 outerAddr1 innerAddr1 hp hget_inner1 hget_outer1]
      rw [show f + 120 - 20 - 58 = f + 42 from by omega]
      dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      rw [show f + 42 = (f + 41) + 1 from by omega]
      rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hsp.1)]
      conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      rw [show f + 41 = (f + 38) + 3 from by omega]
      heap_step_nonbranch_chunks
      conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
      rw [show f + 38 = (f + 37) + 1 from by omega]
      have hr1_slt0 : r1.next.toBitVec.slt 0#32 = false := by
        have : r1.next.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hsp.1
        rw [hlim_nat] at this; dsimp only [bytes] at this
        exact u32_slt_zero_of_lt_2_31 (by omega)
      have hr1_lt_sz : r1.next.toNat < bytes.data.size := by
        have : r1.next.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hsp.1
        rw [hlim_nat] at this; exact this
      rw [runJvmResFast_baload hget_b2 hr1_slt0 hr1_lt_sz]
      conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      rw [show f + 37 = (f + 36) + 1 from by omega]
      rw [runJvmResFast_invokestatic_step rfl]
      conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
      rw [show f + 36 = (f + 33) + 3 from by omega]
      heap_step_nonbranch_chunks
      conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
      dsimp only [Jvm.JvmVal.asI32]
      have hgetb_eq : bytes.data[r1.next.toNat] = bytes.get! r1.next.toNat := by
        simp only [ByteArray.get!]
        exact (getElem!_pos bytes.data r1.next.toNat hr1_lt_sz).symm
      rw [hgetb_eq]
      let locs89 : Nat → JvmVal :=
        setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          (setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
            0 (.str line)) 1 (.heapRef jh.objects.size)) 2 (.i32 limit)) 3 (.i32 p0))
            4 (.heapRef outerAddr1)) 5 (.heapRef innerAddr1))
          7 (.boxedInt r1.val.toUInt32)) 8 (.i32 0)) 6 (.i32 r1.val.toUInt32))
          8 (.boxedUInt r1.next)) 9 (.i32 0)) 7 (.i32 r1.next)
      have htrap_pc109 : ∀ k, 20 ≤ k →
          runJvmResFast k f_Algorithm_parseCoordLine_prog 109
            (f_Algorithm_parseCoordLine_prog.drop 109)
            ⟨109, [], setLocal locs89 8 (.i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))),
              jh2, hp⟩ = none := by
        intro k hk
        have hl1 : locs89 1 = .heapRef jh.objects.size := rfl
        have hl2 : locs89 2 = .i32 limit := rfl
        have hl7 : locs89 7 = .i32 r1.next := rfl
        rw [show k = (k - 4) + 1 + 3 from by omega]
        dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        heap_step_nonbranch_chunks
        conv => lhs; arg 5; arg 1; change 112
        rw [runJvmResFast_invokestatic_step (stepStatic_skipSpaces_heap (Or.inr (Or.inl rfl)) hget_b2)]
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        rw [show k - 4 = (k - 9) + 1 + 4 from by omega]
        heap_step_nonbranch_chunks
        conv => lhs; arg 5; arg 1; change 117
        rw [runJvmResFast_invokestatic_step (stepStatic_parseInt32At_heap (Or.inr (Or.inl rfl)) hget_b2)]
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        have hbytes_eta : (⟨bytes.data⟩ : ByteArray) = bytes := rfl
        dsimp only [encodeOptScalarPair, Jvm.JvmVal.asI32]
        rw [hbytes_eta, h2]
        dsimp only [Option.map_none]
        rw [show k - 9 = (k - 12) + 1 + 2 from by omega]
        heap_step_nonbranch_chunks
        conv => lhs; arg 5; arg 1; change 120
        dsimp only [Jvm.JvmHeap.alloc]
        rw [runJvmResFast_ifnonnull_branch (v := .heapRef jh2.objects.size) rfl]
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        rw [show k - 12 = (k - 14) + 1 + 1 from by omega]
        heap_step_nonbranch_chunks
        conv => lhs; arg 5; arg 1; change 124
        have hget_outer2 : (jh2.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2.get? jh2.objects.size =
            some (.objArray "java/lang/Object" #[.boxedInt 0]) := jvmHeap_get?_alloc_self _ _
        dsimp only [Jvm.JvmHeap.alloc] at hget_outer2
        rw [runJvmResFast_checkcast_objArray hget_outer2 (Or.inl rfl)]
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        rw [show k - 14 = (k - 16) + 1 + 1 from by omega]
        heap_step_nonbranch_chunks
        conv => lhs; arg 5; arg 1; change 126
        dsimp only [jh2, jh1a, jh1, jh, Jvm.JvmHeap.alloc]
        exact runJvmResFast_aaload1_len1_none_rfl
      have hb_cases : bytes.get! r1.next.toNat = 32 ∨ bytes.get! r1.next.toNat = 9 ∨
          bytes.get! r1.next.toNat = 13 := by
        have hsp' := hsp.2
        unfold Algorithm.isSpaceByte at hsp'
        simp only [Bool.or_eq_true, beq_iff_eq] at hsp'
        rcases hsp' with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      rcases hb_cases with hb | hb | hb
      · rw [show f + 33 = (f + 32) + 1 from by omega]
        rw [runJvmResFast_if_icmpeq_branch (by rw [hb]; decide)]
        exact htrap_pc109 _ (by omega)
      · rw [show f + 33 = (f + 32) + 1 from by omega]
        rw [runJvmResFast_if_icmpeq_fallthrough (by rw [u8_signExtend_beq_32, hb]; rfl)]
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        rw [show f + 32 = (f + 30) + 2 from by omega]
        heap_step_nonbranch_chunks
        conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
        rw [show f + 30 = (f + 29) + 1 from by omega]
        rw [runJvmResFast_if_icmpeq_branch (by rw [hb]; decide)]
        exact htrap_pc109 _ (by omega)
      · rw [show f + 33 = (f + 32) + 1 from by omega]
        rw [runJvmResFast_if_icmpeq_fallthrough (by rw [u8_signExtend_beq_32, hb]; rfl)]
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        rw [show f + 32 = (f + 30) + 2 from by omega]
        heap_step_nonbranch_chunks
        conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
        rw [show f + 30 = (f + 29) + 1 from by omega]
        rw [runJvmResFast_if_icmpeq_fallthrough (by rw [u8_signExtend_beq_9, hb]; rfl)]
        conv => lhs; arg 4; dsimp only [f_Algorithm_parseCoordLine_prog, List.drop]
        rw [show f + 29 = (f + 27) + 2 from by omega]
        heap_step_nonbranch_chunks
        conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
        rw [show f + 27 = (f + 26) + 1 from by omega]
        rw [runJvmResFast_if_icmpeq_branch (by rw [hb]; decide)]
        exact htrap_pc109 _ (by omega)
    have h1' : Algorithm.parseInt32At line.toByteArray
        (Algorithm.skipSpaces line.toByteArray 0 line.toByteArray.size.toUInt32)
        line.toByteArray.size.toUInt32 = some r1 := h1
    rw [h1'] at h120
    dsimp only [Option.map_some, jh2, outerAddr1, jh1a, innerAddr1, inner1, jh1, bytes, limit, p0,
      Jvm.JvmHeap.alloc] at h120 hpc89_none
    rw [hpc89_none] at h120
    simp at h120
