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
import proofs.JvmEquiv.Family6a

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

/-! ### Family 6b: RLE Deserialization (`copyAscii`, `parseRLEComments`, `parseRLEData`, `expandRuns`,
`deserializeRLE`) -/

private theorem list_drop_step {α : Type} {l : List α} {k : Nat} {x : α}
    (h : l[k]? = some x) : l.drop k = x :: l.drop (k + 1) := by
  induction k generalizing l with
  | zero => cases l <;> simp_all
  | succ k ih =>
    cases l with
    | nil => simp at h
    | cons a as => exact ih h

open Lean Elab Tactic in
local elab "step_drop " n:num : tactic => do
  for _ in [:n.getNat] do
    evalTactic (← `(tactic| (conv => lhs; arg 4; rw [list_drop_step rfl]; try simp only [Nat.reduceAdd])))

open Lean Elab Tactic in
local elab "drop_prefix " n:num : tactic => do
  for _ in [:n.getNat] do
    evalTactic (← `(tactic| (conv => lhs; rw [list_drop_step rfl]); try simp only [Nat.reduceAdd]))
  evalTactic (← `(tactic| try rfl))

private def HeapExtends (h1 h2 : Jvm.JvmHeap AlgExt) : Prop :=
  ∀ addr obj, h1.get? addr = some obj → h2.get? addr = some obj

private theorem heapExtends_refl (h : Jvm.JvmHeap AlgExt) : HeapExtends h h :=
  fun _ _ hx => hx

private theorem heapExtends_trans {h1 h2 h3 : Jvm.JvmHeap AlgExt}
    (h12 : HeapExtends h1 h2) (h23 : HeapExtends h2 h3) : HeapExtends h1 h3 :=
  fun addr obj hx => h23 addr obj (h12 addr obj hx)

private theorem heapExtends_alloc (h : Jvm.JvmHeap AlgExt) (obj : Jvm.HeapObj AlgExt) :
    HeapExtends h (h.alloc obj).2 := by
  intro addr o hget
  simp only [Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc] at hget ⊢
  have hlt : addr < h.objects.size := (Array.getElem?_eq_some_iff.mp hget).1
  rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt]
  exact hget

private theorem heapExtends_statics {h1 h2 : Jvm.JvmHeap AlgExt}
    (hext : h1.statics = [] → h2.statics = []) (hs : h1.statics = []) : h2.statics = [] :=
  hext hs

/-! #### Fast Non-WHNF Step Helpers -/

private theorem runJvmResFast_iload {f pc idx : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.iload idx :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_istore {f pc idx : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.istore idx :: rest) ⟨pc, v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_ldcStr {f pc : Nat} {s : String} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.ldcStr s :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .str s :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_newClass {f pc : Nat} {cls : String} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hnsb : cls ≠ "java/lang/StringBuilder" := by decide) :
    runJvmResFast (f + 1) prog pc (.newClass cls :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp)
    (by unfold Jvm.stepInstr; dsimp only; simp only [beq_iff_eq, hnsb, ↓reduceIte]) rfl

private theorem runJvmResFast_aconstNull {f pc : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.aconstNull :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .null :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_nop_local {f pc : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.nop :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_dup_local {f pc : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.dup :: rest) ⟨pc, v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, v :: v :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_iconst_local {f pc : Nat} {prog rest : List JvmInstr} {c : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.iconst c :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 c :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_lconst_local {f pc : Nat} {prog rest : List JvmInstr} {c : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.lconst c :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i64 c :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_astore_local {f pc idx : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.astore idx :: rest) ⟨pc, v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_aload_local {f pc idx : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.aload idx :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_iadd_local {f pc : Nat} {prog rest : List JvmInstr} {a b : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.iadd :: rest) ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 (a + b) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_iand_local {f pc : Nat} {prog rest : List JvmInstr} {a b : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.iand :: rest) ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 (a &&& b) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_vreturn_local {f pc : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.vreturn :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      some (.unit, ⟨pc, stk, locs, jh, hp⟩) := by
  unfold runJvmResFast; rw [Jvm.runJvmResFast.eq_def]; rfl

private theorem runJvmResFast_areturn_local {f pc : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.areturn :: rest) ⟨pc, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  unfold runJvmResFast; rw [Jvm.runJvmResFast.eq_def]; rfl

private theorem runJvmResFast_tableswitch_local {f pc dflt : Nat} {low : Int32}
    {targets : List Nat} {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.tableswitch low targets dflt :: rest)
        ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      let tgt := Jvm.tableswitchTarget v low targets dflt
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  unfold runJvmResFast; rw [Jvm.runJvmResFast.eq_def]; rfl

private theorem runJvmResFast_instanceof_boxedInt_uint {f pc : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.instanceof "kotlin/UInt" :: rest)
        ⟨pc, .boxedInt v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 0 :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.instanceof "kotlin/UInt")
      ⟨pc, .boxedInt v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 0 :: stk, locs, jh, hp⟩) := rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

private theorem list_set_eq_self {α : Type} :
    ∀ (l : List α) {i : Nat} {x : α}, l[i]? = some x → l.set i x = l
  | [], _, _, h => by simp at h
  | a :: as, 0, x, h => by simp at h; subst h; rfl
  | a :: as, i + 1, x, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, list_set_eq_self as h]

@[simp]
private theorem setLocal_self (locs : Nat → JvmVal) (k : Nat) (v : JvmVal) :
    setLocal locs k v k = v := by simp [setLocal]

private theorem setLocal_ne (locs : Nat → JvmVal) {k j : Nat} (v : JvmVal) (hne : j ≠ k) :
    setLocal locs k v j = locs j := by simp [setLocal, hne]

private theorem stepStatic_uintCtor_local {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩ "kotlin/UInt" "constructor-impl" "(I)I" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

private theorem stepStatic_ubyteCtor_local {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩ "kotlin/UByte" "constructor-impl" "(B)B" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

private theorem stepStatic_compareUnsigned_i32 {pc : Nat} {a b : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩
      "java/lang/Integer" "compareUnsigned" "(II)I" =
      .inl (some ⟨pc + 1, .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: stk,
        locs, jh, hp⟩) := rfl

private theorem stepStatic_compareUnsigned_local {pc : Nat} {b a : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩
      "java/lang/Integer" "compareUnsigned" "(II)I" =
      .inl (some ⟨pc + 1, .i32 (if a == b then 0
        else if a < b then 4294967295 else 1) :: stk, locs, jh, hp⟩) := rfl

private theorem stepStatic_intrinsicsCompare_local {pc : Nat} {b a : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "compare" "(II)I" =
      .inl (some ⟨pc + 1, .i32 (if a == b then 0
        else if a.toBitVec.slt b.toBitVec then 4294967295 else 1) :: stk,
        locs, jh, hp⟩) := rfl

private theorem stepStatic_checkNotNullParam_local {pc : Nat} {v name : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hn : v.isNull = false) :
    stepInvokeStatic ⟨pc, name :: v :: stk, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
      "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, name :: v :: stk, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
      "(Ljava/lang/Object;Ljava/lang/String;)V" =
      (if v.isNull then .inr none else .inl (some ⟨pc + 1, stk, locs, jh, hp⟩)) := rfl
  rw [hfn, hn]; rfl

private theorem stepStatic_checkNotNull_local {pc : Nat} {v name : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hn : v.isNull = false) :
    stepInvokeStatic ⟨pc, name :: v :: stk, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, name :: v :: stk, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      (if v.isNull then .inr none else .inl (some ⟨pc + 1, stk, locs, jh, hp⟩)) := rfl
  rw [hfn, hn]; rfl

private theorem stepStatic_noCells_rle_local {pc : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)}
    {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩ "RleLeanKt" "f_Algorithm_noCells" "()[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref u64.length) :: rest, locs, jh,
        ⟨ar, u64 ++ [Algorithm.noCells], asc⟩⟩) := rfl

private theorem stepStatic_growBufEmpty_rle_local {pc : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .null :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_GrowBuf_empty___redArg" "(Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_parseRLEComments_closed1_local {pc : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_parseRLEComments___closed__1"
      "()Lcom/alexvanyo/composelife/model/RLEStatus;" =
      .inl (some ⟨pc + 1, .ext (.rleStatus (.invalidHeader "none")) :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_parseRLEOffset_heap_local {pc addr : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_parseRLEOffset" "([B)Ljava/lang/Object;" =
      let optPair := (Algorithm.parseRLEOffset ⟨elems⟩).map fun r =>
        (.boxedInt r.x.toUInt32, .boxedInt r.y.toUInt32)
      let (res, h') := encodeOptScalarPair jh optPair
      .inl (some ⟨pc + 1, res :: rest, locs, h', hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_parseRLEOffset" "([B)Ljava/lang/Object;" =
      match decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) with
      | some bytes =>
        let optPair := (Algorithm.parseRLEOffset bytes).map
          fun (r : Algorithm.ParsedCoords) => (.boxedInt r.x.toUInt32, .boxedInt r.y.toUInt32)
        let (res, h') := encodeOptScalarPair jh optPair
        .inl (some ⟨pc + 1, res :: rest, locs, h', hp⟩)
      | none => .inr none := rfl
  rw [hfn]; simp only [decodeBytes, hget]

private theorem stepStatic_parseRLEHeader_heap_local {pc addr : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_parseRLEHeader" "([B)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.parseRLEHeader ⟨elems⟩) :: rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_parseRLEHeader" "([B)I" =
      match decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) with
      | some bytes =>
        .inl (some ⟨pc + 1, .i32 (Algorithm.parseRLEHeader bytes) :: rest, locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn]; simp only [decodeBytes, hget]

private theorem stepStatic_deserializeRLE_closed1_local {pc : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_deserializeRLE___closed__1"
      "()Lcom/alexvanyo/composelife/model/RLEResult;" =
      let res := Algorithm.RLEResult.mk .emptyFile #[.emptyFile] Algorithm.noCells
      let (resVal, h', u64s') := encodeRLEResult jh hp.u64Arrays res
      .inl (some ⟨pc + 1, resVal :: rest, locs, h', { hp with u64Arrays := u64s' }⟩) := rfl

private theorem stepSpecial_rleWarnDupOffset_init {pc : Nat} {marker y x ln : JvmVal}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, marker :: y :: x :: ln ::
        .allocRef "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset" ::
        .allocRef "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset" :: rest,
        locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset" "<init>"
      "(IIILkotlin/jvm/internal/DefaultConstructorMarker;)V" =
      let (addr, h') := jh.alloc (.instance
        "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset"
        [("lineIndex", ln), ("x", x), ("y", y)])
      .inl (some ⟨pc + 1, .heapRef addr :: rest, locs, h', hp⟩) := rfl

private theorem stepSpecial_rleStatusInvalidHeader_init {pc : Nat} {s : String}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, .str s ::
        .allocRef "com/alexvanyo/composelife/model/RLEStatus$InvalidHeader" ::
        .allocRef "com/alexvanyo/composelife/model/RLEStatus$InvalidHeader" :: rest,
        locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RLEStatus$InvalidHeader" "<init>"
      "(Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, .ext (.rleStatus (.invalidHeader s)) :: rest, locs, jh, hp⟩) := rfl

private theorem stepSpecial_rleResult_init {pc : Nat} {marker cells warns status : JvmVal}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, marker :: cells :: warns :: status ::
        .allocRef "com/alexvanyo/composelife/model/RLEResult" ::
        .allocRef "com/alexvanyo/composelife/model/RLEResult" :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RLEResult" "<init>"
  "(Lcom/alexvanyo/composelife/model/RLEStatus;[Ljava/lang/Object;[JLkotlin/jvm/internal/DefaultConstructorMarker;)V" =
      let (addr, h') := jh.alloc (.instance "com/alexvanyo/composelife/model/RLEResult"
        [("status", status), ("warnings", warns), ("cells", cells)])
      .inl (some ⟨pc + 1, .heapRef addr :: rest, locs, h', hp⟩) := rfl

private theorem u8Sext_eq_u8_toUInt8 (b : UInt8) :
    (UInt32.ofBitVec (b.toBitVec.signExtend 32)).toUInt8 = b := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_toUInt8, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend,
    hi, (by omega : i < 32), decide_true, ↓reduceIte, Bool.true_and]

private theorem ubyte_sext_mask (b : UInt8) :
    UInt32.ofBitVec (b.toBitVec.signExtend 32) &&& 255 = b.toUInt32 := by
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_and, BitVec.getLsbD_and,
    BitVec.getLsbD_signExtend, hi, decide_true, Bool.true_and,
    UInt8.toBitVec_toUInt32, BitVec.getLsbD_setWidth]
  rw [show UInt32.toBitVec 255 = 255#32 from rfl]
  by_cases h8 : i < 8
  · have hm : (255#32).getLsbD i = true := by
      rw [BitVec.getLsbD_eq_getElem hi]; revert i hi h8; decide
    simp [h8, hm]
  · have hm : (255#32).getLsbD i = false := by
      rw [BitVec.getLsbD_eq_getElem hi]; revert i hi h8; decide
    have hge : @BitVec.getLsbD 8 b.toBitVec i = false :=
      BitVec.getLsbD_of_ge b.toBitVec i (Nat.le_of_not_lt h8)
    simp [h8, hm, hge]

private theorem byteArray_get_eq_getBang (bytes : ByteArray) {idx : Nat} (hlt : idx < bytes.data.size) :
    bytes.data[idx] = bytes.get! idx := by
  simp only [ByteArray.get!, getElem!_pos bytes.data idx hlt]

private theorem decodeRLEResult_encode_proj
    (pc : Nat) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (res : Algorithm.RLEResult) :
    decodeRLEResult
        ⟨pc, stk, locs, (encodeRLEResult jh u64 res).2.1,
          ⟨ar, (encodeRLEResult jh u64 res).2.2, asc⟩⟩
        (encodeRLEResult jh u64 res).1 =
      some res := by
  have h := decodeRLEResult_encode jh ⟨ar, u64, asc⟩ res
  rcases he : encodeRLEResult jh u64 res with ⟨a, b, c⟩
  dsimp only at h
  rw [he] at h
  dsimp only [decodeRLEResult] at h ⊢
  exact h

private theorem encodeRLEResult_heapExtends
    (jh : Jvm.JvmHeap AlgExt) (u64 : List (Array UInt64)) (res : Algorithm.RLEResult) :
    HeapExtends jh (encodeRLEResult jh u64 res).2.1 := by
  rcases res with ⟨status, warns, cells⟩
  dsimp only [encodeRLEResult]
  have hfold : ∀ (l : List Algorithm.RLEWarning) (p : Array JvmVal × Jvm.JvmHeap AlgExt),
      HeapExtends p.2 (l.foldl (fun acc w =>
        (acc.1.push (encodeRLEWarning acc.2 w).1, (encodeRLEWarning acc.2 w).2)) p).2 := by
    intro l
    induction l with
    | nil => intro p; exact heapExtends_refl p.2
    | cons w ws ih =>
      intro p
      simp only [List.foldl_cons]
      have hw : HeapExtends p.2 (encodeRLEWarning p.2 w).2 := by
        cases w <;> simp only [encodeRLEWarning]
        · exact heapExtends_refl p.2
        · exact heapExtends_alloc _ _
        · exact heapExtends_alloc _ _
        · exact heapExtends_alloc _ _
        · exact heapExtends_alloc _ _
      exact heapExtends_trans hw (ih (p.1.push (encodeRLEWarning p.2 w).1, (encodeRLEWarning p.2 w).2))
  have h1 := hfold warns.toList (#[], jh)
  rw [Array.foldl_toList] at h1
  exact heapExtends_trans h1 (heapExtends_trans (heapExtends_alloc _ _) (heapExtends_alloc _ _))

/-! #### `GrowBuf (UInt32 × UInt32)` Representation -/

private inductive RlePairRep : Algorithm.GrowBuf (UInt32 × UInt32) → JvmVal → Prop
  | empty (b : Algorithm.GrowBuf (UInt32 × UInt32))
      (he : b.data.isEmpty = true) (hz : b.size = 0) :
      RlePairRep b (.ext (.strGrowBuf Algorithm.GrowBuf.empty))
  | full (b : Algorithm.GrowBuf (UInt32 × UInt32)) :
      RlePairRep b (.ext (.u32PairGrowBuf b))

private theorem rlePairRep_empty :
    RlePairRep (Algorithm.GrowBuf.empty : Algorithm.GrowBuf (UInt32 × UInt32))
      (.ext (.strGrowBuf Algorithm.GrowBuf.empty)) :=
  RlePairRep.empty _ rfl rfl

private theorem growBuf_eq_empty_of' {α : Type} {b : Algorithm.GrowBuf α}
    (he : b.data.isEmpty = true) (hz : b.size = 0) : b = Algorithm.GrowBuf.empty := by
  have hd : b.data = #[] := Array.isEmpty_iff.mp he
  rcases b with ⟨d, s⟩
  dsimp only at hd hz
  subst hd hz
  simp [Algorithm.GrowBuf.empty]

private theorem stepStatic_growBufPush_u32Pair
    {pc : Nat} {a c : UInt32} {bufVal : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {b : Algorithm.GrowBuf (UInt32 × UInt32)}
    (hrep : RlePairRep b bufVal) :
    stepInvokeStatic ⟨pc, .pair (.boxedUInt a) (.boxedUInt c) :: bufVal :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
      "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.u32PairGrowBuf (b.push (a, c))) :: rest, locs, jh, hp⟩) := by
  cases hrep with
  | empty he hz =>
    have hb : b = Algorithm.GrowBuf.empty := growBuf_eq_empty_of' he hz
    subst hb; rfl
  | full => rfl

/-! #### 1. `f_Algorithm_copyAscii_prog` -/

section CopyAscii
set_option maxRecDepth 2048

private theorem copyAscii_loop (m : Nat) :
    ∀ (f : Nat) (bytes : ByteArray) (bytesAddr : Nat) (s n k : UInt32)
      (gId : Nat) (g : Algorithm.AsciiBytes) (locs : Nat → JvmVal)
      (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
      (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes),
      n.toNat - k.toNat ≤ m →
      f ≥ m * 50 + 6 →
      bytes.data.size < 2 ^ 31 →
      s.toNat + n.toNat ≤ bytes.data.size →
      jh.get? bytesAddr = some (.byteArray bytes.data) →
      asc[gId]? = some g →
      locs 0 = .heapRef bytesAddr →
      locs 1 = .i32 s →
      locs 2 = .i32 n →
      locs 3 = .i32 k →
      locs 4 = .ext (.asciiRef gId) →
      ∃ st', runJvmResFast f f_Algorithm_copyAscii_prog 6 (f_Algorithm_copyAscii_prog.drop 6)
          ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ = some (.unit, st') ∧
        st'.jvmHeap = jh ∧
        st'.heap = ⟨ar, u64, asc.set gId (Algorithm.copyAscii bytes s n k g)⟩ := by
  induction m with
  | zero =>
    intro f bytes bytesAddr s n k gId g locs jh ar u64 asc hle hf hsz hbound hbytes hasc
      hl0 hl1 hl2 hl3 hl4
    have hk_ge : ¬ (k < n) := by
      intro hlt
      have h1 := UInt32.lt_iff_toNat_lt.mp hlt
      omega
    have h6 : f_Algorithm_copyAscii_prog.drop 6 =
        .iload 3 :: .iload 2 ::
        .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" ::
        .iflt 11 :: .vreturn :: f_Algorithm_copyAscii_prog.drop 11 := by drop_prefix 5
    apply Exists.intro; refine ⟨?_, ?_, ?_⟩
    · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 5 := ⟨f - 5, by omega⟩
      rw [h6]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl3]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl2]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
      rw [runJvmResFast_iflt_fallthrough (by
        rw [compareUnsigned_slt_zero]; exact decide_eq_false hk_ge)]
      norm_res_fuel
      rw [runJvmResFast_vreturn_local]
    · rfl
    · have hca : Algorithm.copyAscii bytes s n k g = g := by
        unfold Algorithm.copyAscii
        simp only [hk_ge, ↓reduceDIte]
      rw [hca, list_set_eq_self asc hasc]
  | succ m ih =>
    intro f bytes bytesAddr s n k gId g locs jh ar u64 asc hle hf hsz hbound hbytes hasc
      hl0 hl1 hl2 hl3 hl4
    by_cases hkn : k < n
    · have hkn_nat : k.toNat < n.toNat := UInt32.lt_iff_toNat_lt.mp hkn
      have hsk_lt : s.toNat + k.toNat < bytes.data.size := by omega
      have hsk_eq : (s + k).toNat = s.toNat + k.toNat := by
        rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
      have hsk_slt : (s + k).toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
      have hsk_sz : (s + k).toNat < bytes.data.size := by rw [hsk_eq]; exact hsk_lt
      let b := bytes.get! (s + k).toNat
      have hk1_eq : (k + 1).toNat = k.toNat + 1 := by
        rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by have := UInt32.toNat_lt n; omega)]
      have hsub : n.toNat - (k + 1).toNat ≤ m := by rw [hk1_eq]; omega
      let locs1 : Nat → JvmVal := setLocal (setLocal locs 5 (.i32 (UInt32.ofBitVec (b.toBitVec.signExtend 32))))
        6 (.i32 (k + 1))
      have h6_32 : runJvmResFast f f_Algorithm_copyAscii_prog 6 (f_Algorithm_copyAscii_prog.drop 6)
          ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
          runJvmResFast (f - 25) f_Algorithm_copyAscii_prog 32 (f_Algorithm_copyAscii_prog.drop 32)
            ⟨32, [.i32 (if b.toUInt32 == 128 then 0
              else if b.toUInt32.toBitVec.slt (128 : UInt32).toBitVec then 4294967295 else 1)],
              locs1, jh, ⟨ar, u64, asc⟩⟩ := by
        have h6 : f_Algorithm_copyAscii_prog.drop 6 =
            .iload 3 :: .iload 2 ::
            .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" ::
            .iflt 11 :: f_Algorithm_copyAscii_prog.drop 10 := by drop_prefix 4
        have h11 : f_Algorithm_copyAscii_prog.drop 11 =
            .nop :: .aload 0 :: .iload 1 :: .iload 3 :: .iadd ::
            .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .baload ::
            .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: .istore 5 ::
            .iload 3 :: .iconst 1 :: .iadd ::
            .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 6 ::
            .iload 5 :: .iconst 255 :: .iand :: .iconst 4294967168 :: .iconst 255 :: .iand ::
            .invokestatic "kotlin/jvm/internal/Intrinsics" "compare" "(II)I" ::
            f_Algorithm_copyAscii_prog.drop 32 := by drop_prefix 21
        rw [h6]
        split_res_fuel 25
        rw [runJvmResFast_iload]; norm_res_fuel; rw [hl3]
        rw [runJvmResFast_iload]; norm_res_fuel; rw [hl2]
        rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
        rw [runJvmResFast_iflt_branch (by
          rw [compareUnsigned_slt_zero]; exact decide_eq_true hkn)]
        norm_res_fuel
        rw [h11]
        rw [runJvmResFast_nop_local]; norm_res_fuel
        rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl0]
        rw [runJvmResFast_iload]; norm_res_fuel; rw [hl1]
        rw [runJvmResFast_iload]; norm_res_fuel; rw [hl3]
        rw [runJvmResFast_iadd_local]; norm_res_fuel
        rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
        rw [runJvmResFast_baload_byteArray (idx := s + k) hbytes hsk_slt hsk_sz]; norm_res_fuel
        rw [runJvmResFast_invokestatic_step stepStatic_ubyteCtor_local]; norm_res_fuel
        rw [runJvmResFast_istore]; norm_res_fuel
        rw [runJvmResFast_iload]; norm_res_fuel
        rw [setLocal_ne _ _ (by decide), hl3]
        rw [runJvmResFast_iconst_local]; norm_res_fuel
        rw [runJvmResFast_iadd_local]; norm_res_fuel
        rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
        rw [runJvmResFast_istore]; norm_res_fuel
        rw [runJvmResFast_iload]; norm_res_fuel
        rw [setLocal_ne _ _ (by decide), setLocal_self]
        rw [runJvmResFast_iconst_local]; norm_res_fuel
        rw [runJvmResFast_iand_local]; norm_res_fuel
        rw [runJvmResFast_iconst_local]; norm_res_fuel
        rw [runJvmResFast_iconst_local]; norm_res_fuel
        rw [runJvmResFast_iand_local]; norm_res_fuel
        rw [runJvmResFast_invokestatic_step stepStatic_intrinsicsCompare_local]; norm_res_fuel
        rw [byteArray_get_eq_getBang bytes hsk_sz]
        simp only [show (UInt32.ofBitVec ((bytes.get! (s + k).toNat).toBitVec.signExtend 32) &&& (255 : UInt32)) =
          b.toUInt32 from ubyte_sext_mask b]
        simp only [show ((4294967168 : UInt32) &&& (255 : UInt32)) = (128 : UInt32) from by decide]
        rfl
      have hslt_cmp : b.toUInt32.toBitVec.slt (128 : UInt32).toBitVec = decide (b < 128) := by
        have hbi : b.toUInt32.toBitVec.toInt = (b.toNat : Int) := by
          rw [BitVec.toInt]
          simp only [UInt32.toNat_toBitVec, UInt8.toNat_toUInt32]
          have hlt256 : b.toNat < 256 := UInt8.toNat_lt b
          split <;> omega
        have h128 : (128 : UInt32).toBitVec.toInt = 128 := by decide
        have hslt_def : b.toUInt32.toBitVec.slt (128 : UInt32).toBitVec =
            decide (b.toUInt32.toBitVec.toInt < (128 : UInt32).toBitVec.toInt) := rfl
        rw [hslt_def, hbi, h128]
        by_cases hb : b < 128
        · have hb' : (b.toNat : Int) < 128 := Int.ofNat_lt.mpr (UInt8.lt_iff_toNat_lt.mp hb)
          simp [hb, hb']
        · have hb' : ¬ ((b.toNat : Int) < 128) := by
            have : ¬ (b.toNat < 128) := fun h => hb (UInt8.lt_iff_toNat_lt.mpr h)
            omega
          simp [hb, hb']
      by_cases hb128 : b < 128
      · have hne128 : (b.toUInt32 == 128) = false := by
          have : b.toNat < 128 := UInt8.lt_iff_toNat_lt.mp hb128
          apply beq_false_of_ne
          intro heq
          have := congrArg UInt32.toNat heq
          simp only [UInt8.toNat_toUInt32] at this
          have h128n : (128 : UInt32).toNat = 128 := rfl
          omega
        have hcmp_slt : (if b.toUInt32 == 128 then (0 : UInt32)
            else if b.toUInt32.toBitVec.slt (128 : UInt32).toBitVec then 4294967295 else 1).toBitVec.slt 0#32 =
            true := by
          have hb_slt_true : b.toUInt32.toBitVec.slt (128 : UInt32).toBitVec = true := by
            rw [hslt_cmp]; exact decide_eq_true hb128
          rw [hne128, hb_slt_true]
          decide
        let g' := g.set k b hb128
        let asc' := asc.set gId g'
        have hasc' : asc'[gId]? = some g' := by
          have hg_lt : gId < asc.length := List.getElem?_eq_some_iff.mp hasc |>.1
          simp [asc', List.getElem?_set_self hg_lt]
        have h32_6 : ∃ locs2, runJvmResFast (f - 25) f_Algorithm_copyAscii_prog 32
            (f_Algorithm_copyAscii_prog.drop 32)
            ⟨32, [.i32 (if b.toUInt32 == 128 then 0
              else if b.toUInt32.toBitVec.slt (128 : UInt32).toBitVec then 4294967295 else 1)],
              locs1, jh, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast (f - 49) f_Algorithm_copyAscii_prog 6 (f_Algorithm_copyAscii_prog.drop 6)
              ⟨6, [], locs2, jh, ⟨ar, u64, asc'⟩⟩ ∧
            locs2 0 = .heapRef bytesAddr ∧ locs2 1 = .i32 s ∧ locs2 2 = .i32 n ∧
            locs2 3 = .i32 (k + 1) ∧ locs2 4 = .ext (.asciiRef gId) := by
          have h32 : f_Algorithm_copyAscii_prog.drop 32 =
              .iflt 52 :: f_Algorithm_copyAscii_prog.drop 33 := by drop_prefix 1
          have h52 : f_Algorithm_copyAscii_prog.drop 52 =
              .aload 4 :: .iload 3 :: .iload 5 ::
              .invokestatic "RleLeanKt" "f_Algorithm_AsciiBytes_set___redArg-snO9OKE" "([BIB)V" ::
              .aload 0 :: .astore 7 :: .iload 1 :: .istore 8 :: .iload 2 :: .istore 9 ::
              .aload 4 :: .astore 10 :: .aload 7 :: .astore 0 :: .iload 8 :: .istore 1 ::
              .iload 9 :: .istore 2 :: .iload 6 :: .istore 3 :: .aload 10 :: .astore 4 ::
              .goto 6 :: f_Algorithm_copyAscii_prog.drop 75 := by drop_prefix 23
          let locs2 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
            locs1 7 (.heapRef bytesAddr)) 8 (.i32 s)) 9 (.i32 n)) 10 (.ext (.asciiRef gId)))
            0 (.heapRef bytesAddr)) 1 (.i32 s)) 2 (.i32 n)) 3 (.i32 (k + 1))) 4 (.ext (.asciiRef gId))
          refine ⟨locs2, ?_,
            by dsimp only [locs2, setLocal]; simp,
            by dsimp only [locs2, setLocal]; simp,
            by dsimp only [locs2, setLocal]; simp,
            by dsimp only [locs2, setLocal]; simp,
            by dsimp only [locs2, setLocal]; simp⟩
          · rw [h32]
            obtain ⟨f', hf'⟩ : ∃ f', f - 25 = f' + 24 := ⟨f - 49, by omega⟩
            rw [hf', show (f' + 24 : Nat) = (f' + 23) + 1 from rfl]
            rw [runJvmResFast_iflt_branch hcmp_slt]; norm_res_fuel
            rw [h52]
            rw [runJvmResFast_aload_local]; norm_res_fuel
            simp [setLocal, hl4]
            rw [runJvmResFast_iload]; norm_res_fuel
            simp [setLocal, hl3]
            rw [runJvmResFast_iload]; norm_res_fuel
            simp [setLocal]
            have hbu8 : (UInt32.ofBitVec (b.toBitVec.signExtend 32)).toUInt8 < 128 := by
              rw [u8Sext_eq_u8_toUInt8]; exact hb128
            have hb_eq : bytes.get! ((s.toNat + k.toNat) % 4294967296) = b := by
              rw [← UInt32.toNat_add]
            rw [hb_eq]
            rw [runJvmResFast_invokestatic_step (stepStatic_asciiSet_rle hasc hbu8)]; norm_res_fuel
            simp only [u8Sext_eq_u8_toUInt8]
            rw [runJvmResFast_aload_local]; norm_res_fuel
            simp [setLocal, hl0]
            rw [runJvmResFast_astore_local]; norm_res_fuel
            rw [runJvmResFast_iload]; norm_res_fuel
            simp [setLocal, hl1]
            rw [runJvmResFast_istore]; norm_res_fuel
            rw [runJvmResFast_iload]; norm_res_fuel
            simp [setLocal, hl2]
            rw [runJvmResFast_istore]; norm_res_fuel
            rw [runJvmResFast_aload_local]; norm_res_fuel
            simp [setLocal, hl4]
            rw [runJvmResFast_astore_local]; norm_res_fuel
            rw [runJvmResFast_aload_local]; norm_res_fuel
            simp [setLocal]
            rw [runJvmResFast_astore_local]; norm_res_fuel
            rw [runJvmResFast_iload]; norm_res_fuel
            simp [setLocal]
            rw [runJvmResFast_istore]; norm_res_fuel
            rw [runJvmResFast_iload]; norm_res_fuel
            simp [setLocal]
            rw [runJvmResFast_istore]; norm_res_fuel
            rw [runJvmResFast_iload]; norm_res_fuel
            simp [setLocal]
            rw [runJvmResFast_istore]; norm_res_fuel
            rw [runJvmResFast_aload_local]; norm_res_fuel
            simp [setLocal]
            rw [runJvmResFast_astore_local]; norm_res_fuel
            rw [runJvmResFast_goto]
            rw [show f' = f - 49 from by omega]
            rfl
        rcases h32_6 with ⟨locs2, h32_step, h2_0, h2_1, h2_2, h2_3, h2_4⟩
        rcases ih (f - 49) bytes bytesAddr s n (k + 1) gId g' locs2 jh ar u64 asc'
          hsub (by omega) hsz hbound hbytes hasc' h2_0 h2_1 h2_2 h2_3 h2_4 with ⟨st', hrun, hjh, hhp⟩
        refine ⟨st', ?_, hjh, ?_⟩
        · rw [h6_32, h32_step]; exact hrun
        · rw [hhp]
          have hca : Algorithm.copyAscii bytes s n k g = Algorithm.copyAscii bytes s n (k + 1) g' := by
            conv => lhs; unfold Algorithm.copyAscii
            have hb' : bytes.get! (s + k).toNat < 128 := hb128
            simp only [hkn, ↓reduceDIte, hb', g', b]
          rw [hca]
          simp [asc', List.set_set]
      · have hcmp_slt : (if b.toUInt32 == 128 then (0 : UInt32)
            else if b.toUInt32.toBitVec.slt (128 : UInt32).toBitVec then 4294967295 else 1).toBitVec.slt 0#32 =
            false := by
          by_cases h128 : b.toUInt32 == 128
          · simp [h128]
          · simp only [h128, Bool.false_eq_true, ↓reduceIte, hslt_cmp, decide_eq_false hb128]
            decide
        let locs2 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          locs1 7 (.heapRef bytesAddr)) 8 (.i32 s)) 9 (.i32 n)) 10 (.ext (.asciiRef gId)))
          0 (.heapRef bytesAddr)) 1 (.i32 s)) 2 (.i32 n)) 3 (.i32 (k + 1))) 4 (.ext (.asciiRef gId))
        have h32_6 : runJvmResFast (f - 25) f_Algorithm_copyAscii_prog 32
            (f_Algorithm_copyAscii_prog.drop 32)
            ⟨32, [.i32 (if b.toUInt32 == 128 then 0
              else if b.toUInt32.toBitVec.slt (128 : UInt32).toBitVec then 4294967295 else 1)],
              locs1, jh, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast (f - 45) f_Algorithm_copyAscii_prog 6 (f_Algorithm_copyAscii_prog.drop 6)
              ⟨6, [], locs2, jh, ⟨ar, u64, asc⟩⟩ := by
          have h32 : f_Algorithm_copyAscii_prog.drop 32 =
              .iflt 52 :: .aload 0 :: .astore 7 :: .iload 1 :: .istore 8 :: .iload 2 :: .istore 9 ::
              .aload 4 :: .astore 10 :: .aload 7 :: .astore 0 :: .iload 8 :: .istore 1 ::
              .iload 9 :: .istore 2 :: .iload 6 :: .istore 3 :: .aload 10 :: .astore 4 ::
              .goto 6 :: f_Algorithm_copyAscii_prog.drop 52 := by drop_prefix 20
          rw [h32]
          split_res_fuel 20
          rw [runJvmResFast_iflt_fallthrough hcmp_slt]; norm_res_fuel
          rw [runJvmResFast_aload_local]; norm_res_fuel
          simp [setLocal, hl0]
          rw [runJvmResFast_astore_local]; norm_res_fuel
          rw [runJvmResFast_iload]; norm_res_fuel
          simp [setLocal, hl1]
          rw [runJvmResFast_istore]; norm_res_fuel
          rw [runJvmResFast_iload]; norm_res_fuel
          simp [setLocal, hl2]
          rw [runJvmResFast_istore]; norm_res_fuel
          rw [runJvmResFast_aload_local]; norm_res_fuel
          simp [setLocal, hl4]
          rw [runJvmResFast_astore_local]; norm_res_fuel
          rw [runJvmResFast_aload_local]; norm_res_fuel
          simp [setLocal]
          rw [runJvmResFast_astore_local]; norm_res_fuel
          rw [runJvmResFast_iload]; norm_res_fuel
          simp [setLocal]
          rw [runJvmResFast_istore]; norm_res_fuel
          rw [runJvmResFast_iload]; norm_res_fuel
          simp [setLocal]
          rw [runJvmResFast_istore]; norm_res_fuel
          rw [runJvmResFast_iload]; norm_res_fuel
          simp [setLocal]
          rw [runJvmResFast_istore]; norm_res_fuel
          rw [runJvmResFast_aload_local]; norm_res_fuel
          simp [setLocal]
          rw [runJvmResFast_astore_local]; norm_res_fuel
          rw [runJvmResFast_goto]
          rfl
        rcases ih (f - 45) bytes bytesAddr s n (k + 1) gId g locs2 jh ar u64 asc
          hsub (by omega) hsz hbound hbytes hasc
          (by dsimp only [locs2, setLocal]; simp)
          (by dsimp only [locs2, setLocal]; simp)
          (by dsimp only [locs2, setLocal]; simp)
          (by dsimp only [locs2, setLocal]; simp)
          (by dsimp only [locs2, setLocal]; simp)
          with ⟨st', hrun, hjh, hhp⟩
        refine ⟨st', ?_, hjh, ?_⟩
        · rw [h6_32, h32_6]; exact hrun
        · rw [hhp]
          have hca : Algorithm.copyAscii bytes s n k g = Algorithm.copyAscii bytes s n (k + 1) g := by
            conv => lhs; unfold Algorithm.copyAscii
            have hb' : ¬(bytes.get! (s + k).toNat < 128) := hb128
            simp only [hkn, ↓reduceDIte, hb']
          rw [hca]
    · have hle0 : n.toNat - k.toNat = 0 := by
        have hk' : n.toNat ≤ k.toNat := Nat.le_of_not_lt (fun hlt => hkn (UInt32.lt_iff_toNat_lt.mpr hlt))
        omega
      have h6 : f_Algorithm_copyAscii_prog.drop 6 =
          .iload 3 :: .iload 2 ::
          .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" ::
          .iflt 11 :: .vreturn :: f_Algorithm_copyAscii_prog.drop 11 := by drop_prefix 5
      apply Exists.intro; refine ⟨?_, ?_, ?_⟩
      · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 5 := ⟨f - 5, by omega⟩
        rw [h6]
        rw [runJvmResFast_iload]; norm_res_fuel; rw [hl3]
        rw [runJvmResFast_iload]; norm_res_fuel; rw [hl2]
        rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
        rw [runJvmResFast_iflt_fallthrough (by
          rw [compareUnsigned_slt_zero]; exact decide_eq_false hkn)]
        norm_res_fuel
        rw [runJvmResFast_vreturn_local]
      · rfl
      · have hca : Algorithm.copyAscii bytes s n k g = g := by
          unfold Algorithm.copyAscii
          simp only [hkn, ↓reduceDIte]
        rw [hca, list_set_eq_self asc hasc]

theorem copyAscii_equiv (bytes : ByteArray) (bytesAddr : Nat) (s n k : UInt32)
    (gId : Nat) (g : Algorithm.AsciiBytes) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hsz : bytes.data.size < 2 ^ 31)
    (hbound : s.toNat + n.toNat ≤ bytes.data.size)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hasc : asc[gId]? = some g) :
    ∃ f st', runJvmRes f f_Algorithm_copyAscii_prog
        ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (fun (_ : Nat) => (.null : JvmVal))
          0 (.heapRef bytesAddr)) 1 (.i32 s)) 2 (.i32 n)) 3 (.i32 k)) 4 (.ext (.asciiRef gId)),
          jh, ⟨ar, u64, asc⟩⟩ = some (.unit, st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = ⟨ar, u64, asc.set gId (Algorithm.copyAscii bytes s n k g)⟩ := by
  let f := (n.toNat - k.toNat) * 50 + 16
  rcases copyAscii_loop (n.toNat - k.toNat) (f - 6) bytes bytesAddr s n k gId g
    (setLocal (setLocal (setLocal (setLocal (setLocal (fun (_ : Nat) => (.null : JvmVal))
      0 (.heapRef bytesAddr)) 1 (.i32 s)) 2 (.i32 n)) 3 (.i32 k)) 4 (.ext (.asciiRef gId)))
    jh ar u64 asc (Nat.le_refl _) (by omega) hsz hbound hbytes hasc
    (by simp [setLocal]) (by simp [setLocal]) (by simp [setLocal])
    (by simp [setLocal]) (by simp [setLocal]) with ⟨st', hrun, hjh, hhp⟩
  refine ⟨f, st', ?_, hjh, hhp⟩
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  have h0 : f_Algorithm_copyAscii_prog =
      .aload 0 :: .ldcStr "bytes" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 4 :: .ldcStr "g" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      f_Algorithm_copyAscii_prog.drop 6 := by
    conv => lhs; rw [← List.drop_zero (l := f_Algorithm_copyAscii_prog)]
    drop_prefix 6
  rw [h0]
  split_res_fuel 6
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp only [setLocal]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam_local rfl)]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp only [setLocal]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam_local rfl)]; norm_res_fuel
  exact hrun

end CopyAscii

/-! #### 2. `f_Algorithm_parseRLEComments_prog` -/

section ParseRLEComments
set_option maxRecDepth 2048

private def rleWarns? : JvmVal → Option (Algorithm.GrowBuf Algorithm.RLEWarning)
  | .ext (.rleWarnGrowBuf b) => some b
  | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
  | _ => none

private def rleRuns? : JvmVal → Option (Algorithm.GrowBuf (UInt32 × UInt32))
  | .ext (.u32PairGrowBuf b) => some b
  | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
  | _ => none

private theorem rleWarns?_of_rep {w : Algorithm.GrowBuf Algorithm.RLEWarning} {v : JvmVal}
    (h : RleWarnRep w v) : rleWarns? v = some w := by
  cases h with
  | empty he hz => rw [growBuf_eq_empty_of' he hz]; rfl
  | full => rfl

private theorem rleRuns?_of_rep {r : Algorithm.GrowBuf (UInt32 × UInt32)} {v : JvmVal}
    (h : RlePairRep r v) : rleRuns? v = some r := by
  cases h with
  | empty he hz => rw [growBuf_eq_empty_of' he hz]; rfl
  | full => rfl

private abbrev parseRLEDataDesc :=
  "([Ljava/lang/Object;IIZ[BIIIJZIILjava/lang/Object;Ljava/lang/Object;II)Lcom/alexvanyo/composelife/model/RLEResult;"

private abbrev RleDataFn :=
  Array String → UInt32 → UInt32 → Bool → ByteArray → UInt32 → UInt32 → UInt32 →
    UInt64 → Bool → UInt32 → UInt32 → Algorithm.GrowBuf Algorithm.RLEWarning →
    Algorithm.GrowBuf (UInt32 × UInt32) → Int32 → Int32 → Algorithm.RLEResult

private abbrev RleEncFn :=
  Jvm.JvmHeap AlgExt → List (Array UInt64) → Algorithm.RLEResult →
    JvmVal × Jvm.JvmHeap AlgExt × List (Array UInt64)

private def rleDataDispatch (pc : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (hp : AlgHeap) (startY startX : UInt32) (runsVal warnsVal : JvmVal)
    (countCol countP hasCount : UInt32) (count : UInt64)
    (col p limit : UInt32) (bytesVal : JvmVal) (inLine i numLines : UInt32) (linesVal : JvmVal)
    (rest : List JvmVal) (pdFn : RleDataFn) (encFn : RleEncFn) : Option JvmState ⊕ Option JvmVal :=
  let st : JvmState := ⟨pc, .i32 startY :: .i32 startX :: runsVal :: warnsVal ::
    .i32 countCol :: .i32 countP :: .i32 hasCount :: .i64 count :: .i32 col :: .i32 p ::
    .i32 limit :: bytesVal :: .i32 inLine :: .i32 i :: .i32 numLines ::
    linesVal :: rest, locs, jh, hp⟩
  match decodeStrArray st linesVal, decodeBytes st bytesVal, rleWarns? warnsVal, rleRuns? runsVal with
  | some lines, some bytes, some warns, some runs =>
    let res := pdFn lines numLines i (inLine != 0)
      bytes limit p col count (hasCount != 0) countP
      countCol warns runs startX.toInt32 startY.toInt32
    let (resVal, h', u64s') := encFn st.jvmHeap st.heap.u64Arrays res
    .inl (some { st with
      pc := st.pc + 1, stack := resVal :: rest,
      jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
  | _, _, _, _ => .inr none

private theorem stepStatic_rleData_match_only (pc : Nat) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (startY startX : UInt32) (runsVal warnsVal : JvmVal)
    (countCol countP hasCount : UInt32) (count : UInt64)
    (col p limit : UInt32) (bytesVal : JvmVal) (inLine i numLines : UInt32) (linesVal : JvmVal)
    (rest : List JvmVal) :
    let st : JvmState := ⟨pc, .i32 startY :: .i32 startX :: runsVal :: warnsVal ::
      .i32 countCol :: .i32 countP :: .i32 hasCount :: .i64 count :: .i32 col :: .i32 p ::
      .i32 limit :: bytesVal :: .i32 inLine :: .i32 i :: .i32 numLines ::
      linesVal :: rest, locs, jh, hp⟩
    stepInvokeStatic st "RleLeanKt" "f_Algorithm_parseRLEData-RjVw3pI" parseRLEDataDesc =
      rleDataDispatch pc locs jh hp startY startX runsVal warnsVal countCol countP hasCount count
        col p limit bytesVal inLine i numLines linesVal rest
        Algorithm.parseRLEData encodeRLEResult := rfl

private theorem rleData_match_elim (pc : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (hp : AlgHeap) (startY startX : UInt32) (runsVal warnsVal : JvmVal)
    (countCol countP hasCount : UInt32) (count : UInt64)
    (col p limit : UInt32) (bytesVal : JvmVal) (inLine i numLines : UInt32) (linesVal : JvmVal)
    (rest : List JvmVal)
    (pdFn : RleDataFn) (encFn : RleEncFn)
    {lines : Array String} {bytes : ByteArray}
    {warns : Algorithm.GrowBuf Algorithm.RLEWarning}
    {runs : Algorithm.GrowBuf (UInt32 × UInt32)}
    (hl : decodeStrArray ⟨pc, .i32 startY :: .i32 startX :: runsVal :: warnsVal ::
        .i32 countCol :: .i32 countP :: .i32 hasCount :: .i64 count :: .i32 col :: .i32 p ::
        .i32 limit :: bytesVal :: .i32 inLine :: .i32 i :: .i32 numLines ::
        linesVal :: rest, locs, jh, hp⟩ linesVal = some lines)
    (hb : decodeBytes ⟨pc, .i32 startY :: .i32 startX :: runsVal :: warnsVal ::
        .i32 countCol :: .i32 countP :: .i32 hasCount :: .i64 count :: .i32 col :: .i32 p ::
        .i32 limit :: bytesVal :: .i32 inLine :: .i32 i :: .i32 numLines ::
        linesVal :: rest, locs, jh, hp⟩ bytesVal = some bytes)
    (hw : rleWarns? warnsVal = some warns)
    (hr : rleRuns? runsVal = some runs) :
    rleDataDispatch pc locs jh hp startY startX runsVal warnsVal countCol countP hasCount count
        col p limit bytesVal inLine i numLines linesVal rest pdFn encFn =
      (.inl (some ⟨pc + 1,
        (encFn jh hp.u64Arrays (pdFn lines numLines i (inLine != 0)
          bytes limit p col count (hasCount != 0) countP
          countCol warns runs startX.toInt32 startY.toInt32)).1 :: rest,
        locs,
        (encFn jh hp.u64Arrays (pdFn lines numLines i (inLine != 0)
          bytes limit p col count (hasCount != 0) countP
          countCol warns runs startX.toInt32 startY.toInt32)).2.1,
        { arenas := hp.arenas,
          u64Arrays := (encFn jh hp.u64Arrays (pdFn lines numLines i
            (inLine != 0) bytes limit p col count
            (hasCount != 0) countP countCol warns runs
            startX.toInt32 startY.toInt32)).2.2,
          asciiArrays := hp.asciiArrays }⟩) : Option JvmState ⊕ Option JvmVal) := by
  dsimp only [rleDataDispatch]
  rw [hl, hb, hw, hr]

private theorem stepStatic_parseRLEData_rle
    {pc : Nat} {startY startX : UInt32} {runsVal warnsVal : JvmVal}
    {countCol countP hasCount : UInt32} {count : UInt64}
    {col p limit : UInt32} {bytesVal : JvmVal} {inLine i numLines : UInt32} {linesVal : JvmVal}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {lines : Array String} {bytes : ByteArray}
    {warns : Algorithm.GrowBuf Algorithm.RLEWarning}
    {runs : Algorithm.GrowBuf (UInt32 × UInt32)}
    (hl : decodeStrArray ⟨pc, .i32 startY :: .i32 startX :: runsVal :: warnsVal ::
        .i32 countCol :: .i32 countP :: .i32 hasCount :: .i64 count :: .i32 col :: .i32 p ::
        .i32 limit :: bytesVal :: .i32 inLine :: .i32 i :: .i32 numLines ::
        linesVal :: rest, locs, jh, hp⟩ linesVal = some lines)
    (hb : decodeBytes ⟨pc, .i32 startY :: .i32 startX :: runsVal :: warnsVal ::
        .i32 countCol :: .i32 countP :: .i32 hasCount :: .i64 count :: .i32 col :: .i32 p ::
        .i32 limit :: bytesVal :: .i32 inLine :: .i32 i :: .i32 numLines ::
        linesVal :: rest, locs, jh, hp⟩ bytesVal = some bytes)
    (hw : RleWarnRep warns warnsVal)
    (hr : RlePairRep runs runsVal) :
    stepInvokeStatic ⟨pc, .i32 startY :: .i32 startX :: runsVal :: warnsVal ::
        .i32 countCol :: .i32 countP :: .i32 hasCount :: .i64 count :: .i32 col :: .i32 p ::
        .i32 limit :: bytesVal :: .i32 inLine :: .i32 i :: .i32 numLines ::
        linesVal :: rest, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_parseRLEData-RjVw3pI" parseRLEDataDesc =
      let res := Algorithm.parseRLEData lines numLines i (inLine != 0)
        bytes limit p col count (hasCount != 0) countP
        countCol warns runs startX.toInt32 startY.toInt32
      let enc := encodeRLEResult jh hp.u64Arrays res
      .inl (some ⟨pc + 1, enc.1 :: rest, locs, enc.2.1,
        ⟨hp.arenas, enc.2.2, hp.asciiArrays⟩⟩) := by
  rw [stepStatic_rleData_match_only]
  exact rleData_match_elim pc locs jh hp startY startX runsVal warnsVal countCol countP hasCount
    count col p limit bytesVal inLine i numLines linesVal rest
    Algorithm.parseRLEData encodeRLEResult hl hb (rleWarns?_of_rep hw) (rleRuns?_of_rep hr)

private theorem stepStatic_parseRLEData_header
    {pc : Nat} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)}
    {asc : List Algorithm.AsciiBytes}
    {lines : Array String} {numLines i : UInt32} {bytes : ByteArray} {bytesAddr : Nat}
    {warns : Algorithm.GrowBuf Algorithm.RLEWarning} {warnsVal : JvmVal}
    {offsetX offsetY : Int32}
    (hget : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hrep : RleWarnRep warns warnsVal) :
    let res := Algorithm.parseRLEData lines numLines i false bytes 0 0 0 0 false 0 0
      warns Algorithm.GrowBuf.empty offsetX offsetY
    let enc := encodeRLEResult jh u64 res
    stepInvokeStatic ⟨pc, .i32 offsetY.toUInt32 :: .i32 offsetX.toUInt32 ::
        .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: warnsVal :: .i32 0 :: .i32 0 ::
        .i32 0 :: .i64 0 :: .i32 0 :: .i32 0 :: .i32 0 :: .heapRef bytesAddr :: .i32 0 ::
        .i32 i :: .i32 numLines :: .strArr lines :: [], locs, jh, ⟨ar, u64, asc⟩⟩
      "RleLeanKt" "f_Algorithm_parseRLEData-RjVw3pI" parseRLEDataDesc =
      .inl (some ⟨pc + 1, enc.1 :: [], locs, enc.2.1, ⟨ar, enc.2.2, asc⟩⟩) := by
  have hb : decodeBytes ⟨pc, .i32 offsetY.toUInt32 :: .i32 offsetX.toUInt32 ::
      .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: warnsVal :: .i32 0 :: .i32 0 ::
      .i32 0 :: .i64 0 :: .i32 0 :: .i32 0 :: .i32 0 :: .heapRef bytesAddr :: .i32 0 ::
      .i32 i :: .i32 numLines :: .strArr lines :: [], locs, jh, ⟨ar, u64, asc⟩⟩
      (.heapRef bytesAddr) = some bytes := by
    simp only [decodeBytes, hget]
  have h := stepStatic_parseRLEData_rle (pc := pc)
    (startY := offsetY.toUInt32) (startX := offsetX.toUInt32)
    (runsVal := .ext (.strGrowBuf Algorithm.GrowBuf.empty)) (warnsVal := warnsVal)
    (countCol := 0) (countP := 0) (hasCount := 0) (count := 0)
    (col := 0) (p := 0) (limit := 0) (bytesVal := .heapRef bytesAddr)
    (inLine := 0) (i := i) (numLines := numLines) (linesVal := .strArr lines)
    (rest := []) (locs := locs) (jh := jh) (hp := ⟨ar, u64, asc⟩)
    rfl hb hrep rlePairRep_empty
  rw [Int32.toInt32_toUInt32, Int32.toInt32_toUInt32, bne_self_eq_false] at h
  exact h

private theorem u8Sext_eq_u32 {b : UInt8} {c : UInt32} (h : b.toNat = c.toNat) (hc : c.toNat < 128) :
    UInt32.ofBitVec (b.toBitVec.signExtend 32) = c := by
  have hbt : b.toBitVec.toNat = b.toNat := rfl
  have hmsb : b.toBitVec.msb = false := by
    rw [BitVec.msb_eq_decide]; exact decide_eq_false (by omega)
  have hsw : b.toBitVec.signExtend 32 = b.toBitVec.setWidth 32 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_signExtend, hi, decide_true, Bool.true_and, BitVec.getLsbD_setWidth]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [h8, hmsb, BitVec.getLsbD_of_ge b.toBitVec i (Nat.le_of_not_lt h8)]
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  simp [hsw]
  exact hbt.trans h

private theorem u8Sext_beq_false (b : UInt8) (c : UInt32) (hne : b.toNat ≠ c.toNat) (hc : c.toNat < 128) :
    (UInt32.ofBitVec (b.toBitVec.signExtend 32) == c) = false := by
  cases he : UInt32.ofBitVec (b.toBitVec.signExtend 32) == c
  · rfl
  · have hb_eq : UInt32.ofBitVec (b.toBitVec.signExtend 32) = c := LawfulBEq.eq_of_beq he
    cases hm : b.toBitVec.msb
    · have hsw : b.toBitVec.signExtend 32 = b.toBitVec.setWidth 32 := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [BitVec.getLsbD_signExtend, hi, decide_true, Bool.true_and, BitVec.getLsbD_setWidth]
        by_cases h8 : i < 8
        · simp [h8]
        · simp [h8, hm, BitVec.getLsbD_of_ge b.toBitVec i (Nat.le_of_not_lt h8)]
      have h2 := congrArg UInt32.toNat hb_eq
      have hblt : b.toBitVec.toNat < 2 ^ 32 := Nat.lt_trans b.toBitVec.isLt (by decide)
      simp only [hsw, UInt32.toNat_ofBitVec, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hblt] at h2
      exact absurd h2 hne
    · have hu31 : (UInt32.ofBitVec (b.toBitVec.signExtend 32)).toBitVec.getLsbD 31 = true := by
        simp [BitVec.getLsbD_signExtend, hm]
      have hc31 : c.toBitVec.getLsbD 31 = false := by
        rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
        have hct : c.toBitVec.toNat < 2 ^ 31 := by simpa using Nat.lt_trans hc (by decide)
        exact Nat.testBit_lt_two_pow hct
      have hcontra := congrArg (fun x : UInt32 => x.toBitVec.getLsbD 31) hb_eq
      rw [hu31, hc31] at hcontra
      contradiction

private theorem decodeRLEWarning_mono {h1 h2 : Jvm.JvmHeap AlgExt} (hext : HeapExtends h1 h2)
    (v : JvmVal) (w : Algorithm.RLEWarning) (hd : decodeRLEWarning h1 v = some w) :
    decodeRLEWarning h2 v = some w := by
  cases v with
  | allocRef cls =>
    by_cases hc : cls = "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"
    · subst hc; simpa [decodeRLEWarning] using hd
    · simp [decodeRLEWarning, hc] at hd
  | heapRef addr =>
    simp only [decodeRLEWarning] at hd ⊢
    cases hget : h1.get? addr with
    | none => simp [hget] at hd
    | some obj =>
      rw [hget] at hd
      rw [hext addr obj hget]
      exact hd
  | _ => simp [decodeRLEWarning] at hd

private theorem mapM_decodeRLEWarning_mono {h1 h2 : Jvm.JvmHeap AlgExt} (hext : HeapExtends h1 h2)
    {vs : List JvmVal} {ws : List Algorithm.RLEWarning}
    (hm : vs.mapM (decodeRLEWarning h1) = some ws) :
    vs.mapM (decodeRLEWarning h2) = some ws := by
  induction vs generalizing ws with
  | nil => simpa using hm
  | cons v vs ih =>
    simp only [List.mapM_cons] at hm ⊢
    cases hdv : decodeRLEWarning h1 v with
    | none => simp [hdv] at hm
    | some w =>
      rw [decodeRLEWarning_mono hext v w hdv]
      rw [hdv] at hm
      cases hrest : vs.mapM (decodeRLEWarning h1) with
      | none => simp [hrest] at hm
      | some ws' =>
        rw [hrest] at hm
        rw [ih hrest]
        exact hm

private theorem encodeGrowBufArray_rleWarn_ext (jh : Jvm.JvmHeap AlgExt)
    (b : Algorithm.GrowBuf Algorithm.RLEWarning) :
    HeapExtends jh (encodeGrowBufArray jh encodeRLEWarning b).2 ∧
    (encodeGrowBufArray jh encodeRLEWarning b).2.statics = jh.statics := by
  dsimp only [encodeGrowBufArray]
  have hfold : ∀ (l : List Algorithm.RLEWarning) (p : Array JvmVal × Jvm.JvmHeap AlgExt),
      HeapExtends p.2 (l.foldl (fun acc w =>
        (acc.1.push (encodeRLEWarning acc.2 w).1, (encodeRLEWarning acc.2 w).2)) p).2 ∧
      (l.foldl (fun acc w =>
        (acc.1.push (encodeRLEWarning acc.2 w).1, (encodeRLEWarning acc.2 w).2)) p).2.statics = p.2.statics := by
    intro l
    induction l with
    | nil => intro p; exact ⟨heapExtends_refl p.2, rfl⟩
    | cons w ws ih =>
      intro p
      simp only [List.foldl_cons]
      have hw : HeapExtends p.2 (encodeRLEWarning p.2 w).2 ∧
          (encodeRLEWarning p.2 w).2.statics = p.2.statics := by
        cases w with
        | emptyFile => exact ⟨heapExtends_refl p.2, rfl⟩
        | _ => exact ⟨heapExtends_alloc _ _, rfl⟩
      rcases ih (p.1.push (encodeRLEWarning p.2 w).1, (encodeRLEWarning p.2 w).2) with ⟨hext, hst⟩
      exact ⟨heapExtends_trans hw.1 hext, hst.trans hw.2⟩
  have h1 := hfold b.toArray.toList (#[], jh)
  rw [Array.foldl_toList] at h1
  exact ⟨heapExtends_trans h1.1 (heapExtends_alloc _ _), h1.2⟩

private theorem encodeRLEResult_statics
    (jh : Jvm.JvmHeap AlgExt) (u64 : List (Array UInt64)) (res : Algorithm.RLEResult) :
    (encodeRLEResult jh u64 res).2.1.statics = jh.statics := by
  rcases res with ⟨status, warns, cells⟩
  dsimp only [encodeRLEResult]
  have hfold : ∀ (l : List Algorithm.RLEWarning) (p : Array JvmVal × Jvm.JvmHeap AlgExt),
      (l.foldl (fun acc w =>
        (acc.1.push (encodeRLEWarning acc.2 w).1, (encodeRLEWarning acc.2 w).2)) p).2.statics = p.2.statics := by
    intro l
    induction l with
    | nil => intro p; rfl
    | cons w ws ih =>
      intro p
      simp only [List.foldl_cons]
      have hw : (encodeRLEWarning p.2 w).2.statics = p.2.statics := by
        cases w <;> rfl
      exact (ih _).trans hw
  have h1 := hfold warns.toList (#[], jh)
  rw [Array.foldl_toList] at h1
  exact h1

private theorem stepStatic_growBufToArray_rleWarn_ext
    {pc : Nat} {bufVal : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {b : Algorithm.GrowBuf Algorithm.RLEWarning}
    (hrep : RleWarnRep b bufVal) :
    ∃ (arrVal : JvmVal) (jh' : Jvm.JvmHeap AlgExt) (warnVals? : Option Nat),
      stepInvokeStatic ⟨pc, bufVal :: rest, locs, jh, hp⟩
        "RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
        "(Ljava/lang/Object;)[Ljava/lang/Object;" =
        .inl (some ⟨pc + 1, arrVal :: rest, locs, jh', hp⟩) ∧
      HeapExtends jh jh' ∧
      jh'.statics = jh.statics ∧
      match warnVals? with
      | none => arrVal = .strArr #[] ∧ b.toArray = #[]
      | some addr =>
        arrVal = .heapRef addr ∧
        ∃ warnVals, jh'.get? addr = some (.objArray "java/lang/Object" warnVals) ∧
          warnVals.toList.mapM (decodeRLEWarning jh') = some b.toArray.toList := by
  rcases stepStatic_growBufToArray_rleWarn hrep (pc := pc) (rest := rest) (locs := locs)
    (jh := jh) (hp := hp) with ⟨arrVal, jh', warnVals?, hstep, hspec⟩
  refine ⟨arrVal, jh', warnVals?, hstep, ?_, ?_, ?_⟩
  · cases hrep with
    | empty he hz =>
      have hb := growBuf_eq_empty_of' he hz; subst hb
      cases warnVals? with
      | none => rcases hspec with ⟨_, rfl, _⟩; exact heapExtends_refl _
      | some a =>
        simp only [stepInvokeStatic] at hstep
        rcases hstep with ⟨_, rfl⟩; exact heapExtends_refl _
    | full =>
      simp only [stepInvokeStatic] at hstep
      rcases hstep with ⟨_, rfl⟩
      exact (encodeGrowBufArray_rleWarn_ext jh _).1
  · cases hrep with
    | empty he hz =>
      have hb := growBuf_eq_empty_of' he hz; subst hb
      cases warnVals? with
      | none => rcases hspec with ⟨_, rfl, _⟩; rfl
      | some a =>
        simp only [stepInvokeStatic] at hstep
        rcases hstep with ⟨_, rfl⟩; rfl
    | full =>
      simp only [stepInvokeStatic] at hstep
      rcases hstep with ⟨_, rfl⟩
      exact (encodeGrowBufArray_rleWarn_ext jh _).2
  · cases warnVals? with
    | none => rcases hspec with ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    | some a => exact hspec

private theorem rleResult_decode_of_parts
    {pc : Nat} {locs : Nat → JvmVal} {jh1 : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)}
    {asc : List Algorithm.AsciiBytes}
    (status : Algorithm.RLEStatus) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (arrVal : JvmVal) (warnVals? : Option Nat)
    (hspec : match warnVals? with
      | none => arrVal = .strArr #[] ∧ warns.toArray = #[]
      | some addr =>
        arrVal = .heapRef addr ∧
        ∃ warnVals, jh1.get? addr = some (.objArray "java/lang/Object" warnVals) ∧
          warnVals.toList.mapM (decodeRLEWarning jh1) = some warns.toArray.toList) :
    let resObj := Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus status)), ("warnings", arrVal), ("cells", .ext (.u64Ref u64.length))]
    let jh2 := (jh1.alloc resObj).2
    let resAddr := jh1.objects.size
    let hp1 : AlgHeap := ⟨ar, u64 ++ [Algorithm.noCells], asc⟩
    decodeRLEResult ⟨pc, [.heapRef resAddr], locs, jh2, hp1⟩ (.heapRef resAddr) =
      some ⟨status, warns.toArray, Algorithm.noCells⟩ := by
  intro resObj jh2 resAddr hp1
  have hget_res : jh2.get? resAddr = some resObj := by
    simp [jh2, resAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  have hext12 : HeapExtends jh1 jh2 := heapExtends_alloc jh1 resObj
  have hcid : hp1.u64Arrays[u64.length]? = some Algorithm.noCells := by
    simp [hp1]
  cases warnVals? with
  | none =>
    rcases hspec with ⟨rfl, hweq⟩
    have hws : ("warnings" == "status") = false := by decide
    have hcs : ("cells" == "status") = false := by decide
    have hcw : ("cells" == "warnings") = false := by decide
    dsimp only [decodeRLEResult]
    rw [hget_res]
    dsimp only [resObj]
    simp only [List.lookup, beq_self_eq_true, hws, hcs, hcw]
    simp only [hcid, Option.map, Array.isEmpty, Array.size_empty]
    rw [← hweq]
    rfl
  | some wAddr =>
    rcases hspec with ⟨rfl, warnVals, hget_w, hmap⟩
    have hws : ("warnings" == "status") = false := by decide
    have hcs : ("cells" == "status") = false := by decide
    have hcw : ("cells" == "warnings") = false := by decide
    dsimp only [decodeRLEResult]
    rw [hget_res]
    dsimp only [resObj]
    simp only [List.lookup, beq_self_eq_true, hws, hcs, hcw]
    rw [hext12 wAddr _ hget_w, hcid]
    dsimp only
    rw [mapM_decodeRLEWarning_mono hext12 hmap]
    rfl

private theorem parseRLEComments_ret_result
    (f pc : Nat) (status : Algorithm.RLEStatus)
    (warns : Algorithm.GrowBuf Algorithm.RLEWarning) (warnsVal : JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hrep : RleWarnRep warns warnsVal)
    (hf : f ≥ 15)
    (hd : f_Algorithm_parseRLEComments_prog.drop pc =
      .astore 10 :: .aload 6 ::
      .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
        "(Ljava/lang/Object;)[Ljava/lang/Object;" ::
      .astore 11 :: .invokestatic "RleLeanKt" "f_Algorithm_noCells" "()[J" :: .astore 12 ::
      .newClass "com/alexvanyo/composelife/model/RLEResult" :: .dup ::
      .aload 10 :: .checkcast "com/alexvanyo/composelife/model/RLEStatus" ::
      .aload 11 :: .aload 12 :: .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/RLEResult" "<init>"
        ("(Lcom/alexvanyo/composelife/model/RLEStatus;" ++
          "[Ljava/lang/Object;[JLkotlin/jvm/internal/DefaultConstructorMarker;)V") ::
      .areturn :: f_Algorithm_parseRLEComments_prog.drop (pc + 15))
    (hl6 : locs 6 = warnsVal) :
    ∃ v st', runJvmResFast f f_Algorithm_parseRLEComments_prog pc
        (f_Algorithm_parseRLEComments_prog.drop pc)
        ⟨pc, [.ext (.rleStatus status)], locs, jh, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
      decodeRLEResult st' v = some ⟨status, warns.toArray, Algorithm.noCells⟩ ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  rcases stepStatic_growBufToArray_rleWarn_ext hrep (pc := pc + 2) (rest := [])
    (locs := setLocal locs 10 (.ext (.rleStatus status))) (jh := jh) (hp := ⟨ar, u64, asc⟩)
    with ⟨arrVal, jh1, warnVals?, htoarr, hext01, hstat01, hspec⟩
  let resObj := Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEResult"
    [("status", .ext (.rleStatus status)), ("warnings", arrVal), ("cells", .ext (.u64Ref u64.length))]
  let jh2 := (jh1.alloc resObj).2
  let resAddr := jh1.objects.size
  let hp1 : AlgHeap := ⟨ar, u64 ++ [Algorithm.noCells], asc⟩
  let locs3 := setLocal (setLocal (setLocal locs 10 (.ext (.rleStatus status))) 11 arrVal)
    12 (.ext (.u64Ref u64.length))
  refine ⟨.heapRef resAddr, ⟨pc + 14, [.heapRef resAddr], locs3, jh2, hp1⟩, ?_, ?_,
    heapExtends_trans hext01 (heapExtends_alloc jh1 resObj), hstat01, rfl, rfl⟩
  · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 15 := ⟨f - 15, by omega⟩
    rw [hd]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel
    have h1_6 : setLocal locs 10 (.ext (.rleStatus status)) 6 = warnsVal := by
      simp [setLocal, hl6]
    rw [h1_6]
    rw [runJvmResFast_invokestatic_step htoarr]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_noCells_rle_local]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_newClass]; norm_res_fuel
    rw [runJvmResFast_dup_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel
    simp [setLocal]
    rw [runJvmResFast_checkcast_step (by rfl)]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel
    simp [setLocal]
    rw [runJvmResFast_aload_local]; norm_res_fuel
    simp [setLocal]
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_invokespecial_step stepSpecial_rleResult_init]; norm_res_fuel
    rw [runJvmResFast_areturn_local]
    rw [show pc + 2 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = pc + 14 from by omega]
    rfl
  · exact rleResult_decode_of_parts status warns arrVal warnVals? hspec

private theorem parseRLEComments_ret_closed1
    (f : Nat) (warns : Algorithm.GrowBuf Algorithm.RLEWarning) (warnsVal : JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hrep : RleWarnRep warns warnsVal)
    (hf : f ≥ 15)
    (hl6 : locs 6 = warnsVal) :
    ∃ v st', runJvmResFast f f_Algorithm_parseRLEComments_prog 7
        (f_Algorithm_parseRLEComments_prog.drop 7)
        ⟨7, [], locs, jh, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
      decodeRLEResult st' v = some ⟨.invalidHeader "none", warns.toArray, Algorithm.noCells⟩ ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  rcases stepStatic_growBufToArray_rleWarn_ext hrep (pc := 10) (rest := [])
    (locs := setLocal locs 7 (.ext (.rleStatus (.invalidHeader "none"))))
    (jh := jh) (hp := ⟨ar, u64, asc⟩)
    with ⟨arrVal, jh1, warnVals?, htoarr, hext01, hstat01, hspec⟩
  let resObj := Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEResult"
    [("status", .ext (.rleStatus (.invalidHeader "none"))), ("warnings", arrVal),
      ("cells", .ext (.u64Ref u64.length))]
  let jh2 := (jh1.alloc resObj).2
  let resAddr := jh1.objects.size
  let hp1 : AlgHeap := ⟨ar, u64 ++ [Algorithm.noCells], asc⟩
  let locs3 := setLocal (setLocal (setLocal locs 7 (.ext (.rleStatus (.invalidHeader "none")))) 8 arrVal)
    9 (.ext (.u64Ref u64.length))
  refine ⟨.heapRef resAddr, ⟨21, [.heapRef resAddr], locs3, jh2, hp1⟩, ?_, ?_,
    heapExtends_trans hext01 (heapExtends_alloc jh1 resObj), hstat01, rfl, rfl⟩
  · have h7 : f_Algorithm_parseRLEComments_prog.drop 7 =
        .invokestatic "RleLeanKt" "f_Algorithm_parseRLEComments___closed__1"
          "()Lcom/alexvanyo/composelife/model/RLEStatus;" ::
        .astore 7 :: .aload 6 ::
        .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
          "(Ljava/lang/Object;)[Ljava/lang/Object;" ::
        .astore 8 :: .invokestatic "RleLeanKt" "f_Algorithm_noCells" "()[J" :: .astore 9 ::
        .newClass "com/alexvanyo/composelife/model/RLEResult" :: .dup ::
        .aload 7 :: .aload 8 :: .aload 9 :: .aconstNull ::
        .invokespecial "com/alexvanyo/composelife/model/RLEResult" "<init>"
          ("(Lcom/alexvanyo/composelife/model/RLEStatus;" ++
            "[Ljava/lang/Object;[JLkotlin/jvm/internal/DefaultConstructorMarker;)V") ::
        .areturn :: f_Algorithm_parseRLEComments_prog.drop 22 := by drop_prefix 15
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 15 := ⟨f - 15, by omega⟩
    rw [h7]
    rw [runJvmResFast_invokestatic_step stepStatic_parseRLEComments_closed1_local]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel
    have h1_6 : setLocal locs 7 (.ext (.rleStatus (.invalidHeader "none"))) 6 = warnsVal := by
      simp [setLocal, hl6]
    rw [h1_6]
    rw [runJvmResFast_invokestatic_step htoarr]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_noCells_rle_local]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_newClass]; norm_res_fuel
    rw [runJvmResFast_dup_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel
    simp [setLocal]
    rw [runJvmResFast_aload_local]; norm_res_fuel
    simp [setLocal]
    rw [runJvmResFast_aload_local]; norm_res_fuel
    simp [setLocal]
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_invokespecial_step stepSpecial_rleResult_init]; norm_res_fuel
    rw [runJvmResFast_areturn_local]
    rfl
  · exact rleResult_decode_of_parts (.invalidHeader "none") warns arrVal warnVals? hspec

private theorem parseRLEComments_header_ok
    (f' : Nat) (lines : Array String) (numLines i : UInt32)
    (offsetX offsetY : Int32) (warnsVal : JvmVal)
    (bytesAddr : Nat) (locs1 : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (pdRes : Algorithm.RLEResult)
    (hl0 : locs1 0 = .strArr lines)
    (hl1 : locs1 1 = .i32 numLines)
    (hl2 : locs1 2 = .i32 i)
    (hl3 : locs1 3 = .i32 offsetX.toUInt32)
    (hl4 : locs1 4 = .i32 offsetY.toUInt32)
    (hl6 : locs1 6 = warnsVal)
    (hl8 : locs1 8 = .heapRef bytesAddr)
    (h262_287 : f_Algorithm_parseRLEComments_prog.drop 262 =
      .iload 2 :: .iconst 1 :: .iadd :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .istore 10 :: .aconstNull ::
      .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_empty___redArg"
        "(Ljava/lang/Object;)Ljava/lang/Object;" ::
      .astore 11 :: .aload 0 :: .iload 1 :: .iload 10 :: .iconst 0 :: .aload 8 ::
      .iconst 0 :: .iconst 0 :: .iconst 0 :: .lconst 0 :: .iconst 0 :: .iconst 0 ::
      .iconst 0 :: .aload 6 :: .aload 11 :: .iload 3 :: .iload 4 ::
      .invokestatic "RleLeanKt" "f_Algorithm_parseRLEData-RjVw3pI" parseRLEDataDesc ::
      .areturn :: f_Algorithm_parseRLEComments_prog.drop 288)
    (hstep_pd :
      let locs2 := setLocal (setLocal locs1 10 (.i32 (i + 1))) 11
        (.ext (.strGrowBuf Algorithm.GrowBuf.empty))
      let enc := encodeRLEResult jh u64 pdRes
      stepInvokeStatic ⟨286, .i32 offsetY.toUInt32 :: .i32 offsetX.toUInt32 ::
          .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: warnsVal :: .i32 0 :: .i32 0 ::
          .i32 0 :: .i64 0 :: .i32 0 :: .i32 0 :: .i32 0 :: .heapRef bytesAddr :: .i32 0 ::
          .i32 (i + 1) :: .i32 numLines :: .strArr lines :: [], locs2, jh, ⟨ar, u64, asc⟩⟩
        "RleLeanKt" "f_Algorithm_parseRLEData-RjVw3pI" parseRLEDataDesc =
        .inl (some ⟨287, enc.1 :: [], locs2, enc.2.1, ⟨ar, enc.2.2, asc⟩⟩)) :
    let enc := encodeRLEResult jh u64 pdRes
    let locs2 := setLocal (setLocal locs1 10 (.i32 (i + 1))) 11
      (.ext (.strGrowBuf Algorithm.GrowBuf.empty))
    runJvmResFast (f' + 26) f_Algorithm_parseRLEComments_prog 262
        (f_Algorithm_parseRLEComments_prog.drop 262) ⟨262, [], locs1, jh, ⟨ar, u64, asc⟩⟩ =
      some (enc.1, ⟨287, [enc.1], locs2, enc.2.1, ⟨ar, enc.2.2, asc⟩⟩) := by
  dsimp only
  rw [h262_287]
  rw [runJvmResFast_iload]; norm_res_fuel; rw [hl2]
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_iadd_local]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_aconstNull]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step stepStatic_growBufEmpty_rle_local]; norm_res_fuel
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl0]
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl1]
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl8]
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_lconst_local]; norm_res_fuel
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl6]
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl3]
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl4]
  rw [runJvmResFast_invokestatic_step hstep_pd]; norm_res_fuel
  rw [runJvmResFast_areturn_local]

private theorem parseRLEComments_header_branch
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (offsetX offsetY : Int32)
    (warns : Algorithm.GrowBuf Algorithm.RLEWarning) (warnsVal : JvmVal)
    (line : String) (bytesAddr : Nat) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hstat : jh.statics = [])
    (hrep : RleWarnRep warns warnsVal)
    (hf : f ≥ 34)
    (hl0 : locs 0 = .strArr lines)
    (hl1 : locs 1 = .i32 numLines)
    (hl2 : locs 2 = .i32 i)
    (hl3 : locs 3 = .i32 offsetX.toUInt32)
    (hl4 : locs 4 = .i32 offsetY.toUInt32)
    (hl6 : locs 6 = warnsVal)
    (hl7 : locs 7 = .str line)
    (hl8 : locs 8 = .heapRef bytesAddr)
    (hget : jh.get? bytesAddr = some (.byteArray line.toByteArray.data)) :
    let st := Algorithm.parseRLEHeader line.toByteArray
    let res :=
      if st == 3 then ⟨.ruleNotSupported, warns.toArray, Algorithm.noCells⟩
      else if st != 0 then ⟨.invalidHeader line, warns.toArray, Algorithm.noCells⟩
      else Algorithm.parseRLEData lines numLines (i + 1) false line.toByteArray 0 0 0 0 false 0 0
        warns Algorithm.GrowBuf.empty offsetX offsetY
    ∃ v st', runJvmResFast f f_Algorithm_parseRLEComments_prog 234
        (f_Algorithm_parseRLEComments_prog.drop 234)
        ⟨234, [], locs, jh, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
      decodeRLEResult st' v = some res ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = [] ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  intro st res
  have h234 : f_Algorithm_parseRLEComments_prog.drop 234 =
      .aload 8 ::
      .invokestatic "RleLeanKt" "f_Algorithm_parseRLEHeader" "([B)I" ::
      .istore 9 :: .iload 9 :: .iconst 3 :: .if_icmpeq 288 ::
      .iload 9 :: .ifeq 262 :: f_Algorithm_parseRLEComments_prog.drop 242 := by drop_prefix 8
  have hp_234 : runJvmResFast f f_Algorithm_parseRLEComments_prog 234
      (f_Algorithm_parseRLEComments_prog.drop 234) ⟨234, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 3) f_Algorithm_parseRLEComments_prog 237
        (.iload 9 :: .iconst 3 :: .if_icmpeq 288 :: .iload 9 :: .ifeq 262 ::
          f_Algorithm_parseRLEComments_prog.drop 242)
        ⟨237, [], setLocal locs 9 (.i32 st), jh, ⟨ar, u64, asc⟩⟩ := by
    obtain ⟨f', hf'⟩ : ∃ f', f = f' + 3 := ⟨f - 3, by omega⟩
    rw [h234, hf', show f' + 3 - 3 = f' from by omega]
    rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl8]
    rw [runJvmResFast_invokestatic_step (stepStatic_parseRLEHeader_heap_local hget)]; norm_res_fuel
    rw [runJvmResFast_istore]
  let locs1 := setLocal locs 9 (.i32 st)
  by_cases h3 : st == 3
  · have h288_303 : f_Algorithm_parseRLEComments_prog.drop 288 =
        .getstatic "com/alexvanyo/composelife/model/RLEStatus$RuleNotSupported" "INSTANCE"
          "Lcom/alexvanyo/composelife/model/RLEStatus$RuleNotSupported;" ::
        f_Algorithm_parseRLEComments_prog.drop 289 := by drop_prefix 1
    have h289_303 : f_Algorithm_parseRLEComments_prog.drop 289 =
        .astore 10 :: .aload 6 ::
        .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
          "(Ljava/lang/Object;)[Ljava/lang/Object;" ::
        .astore 11 :: .invokestatic "RleLeanKt" "f_Algorithm_noCells" "()[J" :: .astore 12 ::
        .newClass "com/alexvanyo/composelife/model/RLEResult" :: .dup ::
        .aload 10 :: .checkcast "com/alexvanyo/composelife/model/RLEStatus" ::
        .aload 11 :: .aload 12 :: .aconstNull ::
        .invokespecial "com/alexvanyo/composelife/model/RLEResult" "<init>"
          ("(Lcom/alexvanyo/composelife/model/RLEStatus;" ++
            "[Ljava/lang/Object;[JLkotlin/jvm/internal/DefaultConstructorMarker;)V") ::
        .areturn :: f_Algorithm_parseRLEComments_prog.drop 304 := by drop_prefix 15
    rcases parseRLEComments_ret_result (f - 7) 289 .ruleNotSupported warns warnsVal locs1 jh ar u64 asc
      hrep (by omega) h289_303 (by simp [locs1, setLocal, hl6]) with
      ⟨v, st', hrun, hdec, hext, hst, har, hasc⟩
    refine ⟨v, st', ?_, ?_, hext, hstat ▸ hst, har, hasc⟩
    · rw [hp_234]
      obtain ⟨f', hf'⟩ : ∃ f', f - 3 = f' + 4 := ⟨f - 7, by omega⟩
      rw [hf']
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_if_icmpeq_branch (beq_iff_eq.mp h3)]; norm_res_fuel
      rw [h288_303]
      rw [runJvmResFast_getstatic_step hstat (by rfl)]; norm_res_fuel
      rw [show f' = f - 7 from by omega]
      exact hrun
    · simpa [res, h3] using hdec
  · have h3f : (st == 3) = false := Bool.eq_false_iff.mpr h3
    by_cases h0 : st == 0
    · have h262_287 : f_Algorithm_parseRLEComments_prog.drop 262 =
          .iload 2 :: .iconst 1 :: .iadd :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
          .istore 10 :: .aconstNull ::
          .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_empty___redArg"
            "(Ljava/lang/Object;)Ljava/lang/Object;" ::
          .astore 11 :: .aload 0 :: .iload 1 :: .iload 10 :: .iconst 0 :: .aload 8 ::
          .iconst 0 :: .iconst 0 :: .iconst 0 :: .lconst 0 :: .iconst 0 :: .iconst 0 ::
          .iconst 0 :: .aload 6 :: .aload 11 :: .iload 3 :: .iload 4 ::
          .invokestatic "RleLeanKt" "f_Algorithm_parseRLEData-RjVw3pI" parseRLEDataDesc ::
          .areturn :: f_Algorithm_parseRLEComments_prog.drop 288 := by drop_prefix 26
      let locs2 := setLocal (setLocal locs1 10 (.i32 (i + 1))) 11
        (.ext (.strGrowBuf Algorithm.GrowBuf.empty))
      have hstep_pd := stepStatic_parseRLEData_header (pc := 286) (locs := locs2) (jh := jh)
        (ar := ar) (u64 := u64) (asc := asc) (lines := lines) (numLines := numLines)
        (i := i + 1) (bytes := line.toByteArray) (bytesAddr := bytesAddr)
        (warns := warns) (warnsVal := warnsVal) (offsetX := offsetX) (offsetY := offsetY)
        hget hrep
      have hne0 : (bne st 0) = false := by simp [bne, h0]
      have hres_eq : res = Algorithm.parseRLEData lines numLines (i + 1) false line.toByteArray
          0 0 0 0 false 0 0 warns Algorithm.GrowBuf.empty offsetX offsetY := by
        dsimp only [res]; simp only [h3f, hne0, Bool.false_eq_true, ↓reduceIte]
      have hgoal : ∀ (pdRes : Algorithm.RLEResult)
          (hsp : stepInvokeStatic ⟨286, .i32 offsetY.toUInt32 :: .i32 offsetX.toUInt32 ::
              .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: warnsVal :: .i32 0 :: .i32 0 ::
              .i32 0 :: .i64 0 :: .i32 0 :: .i32 0 :: .i32 0 :: .heapRef bytesAddr :: .i32 0 ::
              .i32 (i + 1) :: .i32 numLines :: .strArr lines :: [], locs2, jh, ⟨ar, u64, asc⟩⟩
            "RleLeanKt" "f_Algorithm_parseRLEData-RjVw3pI" parseRLEDataDesc =
            .inl (some ⟨287, (encodeRLEResult jh u64 pdRes).1 :: [], locs2,
              (encodeRLEResult jh u64 pdRes).2.1,
              ⟨ar, (encodeRLEResult jh u64 pdRes).2.2, asc⟩⟩)),
          ∃ v st', runJvmResFast f f_Algorithm_parseRLEComments_prog 234
              (f_Algorithm_parseRLEComments_prog.drop 234)
              ⟨234, [], locs, jh, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
            decodeRLEResult st' v = some pdRes ∧
            HeapExtends jh st'.jvmHeap ∧
            st'.jvmHeap.statics = [] ∧
            st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
        intro pdRes hsp
        refine ⟨(encodeRLEResult jh u64 pdRes).1,
          ⟨287, [(encodeRLEResult jh u64 pdRes).1], locs2, (encodeRLEResult jh u64 pdRes).2.1,
            ⟨ar, (encodeRLEResult jh u64 pdRes).2.2, asc⟩⟩,
          ?_, ?_, encodeRLEResult_heapExtends jh u64 pdRes,
          by rw [encodeRLEResult_statics]; exact hstat, rfl, rfl⟩
        · rw [hp_234]
          obtain ⟨f', hf'⟩ : ∃ f', f - 3 = f' + 31 := ⟨f - 34, by omega⟩
          rw [hf']
          rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
          rw [runJvmResFast_iconst_local]; norm_res_fuel
          rw [runJvmResFast_if_icmpeq_fallthrough h3f]; norm_res_fuel
          rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
          rw [runJvmResFast_ifeq_branch (beq_iff_eq.mp h0)]; norm_res_fuel
          exact parseRLEComments_header_ok f' lines numLines i offsetX offsetY warnsVal
            bytesAddr locs1 jh ar u64 asc pdRes
            (by dsimp only [locs1]; rw [setLocal_ne _ _ (by decide), hl0])
            (by dsimp only [locs1]; rw [setLocal_ne _ _ (by decide), hl1])
            (by dsimp only [locs1]; rw [setLocal_ne _ _ (by decide), hl2])
            (by dsimp only [locs1]; rw [setLocal_ne _ _ (by decide), hl3])
            (by dsimp only [locs1]; rw [setLocal_ne _ _ (by decide), hl4])
            (by dsimp only [locs1]; rw [setLocal_ne _ _ (by decide), hl6])
            (by dsimp only [locs1]; rw [setLocal_ne _ _ (by decide), hl8]) h262_287 hsp
        · exact decodeRLEResult_encode_proj 287 [(encodeRLEResult jh u64 pdRes).1]
            locs2 jh ar u64 asc pdRes
      rw [hres_eq]
      exact hgoal _ hstep_pd
    · have h0f : (st == 0) = false := Bool.eq_false_iff.mpr h0
      have h242_247 : f_Algorithm_parseRLEComments_prog.drop 242 =
          .newClass "com/alexvanyo/composelife/model/RLEStatus$InvalidHeader" :: .dup ::
          .aload 7 :: .checkcast "java/lang/String" ::
          .invokespecial "com/alexvanyo/composelife/model/RLEStatus$InvalidHeader" "<init>"
            "(Ljava/lang/String;)V" ::
          f_Algorithm_parseRLEComments_prog.drop 247 := by drop_prefix 5
      have h247_262 : f_Algorithm_parseRLEComments_prog.drop 247 =
          .astore 10 :: .aload 6 ::
          .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
            "(Ljava/lang/Object;)[Ljava/lang/Object;" ::
          .astore 11 :: .invokestatic "RleLeanKt" "f_Algorithm_noCells" "()[J" :: .astore 12 ::
          .newClass "com/alexvanyo/composelife/model/RLEResult" :: .dup ::
          .aload 10 :: .checkcast "com/alexvanyo/composelife/model/RLEStatus" ::
          .aload 11 :: .aload 12 :: .aconstNull ::
          .invokespecial "com/alexvanyo/composelife/model/RLEResult" "<init>"
            ("(Lcom/alexvanyo/composelife/model/RLEStatus;" ++
              "[Ljava/lang/Object;[JLkotlin/jvm/internal/DefaultConstructorMarker;)V") ::
          .areturn :: f_Algorithm_parseRLEComments_prog.drop 262 := by drop_prefix 15
      rcases parseRLEComments_ret_result (f - 13) 247 (.invalidHeader line) warns warnsVal locs1 jh ar u64 asc
        hrep (by omega) h247_262 (by simp [locs1, setLocal, hl6]) with
        ⟨v, st', hrun, hdec, hext, hst, har, hasc⟩
      refine ⟨v, st', ?_, ?_, hext, hstat ▸ hst, har, hasc⟩
      · rw [hp_234]
        obtain ⟨f', hf'⟩ : ∃ f', f - 3 = f' + 10 := ⟨f - 13, by omega⟩
        rw [hf']
        rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
        rw [runJvmResFast_iconst_local]; norm_res_fuel
        rw [runJvmResFast_if_icmpeq_fallthrough h3f]; norm_res_fuel
        rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
        rw [runJvmResFast_ifeq_fallthrough h0f]; norm_res_fuel
        rw [h242_247]
        rw [runJvmResFast_newClass]; norm_res_fuel
        rw [runJvmResFast_dup_local]; norm_res_fuel
        rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl7]
        rw [runJvmResFast_checkcast_step (by rfl)]; norm_res_fuel
        rw [runJvmResFast_invokespecial_step stepSpecial_rleStatusInvalidHeader_init]; norm_res_fuel
        rw [show f' = f - 13 from by omega]
        exact hrun
      · have hne0 : (st != 0) = true := by simp [bne, h0f]
        simpa [res, h3f, hne0] using hdec

private theorem parseRLEComments_dupOffset_branch
    (f : Nat) (i : UInt32) (hasOffset : Bool) (c : Algorithm.ParsedCoords)
    (warns : Algorithm.GrowBuf Algorithm.RLEWarning) (warnsVal : JvmVal)
    (outerAddr innerAddr : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hrep : RleWarnRep warns warnsVal)
    (hf : f ≥ 70)
    (hl2 : locs 2 = .i32 i)
    (hl5 : locs 5 = .i32 (if hasOffset then 1 else 0))
    (hl6 : locs 6 = warnsVal)
    (hl9 : locs 9 = .heapRef outerAddr)
    (houter : jh.get? outerAddr = some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr]))
    (hinner : jh.get? innerAddr = some (.objArray "java/lang/Object"
      #[.boxedInt 0, .boxedInt c.x.toUInt32, .null, .null, .null, .boxedInt c.y.toUInt32])) :
    let warns' := if hasOffset then warns.push (.duplicateOffset (i + 1) c.x c.y) else warns
    ∃ f1 warnsVal' locs' jh',
      f - 63 ≤ f1 ∧ f1 ≤ f ∧
      RleWarnRep warns' warnsVal' ∧
      HeapExtends jh jh' ∧
      jh'.statics = jh.statics ∧
      runJvmResFast f f_Algorithm_parseRLEComments_prog 91
        (f_Algorithm_parseRLEComments_prog.drop 91)
        ⟨91, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast f1 f_Algorithm_parseRLEComments_prog 159
        (f_Algorithm_parseRLEComments_prog.drop 159)
        ⟨159, [], locs', jh', ⟨ar, u64, asc⟩⟩ ∧
      locs' 0 = locs 0 ∧ locs' 1 = locs 1 ∧ locs' 2 = .i32 i ∧
      locs' 6 = warnsVal ∧ locs' 11 = .heapRef innerAddr ∧ locs' 12 = warnsVal' := by
  have h91_103 : f_Algorithm_parseRLEComments_prog.drop 91 =
      .aload 9 :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload :: .astore 11 ::
      .aconstNull :: .astore 12 :: .iload 5 :: .ifne 103 ::
      .aload 6 :: .astore 12 :: .goto 159 :: f_Algorithm_parseRLEComments_prog.drop 103 := by
    drop_prefix 12
  cases hasOffset with
  | false =>
    let locs' := setLocal (setLocal (setLocal locs 11 (.heapRef innerAddr)) 12 .null) 12 warnsVal
    refine ⟨f - 12, warnsVal, locs', jh, by omega, by omega, hrep, heapExtends_refl jh, rfl, ?_,
      by dsimp only [locs', setLocal]; simp,
      by dsimp only [locs', setLocal]; simp,
      by dsimp only [locs', setLocal]; simp [hl2],
      by dsimp only [locs', setLocal]; simp [hl6],
      by dsimp only [locs', setLocal]; simp,
      by dsimp only [locs', setLocal]; simp⟩
    obtain ⟨f', hf'⟩ : ∃ f', f = f' + 12 := ⟨f - 12, by omega⟩
    rw [h91_103, hf', show f' + 12 - 12 = f' from by omega]
    rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl9]
    rw [runJvmResFast_checkcast_objArray houter (Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_aaload houter (by decide) (by simp)]; norm_res_fuel
    rw [show (#[.boxedInt 1, .heapRef innerAddr] : Array JvmVal)[UInt32.toNat 1] =
      .heapRef innerAddr from rfl]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel
    rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), hl5]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel
    rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), hl6]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_goto]
  | true =>
    let w : Algorithm.RLEWarning := .duplicateOffset (i + 1) c.x c.y
    let wObj : Jvm.HeapObj AlgExt :=
      Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset"
        [("lineIndex", .i32 (i + 1)), ("x", .i32 c.x.toUInt32), ("y", .i32 c.y.toUInt32)]
    let jh1 := (jh.alloc wObj).2
    let wAddr := jh.objects.size
    let warnsVal' : JvmVal := .ext (.rleWarnGrowBuf (warns.push w))
    have hw_dec : decodeRLEWarning jh1 (.heapRef wAddr) = some w := by
      simp [decodeRLEWarning, jh1, wAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc, wObj, w]
      rfl
    have h103_123 : f_Algorithm_parseRLEComments_prog.drop 103 =
        .aload 6 :: .newClass "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset" ::
        .dup :: .iload 2 :: .iconst 1 :: .iadd ::
        .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
        .aload 11 :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
        .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" ::
        .aload 11 :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload :: .astore 14 ::
        .iconst 0 :: .istore 15 :: .aload 14 :: .instanceof "kotlin/UInt" :: .ifeq 127 ::
        f_Algorithm_parseRLEComments_prog.drop 123 := by
      drop_prefix 20
    have h127_143 : f_Algorithm_parseRLEComments_prog.drop 127 =
        .aload 14 :: .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
        .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" ::
        .aload 14 :: .checkcast "java/lang/Integer" :: .invokevirtual "java/lang/Integer" "intValue" "()I" ::
        .aload 11 :: .checkcast "[Ljava/lang/Object;" :: .iconst 5 :: .aaload :: .astore 14 ::
        .iconst 0 :: .istore 15 :: .aload 14 :: .instanceof "kotlin/UInt" :: .ifeq 147 ::
        f_Algorithm_parseRLEComments_prog.drop 143 := by
      drop_prefix 16
    have h147_159 : f_Algorithm_parseRLEComments_prog.drop 147 =
        .aload 14 :: .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
        .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" ::
        .aload 14 :: .checkcast "java/lang/Integer" :: .invokevirtual "java/lang/Integer" "intValue" "()I" ::
        .aconstNull ::
        .invokespecial "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset" "<init>"
          "(IIILkotlin/jvm/internal/DefaultConstructorMarker;)V" ::
        .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
          "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" ::
        .astore 13 :: .aload 13 :: .astore 12 :: f_Algorithm_parseRLEComments_prog.drop 159 := by
      drop_prefix 12
    let locs' := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
      11 (.heapRef innerAddr)) 12 .null) 14 (.boxedInt c.x.toUInt32)) 15 (.i32 0))
      14 (.boxedInt c.y.toUInt32)) 15 (.i32 0)) 13 warnsVal') 12 warnsVal'
    refine ⟨f - 57, warnsVal', locs', jh1, by omega, Nat.sub_le f 57, RleWarnRep.full (warns.push w),
      heapExtends_alloc jh wObj, rfl, ?_,
      by simp [locs', setLocal], by simp [locs', setLocal], by simp [locs', setLocal, hl2],
      by simp [locs', setLocal, hl6], by simp [locs', setLocal], by simp [locs']⟩
    · obtain ⟨f', hf'⟩ : ∃ f', f = f' + 57 := ⟨f - 57, by omega⟩
      rw [h91_103, hf', show f' + 57 - 57 = f' from by omega]
      rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl9]
      rw [runJvmResFast_checkcast_objArray houter (Or.inl rfl)]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_aaload houter (by decide) (by simp)]; norm_res_fuel
      rw [show (#[.boxedInt 1, .heapRef innerAddr] : Array JvmVal)[UInt32.toNat 1] =
        .heapRef innerAddr from rfl]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_aconstNull]; norm_res_fuel
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel
      rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), hl5]
      simp only [↓reduceIte]
      rw [runJvmResFast_ifne_branch (by decide)]; norm_res_fuel
      rw [h103_123]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl6]
      rw [runJvmResFast_newClass]; norm_res_fuel
      rw [runJvmResFast_dup_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl2]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_iadd_local]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_ldcStr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_checkcast_objArray hinner (Or.inl rfl)]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_aaload hinner (by decide) (by simp)]; norm_res_fuel
      rw [show (#[.boxedInt 0, .boxedInt c.x.toUInt32, .null, .null, .null, .boxedInt c.y.toUInt32] :
        Array JvmVal)[UInt32.toNat 1] = .boxedInt c.x.toUInt32 from rfl]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_instanceof_boxedInt_uint]; norm_res_fuel
      rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
      rw [h127_143]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_ldcStr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
      rw [runJvmResFast_invokevirtual_step (stepVirtual_integer_intValue)]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_checkcast_objArray hinner (Or.inl rfl)]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_aaload hinner (by decide) (by simp)]; norm_res_fuel
      rw [show (#[.boxedInt 0, .boxedInt c.x.toUInt32, .null, .null, .null, .boxedInt c.y.toUInt32] :
        Array JvmVal)[UInt32.toNat 5] = .boxedInt c.y.toUInt32 from rfl]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_instanceof_boxedInt_uint]; norm_res_fuel
      rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
      rw [h147_159]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_ldcStr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
      rw [runJvmResFast_invokevirtual_step (stepVirtual_integer_intValue)]; norm_res_fuel
      rw [runJvmResFast_aconstNull]; norm_res_fuel
      rw [runJvmResFast_invokespecial_step stepSpecial_rleWarnDupOffset_init]; norm_res_fuel
      have hw_dec' : decodeRLEWarning { objects := jh.objects.push wObj, statics := jh.statics }
          (.heapRef jh.objects.size) = some w := hw_dec
      rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_rleWarn hrep hw_dec')]; norm_res_fuel
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; rw [setLocal_self]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rfl

private theorem parseRLEComments_finish_some_offset
    (f : Nat) (c : Algorithm.ParsedCoords) (i : UInt32) (warnsVal' : JvmVal)
    (innerAddr : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 61)
    (hl2 : locs 2 = .i32 i)
    (hl11 : locs 11 = .heapRef innerAddr)
    (hl12 : locs 12 = warnsVal')
    (hinner : jh.get? innerAddr = some (.objArray "java/lang/Object"
      #[.boxedInt 0, .boxedInt c.x.toUInt32, .null, .null, .null, .boxedInt c.y.toUInt32])) :
    ∃ locs2,
      runJvmResFast f f_Algorithm_parseRLEComments_prog 159
        (f_Algorithm_parseRLEComments_prog.drop 159)
        ⟨159, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 61) f_Algorithm_parseRLEComments_prog 3
        (f_Algorithm_parseRLEComments_prog.drop 3)
        ⟨3, [], locs2, jh, ⟨ar, u64, asc⟩⟩ ∧
      locs2 0 = locs 0 ∧ locs2 1 = locs 1 ∧ locs2 2 = .i32 (i + 1) ∧
      locs2 3 = .i32 c.x.toUInt32 ∧ locs2 4 = .i32 c.y.toUInt32 ∧
      locs2 5 = .i32 1 ∧ locs2 6 = warnsVal' := by
  have h159_181 : f_Algorithm_parseRLEComments_prog.drop 159 =
      .aload 0 :: .astore 13 :: .iload 1 :: .istore 14 :: .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 15 ::
      .aload 11 :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 11 :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload :: .astore 17 ::
      .iconst 0 :: .istore 18 :: .aload 17 :: .instanceof "kotlin/UInt" :: .ifeq 185 ::
      f_Algorithm_parseRLEComments_prog.drop 181 := by drop_prefix 22
  have h185_202 : f_Algorithm_parseRLEComments_prog.drop 185 =
      .aload 17 :: .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 17 :: .checkcast "java/lang/Integer" :: .invokevirtual "java/lang/Integer" "intValue" "()I" ::
      .istore 16 ::
      .aload 11 :: .checkcast "[Ljava/lang/Object;" :: .iconst 5 :: .aaload :: .astore 18 ::
      .iconst 0 :: .istore 19 :: .aload 18 :: .instanceof "kotlin/UInt" :: .ifeq 206 ::
      f_Algorithm_parseRLEComments_prog.drop 202 := by drop_prefix 17
  have h206_228 : f_Algorithm_parseRLEComments_prog.drop 206 =
      .aload 18 :: .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 18 :: .checkcast "java/lang/Integer" :: .invokevirtual "java/lang/Integer" "intValue" "()I" ::
      .istore 17 ::
      .aload 13 :: .astore 0 :: .iload 14 :: .istore 1 :: .iload 15 :: .istore 2 ::
      .iload 16 :: .istore 3 :: .iload 17 :: .istore 4 :: .iconst 1 :: .istore 5 ::
      .aload 12 :: .astore 6 :: .goto 3 :: f_Algorithm_parseRLEComments_prog.drop 228 := by
    drop_prefix 22
  let locsA := setLocal (setLocal (setLocal locs 13 (locs 0)) 14 (locs 1)) 15 (.i32 (i + 1))
  let locsB := setLocal (setLocal (setLocal locsA 17 (.boxedInt c.x.toUInt32)) 18 (.i32 0)) 16
    (.i32 c.x.toUInt32)
  let locsC := setLocal (setLocal (setLocal locsB 18 (.boxedInt c.y.toUInt32)) 19 (.i32 0)) 17
    (.i32 c.y.toUInt32)
  let locs2 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locsC 0 (locs 0))
    1 (locs 1)) 2 (.i32 (i + 1))) 3 (.i32 c.x.toUInt32)) 4 (.i32 c.y.toUInt32)) 5 (.i32 1)) 6 warnsVal'
  refine ⟨locs2, ?_,
    by dsimp only [locs2, setLocal]; simp,
    by dsimp only [locs2, setLocal]; simp,
    by dsimp only [locs2, setLocal]; simp,
    by dsimp only [locs2, setLocal]; simp,
    by dsimp only [locs2, setLocal]; simp,
    by dsimp only [locs2, setLocal]; simp,
    by dsimp only [locs2, setLocal]; simp⟩
  · obtain ⟨f', hf'⟩ : ∃ f', f = f' + 61 := ⟨f - 61, by omega⟩
    rw [h159_181, hf', show f' + 61 - 61 = f' from by omega]
    rw [runJvmResFast_aload_local]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl2]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl11]
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl11]
    rw [runJvmResFast_checkcast_objArray hinner (Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_aaload hinner (by decide) (by simp)]; norm_res_fuel
    rw [show (#[.boxedInt 0, .boxedInt c.x.toUInt32, .null, .null, .null, .boxedInt c.y.toUInt32] :
      Array JvmVal)[UInt32.toNat 1] = .boxedInt c.x.toUInt32 from rfl]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_instanceof_boxedInt_uint]; norm_res_fuel
    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
    rw [h185_202]
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl11]
    rw [runJvmResFast_checkcast_objArray hinner (Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_aaload hinner (by decide) (by simp)]; norm_res_fuel
    rw [show (#[.boxedInt 0, .boxedInt c.x.toUInt32, .null, .null, .null, .boxedInt c.y.toUInt32] :
      Array JvmVal)[UInt32.toNat 5] = .boxedInt c.y.toUInt32 from rfl]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_instanceof_boxedInt_uint]; norm_res_fuel
    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
    rw [h206_228]
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl12]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_goto]

private theorem parseRLEComments_none_offset
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (offsetX offsetY : Int32) (hasOffset : Bool) (warnsVal : JvmVal)
    (bytesAddr outerAddr : Nat) (locs1 : Nat → JvmVal)
    (jh1 jh2 : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 49)
    (h1_0 : locs1 0 = .strArr lines)
    (h1_1 : locs1 1 = .i32 numLines)
    (h1_2 : locs1 2 = .i32 i)
    (h1_3 : locs1 3 = .i32 offsetX.toUInt32)
    (h1_4 : locs1 4 = .i32 offsetY.toUInt32)
    (h1_5 : locs1 5 = .i32 (if hasOffset then 1 else 0))
    (h1_6 : locs1 6 = warnsVal)
    (h1_8 : locs1 8 = .heapRef bytesAddr)
    (hget2 : jh2.get? outerAddr = some (.objArray "java/lang/Object" #[.boxedInt 0]))
    (h43_59 : f_Algorithm_parseRLEComments_prog.drop 43 =
      .aload 8 :: .invokestatic "RleLeanKt" "f_Algorithm_parseRLEOffset" "([B)Ljava/lang/Object;" ::
      .astore 9 :: .aload 9 :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 9 :: .checkcast "[Ljava/lang/Object;" :: .iconst 0 :: .aaload :: .dup ::
      .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .checkcast "java/lang/Integer" ::
      .invokevirtual "java/lang/Integer" "intValue" "()I" ::
      .tableswitch 0 [59, 91] 228 :: f_Algorithm_parseRLEComments_prog.drop 59)
    (h59_91 : f_Algorithm_parseRLEComments_prog.drop 59 =
      .aload 0 :: .astore 11 :: .iload 1 :: .istore 12 :: .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 13 ::
      .iload 3 :: .istore 14 :: .iload 4 :: .istore 15 :: .iload 5 :: .istore 16 ::
      .aload 6 :: .astore 17 :: .aload 11 :: .astore 0 :: .iload 12 :: .istore 1 ::
      .iload 13 :: .istore 2 :: .iload 14 :: .istore 3 :: .iload 15 :: .istore 4 ::
      .iload 16 :: .istore 5 :: .aload 17 :: .astore 6 :: .goto 3 ::
      f_Algorithm_parseRLEComments_prog.drop 91)
    (hpo_step : stepInvokeStatic ⟨44, .heapRef bytesAddr :: [], locs1, jh1, ⟨ar, u64, asc⟩⟩
        "RleLeanKt" "f_Algorithm_parseRLEOffset" "([B)Ljava/lang/Object;" =
      .inl (some ⟨45, .heapRef outerAddr :: [], locs1, jh2, ⟨ar, u64, asc⟩⟩)) :
    ∃ locs2,
      runJvmResFast f f_Algorithm_parseRLEComments_prog 43
          (f_Algorithm_parseRLEComments_prog.drop 43) ⟨43, [], locs1, jh1, ⟨ar, u64, asc⟩⟩ =
        runJvmResFast (f - 48) f_Algorithm_parseRLEComments_prog 3
          (f_Algorithm_parseRLEComments_prog.drop 3) ⟨3, [], locs2, jh2, ⟨ar, u64, asc⟩⟩ ∧
      locs2 0 = .strArr lines ∧ locs2 1 = .i32 numLines ∧ locs2 2 = .i32 (i + 1) ∧
      locs2 3 = .i32 offsetX.toUInt32 ∧ locs2 4 = .i32 offsetY.toUInt32 ∧
      locs2 5 = .i32 (if hasOffset then 1 else 0) ∧ locs2 6 = warnsVal := by
  let locs2 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
    (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      locs1 9 (.heapRef outerAddr))
      11 (.strArr lines)) 12 (.i32 numLines)) 13 (.i32 (i + 1))) 14 (.i32 offsetX.toUInt32))
      15 (.i32 offsetY.toUInt32)) 16 (.i32 (if hasOffset then 1 else 0))) 17 warnsVal)
      0 (.strArr lines)) 1 (.i32 numLines)) 2 (.i32 (i + 1))) 3 (.i32 offsetX.toUInt32))
      4 (.i32 offsetY.toUInt32)) 5 (.i32 (if hasOffset then 1 else 0))) 6 warnsVal
  refine ⟨locs2, ?_,
    by dsimp only [locs2]; rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
      setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
      setLocal_ne _ _ (by decide), setLocal_self],
    by dsimp only [locs2]; rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
      setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
      setLocal_self],
    by dsimp only [locs2]; rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
      setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_self],
    by dsimp only [locs2]; rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
      setLocal_ne _ _ (by decide), setLocal_self],
    by dsimp only [locs2]; rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
      setLocal_self],
    by dsimp only [locs2]; rw [setLocal_ne _ _ (by decide), setLocal_self],
    by dsimp only [locs2]; exact setLocal_self _ _ _⟩
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 48 := ⟨f - 48, by omega⟩
  rw [h43_59, hf', show f' + 48 - 48 = f' from by omega]
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [h1_8]
  rw [runJvmResFast_invokestatic_step hpo_step]; norm_res_fuel
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [setLocal_self]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [setLocal_self]
  rw [runJvmResFast_checkcast_objArray hget2 (Or.inl rfl)]; norm_res_fuel
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_aaload hget2 (by decide) (by decide)]; norm_res_fuel
  rw [show (#[.boxedInt 0] : Array JvmVal)[UInt32.toNat 0] = .boxedInt 0 from rfl]
  rw [runJvmResFast_dup_local]; norm_res_fuel
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
  rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
  rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]; norm_res_fuel
  rw [runJvmResFast_tableswitch_local]; norm_res_fuel
  have hts : Jvm.tableswitchTarget 0 0 [59, 91] 228 = 59 := by decide
  rw [hts]
  rw [h59_91]
  rw [runJvmResFast_aload_local]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), h1_0]
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), h1_1]
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), h1_2]
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_iadd_local]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_ne _ _ (by decide), h1_3]
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), h1_4]
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), h1_5]
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_ne _ _ (by decide), h1_6]
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_self]
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_self]
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_self]
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_self]
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_self]
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_self]
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel
  rw [setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide), setLocal_ne _ _ (by decide),
    setLocal_self]
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_goto]

private theorem parseRLEComments_drop_3_7 :
    f_Algorithm_parseRLEComments_prog.drop 3 =
      .iload 2 :: .iload 1 :: .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" ::
      .iflt 22 :: f_Algorithm_parseRLEComments_prog.drop 7 := by drop_prefix 4

private theorem parseRLEComments_drop_22_37 :
    f_Algorithm_parseRLEComments_prog.drop 22 =
      .aload 0 :: .iload 2 :: .aaload :: .astore 7 ::
      .aload 7 :: .ldcStr "null cannot be cast to non-null type kotlin.String" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 7 :: .checkcast "java/lang/String" ::
      .invokestatic "kotlin/text/StringsKt" "encodeToByteArray" "(Ljava/lang/String;)[B" ::
      .astore 8 :: .aload 8 :: .arraylength ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .ifeq 234 :: f_Algorithm_parseRLEComments_prog.drop 37 := by drop_prefix 15

private theorem parseRLEComments_drop_37_43 :
    f_Algorithm_parseRLEComments_prog.drop 37 =
      .aload 8 :: .iconst 0 :: .baload ::
      .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" ::
      .iconst 35 :: .if_icmpne 234 :: f_Algorithm_parseRLEComments_prog.drop 43 := by drop_prefix 6

private theorem parseRLEComments_drop_43_59 :
    f_Algorithm_parseRLEComments_prog.drop 43 =
      .aload 8 :: .invokestatic "RleLeanKt" "f_Algorithm_parseRLEOffset" "([B)Ljava/lang/Object;" ::
      .astore 9 :: .aload 9 :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 9 :: .checkcast "[Ljava/lang/Object;" :: .iconst 0 :: .aaload :: .dup ::
      .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .checkcast "java/lang/Integer" ::
      .invokevirtual "java/lang/Integer" "intValue" "()I" ::
      .tableswitch 0 [59, 91] 228 :: f_Algorithm_parseRLEComments_prog.drop 59 := by drop_prefix 16

private theorem parseRLEComments_drop_59_91 :
    f_Algorithm_parseRLEComments_prog.drop 59 =
      .aload 0 :: .astore 11 :: .iload 1 :: .istore 12 :: .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 13 ::
      .iload 3 :: .istore 14 :: .iload 4 :: .istore 15 :: .iload 5 :: .istore 16 ::
      .aload 6 :: .astore 17 :: .aload 11 :: .astore 0 :: .iload 12 :: .istore 1 ::
      .iload 13 :: .istore 2 :: .iload 14 :: .istore 3 :: .iload 15 :: .istore 4 ::
      .iload 16 :: .istore 5 :: .aload 17 :: .astore 6 :: .goto 3 ::
      f_Algorithm_parseRLEComments_prog.drop 91 := by drop_prefix 32

private theorem parseRLEComments_step_head
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hilt : i < numLines)
    (hi_lt : i.toNat < lines.size)
    (hlines31 : lines.size < 2 ^ 31)
    (hf : f ≥ 18)
    (hl0 : locs 0 = .strArr lines)
    (hl1 : locs 1 = .i32 numLines)
    (hl2 : locs 2 = .i32 i) :
    let line := lines[i.toNat]!
    let bytes := line.toByteArray
    let jh1 := (jh.alloc (.byteArray bytes.data)).2
    let bytesAddr := jh.objects.size
    let locs1 := setLocal (setLocal locs 7 (.str line)) 8 (.heapRef bytesAddr)
    runJvmResFast f f_Algorithm_parseRLEComments_prog 3
      (f_Algorithm_parseRLEComments_prog.drop 3) ⟨3, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 18) f_Algorithm_parseRLEComments_prog 36
        (.ifeq 234 :: f_Algorithm_parseRLEComments_prog.drop 37)
        ⟨36, [.i32 (UInt32.ofNat bytes.data.size)], locs1, jh1, ⟨ar, u64, asc⟩⟩ := by
  have hislt : i.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by
    have := UInt32.lt_iff_toNat_lt.mp hilt; omega)
  let line := lines[i.toNat]!
  let bytes := line.toByteArray
  let jh1 := (jh.alloc (.byteArray bytes.data)).2
  let bytesAddr := jh.objects.size
  have hget1 : jh1.get? bytesAddr = some (.byteArray bytes.data) := by
    simp [jh1, bytesAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 18 := ⟨f - 18, by omega⟩
  dsimp only
  rw [parseRLEComments_drop_3_7, hf', show f' + 18 - 18 = f' from by omega]
  rw [runJvmResFast_iload]; norm_res_fuel; rw [hl2]
  rw [runJvmResFast_iload]; norm_res_fuel; rw [hl1]
  rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
  rw [runJvmResFast_iflt_branch (by
    rw [compareUnsigned_slt_zero]; exact decide_eq_true hilt)]
  norm_res_fuel
  rw [parseRLEComments_drop_22_37]
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl0]
  rw [runJvmResFast_iload]; norm_res_fuel; rw [hl2]
  rw [runJvmResFast_aaload_strArr hislt hi_lt]; norm_res_fuel
  rw [← getElem!_pos lines i.toNat hi_lt]
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_checkcast_step (by rfl)]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step stepStatic_stringsEncodeToByteArray]; norm_res_fuel
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_arraylength_byteArray hget1]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
  rfl

private theorem parseRLEComments_step_some_offset
    (f : Nat) (bytesAddr innerAddr outerAddr : Nat)
    (locs1 : Nat → JvmVal) (jh1 jh2 : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 16)
    (h1_8 : locs1 8 = .heapRef bytesAddr)
    (houter2 : jh2.get? outerAddr = some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr]))
    (hpo_step : stepInvokeStatic ⟨44, .heapRef bytesAddr :: [], locs1, jh1, ⟨ar, u64, asc⟩⟩
        "RleLeanKt" "f_Algorithm_parseRLEOffset" "([B)Ljava/lang/Object;" =
      .inl (some ⟨45, .heapRef outerAddr :: [], locs1, jh2, ⟨ar, u64, asc⟩⟩)) :
    runJvmResFast f f_Algorithm_parseRLEComments_prog 43
      (f_Algorithm_parseRLEComments_prog.drop 43) ⟨43, [], locs1, jh1, ⟨ar, u64, asc⟩⟩ =
    runJvmResFast (f - 16) f_Algorithm_parseRLEComments_prog 91
      (f_Algorithm_parseRLEComments_prog.drop 91)
      ⟨91, [], setLocal locs1 9 (.heapRef outerAddr), jh2, ⟨ar, u64, asc⟩⟩ := by
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 16 := ⟨f - 16, by omega⟩
  rw [parseRLEComments_drop_43_59, hf', show f' + 16 - 16 = f' from by omega]
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [h1_8]
  rw [runJvmResFast_invokestatic_step hpo_step]; norm_res_fuel
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [setLocal_self]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [setLocal_self]
  rw [runJvmResFast_checkcast_objArray houter2 (Or.inl rfl)]; norm_res_fuel
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_aaload houter2 (by decide) (by simp)]; norm_res_fuel
  rw [show (#[.boxedInt 1, .heapRef innerAddr] : Array JvmVal)[UInt32.toNat 0] =
    .boxedInt 1 from rfl]
  rw [runJvmResFast_dup_local]; norm_res_fuel
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
  rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
  rw [runJvmResFast_invokevirtual_step stepVirtual_integer_intValue]; norm_res_fuel
  rw [runJvmResFast_tableswitch_local]; norm_res_fuel
  have hts : Jvm.tableswitchTarget 1 0 [59, 91] 228 = 91 := by decide
  rw [hts]

private theorem parseRLEComments_loop
    (m f : Nat) (lines : Array String) (numLines i : UInt32)
    (offsetX offsetY : Int32) (hasOffset : Bool)
    (warns : Algorithm.GrowBuf Algorithm.RLEWarning) (warnsVal : JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hm : numLines.toNat - i.toNat ≤ m)
    (hf : f ≥ (m + 1) * 180)
    (hstat : jh.statics = [])
    (hsz : numLines.toNat ≤ lines.size)
    (hlines31 : lines.size < 2 ^ 31)
    (hutf8 : ∀ k < lines.size, lines[k]!.toUTF8.data.size < 2 ^ 31)
    (hrep : RleWarnRep warns warnsVal)
    (hl0 : locs 0 = .strArr lines)
    (hl1 : locs 1 = .i32 numLines)
    (hl2 : locs 2 = .i32 i)
    (hl3 : locs 3 = .i32 offsetX.toUInt32)
    (hl4 : locs 4 = .i32 offsetY.toUInt32)
    (hl5 : locs 5 = .i32 (if hasOffset then 1 else 0))
    (hl6 : locs 6 = warnsVal) :
    ∃ v st', runJvmResFast f f_Algorithm_parseRLEComments_prog 3
        (f_Algorithm_parseRLEComments_prog.drop 3)
        ⟨3, [], locs, jh, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEComments lines numLines i offsetX offsetY hasOffset warns) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = [] ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  induction m generalizing f i offsetX offsetY hasOffset warns warnsVal locs jh u64 with
  | zero =>
    have hnot : ¬(i < numLines) := by
      intro hlt; have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    rcases parseRLEComments_ret_closed1 (f - 4) warns warnsVal locs jh ar u64 asc hrep (by omega) hl6
      with ⟨v, st', hrun, hdec, hext, hst, har, hasc⟩
    refine ⟨v, st', ?_, ?_, hext, hstat ▸ hst, har, hasc⟩
    · obtain ⟨f', hf'⟩ : ∃ f', f = f' + 4 := ⟨f - 4, by omega⟩
      rw [parseRLEComments_drop_3_7, hf']
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl2]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl1]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
      rw [runJvmResFast_iflt_fallthrough (by
        rw [compareUnsigned_slt_zero]; exact decide_eq_false hnot)]
      norm_res_fuel
      rw [show f' = f - 4 from by omega]
      exact hrun
    · unfold Algorithm.parseRLEComments
      simp only [hnot, ↓reduceDIte]
      exact hdec
  | succ m ih =>
    have hf_succ : f ≥ (m + 1) * 180 + 180 := by
      rw [Nat.succ_mul] at hf; exact hf
    have hf360 : f ≥ 180 := Nat.le_trans (Nat.le_add_left 180 _) hf_succ
    have hf73 : f - 73 ≥ (m + 1) * 180 :=
      Nat.le_sub_of_add_le (Nat.le_trans (Nat.add_le_add_left (by decide) _) hf_succ)
    have hf165 : ∀ f1, f - 41 - 63 ≤ f1 → f1 - 61 ≥ (m + 1) * 180 := by
      intro f1 hf1
      have hsub2 : f - 165 ≥ (m + 1) * 180 :=
        Nat.le_sub_of_add_le (Nat.le_trans (Nat.add_le_add_left (by decide) _) hf_succ)
      clear ih
      exact Nat.le_trans hsub2 (by omega)
    by_cases hilt : i < numLines
    · have hi_lt : i.toNat < lines.size := Nat.lt_of_lt_of_le (UInt32.lt_iff_toNat_lt.mp hilt) hsz
      have hsub : numLines.toNat - (i + 1).toNat ≤ m := by
        have hiu : i.toNat < numLines.toNat := UInt32.lt_iff_toNat_lt.mp hilt
        have h1 : (1 : UInt32).toNat = 1 := rfl
        have hi1 : (i + 1).toNat = i.toNat + 1 := by
          rw [UInt32.toNat_add, h1]
          exact Nat.mod_eq_of_lt (by clear ih; omega)
        clear ih; omega
      let line := lines[i.toNat]!
      let bytes := line.toByteArray
      have hbsz31 : bytes.data.size < 2 ^ 31 := hutf8 i.toNat hi_lt
      have hb_u32 : (UInt32.ofNat bytes.data.size).toNat = bytes.data.size := by
        rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by clear ih; omega)]
      let jh1 := (jh.alloc (.byteArray bytes.data)).2
      let bytesAddr := jh.objects.size
      have hget1 : jh1.get? bytesAddr = some (.byteArray bytes.data) := by
        simp [jh1, bytesAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
      have hext01 : HeapExtends jh jh1 := heapExtends_alloc jh (.byteArray bytes.data)
      let locs1 := setLocal (setLocal locs 7 (.str line)) 8 (.heapRef bytesAddr)
      have hp_3_36 := parseRLEComments_step_head f lines numLines i
        locs jh ar u64 asc hilt hi_lt hlines31 (by clear ih; omega) hl0 hl1 hl2
      dsimp only at hp_3_36
      have h1_0 : locs1 0 = .strArr lines := by simp [locs1, setLocal, hl0]
      have h1_1 : locs1 1 = .i32 numLines := by simp [locs1, setLocal, hl1]
      have h1_2 : locs1 2 = .i32 i := by simp [locs1, setLocal, hl2]
      have h1_3 : locs1 3 = .i32 offsetX.toUInt32 := by simp [locs1, setLocal, hl3]
      have h1_4 : locs1 4 = .i32 offsetY.toUInt32 := by simp [locs1, setLocal, hl4]
      have h1_5 : locs1 5 = .i32 (if hasOffset then 1 else 0) := by simp [locs1, setLocal, hl5]
      have h1_6 : locs1 6 = warnsVal := by simp [locs1, setLocal, hl6]
      have h1_7 : locs1 7 = .str line := by simp [locs1, setLocal]
      have h1_8 : locs1 8 = .heapRef bytesAddr := by simp [locs1]
      by_cases hbz : bytes.data.size = 0
      · have hbu0 : (UInt32.ofNat bytes.data.size == 0) = true := by simp [hbz]
        have hbz_u32 : (bytes.size.toUInt32 != 0) = false := by
          rw [ByteArray.size, hbz]; rfl
        rcases parseRLEComments_header_branch (f - 19) lines numLines i offsetX offsetY
          warns warnsVal line bytesAddr locs1 jh1 ar u64 asc hstat hrep (by clear ih; omega)
          h1_0 h1_1 h1_2 h1_3 h1_4 h1_6 h1_7 h1_8 hget1 with ⟨v, st', hrun, hdec, hext1, hst, har, hasc⟩
        refine ⟨v, st', ?_, ?_, heapExtends_trans hext01 hext1, hst, har, hasc⟩
        · rw [hp_3_36]
          obtain ⟨f', hf'⟩ : ∃ f', f - 18 = f' + 1 := ⟨f - 19, by omega⟩
          rw [hf']
          rw [runJvmResFast_ifeq_branch (beq_iff_eq.mp hbu0)]; norm_res_fuel
          rw [show f' = f - 19 from by omega]
          exact hrun
        · unfold Algorithm.parseRLEComments
          simp only [hilt, ↓reduceDIte]
          have hbsz : ((lines[i.toNat]!).toByteArray.size.toUInt32 != 0) = false := hbz_u32
          simp only [hbsz, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact hdec
      · have hbnz : 0 < bytes.data.size := Nat.pos_of_ne_zero hbz
        have hbu_nz : (UInt32.ofNat bytes.data.size == 0) = false := by
          apply beq_false_of_ne
          intro heq
          have h2 := congrArg UInt32.toNat heq
          rw [hb_u32] at h2
          simp only [UInt32.toNat_zero] at h2
          exact hbz h2
        have hbsz_nz : (bytes.size.toUInt32 != 0) = true := by
          have : bytes.size.toUInt32 = UInt32.ofNat bytes.data.size := rfl
          rw [bne, this, hbu_nz]; rfl
        let b0 := bytes.data[0]
        have hb0_get : bytes.get! 0 = b0 := (byteArray_get_eq_getBang bytes hbnz).symm
        have hp_36_42 : runJvmResFast f f_Algorithm_parseRLEComments_prog 3
            (f_Algorithm_parseRLEComments_prog.drop 3) ⟨3, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast (f - 24) f_Algorithm_parseRLEComments_prog 42
              (.if_icmpne 234 :: f_Algorithm_parseRLEComments_prog.drop 43)
              ⟨42, [.i32 35, .i32 (UInt32.ofBitVec (b0.toBitVec.signExtend 32))], locs1, jh1,
                ⟨ar, u64, asc⟩⟩ := by
          rw [hp_3_36]
          obtain ⟨f', hf'⟩ : ∃ f', f - 18 = f' + 6 := ⟨f - 24, by omega⟩
          rw [hf']
          rw [runJvmResFast_ifeq_fallthrough hbu_nz]; norm_res_fuel
          rw [parseRLEComments_drop_37_43]
          rw [runJvmResFast_aload_local]; norm_res_fuel; rw [setLocal_self]
          rw [runJvmResFast_iconst_local]; norm_res_fuel
          rw [runJvmResFast_baload_byteArray (idx := 0) hget1 (by decide) hbnz]; norm_res_fuel
          rw [runJvmResFast_invokestatic_step stepStatic_ubyteCtor_local]; norm_res_fuel
          rw [runJvmResFast_iconst_local]; norm_res_fuel
          rw [show f' = f - 24 from by omega]
          rfl
        by_cases hb35 : b0 = 35
        · have hs35 : UInt32.ofBitVec (b0.toBitVec.signExtend 32) = 35 :=
            u8Sext_eq_u32 (by simp [hb35]) (by decide)
          cases hpo : Algorithm.parseRLEOffset bytes with
          | none =>
            let outerObj : Jvm.HeapObj AlgExt := Jvm.HeapObj.objArray "java/lang/Object" #[.boxedInt 0]
            let jh2 := (jh1.alloc outerObj).2
            let outerAddr := jh1.objects.size
            have hget2 : jh2.get? outerAddr = some outerObj := by
              simp [jh2, outerAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
            have hext12 : HeapExtends jh1 jh2 := heapExtends_alloc jh1 outerObj
            have hpo_step : stepInvokeStatic ⟨44, .heapRef bytesAddr :: [], locs1, jh1, ⟨ar, u64, asc⟩⟩
                "RleLeanKt" "f_Algorithm_parseRLEOffset" "([B)Ljava/lang/Object;" =
                .inl (some ⟨45, .heapRef outerAddr :: [], locs1, jh2, ⟨ar, u64, asc⟩⟩) := by
              rw [stepStatic_parseRLEOffset_heap_local hget1]
              have hbs' : (⟨bytes.data⟩ : ByteArray) = bytes := rfl
              rw [hbs', hpo]; rfl
            rcases parseRLEComments_none_offset (f - 25) lines numLines i offsetX offsetY hasOffset
              warnsVal bytesAddr outerAddr locs1 jh1 jh2 ar u64 asc (by omega)
              h1_0 h1_1 h1_2 h1_3 h1_4 h1_5 h1_6 h1_8 hget2
              parseRLEComments_drop_43_59 parseRLEComments_drop_59_91 hpo_step with
              ⟨locs2, hrun43, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6⟩
            have hjh2_stat : jh2.statics = [] := by simp [jh2, jh1, Jvm.JvmHeap.alloc, hstat]
            rcases ih (f - 73) (i + 1) offsetX offsetY hasOffset warns warnsVal locs2 jh2 u64
              hsub hf73 hjh2_stat hrep h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6
              with ⟨v, st', hrun, hdec, hext2, hst, har, hasc⟩
            refine ⟨v, st', ?_, ?_, heapExtends_trans (heapExtends_trans hext01 hext12) hext2,
              hst, har, hasc⟩
            · rw [hp_36_42]
              obtain ⟨f', hf'⟩ : ∃ f', f - 24 = f' + 1 := ⟨f - 25, by clear ih; omega⟩
              rw [hf']
              rw [runJvmResFast_if_icmpne_fallthrough hs35]; norm_res_fuel
              rw [show f' = f - 25 from by clear ih; omega]
              rw [hrun43, show f - 25 - 48 = f - 73 from by clear ih; omega]
              exact hrun
            · unfold Algorithm.parseRLEComments
              have hbs : (lines[i.toNat]!).toByteArray = bytes := rfl
              simp only [hilt, ↓reduceDIte, hbs, hbsz_nz, hb0_get, hb35, beq_self_eq_true, Bool.and_self,
                ↓reduceIte, hpo]
              exact hdec
          | some c =>
            let innerObj : Jvm.HeapObj AlgExt := Jvm.HeapObj.objArray "java/lang/Object"
              #[.boxedInt 0, .boxedInt c.x.toUInt32, .null, .null, .null, .boxedInt c.y.toUInt32]
            let jh1a := (jh1.alloc innerObj).2
            let innerAddr := jh1.objects.size
            let outerObj : Jvm.HeapObj AlgExt := Jvm.HeapObj.objArray "java/lang/Object"
              #[.boxedInt 1, .heapRef innerAddr]
            let jh2 := (jh1a.alloc outerObj).2
            let outerAddr := jh1a.objects.size
            have hinner2 : jh2.get? innerAddr = some innerObj := by
              have h1a : jh1a.get? innerAddr = some innerObj := by
                simp [jh1a, innerAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
              exact heapExtends_alloc jh1a outerObj innerAddr innerObj h1a
            have houter2 : jh2.get? outerAddr = some outerObj := by
              simp [jh2, outerAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
            have hext12 : HeapExtends jh1 jh2 :=
              heapExtends_trans (heapExtends_alloc jh1 innerObj) (heapExtends_alloc jh1a outerObj)
            have hpo_step : stepInvokeStatic ⟨44, .heapRef bytesAddr :: [], locs1, jh1, ⟨ar, u64, asc⟩⟩
                "RleLeanKt" "f_Algorithm_parseRLEOffset" "([B)Ljava/lang/Object;" =
                .inl (some ⟨45, .heapRef outerAddr :: [], locs1, jh2, ⟨ar, u64, asc⟩⟩) := by
              rw [stepStatic_parseRLEOffset_heap_local hget1]
              have hbs' : (⟨bytes.data⟩ : ByteArray) = bytes := rfl
              rw [hbs', hpo]; rfl
            let locs1a := setLocal locs1 9 (.heapRef outerAddr)
            rcases parseRLEComments_dupOffset_branch (f - 41) i hasOffset c warns warnsVal
              outerAddr innerAddr locs1a jh2 ar u64 asc hrep (by omega)
              (by simp [locs1a, setLocal, h1_2]) (by simp [locs1a, setLocal, h1_5])
              (by simp [locs1a, setLocal, h1_6]) (by simp [locs1a])
              houter2 hinner2 with
              ⟨f1, warnsVal', locs1b, jh3, hf1_ge, hf1_le, hrep', hext23, hst23,
                hrun91, hb0, hb1, hb2, _, hb11, hb12⟩
            have hinner3 : jh3.get? innerAddr = some innerObj := hext23 innerAddr innerObj hinner2
            rcases parseRLEComments_finish_some_offset f1 c i warnsVal' innerAddr locs1b jh3
              ar u64 asc (by omega) hb2 hb11 hb12 hinner3 with
              ⟨locs2, hrun159, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6⟩
            have hjh3_stat : jh3.statics = [] := by rw [hst23]; exact hstat
            rcases ih (f1 - 61) (i + 1) c.x c.y true
              (if hasOffset then warns.push (.duplicateOffset (i + 1) c.x c.y) else warns)
              warnsVal' locs2 jh3 u64 hsub (hf165 f1 hf1_ge) hjh3_stat hrep'
              (by rw [h2_0, hb0]; simp [locs1a, setLocal, h1_0])
              (by rw [h2_1, hb1]; simp [locs1a, setLocal, h1_1])
              h2_2 h2_3 h2_4 h2_5 h2_6 with ⟨v, st', hrun, hdec, hext3, hst, har, hasc⟩
            refine ⟨v, st', ?_, ?_,
              heapExtends_trans (heapExtends_trans hext01 (heapExtends_trans hext12 hext23)) hext3,
              hst, har, hasc⟩
            · rw [hp_36_42]
              obtain ⟨f', hf'⟩ : ∃ f', f - 24 = f' + 1 := ⟨f - 25, by clear ih; omega⟩
              rw [hf']
              rw [runJvmResFast_if_icmpne_fallthrough hs35]; norm_res_fuel
              rw [show f' = f - 25 from by clear ih; omega]
              rw [parseRLEComments_step_some_offset (f - 25) bytesAddr innerAddr outerAddr locs1 jh1 jh2
                ar u64 asc (by clear ih; omega) h1_8 houter2 hpo_step]
              rw [show f - 25 - 16 = f - 41 from by clear ih; omega]
              rw [hrun91, hrun159]
              exact hrun
            · unfold Algorithm.parseRLEComments
              have hbs : (lines[i.toNat]!).toByteArray = bytes := rfl
              simp only [hilt, ↓reduceDIte, hbs, hbsz_nz, hb0_get, hb35, beq_self_eq_true, Bool.and_self,
                ↓reduceIte, hpo]
              exact hdec
        · have hne35 : b0.toNat ≠ 35 := fun he => hb35 (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq he))
          have hsne35 : (UInt32.ofBitVec (b0.toBitVec.signExtend 32) == 35) = false :=
            u8Sext_beq_false b0 35 hne35 (by decide)
          have hb35f : (b0 == 35) = false := beq_false_of_ne hb35
          rcases parseRLEComments_header_branch (f - 25) lines numLines i offsetX offsetY
            warns warnsVal line bytesAddr locs1 jh1 ar u64 asc hstat hrep (by clear ih; omega)
            h1_0 h1_1 h1_2 h1_3 h1_4 h1_6 h1_7 h1_8 hget1 with ⟨v, st', hrun, hdec, hext1, hst, har, hasc⟩
          refine ⟨v, st', ?_, ?_, heapExtends_trans hext01 hext1, hst, har, hasc⟩
          · rw [hp_36_42]
            obtain ⟨f', hf'⟩ : ∃ f', f - 24 = f' + 1 := ⟨f - 25, by omega⟩
            rw [hf']
            rw [runJvmResFast_if_icmpne_branch hsne35]; norm_res_fuel
            rw [show f' = f - 25 from by omega]
            exact hrun
          · unfold Algorithm.parseRLEComments
            simp only [hilt, ↓reduceDIte]
            have hb35f' : ((lines[i.toNat]!).toByteArray.get! 0 == 35) = false := by
              change (bytes.get! 0 == 35) = false; rw [hb0_get]; exact hb35f
            simp only [hb35f', Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact hdec
    · have hnot : ¬(i < numLines) := hilt
      rcases parseRLEComments_ret_closed1 (f - 4) warns warnsVal locs jh ar u64 asc hrep
        (by clear ih; omega) hl6
        with ⟨v, st', hrun, hdec, hext, hst, har, hasc⟩
      refine ⟨v, st', ?_, ?_, hext, hstat ▸ hst, har, hasc⟩
      · obtain ⟨f', hf'⟩ : ∃ f', f = f' + 4 := ⟨f - 4, by clear ih; omega⟩
        rw [parseRLEComments_drop_3_7, hf']
        rw [runJvmResFast_iload]; norm_res_fuel; rw [hl2]
        rw [runJvmResFast_iload]; norm_res_fuel; rw [hl1]
        rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
        rw [runJvmResFast_iflt_fallthrough (by
          rw [compareUnsigned_slt_zero]; exact decide_eq_false hnot)]
        norm_res_fuel
        rw [show f' = f - 4 from by clear ih; omega]
        exact hrun
      · unfold Algorithm.parseRLEComments
        simp only [hnot, ↓reduceDIte]
        exact hdec

theorem parseRLEComments_equiv
    (lines : Array String) (numLines i : UInt32) (offsetX offsetY : Int32) (hasOffset : Bool)
    (warns : Algorithm.GrowBuf Algorithm.RLEWarning) (warnsVal : JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hstat : jh.statics = [])
    (hsz : numLines.toNat ≤ lines.size)
    (hlines31 : lines.size < 2 ^ 31)
    (hutf8 : ∀ k < lines.size, lines[k]!.toUTF8.data.size < 2 ^ 31)
    (hrep : RleWarnRep warns warnsVal)
    (hl0 : locs 0 = .strArr lines)
    (hl1 : locs 1 = .i32 numLines)
    (hl2 : locs 2 = .i32 i)
    (hl3 : locs 3 = .i32 offsetX.toUInt32)
    (hl4 : locs 4 = .i32 offsetY.toUInt32)
    (hl5 : locs 5 = .i32 (if hasOffset then 1 else 0))
    (hl6 : locs 6 = warnsVal) :
    ∃ f v st', runJvmRes f f_Algorithm_parseRLEComments_prog ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEComments lines numLines i offsetX offsetY hasOffset warns) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = [] ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  let m := numLines.toNat - i.toNat
  let f := (m + 1) * 180 + 3
  rcases parseRLEComments_loop m (f - 3) lines numLines i offsetX offsetY hasOffset warns warnsVal
    locs jh ar u64 asc (Nat.le_refl _) (by omega) hstat hsz hlines31 hutf8 hrep
    hl0 hl1 hl2 hl3 hl4 hl5 hl6 with ⟨v, st', hrun, hdec, hext, hst, har, hasc⟩
  refine ⟨f, v, st', ?_, hdec, hext, hst, har, hasc⟩
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  have h0 : f_Algorithm_parseRLEComments_prog =
      .aload 0 :: .ldcStr "lines" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      f_Algorithm_parseRLEComments_prog.drop 3 := by
    conv => lhs; rw [← List.drop_zero (l := f_Algorithm_parseRLEComments_prog)]
    drop_prefix 3
  rw [h0]
  split_res_fuel 3
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl0]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam_local rfl)]; norm_res_fuel
  exact hrun

end ParseRLEComments

/-! #### 3. `f_Algorithm_deserializeRLE_prog` -/

section DeserializeRLE

theorem deserializeRLE_equiv
    (lines : Array String) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hstat : jh.statics = [])
    (hl0 : locs 0 = .strArr lines) :
    ∃ f v st', runJvmRes f f_Algorithm_deserializeRLE_prog ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v = some (Algorithm.deserializeRLE lines) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = [] ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  let numLines := lines.size.toUInt32
  have h0_9 : f_Algorithm_deserializeRLE_prog =
      .aload 0 :: .ldcStr "lines" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 0 :: .arraylength :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .istore 1 :: .iload 1 :: .ifeq 21 :: f_Algorithm_deserializeRLE_prog.drop 9 := by
    conv => lhs; rw [← List.drop_zero (l := f_Algorithm_deserializeRLE_prog)]
    drop_prefix 9
  let locs1 := setLocal locs 1 (.i32 numLines)
  by_cases h0 : numLines == 0
  · let res := Algorithm.RLEResult.mk .emptyFile #[.emptyFile] Algorithm.noCells
    let enc := encodeRLEResult jh u64 res
    let stFinal : JvmState := ⟨22, [enc.1], locs1, enc.2.1, ⟨ar, enc.2.2, asc⟩⟩
    have h21 : f_Algorithm_deserializeRLE_prog.drop 21 =
        .invokestatic "RleLeanKt" "f_Algorithm_deserializeRLE___closed__1"
          "()Lcom/alexvanyo/composelife/model/RLEResult;" ::
        .areturn :: f_Algorithm_deserializeRLE_prog.drop 23 := by drop_prefix 2
    refine ⟨15, enc.1, stFinal, ?_, ?_, encodeRLEResult_heapExtends jh u64 res,
      by rw [encodeRLEResult_statics]; exact hstat, rfl, rfl⟩
    · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      rw [h0_9]
      split_res_fuel 9
      rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl0]
      rw [runJvmResFast_ldcStr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam_local rfl)]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl0]
      rw [runJvmResFast_arraylength_strArr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_ifeq_branch (beq_iff_eq.mp h0)]; norm_res_fuel
      conv => lhs; arg 4; rw [← h0_9, h21]
      rw [runJvmResFast_invokestatic_step stepStatic_deserializeRLE_closed1_local]; norm_res_fuel
      rw [runJvmResFast_areturn_local]
      rfl
    · have hdes : Algorithm.deserializeRLE lines = res := by
        unfold Algorithm.deserializeRLE
        have : lines.size.toUInt32 = numLines := rfl
        simp only [this, h0, ↓reduceIte, res]
      rw [hdes]
      exact decodeRLEResult_encode_proj 22 [enc.1] locs1 jh ar u64 asc res
  · have h0f : (numLines == 0) = false := Bool.eq_false_iff.mpr h0
    let res := Algorithm.parseRLEComments lines numLines 0 0 0 false Algorithm.GrowBuf.empty
    let enc := encodeRLEResult jh u64 res
    let locs2 := setLocal locs1 2 (.ext (.strGrowBuf Algorithm.GrowBuf.empty))
    let stFinal : JvmState := ⟨20, [enc.1], locs2, enc.2.1, ⟨ar, enc.2.2, asc⟩⟩
    have h9 : f_Algorithm_deserializeRLE_prog.drop 9 =
        .aconstNull ::
        .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_empty___redArg"
          "(Ljava/lang/Object;)Ljava/lang/Object;" ::
        .astore 2 :: .aload 0 :: .iload 1 :: .iconst 0 :: .iconst 0 :: .iconst 0 :: .iconst 0 ::
        .aload 2 ::
        .invokestatic "RleLeanKt" "f_Algorithm_parseRLEComments--R0mByA"
          "([Ljava/lang/Object;IIIIZLjava/lang/Object;)Lcom/alexvanyo/composelife/model/RLEResult;" ::
        .areturn :: f_Algorithm_deserializeRLE_prog.drop 21 := by drop_prefix 12
    have hstep_c : stepInvokeStatic ⟨19, .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: .i32 0 ::
        .i32 0 :: .i32 0 :: .i32 0 :: .i32 numLines :: .strArr lines :: [],
        locs2, jh, ⟨ar, u64, asc⟩⟩
        "RleLeanKt" "f_Algorithm_parseRLEComments--R0mByA"
        "([Ljava/lang/Object;IIIIZLjava/lang/Object;)Lcom/alexvanyo/composelife/model/RLEResult;" =
        .inl (some ⟨20, enc.1 :: [], locs2, enc.2.1, ⟨ar, enc.2.2, asc⟩⟩) := rfl
    refine ⟨25, enc.1, stFinal, ?_, ?_, encodeRLEResult_heapExtends jh u64 res,
      by rw [encodeRLEResult_statics]; exact hstat, rfl, rfl⟩
    · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      rw [h0_9]
      split_res_fuel 9
      rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl0]
      rw [runJvmResFast_ldcStr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam_local rfl)]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl0]
      rw [runJvmResFast_arraylength_strArr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_ifeq_fallthrough h0f]; norm_res_fuel
      rw [h9]
      rw [runJvmResFast_aconstNull]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step stepStatic_growBufEmpty_rle_local]; norm_res_fuel
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl0]
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_invokestatic_step hstep_c]; norm_res_fuel
      rw [runJvmResFast_areturn_local]
    · have hdes : Algorithm.deserializeRLE lines = res := by
        unfold Algorithm.deserializeRLE
        have : lines.size.toUInt32 = numLines := rfl
        simp only [this, h0f, Bool.false_eq_true, ↓reduceIte, res]
      rw [hdes]
      exact decodeRLEResult_encode_proj 20 [enc.1] locs2 jh ar u64 asc res

end DeserializeRLE

/-! #### 4. `f_Algorithm_expandRuns_prog` -/

section ExpandRuns
set_option maxRecDepth 2048

private theorem stepVirtual_uintUnbox {pc : Nat} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .boxedUInt v :: stk, locs, jh, hp⟩
      "kotlin/UInt" "unbox-impl" "()I" =
      .inl (some ⟨pc + 1, .i32 v :: stk, locs, jh, hp⟩) := rfl

private theorem runJvmResFast_land {f pc : Nat} {prog rest : List JvmInstr} {a b : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.land :: rest) ⟨pc, .i64 b :: .i64 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i64 (a &&& b) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_lshl_32 {f pc : Nat} {prog rest : List JvmInstr} {a : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.lshl :: rest) ⟨pc, .i32 32 :: .i64 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i64 (a <<< 32) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_ladd {f pc : Nat} {prog rest : List JvmInstr} {a b : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.ladd :: rest) ⟨pc, .i64 b :: .i64 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i64 (a + b) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_i2l_mask {f pc : Nat} {prog rest : List JvmInstr} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 3) prog pc (.i2l :: .lconst 4294967295 :: .land :: rest)
        ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 3) rest ⟨pc + 3, .i64 v.toUInt64 :: stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp only [runJvmResFast]

private theorem runJvmResFast_instanceof_pair {f pc : Nat} {prog rest : List JvmInstr}
    {a b : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.instanceof "kotlin/Pair" :: rest)
        ⟨pc, .pair a b :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 1 :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.instanceof "kotlin/Pair")
      ⟨pc, .pair a b :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 1 :: stk, locs, jh, hp⟩) := rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

private theorem runJvmResFast_checkcast_pair {f pc : Nat} {prog rest : List JvmInstr}
    {a b : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.checkcast "kotlin/Pair" :: rest)
        ⟨pc, .pair a b :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .pair a b :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.checkcast "kotlin/Pair")
      ⟨pc, .pair a b :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .pair a b :: stk, locs, jh, hp⟩) := rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

private theorem stepStatic_ulongCtor_local {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩ "kotlin/ULong" "constructor-impl" "(J)J" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

private theorem stepStatic_expandRuns_closed0_local {pc : Nat} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩ "RleLeanKt"
      "f_Algorithm_expandRuns___closed__0" "()Lkotlin/Pair;" =
      .inl (some ⟨pc + 1, .pair (.boxedUInt 0) (.boxedUInt 0) :: stk, locs, jh, hp⟩) := rfl

private theorem int32_add_toInt32_toUInt32 (x : Int32) (k : UInt32) :
    (x + k.toInt32).toUInt32 = x.toUInt32 + k := by
  apply UInt32.eq_of_toBitVec_eq; rfl

private theorem cellBits_eq_alu (x : Int32) (k : UInt32) (y : Int32) :
    ((((x.toUInt32.toUInt64 + k.toUInt64) % 4294967296) <<< 32) +
      (y.toUInt32.toUInt64 &&& 4294967295)) =
      Algorithm.cellBits (x + k.toInt32, y) := by
  have hx : (x.toUInt32.toUInt64 + k.toUInt64) % 4294967296 = (x.toUInt32 + k).toUInt64 := by
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    change ((x.toUInt32.toUInt64 + k.toUInt64) % 4294967296).toNat = (x.toUInt32 + k).toUInt64.toNat
    simp only [UInt64.toNat_mod, UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_add]
    have hpow : (4294967296 : UInt64).toNat = 2 ^ 32 := by decide
    have hdvd : (2 ^ 32 : Nat) ∣ 2 ^ 64 := ⟨2 ^ 32, by decide⟩
    rw [hpow, Nat.mod_mod_of_dvd _ hdvd]
  rw [hx]
  simp only [Algorithm.cellBits, Algorithm.cellKey, int32_add_toInt32_toUInt32]

private theorem expandRuns_fuel_ge {f m a d : Nat} (hf : f ≥ (m + 1) * 140 + 140)
    (hd : a + d ≤ 140) : f - a ≥ d := by omega

private theorem expandRuns_fuel_step {f m a : Nat} (hf : f ≥ (m + 1) * 140 + 140)
    (ha : a < 140) : f - a = (f - (a + 1)) + 1 := by omega

private theorem expandRuns_fuel_rem {f m a b : Nat} (hf : f ≥ (m + 1) * 140 + 140)
    (hab : a + b ≤ 140) : f - a - b ≥ (m + 1) * 140 := by omega

private theorem expandRuns_measure_next_j {numRuns j k : UInt32} (hj : j < numRuns) :
    (numRuns.toNat - (j + 1).toNat) * 2 ^ 33 + 2 ^ 32 <
      (numRuns.toNat - j.toNat) * 2 ^ 33 + (2 ^ 32 - k.toNat) := by
  have hk0 := UInt32.toNat_lt k
  have hj1 := UInt32.lt_iff_toNat_lt.mp hj
  have hnum := UInt32.toNat_lt numRuns
  have hj2 : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt32.toNat_add, UInt32.toNat_one]; omega
  rw [hj2]
  have hsub : numRuns.toNat - j.toNat = (numRuns.toNat - (j.toNat + 1)) + 1 := by omega
  rw [hsub, Nat.add_mul]
  omega

private theorem expandRuns_measure_next_k {numRuns j k count : UInt32} (hk : k < count) :
    (numRuns.toNat - j.toNat) * 2 ^ 33 + (2 ^ 32 - (k + 1).toNat) <
      (numRuns.toNat - j.toNat) * 2 ^ 33 + (2 ^ 32 - k.toNat) := by
  have hk1 := UInt32.lt_iff_toNat_lt.mp hk
  have hc := UInt32.toNat_lt count
  have hk2 : (k + 1).toNat = k.toNat + 1 := by
    rw [UInt32.toNat_add, UInt32.toNat_one]; omega
  rw [hk2]
  omega

private theorem expandRuns_drop_0_6 : f_Algorithm_expandRuns_prog.drop 0 =
    .aload 0 :: .ldcStr "runs" ::
    .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
      "(Ljava/lang/Object;Ljava/lang/String;)V" ::
    .aload 7 :: .ldcStr "cells" ::
    .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
      "(Ljava/lang/Object;Ljava/lang/String;)V" ::
    f_Algorithm_expandRuns_prog.drop 6 := by
  drop_prefix 6

private theorem expandRuns_drop_6_12 : f_Algorithm_expandRuns_prog.drop 6 =
    .invokestatic "RleLeanKt" "f_Algorithm_expandRuns___closed__0" "()Lkotlin/Pair;" ::
    .astore 8 :: .iload 2 :: .iload 1 ::
    .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" ::
    .iflt 14 :: f_Algorithm_expandRuns_prog.drop 12 := by
  drop_prefix 6

private theorem expandRuns_drop_12_14 : f_Algorithm_expandRuns_prog.drop 12 =
    .aload 7 :: .areturn :: f_Algorithm_expandRuns_prog.drop 14 := by
  drop_prefix 2

private theorem expandRuns_drop_14_25 : f_Algorithm_expandRuns_prog.drop 14 =
    .aload 0 :: .iload 2 :: .aaload :: .astore 9 ::
    .aload 9 :: .instanceof "kotlin/Pair" :: .ifeq 25 ::
    .aload 9 :: .checkcast "kotlin/Pair" ::
    .invokevirtual "kotlin/Pair" "getFirst" "()Ljava/lang/Object;" ::
    .goto 32 :: f_Algorithm_expandRuns_prog.drop 25 := by
  drop_prefix 11

private theorem expandRuns_drop_32_40 : f_Algorithm_expandRuns_prog.drop 32 =
    .astore 10 :: .aload 9 :: .instanceof "kotlin/Pair" :: .ifeq 40 ::
    .aload 9 :: .checkcast "kotlin/Pair" ::
    .invokevirtual "kotlin/Pair" "getSecond" "()Ljava/lang/Object;" ::
    .goto 44 :: f_Algorithm_expandRuns_prog.drop 40 := by
  drop_prefix 8

private theorem expandRuns_drop_44_57 : f_Algorithm_expandRuns_prog.drop 44 =
    .astore 11 :: .aload 10 :: .astore 13 :: .iconst 0 :: .istore 14 ::
    .aload 13 :: .instanceof "java/lang/Integer" :: .ifeq 57 ::
    .aload 13 :: .checkcast "java/lang/Number" ::
    .invokevirtual "java/lang/Number" "intValue" "()I" ::
    .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
    .goto 63 :: f_Algorithm_expandRuns_prog.drop 57 := by
  drop_prefix 13

private theorem expandRuns_drop_57_67 : f_Algorithm_expandRuns_prog.drop 57 =
    .aload 13 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
    .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
      "(Ljava/lang/Object;Ljava/lang/String;)V" ::
    .aload 13 :: .checkcast "kotlin/UInt" ::
    .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
    .istore 12 :: .iload 12 :: .iconst 2 :: .if_icmpeq 199 ::
    f_Algorithm_expandRuns_prog.drop 67 := by
  drop_prefix 10

private theorem expandRuns_drop_67_79 : f_Algorithm_expandRuns_prog.drop 67 =
    .aload 10 :: .astore 14 :: .iconst 0 :: .istore 15 ::
    .aload 14 :: .instanceof "java/lang/Integer" :: .ifeq 79 ::
    .aload 14 :: .checkcast "java/lang/Number" ::
    .invokevirtual "java/lang/Number" "intValue" "()I" ::
    .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
    .goto 85 :: f_Algorithm_expandRuns_prog.drop 79 := by
  drop_prefix 12

private theorem expandRuns_drop_79_89 : f_Algorithm_expandRuns_prog.drop 79 =
    .aload 14 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
    .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
      "(Ljava/lang/Object;Ljava/lang/String;)V" ::
    .aload 14 :: .checkcast "kotlin/UInt" ::
    .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
    .istore 13 :: .iload 13 :: .iconst 1 :: .if_icmpeq 144 ::
    f_Algorithm_expandRuns_prog.drop 89 := by
  drop_prefix 10

private theorem expandRuns_drop_89_101 : f_Algorithm_expandRuns_prog.drop 89 =
    .aload 11 :: .astore 15 :: .iconst 0 :: .istore 16 ::
    .aload 15 :: .instanceof "java/lang/Integer" :: .ifeq 101 ::
    .aload 15 :: .checkcast "java/lang/Number" ::
    .invokevirtual "java/lang/Number" "intValue" "()I" ::
    .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
    .goto 107 :: f_Algorithm_expandRuns_prog.drop 101 := by
  drop_prefix 12

private theorem expandRuns_drop_101_144 : f_Algorithm_expandRuns_prog.drop 101 =
    .aload 15 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
    .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
      "(Ljava/lang/Object;Ljava/lang/String;)V" ::
    .aload 15 :: .checkcast "kotlin/UInt" ::
    .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
    .istore 14 :: .aload 0 :: .astore 15 :: .iload 1 :: .istore 16 ::
    .iload 2 :: .iconst 1 :: .iadd :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
    .istore 17 :: .iload 6 :: .istore 18 :: .iload 5 :: .iload 14 :: .iadd :: .istore 19 ::
    .iload 6 :: .istore 20 :: .aload 7 :: .astore 21 ::
    .aload 15 :: .astore 0 :: .iload 16 :: .istore 1 :: .iload 17 :: .istore 2 ::
    .iconst 0 :: .istore 3 :: .iload 18 :: .istore 4 :: .iload 19 :: .istore 5 ::
    .iload 20 :: .istore 6 :: .aload 21 :: .astore 7 :: .goto 6 ::
    f_Algorithm_expandRuns_prog.drop 144 := by
  drop_prefix 43

private theorem expandRuns_drop_144_156 : f_Algorithm_expandRuns_prog.drop 144 =
    .aload 11 :: .astore 15 :: .iconst 0 :: .istore 16 ::
    .aload 15 :: .instanceof "java/lang/Integer" :: .ifeq 156 ::
    .aload 15 :: .checkcast "java/lang/Number" ::
    .invokevirtual "java/lang/Number" "intValue" "()I" ::
    .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
    .goto 162 :: f_Algorithm_expandRuns_prog.drop 156 := by
  drop_prefix 12

private theorem expandRuns_drop_156_199 : f_Algorithm_expandRuns_prog.drop 156 =
    .aload 15 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
    .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
      "(Ljava/lang/Object;Ljava/lang/String;)V" ::
    .aload 15 :: .checkcast "kotlin/UInt" ::
    .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
    .istore 14 :: .aload 0 :: .astore 15 :: .iload 1 :: .istore 16 ::
    .iload 2 :: .iconst 1 :: .iadd :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
    .istore 17 :: .iload 4 :: .iload 14 :: .iadd :: .istore 18 :: .iload 5 :: .istore 19 ::
    .iload 6 :: .istore 20 :: .aload 7 :: .astore 21 ::
    .aload 15 :: .astore 0 :: .iload 16 :: .istore 1 :: .iload 17 :: .istore 2 ::
    .iconst 0 :: .istore 3 :: .iload 18 :: .istore 4 :: .iload 19 :: .istore 5 ::
    .iload 20 :: .istore 6 :: .aload 21 :: .astore 7 :: .goto 6 ::
    f_Algorithm_expandRuns_prog.drop 199 := by
  drop_prefix 43

private theorem expandRuns_drop_199_211 : f_Algorithm_expandRuns_prog.drop 199 =
    .aload 11 :: .astore 14 :: .iconst 0 :: .istore 15 ::
    .aload 14 :: .instanceof "java/lang/Integer" :: .ifeq 211 ::
    .aload 14 :: .checkcast "java/lang/Number" ::
    .invokevirtual "java/lang/Number" "intValue" "()I" ::
    .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
    .goto 217 :: f_Algorithm_expandRuns_prog.drop 211 := by
  drop_prefix 12

private theorem expandRuns_drop_211_222 : f_Algorithm_expandRuns_prog.drop 211 =
    .aload 14 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
    .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
      "(Ljava/lang/Object;Ljava/lang/String;)V" ::
    .aload 14 :: .checkcast "kotlin/UInt" ::
    .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
    .istore 13 :: .iload 3 :: .iload 13 ::
    .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" ::
    .iflt 277 :: f_Algorithm_expandRuns_prog.drop 222 := by
  drop_prefix 11

private theorem expandRuns_drop_222_234 : f_Algorithm_expandRuns_prog.drop 222 =
    .aload 11 :: .astore 15 :: .iconst 0 :: .istore 16 ::
    .aload 15 :: .instanceof "java/lang/Integer" :: .ifeq 234 ::
    .aload 15 :: .checkcast "java/lang/Number" ::
    .invokevirtual "java/lang/Number" "intValue" "()I" ::
    .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
    .goto 240 :: f_Algorithm_expandRuns_prog.drop 234 := by
  drop_prefix 12

private theorem expandRuns_drop_234_277 : f_Algorithm_expandRuns_prog.drop 234 =
    .aload 15 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
    .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
      "(Ljava/lang/Object;Ljava/lang/String;)V" ::
    .aload 15 :: .checkcast "kotlin/UInt" ::
    .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
    .istore 14 :: .aload 0 :: .astore 15 :: .iload 1 :: .istore 16 ::
    .iload 2 :: .iconst 1 :: .iadd :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
    .istore 17 :: .iload 4 :: .iload 14 :: .iadd :: .istore 18 :: .iload 5 :: .istore 19 ::
    .iload 6 :: .istore 20 :: .aload 7 :: .astore 21 ::
    .aload 15 :: .astore 0 :: .iload 16 :: .istore 1 :: .iload 17 :: .istore 2 ::
    .iconst 0 :: .istore 3 :: .iload 18 :: .istore 4 :: .iload 19 :: .istore 5 ::
    .iload 20 :: .istore 6 :: .aload 21 :: .astore 7 :: .goto 6 ::
    f_Algorithm_expandRuns_prog.drop 277 := by
  drop_prefix 43

private theorem expandRuns_drop_277_338 : f_Algorithm_expandRuns_prog.drop 277 =
    .iload 3 :: .iconst 1 :: .iadd :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
    .istore 14 :: .aload 7 :: .nop :: .iload 4 :: .iload 3 :: .iadd ::
    .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
    .i2l :: .lconst 4294967295 :: .land ::
    .invokestatic "kotlin/ULong" "constructor-impl" "(J)J" ::
    .iconst 32 :: .lshl ::
    .invokestatic "kotlin/ULong" "constructor-impl" "(J)J" :: .nop ::
    .iload 5 :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
    .i2l :: .lconst 4294967295 :: .land ::
    .invokestatic "kotlin/ULong" "constructor-impl" "(J)J" ::
    .lconst 4294967295 :: .land ::
    .invokestatic "kotlin/ULong" "constructor-impl" "(J)J" ::
    .ladd :: .invokestatic "kotlin/ULong" "constructor-impl" "(J)J" ::
    .invokestatic "RleLeanKt" "f_Algorithm_U64Buf_push-3yFGk1Y" "([JJ)[J" ::
    .astore 15 :: .aload 0 :: .astore 16 :: .iload 1 :: .istore 17 :: .iload 2 :: .istore 18 ::
    .iload 4 :: .istore 19 :: .iload 5 :: .istore 20 :: .iload 6 :: .istore 21 ::
    .aload 16 :: .astore 0 :: .iload 17 :: .istore 1 :: .iload 18 :: .istore 2 ::
    .iload 14 :: .istore 3 :: .iload 19 :: .istore 4 :: .iload 20 :: .istore 5 ::
    .iload 21 :: .istore 6 :: .aload 15 :: .astore 7 :: .goto 6 ::
    f_Algorithm_expandRuns_prog.drop 338 := by
  drop_prefix 61

private theorem expandRuns_step_head
    (f : Nat) (runs : Array (UInt32 × UInt32)) (numRuns j k : UInt32) (x y startX : Int32)
    (cId runsAddr : Nat) (cls : String) (elems : Array JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 42) (hj : j < numRuns) (hnum : numRuns.toNat ≤ runs.size) (hruns31 : runs.size < 2 ^ 31)
    (hruns : jh.get? runsAddr = some (.objArray cls elems)) (hsz : elems.size = runs.size)
    (helems : ∀ idx (hlt : idx < runs.size),
      elems[idx]'(hsz ▸ hlt) = .pair (.boxedUInt runs[idx].1) (.boxedUInt runs[idx].2))
    (hl0 : locs 0 = .heapRef runsAddr) (hl1 : locs 1 = .i32 numRuns) (hl2 : locs 2 = .i32 j)
    (hl3 : locs 3 = .i32 k) (hl4 : locs 4 = .i32 x.toUInt32) (hl5 : locs 5 = .i32 y.toUInt32)
    (hl6 : locs 6 = .i32 startX.toUInt32) (hl7 : locs 7 = .ext (.u64Ref cId)) :
    let tag := (runs[j.toNat]!).1
    let count := (runs[j.toNat]!).2
    ∃ locs1,
      runJvmResFast f f_Algorithm_expandRuns_prog 6 (f_Algorithm_expandRuns_prog.drop 6)
        ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 42) f_Algorithm_expandRuns_prog 66
        (.if_icmpeq 199 :: f_Algorithm_expandRuns_prog.drop 67)
        ⟨66, [.i32 2, .i32 tag], locs1, jh, ⟨ar, u64, asc⟩⟩ ∧
      locs1 0 = .heapRef runsAddr ∧ locs1 1 = .i32 numRuns ∧ locs1 2 = .i32 j ∧
      locs1 3 = .i32 k ∧ locs1 4 = .i32 x.toUInt32 ∧ locs1 5 = .i32 y.toUInt32 ∧
      locs1 6 = .i32 startX.toUInt32 ∧ locs1 7 = .ext (.u64Ref cId) ∧
      locs1 10 = .boxedUInt tag ∧ locs1 11 = .boxedUInt count := by
  have hj_lt : j.toNat < runs.size := Nat.lt_of_lt_of_le (UInt32.lt_iff_toNat_lt.mp hj) hnum
  have hel_lt : j.toNat < elems.size := hsz ▸ hj_lt
  have hgetBang : runs[j.toNat]! = runs[j.toNat] := getElem!_pos runs j.toNat hj_lt
  have hpair : elems[j.toNat] = .pair (.boxedUInt (runs[j.toNat]!).1) (.boxedUInt (runs[j.toNat]!).2) := by
    rw [hgetBang]; exact helems j.toNat hj_lt
  have hslt : j.toBitVec.slt 0#32 = false :=
    u32_slt_zero_of_lt_2_31 (Nat.lt_trans hj_lt hruns31)
  have hcmp : (if j == numRuns then (0 : UInt32) else if j < numRuns then 4294967295 else 1).toBitVec.slt 0#32 =
      true := by
    have hne : (j == numRuns) = false := beq_false_of_ne (UInt32.ne_of_lt hj)
    simp [hne, hj]
  let tag := (runs[j.toNat]!).1
  let count := (runs[j.toNat]!).2
  let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
    8 (.pair (.boxedUInt 0) (.boxedUInt 0))) 9 (.pair (.boxedUInt tag) (.boxedUInt count)))
    10 (.boxedUInt tag)) 11 (.boxedUInt count))
    13 (.boxedUInt tag)) 14 (.i32 0)) 12 (.i32 tag)
  refine ⟨locs1, ?_, by simp [locs1, setLocal, hl0], by simp [locs1, setLocal, hl1],
    by simp [locs1, setLocal, hl2], by simp [locs1, setLocal, hl3], by simp [locs1, setLocal, hl4],
    by simp [locs1, setLocal, hl5], by simp [locs1, setLocal, hl6], by simp [locs1, setLocal, hl7],
    by simp [locs1, setLocal]; rfl, by simp [locs1, setLocal]; rfl⟩
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 42 := ⟨f - 42, by omega⟩
  rw [hf', show f' + 42 - 42 = f' from by omega]
  rw [expandRuns_drop_6_12]
  rw [runJvmResFast_invokestatic_step stepStatic_expandRuns_closed0_local]; norm_res_fuel
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl2]
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl1]
  rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
  rw [runJvmResFast_iflt_branch hcmp]; norm_res_fuel
  rw [expandRuns_drop_14_25]
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl0]
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl2]
  rw [runJvmResFast_aaload hruns hslt hel_lt]; norm_res_fuel; rw [hpair]
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [setLocal_self]
  rw [runJvmResFast_instanceof_pair]; norm_res_fuel
  rw [runJvmResFast_ifeq_fallthrough (by decide)]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [setLocal_self]
  rw [runJvmResFast_checkcast_pair]; norm_res_fuel
  rw [runJvmResFast_invokevirtual_step stepVirtual_pair_getFirst]; norm_res_fuel
  rw [runJvmResFast_goto]; norm_res_fuel
  rw [expandRuns_drop_32_40]
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_instanceof_pair]; norm_res_fuel
  rw [runJvmResFast_ifeq_fallthrough (by decide)]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_checkcast_pair]; norm_res_fuel
  rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond]; norm_res_fuel
  rw [runJvmResFast_goto]; norm_res_fuel
  rw [expandRuns_drop_44_57]
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
  rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
  rw [expandRuns_drop_57_67]
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]; norm_res_fuel
  rw [runJvmResFast_invokevirtual_step stepVirtual_uintUnbox]; norm_res_fuel
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel; rw [setLocal_self]
  rw [runJvmResFast_iconst_local]

private theorem expandRuns_step_tag1
    (f : Nat) (tag : UInt32) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 16) (hl10 : locs 10 = .boxedUInt tag) :
    ∃ locs1,
      runJvmResFast f f_Algorithm_expandRuns_prog 67 (f_Algorithm_expandRuns_prog.drop 67)
        ⟨67, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 16) f_Algorithm_expandRuns_prog 88
        (.if_icmpeq 144 :: f_Algorithm_expandRuns_prog.drop 89)
        ⟨88, [.i32 1, .i32 tag], locs1, jh, ⟨ar, u64, asc⟩⟩ ∧
      (∀ idx, idx ≠ 13 → idx ≠ 14 → idx ≠ 15 → locs1 idx = locs idx) := by
  let locs1 := setLocal (setLocal (setLocal locs 14 (.boxedUInt tag)) 15 (.i32 0)) 13 (.i32 tag)
  refine ⟨locs1, ?_, fun idx h13 h14 h15 => by simp [locs1, setLocal, h13, h14, h15]⟩
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 16 := ⟨f - 16, by omega⟩
  rw [hf', show f' + 16 - 16 = f' from by omega]
  rw [expandRuns_drop_67_79]
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl10]
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
  rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
  rw [expandRuns_drop_79_89]
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]; norm_res_fuel
  rw [runJvmResFast_invokevirtual_step stepVirtual_uintUnbox]; norm_res_fuel
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel; rw [setLocal_self]
  rw [runJvmResFast_iconst_local]

private theorem expandRuns_step_rowEnd
    (f : Nat) (numRuns j count : UInt32) (y startX : Int32) (cId runsAddr : Nat)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 50)
    (hl0 : locs 0 = .heapRef runsAddr) (hl1 : locs 1 = .i32 numRuns) (hl2 : locs 2 = .i32 j)
    (hl5 : locs 5 = .i32 y.toUInt32) (hl6 : locs 6 = .i32 startX.toUInt32)
    (hl7 : locs 7 = .ext (.u64Ref cId)) (hl11 : locs 11 = .boxedUInt count) :
    ∃ locs',
      runJvmResFast f f_Algorithm_expandRuns_prog 89 (f_Algorithm_expandRuns_prog.drop 89)
        ⟨89, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 50) f_Algorithm_expandRuns_prog 6 (f_Algorithm_expandRuns_prog.drop 6)
        ⟨6, [], locs', jh, ⟨ar, u64, asc⟩⟩ ∧
      locs' 0 = .heapRef runsAddr ∧ locs' 1 = .i32 numRuns ∧ locs' 2 = .i32 (j + 1) ∧
      locs' 3 = .i32 0 ∧ locs' 4 = .i32 startX.toUInt32 ∧
      locs' 5 = .i32 (y + count.toInt32).toUInt32 ∧ locs' 6 = .i32 startX.toUInt32 ∧
      locs' 7 = .ext (.u64Ref cId) := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨f', hf'⟩ : ∃ f', f = f' + 50 := ⟨f - 50, by omega⟩
    rw [hf', show f' + 50 - 50 = f' from by omega]
    rw [expandRuns_drop_89_101]
    rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl11]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
    rw [expandRuns_drop_101_144]
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_invokevirtual_step stepVirtual_uintUnbox]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl0]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl1]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl2]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl6]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl5]
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl6]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl7]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_goto]
  all_goals simp [setLocal]

private theorem expandRuns_step_dead
    (f : Nat) (numRuns j count : UInt32) (x y startX : Int32) (cId runsAddr : Nat)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 50)
    (hl0 : locs 0 = .heapRef runsAddr) (hl1 : locs 1 = .i32 numRuns) (hl2 : locs 2 = .i32 j)
    (hl4 : locs 4 = .i32 x.toUInt32) (hl5 : locs 5 = .i32 y.toUInt32)
    (hl6 : locs 6 = .i32 startX.toUInt32) (hl7 : locs 7 = .ext (.u64Ref cId))
    (hl11 : locs 11 = .boxedUInt count) :
    ∃ locs',
      runJvmResFast f f_Algorithm_expandRuns_prog 144 (f_Algorithm_expandRuns_prog.drop 144)
        ⟨144, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 50) f_Algorithm_expandRuns_prog 6 (f_Algorithm_expandRuns_prog.drop 6)
        ⟨6, [], locs', jh, ⟨ar, u64, asc⟩⟩ ∧
      locs' 0 = .heapRef runsAddr ∧ locs' 1 = .i32 numRuns ∧ locs' 2 = .i32 (j + 1) ∧
      locs' 3 = .i32 0 ∧ locs' 4 = .i32 (x + count.toInt32).toUInt32 ∧
      locs' 5 = .i32 y.toUInt32 ∧ locs' 6 = .i32 startX.toUInt32 ∧
      locs' 7 = .ext (.u64Ref cId) := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨f', hf'⟩ : ∃ f', f = f' + 50 := ⟨f - 50, by omega⟩
    rw [hf', show f' + 50 - 50 = f' from by omega]
    rw [expandRuns_drop_144_156]
    rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl11]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
    rw [expandRuns_drop_156_199]
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_invokevirtual_step stepVirtual_uintUnbox]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl0]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl1]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl2]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl4]
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl5]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl6]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl7]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_goto]
  all_goals simp [setLocal]

private theorem expandRuns_step_alive_head
    (f : Nat) (k count : UInt32) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 17) (hl3 : locs 3 = .i32 k) (hl11 : locs 11 = .boxedUInt count) :
    let cmp : UInt32 := if k == count then 0 else if k < count then 4294967295 else 1
    ∃ locs1,
      runJvmResFast f f_Algorithm_expandRuns_prog 199 (f_Algorithm_expandRuns_prog.drop 199)
        ⟨199, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 17) f_Algorithm_expandRuns_prog 221
        (.iflt 277 :: f_Algorithm_expandRuns_prog.drop 222)
        ⟨221, [.i32 cmp], locs1, jh, ⟨ar, u64, asc⟩⟩ ∧
      (∀ idx, idx ≠ 13 → idx ≠ 14 → idx ≠ 15 → locs1 idx = locs idx) := by
  let locs1 := setLocal (setLocal (setLocal locs 14 (.boxedUInt count)) 15 (.i32 0)) 13 (.i32 count)
  refine ⟨locs1, ?_, fun idx h13 h14 h15 => by simp [locs1, setLocal, h13, h14, h15]⟩
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 17 := ⟨f - 17, by omega⟩
  rw [hf', show f' + 17 - 17 = f' from by omega]
  rw [expandRuns_drop_199_211]
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl11]
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
  rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
  rw [expandRuns_drop_211_222]
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]; norm_res_fuel
  rw [runJvmResFast_invokevirtual_step stepVirtual_uintUnbox]; norm_res_fuel
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl3]
  rw [runJvmResFast_iload]; norm_res_fuel; rw [setLocal_self]
  rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
  simp only [beq_iff_eq]; rfl

private theorem expandRuns_step_alive_done
    (f : Nat) (numRuns j count : UInt32) (x y startX : Int32) (cId runsAddr : Nat)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 50)
    (hl0 : locs 0 = .heapRef runsAddr) (hl1 : locs 1 = .i32 numRuns) (hl2 : locs 2 = .i32 j)
    (hl4 : locs 4 = .i32 x.toUInt32) (hl5 : locs 5 = .i32 y.toUInt32)
    (hl6 : locs 6 = .i32 startX.toUInt32) (hl7 : locs 7 = .ext (.u64Ref cId))
    (hl11 : locs 11 = .boxedUInt count) :
    ∃ locs',
      runJvmResFast f f_Algorithm_expandRuns_prog 222 (f_Algorithm_expandRuns_prog.drop 222)
        ⟨222, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 50) f_Algorithm_expandRuns_prog 6 (f_Algorithm_expandRuns_prog.drop 6)
        ⟨6, [], locs', jh, ⟨ar, u64, asc⟩⟩ ∧
      locs' 0 = .heapRef runsAddr ∧ locs' 1 = .i32 numRuns ∧ locs' 2 = .i32 (j + 1) ∧
      locs' 3 = .i32 0 ∧ locs' 4 = .i32 (x + count.toInt32).toUInt32 ∧
      locs' 5 = .i32 y.toUInt32 ∧ locs' 6 = .i32 startX.toUInt32 ∧
      locs' 7 = .ext (.u64Ref cId) := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨f', hf'⟩ : ∃ f', f = f' + 50 := ⟨f - 50, by omega⟩
    rw [hf', show f' + 50 - 50 = f' from by omega]
    rw [expandRuns_drop_222_234]
    rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl11]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
    rw [expandRuns_drop_234_277]
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_invokevirtual_step stepVirtual_uintUnbox]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl0]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl1]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl2]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl4]
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl5]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl6]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl7]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_goto]
  all_goals simp [setLocal]

private theorem expandRuns_step_alive_push
    (f : Nat) (numRuns j k : UInt32) (x y startX : Int32) (cells : Array UInt64)
    (cId runsAddr : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 61) (hu : u64[cId]? = some cells)
    (hl0 : locs 0 = .heapRef runsAddr) (hl1 : locs 1 = .i32 numRuns) (hl2 : locs 2 = .i32 j)
    (hl3 : locs 3 = .i32 k) (hl4 : locs 4 = .i32 x.toUInt32) (hl5 : locs 5 = .i32 y.toUInt32)
    (hl6 : locs 6 = .i32 startX.toUInt32) (hl7 : locs 7 = .ext (.u64Ref cId)) :
    let cells' := Algorithm.U64Buf.push cells (Algorithm.cellBits (x + k.toInt32, y))
    let u64' := u64 ++ [cells']
    ∃ locs',
      runJvmResFast f f_Algorithm_expandRuns_prog 277 (f_Algorithm_expandRuns_prog.drop 277)
        ⟨277, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 61) f_Algorithm_expandRuns_prog 6 (f_Algorithm_expandRuns_prog.drop 6)
        ⟨6, [], locs', jh, ⟨ar, u64', asc⟩⟩ ∧
      locs' 0 = .heapRef runsAddr ∧ locs' 1 = .i32 numRuns ∧ locs' 2 = .i32 j ∧
      locs' 3 = .i32 (k + 1) ∧ locs' 4 = .i32 x.toUInt32 ∧ locs' 5 = .i32 y.toUInt32 ∧
      locs' 6 = .i32 startX.toUInt32 ∧ locs' 7 = .ext (.u64Ref u64.length) := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨f', hf'⟩ : ∃ f', f = f' + 61 := ⟨f - 61, by omega⟩
    rw [hf', show f' + 61 - 61 = f' from by omega]
    rw [expandRuns_drop_277_338]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl3]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl7]
    rw [runJvmResFast_nop_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl4]
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl3]
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_i2l_mask]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor_local]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_lshl_32]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor_local]; norm_res_fuel
    rw [runJvmResFast_nop_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl5]
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_i2l_mask]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor_local]; norm_res_fuel
    rw [runJvmResFast_lconst_local]; norm_res_fuel
    rw [runJvmResFast_land]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor_local]; norm_res_fuel
    rw [runJvmResFast_ladd]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor_local]; norm_res_fuel
    rw [cellBits_eq_alu]
    have hpush := stepStatic_u64BufPush_heap
      (pc := 307) (x := Algorithm.cellBits (x + k.toInt32, y))
      (id := cId) (rest := []) (locs := setLocal locs 14 (.i32 (k + 1)))
      (jh := jh) (ar := ar) (u64 := u64) (asc := asc) (arr := cells)
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hu
    rw [runJvmResFast_invokestatic_step hpush]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl0]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl1]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl2]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl4]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl5]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl6]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_goto]
  all_goals simp [setLocal]

private theorem expandRuns_loop (m : Nat) :
    ∀ (f : Nat) (runs : Array (UInt32 × UInt32)) (numRuns j k : UInt32) (x y startX : Int32)
      (cells : Array UInt64) (runsAddr cId : Nat) (cls : String) (elems : Array JvmVal)
      (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
      (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
      (asc : List Algorithm.AsciiBytes),
      (numRuns.toNat - j.toNat) * 2 ^ 33 + (2 ^ 32 - k.toNat) ≤ m →
      f ≥ (m + 1) * 140 →
      numRuns.toNat ≤ runs.size →
      runs.size < 2 ^ 31 →
      jh.get? runsAddr = some (.objArray cls elems) →
      (hsz : elems.size = runs.size) →
      (∀ idx (hlt : idx < runs.size),
        elems[idx]'(hsz ▸ hlt) = .pair (.boxedUInt runs[idx].1) (.boxedUInt runs[idx].2)) →
      u64[cId]? = some cells →
      locs 0 = .heapRef runsAddr →
      locs 1 = .i32 numRuns →
      locs 2 = .i32 j →
      locs 3 = .i32 k →
      locs 4 = .i32 x.toUInt32 →
      locs 5 = .i32 y.toUInt32 →
      locs 6 = .i32 startX.toUInt32 →
      locs 7 = .ext (.u64Ref cId) →
      ∃ resId st',
        runJvmResFast f f_Algorithm_expandRuns_prog 6 (f_Algorithm_expandRuns_prog.drop 6)
          ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
          some (.ext (.u64Ref resId), st') ∧
        st'.heap.u64Arrays[resId]? =
          some (Algorithm.expandRuns runs numRuns j k x y startX cells) ∧
        st'.jvmHeap = jh ∧
        st'.heap.arenas = ar ∧
        st'.heap.asciiArrays = asc := by
  induction m with
  | zero =>
    intro f runs numRuns j k x y startX cells runsAddr cId cls elems locs jh ar u64 asc
      hm hf hnum hruns31 hruns hsz helems hu hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7
    have hnot : ¬(j < numRuns) := by
      intro hj
      have hj1 := UInt32.lt_iff_toNat_lt.mp hj
      have hk0 := UInt32.toNat_lt k
      have hge1 : 1 ≤ numRuns.toNat - j.toNat := by omega
      have hge : 2 ^ 33 ≤ (numRuns.toNat - j.toNat) * 2 ^ 33 + (2 ^ 32 - k.toNat) :=
        Nat.le_trans (by omega) (Nat.le_add_right _ _)
      omega
    have hcmp : (if j == numRuns then (0 : UInt32) else if j < numRuns then 4294967295 else 1).toBitVec.slt 0#32 =
        false := by
      by_cases heq : j = numRuns
      · subst heq; simp
      · have hne : (j == numRuns) = false := beq_false_of_ne heq
        simp [hne, hnot]
    refine ⟨cId, ⟨13, [.ext (.u64Ref cId)], setLocal locs 8 (.pair (.boxedUInt 0) (.boxedUInt 0)), jh,
      ⟨ar, u64, asc⟩⟩, ?_, ?_, rfl, rfl, rfl⟩
    · obtain ⟨f', hf'⟩ : ∃ f', f = f' + 8 := ⟨f - 8, by omega⟩
      rw [hf', expandRuns_drop_6_12]
      rw [runJvmResFast_invokestatic_step stepStatic_expandRuns_closed0_local]; norm_res_fuel
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl2]
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl1]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
      rw [runJvmResFast_iflt_fallthrough hcmp]; norm_res_fuel
      rw [expandRuns_drop_12_14]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl7]
      rw [runJvmResFast_areturn_local]
    · unfold Algorithm.expandRuns; simp only [hnot, ↓reduceDIte]; exact hu
  | succ m ih =>
    intro f runs numRuns j k x y startX cells runsAddr cId cls elems locs jh ar u64 asc
      hm hf hnum hruns31 hruns hsz helems hu hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7
    have hf_succ : f ≥ (m + 1) * 140 + 140 := by
      rw [← Nat.succ_mul]; exact hf
    by_cases hj : j < numRuns
    · rcases expandRuns_step_head f runs numRuns j k x y startX cId runsAddr cls elems locs jh ar u64 asc
        (expandRuns_fuel_ge hf_succ (a := 0) (d := 42) (by decide)) hj hnum hruns31 hruns hsz helems
        hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 with
        ⟨locs1, h6_66, h1_0, h1_1, h1_2, h1_3, h1_4, h1_5, h1_6, h1_7, h1_10, h1_11⟩
      rcases hrc : runs[j.toNat]! with ⟨tag, count⟩
      have htag_eq : (runs[j.toNat]!).1 = tag := by rw [hrc]
      have hcnt_eq : (runs[j.toNat]!).2 = count := by rw [hrc]
      rw [htag_eq] at h6_66 h1_10
      rw [hcnt_eq] at h1_11
      have hsub_j : (numRuns.toNat - (j + 1).toNat) * 2 ^ 33 + (2 ^ 32 - (0 : UInt32).toNat) ≤ m :=
        Nat.le_of_lt_succ (by simpa using Nat.lt_of_lt_of_le (expandRuns_measure_next_j (k := k) hj) hm)
      by_cases htag2 : tag = 2
      · have htag2_b : (tag == 2) = true := beq_iff_eq.mpr htag2
        rcases expandRuns_step_alive_head (f - 43) k count locs1 jh ar u64 asc
          (expandRuns_fuel_ge hf_succ (a := 43) (d := 17) (by decide))
          h1_3 h1_11 with ⟨locs2, h199_221, h2_pres⟩
        have h2_0 : locs2 0 = .heapRef runsAddr := by rw [h2_pres 0 (by decide) (by decide) (by decide)]; exact h1_0
        have h2_1 : locs2 1 = .i32 numRuns := by rw [h2_pres 1 (by decide) (by decide) (by decide)]; exact h1_1
        have h2_2 : locs2 2 = .i32 j := by rw [h2_pres 2 (by decide) (by decide) (by decide)]; exact h1_2
        have h2_4 : locs2 4 = .i32 x.toUInt32 := by rw [h2_pres 4 (by decide) (by decide) (by decide)]; exact h1_4
        have h2_5 : locs2 5 = .i32 y.toUInt32 := by rw [h2_pres 5 (by decide) (by decide) (by decide)]; exact h1_5
        have h2_6 : locs2 6 = .i32 startX.toUInt32 := by
          rw [h2_pres 6 (by decide) (by decide) (by decide)]; exact h1_6
        have h2_7 : locs2 7 = .ext (.u64Ref cId) := by
          rw [h2_pres 7 (by decide) (by decide) (by decide)]; exact h1_7
        have h2_11 : locs2 11 = .boxedUInt count := by
          rw [h2_pres 11 (by decide) (by decide) (by decide)]; exact h1_11
        by_cases hk : k < count
        · have hsub_k : (numRuns.toNat - j.toNat) * 2 ^ 33 + (2 ^ 32 - (k + 1).toNat) ≤ m :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (expandRuns_measure_next_k (numRuns := numRuns) (j := j) hk) hm)
          have hcmp_t : (if k == count then (0 : UInt32) else if k < count then 4294967295 else 1).toBitVec.slt
              0#32 = true := by
            have hne : (k == count) = false := beq_false_of_ne (UInt32.ne_of_lt hk)
            simp [hne, hk]
          have h2_3 : locs2 3 = .i32 k := by rw [h2_pres 3 (by decide) (by decide) (by decide)]; exact h1_3
          rcases expandRuns_step_alive_push (f - 61) numRuns j k x y startX cells cId runsAddr
            locs2 jh ar u64 asc (expandRuns_fuel_ge hf_succ (a := 61) (d := 61) (by decide))
            hu h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 with
            ⟨locs3, h277_6, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7⟩
          let cells' := Algorithm.U64Buf.push cells (Algorithm.cellBits (x + k.toInt32, y))
          have hu' : (u64 ++ [cells'])[u64.length]? = some cells' := by simp
          have hf122 : f - 61 - 61 ≥ (m + 1) * 140 :=
            expandRuns_fuel_rem hf_succ (a := 61) (b := 61) (by decide)
          rcases ih (f - 61 - 61) runs numRuns j (k + 1) x y startX cells' runsAddr u64.length
            cls elems locs3 jh ar (u64 ++ [cells']) asc hsub_k hf122 hnum hruns31 hruns hsz helems
            hu' h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 with
            ⟨resId, st', hrun, harr, hjh, har, hasc⟩
          refine ⟨resId, st', ?_, ?_, hjh, har, hasc⟩
          · rw [h6_66, expandRuns_fuel_step hf_succ (a := 42) (by decide)]
            rw [runJvmResFast_if_icmpeq_branch htag2]; norm_res_fuel
            rw [h199_221, Nat.sub_sub]
            rw [expandRuns_fuel_step hf_succ (a := 60) (by decide)]
            rw [runJvmResFast_iflt_branch hcmp_t]; norm_res_fuel
            rw [h277_6]
            exact hrun
          · unfold Algorithm.expandRuns
            simp only [hj, ↓reduceDIte, hrc, htag2_b, hk, ↓reduceIte]
            exact harr
        · have hcmp_f : (if k == count then (0 : UInt32) else if k < count then 4294967295 else 1).toBitVec.slt
              0#32 = false := by
            by_cases heq : k = count
            · subst heq; simp
            · have hne : (k == count) = false := beq_false_of_ne heq
              simp [hne, hk]
          rcases expandRuns_step_alive_done (f - 61) numRuns (j + 0) count x y startX cId runsAddr
            locs2 jh ar u64 asc (expandRuns_fuel_ge hf_succ (a := 61) (d := 50) (by decide))
            h2_0 h2_1 (by simpa using h2_2) h2_4 h2_5 h2_6 h2_7 h2_11 with
            ⟨locs3, h222_6, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7⟩
          simp only [UInt32.add_zero] at h222_6 h3_2
          have hf111 : f - 61 - 50 ≥ (m + 1) * 140 :=
            expandRuns_fuel_rem hf_succ (a := 61) (b := 50) (by decide)
          rcases ih (f - 61 - 50) runs numRuns (j + 1) 0 (x + count.toInt32) y startX cells runsAddr cId
            cls elems locs3 jh ar u64 asc hsub_j hf111 hnum hruns31 hruns hsz helems
            hu h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 with
            ⟨resId, st', hrun, harr, hjh, har, hasc⟩
          refine ⟨resId, st', ?_, ?_, hjh, har, hasc⟩
          · rw [h6_66, expandRuns_fuel_step hf_succ (a := 42) (by decide)]
            rw [runJvmResFast_if_icmpeq_branch htag2]; norm_res_fuel
            rw [h199_221, Nat.sub_sub]
            rw [expandRuns_fuel_step hf_succ (a := 60) (by decide)]
            rw [runJvmResFast_iflt_fallthrough hcmp_f]; norm_res_fuel
            rw [h222_6]
            exact hrun
          · unfold Algorithm.expandRuns
            simp only [hj, ↓reduceDIte, hrc, htag2_b, hk, ↓reduceIte]
            exact harr
      · have htag2_b : (tag == 2) = false := beq_false_of_ne htag2
        rcases expandRuns_step_tag1 (f - 43) tag locs1 jh ar u64 asc
          (expandRuns_fuel_ge hf_succ (a := 43) (d := 16) (by decide)) h1_10 with
          ⟨locs2, h67_88, h2_pres⟩
        have h2_0 : locs2 0 = .heapRef runsAddr := by rw [h2_pres 0 (by decide) (by decide) (by decide)]; exact h1_0
        have h2_1 : locs2 1 = .i32 numRuns := by rw [h2_pres 1 (by decide) (by decide) (by decide)]; exact h1_1
        have h2_2 : locs2 2 = .i32 j := by rw [h2_pres 2 (by decide) (by decide) (by decide)]; exact h1_2
        have h2_4 : locs2 4 = .i32 x.toUInt32 := by rw [h2_pres 4 (by decide) (by decide) (by decide)]; exact h1_4
        have h2_5 : locs2 5 = .i32 y.toUInt32 := by rw [h2_pres 5 (by decide) (by decide) (by decide)]; exact h1_5
        have h2_6 : locs2 6 = .i32 startX.toUInt32 := by
          rw [h2_pres 6 (by decide) (by decide) (by decide)]; exact h1_6
        have h2_7 : locs2 7 = .ext (.u64Ref cId) := by
          rw [h2_pres 7 (by decide) (by decide) (by decide)]; exact h1_7
        have h2_11 : locs2 11 = .boxedUInt count := by
          rw [h2_pres 11 (by decide) (by decide) (by decide)]; exact h1_11
        by_cases htag1 : tag = 1
        · have htag1_b : (tag == 1) = true := beq_iff_eq.mpr htag1
          rcases expandRuns_step_dead (f - 60) numRuns j count x y startX cId runsAddr
            locs2 jh ar u64 asc (expandRuns_fuel_ge hf_succ (a := 60) (d := 50) (by decide))
            h2_0 h2_1 h2_2 h2_4 h2_5 h2_6 h2_7 h2_11 with
            ⟨locs3, h144_6, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7⟩
          have hf110 : f - 60 - 50 ≥ (m + 1) * 140 :=
            expandRuns_fuel_rem hf_succ (a := 60) (b := 50) (by decide)
          rcases ih (f - 60 - 50) runs numRuns (j + 1) 0 (x + count.toInt32) y startX cells runsAddr cId
            cls elems locs3 jh ar u64 asc hsub_j hf110 hnum hruns31 hruns hsz helems
            hu h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 with
            ⟨resId, st', hrun, harr, hjh, har, hasc⟩
          refine ⟨resId, st', ?_, ?_, hjh, har, hasc⟩
          · rw [h6_66, expandRuns_fuel_step hf_succ (a := 42) (by decide)]
            rw [runJvmResFast_if_icmpeq_fallthrough htag2_b]; norm_res_fuel
            rw [h67_88, Nat.sub_sub]
            rw [expandRuns_fuel_step hf_succ (a := 59) (by decide)]
            rw [runJvmResFast_if_icmpeq_branch htag1]; norm_res_fuel
            rw [h144_6]
            exact hrun
          · unfold Algorithm.expandRuns
            simp only [hj, ↓reduceDIte, hrc, htag2_b, htag1_b, ↓reduceIte, Bool.false_eq_true]
            exact harr
        · have htag1_b : (tag == 1) = false := beq_false_of_ne htag1
          rcases expandRuns_step_rowEnd (f - 60) numRuns j count y startX cId runsAddr
            locs2 jh ar u64 asc (expandRuns_fuel_ge hf_succ (a := 60) (d := 50) (by decide))
            h2_0 h2_1 h2_2 h2_5 h2_6 h2_7 h2_11 with
            ⟨locs3, h89_6, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7⟩
          have hf110 : f - 60 - 50 ≥ (m + 1) * 140 :=
            expandRuns_fuel_rem hf_succ (a := 60) (b := 50) (by decide)
          rcases ih (f - 60 - 50) runs numRuns (j + 1) 0 startX (y + count.toInt32) startX cells runsAddr cId
            cls elems locs3 jh ar u64 asc hsub_j hf110 hnum hruns31 hruns hsz helems
            hu h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 with
            ⟨resId, st', hrun, harr, hjh, har, hasc⟩
          refine ⟨resId, st', ?_, ?_, hjh, har, hasc⟩
          · rw [h6_66, expandRuns_fuel_step hf_succ (a := 42) (by decide)]
            rw [runJvmResFast_if_icmpeq_fallthrough htag2_b]; norm_res_fuel
            rw [h67_88, Nat.sub_sub]
            rw [expandRuns_fuel_step hf_succ (a := 59) (by decide)]
            rw [runJvmResFast_if_icmpeq_fallthrough htag1_b]; norm_res_fuel
            rw [h89_6]
            exact hrun
          · unfold Algorithm.expandRuns
            simp only [hj, ↓reduceDIte, hrc, htag2_b, htag1_b, Bool.false_eq_true, ↓reduceIte]
            exact harr
    · have hcmp : (if j == numRuns then (0 : UInt32) else if j < numRuns then 4294967295 else 1).toBitVec.slt 0#32 =
          false := by
        by_cases heq : j = numRuns
        · subst heq; simp
        · have hne : (j == numRuns) = false := beq_false_of_ne heq
          simp [hne, hj]
      refine ⟨cId, ⟨13, [.ext (.u64Ref cId)], setLocal locs 8 (.pair (.boxedUInt 0) (.boxedUInt 0)), jh,
        ⟨ar, u64, asc⟩⟩, ?_, ?_, rfl, rfl, rfl⟩
      · obtain ⟨f', hf'⟩ : ∃ f', f = f' + 8 :=
          ⟨f - 8, (Nat.sub_add_cancel (expandRuns_fuel_ge hf_succ (a := 0) (d := 8) (by decide))).symm⟩
        rw [hf', expandRuns_drop_6_12]
        rw [runJvmResFast_invokestatic_step stepStatic_expandRuns_closed0_local]; norm_res_fuel
        rw [runJvmResFast_astore_local]; norm_res_fuel
        rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl2]
        rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl1]
        rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
        rw [runJvmResFast_iflt_fallthrough hcmp]; norm_res_fuel
        rw [expandRuns_drop_12_14]
        rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl7]
        rw [runJvmResFast_areturn_local]
      · unfold Algorithm.expandRuns; simp only [hj, ↓reduceDIte]; exact hu

theorem expandRuns_equiv
    (runs : Array (UInt32 × UInt32)) (numRuns j k : UInt32) (x y startX : Int32)
    (cells : Array UInt64) (runsAddr cId : Nat) (cls : String) (elems : Array JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hnum : numRuns.toNat ≤ runs.size)
    (hruns31 : runs.size < 2 ^ 31)
    (hruns : jh.get? runsAddr = some (.objArray cls elems))
    (hsz : elems.size = runs.size)
    (helems : ∀ idx (hlt : idx < runs.size),
      elems[idx]'(hsz ▸ hlt) = .pair (.boxedUInt runs[idx].1) (.boxedUInt runs[idx].2))
    (hu : u64[cId]? = some cells)
    (hl0 : locs 0 = .heapRef runsAddr)
    (hl1 : locs 1 = .i32 numRuns)
    (hl2 : locs 2 = .i32 j)
    (hl3 : locs 3 = .i32 k)
    (hl4 : locs 4 = .i32 x.toUInt32)
    (hl5 : locs 5 = .i32 y.toUInt32)
    (hl6 : locs 6 = .i32 startX.toUInt32)
    (hl7 : locs 7 = .ext (.u64Ref cId)) :
    ∃ f resId st',
      runJvmRes f f_Algorithm_expandRuns_prog ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (.ext (.u64Ref resId), st') ∧
      st'.heap.u64Arrays[resId]? =
        some (Algorithm.expandRuns runs numRuns j k x y startX cells) ∧
      st'.jvmHeap = jh ∧
      st'.heap.arenas = ar ∧
      st'.heap.asciiArrays = asc := by
  let m := (numRuns.toNat - j.toNat) * 2 ^ 33 + (2 ^ 32 - k.toNat)
  let f := (m + 1) * 140 + 6
  rcases expandRuns_loop m (f - 6) runs numRuns j k x y startX cells runsAddr cId cls elems locs jh
    ar u64 asc (Nat.le_refl m) (by omega) hnum hruns31 hruns hsz helems hu
    hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 with ⟨resId, st', hrun, harr, hjh, har, hasc⟩
  refine ⟨f, resId, st', ?_, harr, hjh, har, hasc⟩
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  rw [← List.drop_zero (l := f_Algorithm_expandRuns_prog), expandRuns_drop_0_6]
  split_res_fuel 6
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl0]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam_local rfl)]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl7]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam_local rfl)]; norm_res_fuel
  exact hrun

end ExpandRuns

/-! #### 5. `f_Algorithm_parseRLEData_prog` -/

section ParseRLEData
set_option maxRecDepth 2048

private theorem runJvmResFast_lload_pr {f pc idx : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.lload idx :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_lstore_pr {f pc idx : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.lstore idx :: rest) ⟨pc, v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_lmul_pr {f pc : Nat} {prog rest : List JvmInstr} {a b : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.lmul :: rest) ⟨pc, .i64 b :: .i64 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i64 (a * b) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_lsub_pr {f pc : Nat} {prog rest : List JvmInstr} {a b : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.lsub :: rest) ⟨pc, .i64 b :: .i64 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i64 (a - b) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_l2i_pr {f pc : Nat} {prog rest : List JvmInstr} {v : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.l2i :: rest) ⟨pc, .i64 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 v.toUInt32 :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_ifgt_branch_pr {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : (0#32 : BitVec 32).slt v.toBitVec = true) :
    runJvmResFast (f + 1) prog pc (.ifgt tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, isBranchInstr, Jvm.dispatchBranch, hv]

private theorem runJvmResFast_ifgt_fallthrough_pr {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : (0#32 : BitVec 32).slt v.toBitVec = false) :
    runJvmResFast (f + 1) prog pc (.ifgt tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, isBranchInstr, Jvm.dispatchBranch, hv]

private theorem runJvmResFast_ifge_branch_pr {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : (0#32 : BitVec 32).sle v.toBitVec = true) :
    runJvmResFast (f + 1) prog pc (.ifge tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, isBranchInstr, Jvm.dispatchBranch, hv]

private theorem runJvmResFast_ifge_fallthrough_pr {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : (0#32 : BitVec 32).sle v.toBitVec = false) :
    runJvmResFast (f + 1) prog pc (.ifge tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, isBranchInstr, Jvm.dispatchBranch, hv]

private theorem compareUnsigned_sle_zero (a b : UInt32) :
    ((0#32 : BitVec 32).sle
      (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec) =
      decide (¬ (a < b)) := by
  by_cases heq : a == b
  · have h1 : a = b := beq_iff_eq.mp heq
    subst h1; simp
  · by_cases hlt : a < b
    · simp [heq, hlt]
    · simp [heq, hlt]

private theorem stepVirtual_pairGetFirst_pr {pc : Nat} {a b : JvmVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .pair a b :: stk, locs, jh, hp⟩
      "kotlin/Pair" "getFirst" "()Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, a :: stk, locs, jh, hp⟩) := rfl

private theorem stepVirtual_pairGetSecond_pr {pc : Nat} {a b : JvmVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .pair a b :: stk, locs, jh, hp⟩
      "kotlin/Pair" "getSecond" "()Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, b :: stk, locs, jh, hp⟩) := rfl

private theorem stepStatic_uintBox_pr {pc : Nat} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 v :: stk, locs, jh, hp⟩ "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" =
      .inl (some ⟨pc + 1, .boxedUInt v :: stk, locs, jh, hp⟩) := rfl

private theorem stepStatic_longCompareUnsigned_pr {pc : Nat} {a b : UInt64} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i64 b :: .i64 a :: stk, locs, jh, hp⟩
      "java/lang/Long" "compareUnsigned" "(JJ)I" =
      .inl (some ⟨pc + 1, .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: stk,
        locs, jh, hp⟩) := rfl

private theorem stepStatic_parseRLEData_closed0_pr {pc : Nat} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_parseRLEData___closed__0" "()Lkotlin/Pair;" =
      .inl (some ⟨pc + 1, .pair (.boxedUInt 0) (.boxedUInt 1) :: stk, locs, jh, hp⟩) := rfl

private theorem stepStatic_parseRLEData_closed2_pr {pc : Nat} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_parseRLEData___closed__2" "()[Ljava/lang/Object;" =
      let (addr, h') := jh.alloc (.objArray "java/lang/Object" #[])
      .inl (some ⟨pc + 1, .heapRef addr :: stk, locs, h', hp⟩) := rfl

private theorem stepStatic_asciiStringLossy_heap_pr {pc addr : Nat} {s e : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {bytes : ByteArray} (hget : jh.get? addr = some (.byteArray bytes.data)) :
    stepInvokeStatic ⟨pc, .i32 e :: .i32 s :: .heapRef addr :: stk, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_asciiStringLossy-BltQuoY" "([BII)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (Algorithm.asciiStringLossy bytes s e) :: stk, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 e :: .i32 s :: .heapRef addr :: stk, locs, jh, hp⟩
      "RleLeanKt" "f_Algorithm_asciiStringLossy-BltQuoY" "([BII)Ljava/lang/String;" =
      match decodeBytes ⟨pc, .i32 e :: .i32 s :: .heapRef addr :: stk, locs, jh, hp⟩
          (.heapRef addr) with
      | some bs =>
        .inl (some ⟨pc + 1, .str (Algorithm.asciiStringLossy bs s e) :: stk, locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn]; simp only [decodeBytes, hget]

private theorem stepStatic_finishRLE_pr {pc : Nat} {warnsVal runsVal : JvmVal}
    {startX startY : Int32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {warns : Algorithm.GrowBuf Algorithm.RLEWarning}
    {runs : Algorithm.GrowBuf (UInt32 × UInt32)}
    (hw : RleWarnRep warns warnsVal) (hr : RlePairRep runs runsVal) :
    stepInvokeStatic ⟨pc, .i32 startY.toUInt32 :: .i32 startX.toUInt32 :: runsVal :: warnsVal :: stk,
        locs, jh, ⟨ar, u64, asc⟩⟩
      "RleLeanKt" "f_Algorithm_finishRLE"
      "(Ljava/lang/Object;Ljava/lang/Object;II)Lcom/alexvanyo/composelife/model/RLEResult;" =
      let res := Algorithm.finishRLE warns runs startX startY
      let enc := encodeRLEResult jh u64 res
      .inl (some ⟨pc + 1, enc.1 :: stk, locs, enc.2.1, ⟨ar, enc.2.2, asc⟩⟩) := by
  have hw' := rleWarns?_of_rep hw
  have hr' := rleRuns?_of_rep hr
  dsimp only [rleWarns?] at hw'
  dsimp only [rleRuns?] at hr'
  have hfn : stepInvokeStatic
      ⟨pc, .i32 startY.toUInt32 :: .i32 startX.toUInt32 :: runsVal :: warnsVal :: stk,
        locs, jh, ⟨ar, u64, asc⟩⟩
      "RleLeanKt" "f_Algorithm_finishRLE"
      "(Ljava/lang/Object;Ljava/lang/Object;II)Lcom/alexvanyo/composelife/model/RLEResult;" =
      match (match warnsVal with
        | .ext (.rleWarnGrowBuf b) => some b
        | .ext (.strGrowBuf b) =>
          if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none),
        (match runsVal with
        | .ext (.u32PairGrowBuf b) => some b
        | .ext (.strGrowBuf b) =>
          if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
        | _ => none) with
      | some w, some r =>
        let res := Algorithm.finishRLE w r startX.toUInt32.toInt32 startY.toUInt32.toInt32
        let enc := encodeRLEResult jh u64 res
        .inl (some ⟨pc + 1, enc.1 :: stk, locs, enc.2.1, ⟨ar, enc.2.2, asc⟩⟩)
      | _, _ => .inr none := rfl
  rw [hfn, hw', hr', Int32.toInt32_toUInt32, Int32.toInt32_toUInt32]

private theorem stepSpecial_pair_init_pr {pc : Nat} {a b : JvmVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, b :: a :: .allocRef "kotlin/Pair" :: .allocRef "kotlin/Pair" :: stk,
        locs, jh, hp⟩
      "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V" =
      .inl (some ⟨pc + 1, .pair a b :: stk, locs, jh, hp⟩) := rfl

private theorem stepSpecial_rleStatusUnexpectedInput_init_pr {pc : Nat} {s : String}
    {line col : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, .null :: .i32 col :: .i32 line :: .str s ::
        .allocRef "com/alexvanyo/composelife/model/RLEStatus$UnexpectedInput" ::
        .allocRef "com/alexvanyo/composelife/model/RLEStatus$UnexpectedInput" :: stk,
        locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RLEStatus$UnexpectedInput" "<init>"
      "(Ljava/lang/String;IILkotlin/jvm/internal/DefaultConstructorMarker;)V" =
      .inl (some ⟨pc + 1, .ext (.rleStatus (.unexpectedInput s line col)) :: stk,
        locs, jh, hp⟩) := rfl

private theorem stepSpecial_rleWarnUnexpectedInput_init_pr {pc : Nat} {ln col inp : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, .null :: inp :: col :: ln ::
        .allocRef "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput" ::
        .allocRef "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput" :: stk,
        locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput" "<init>"
      "(IILjava/lang/String;Lkotlin/jvm/internal/DefaultConstructorMarker;)V" =
      let (addr, h') := jh.alloc (.instance
        "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput"
        [("lineIndex", ln), ("columnIndex", col), ("input", inp)])
      .inl (some ⟨pc + 1, .heapRef addr :: stk, locs, h', hp⟩) := rfl

private theorem stepSpecial_rleWarnUnexpectedChar_init_pr {pc : Nat} {ln col cp : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, .null :: cp :: col :: ln ::
        .allocRef "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar" ::
        .allocRef "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar" :: stk,
        locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar" "<init>"
      "(IIILkotlin/jvm/internal/DefaultConstructorMarker;)V" =
      let (addr, h') := jh.alloc (.instance
        "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar"
        [("lineIndex", ln), ("columnIndex", col), ("codePoint", cp)])
      .inl (some ⟨pc + 1, .heapRef addr :: stk, locs, h', hp⟩) := rfl

private theorem stepSpecial_rleWarnCharAfterEnd_init_pr {pc : Nat} {ln col cp : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, .null :: cp :: col :: ln ::
        .allocRef "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd" ::
        .allocRef "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd" :: stk,
        locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd" "<init>"
      "(IIILkotlin/jvm/internal/DefaultConstructorMarker;)V" =
      let (addr, h') := jh.alloc (.instance
        "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd"
        [("lineIndex", ln), ("columnIndex", col), ("codePoint", cp)])
      .inl (some ⟨pc + 1, .heapRef addr :: stk, locs, h', hp⟩) := rfl

private theorem compareUnsigned_sgt_iff (a b : UInt32) :
    ((0#32 : BitVec 32).slt
      (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec) =
      decide (b < a) := by
  by_cases heq : a == b
  · have h1 : a = b := beq_iff_eq.mp heq
    subst h1; simp
  · by_cases hlt : a < b
    · have hgt : ¬(b < a) := UInt32.lt_asymm hlt
      simp [heq, hlt, hgt]
    · have hgt : b < a := UInt32.lt_of_le_of_ne (UInt32.not_lt.mp hlt) (fun h => heq (beq_iff_eq.mpr h.symm))
      simp [heq, hlt, hgt]

private theorem longCompareUnsigned_slt_iff (a b : UInt64) :
    ((if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32) =
      decide (a < b) := by
  by_cases heq : a == b
  · have h1 : a = b := beq_iff_eq.mp heq
    subst h1; simp
  · by_cases hlt : a < b
    · simp [heq, hlt]
    · simp [heq, hlt]

private def parseRLEDataMeasure (numLines i : UInt32) (inLine : Bool) (limit p : UInt32) : Nat :=
  (numLines.toNat - i.toNat) * (2 ^ 32 + 3) +
    if inLine then limit.toNat - p.toNat + 1 else 2 ^ 32 + 2

private theorem parseRLEData_measure_newLine {numLines i limit p limit' : UInt32} :
    parseRLEDataMeasure numLines i true limit' 0 <
      parseRLEDataMeasure numLines i false limit p := by
  simp only [parseRLEDataMeasure, ↓reduceIte, Bool.false_eq_true, UInt32.toNat_zero, Nat.sub_zero]
  have hlt := UInt32.toNat_lt limit'
  omega

private theorem parseRLEData_measure_eol {numLines i limit p limit' : UInt32}
    (hlt : i < numLines) :
    parseRLEDataMeasure numLines (i + 1) false limit' 0 <
      parseRLEDataMeasure numLines i true limit p := by
  have hi_lt : i.toNat < numLines.toNat := UInt32.lt_iff_toNat_lt.mp hlt
  have hnum := UInt32.toNat_lt numLines
  have hi1 : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]
  simp only [parseRLEDataMeasure, ↓reduceIte, Bool.false_eq_true]
  rw [hi1]
  have hsub : numLines.toNat - i.toNat = (numLines.toNat - (i.toNat + 1)) + 1 := by omega
  rw [hsub, Nat.add_mul, Nat.one_mul]
  omega

private theorem parseRLEData_measure_step {numLines i : UInt32} {bytes : ByteArray}
    {limit p : UInt32} (hp : p < limit) :
    parseRLEDataMeasure numLines i true limit (Algorithm.decodeCharAt bytes p limit).2 <
      parseRLEDataMeasure numLines i true limit p := by
  have hnext := Algorithm.decodeCharAt_next bytes p limit hp
  simp only [parseRLEDataMeasure, ↓reduceIte]
  omega

private theorem pr_fuel_ge {f m a d : Nat} (hf : f ≥ (m + 1) * 260 + 260) (hd : a + d ≤ 260) :
    f - a ≥ d := by omega

private theorem pr_fuel_step {f m a : Nat} (hf : f ≥ (m + 2) * 260 + 260) (m' : Nat)
    (hm : m' ≤ m) (ha : a ≤ 260) : f - a ≥ (m' + 1) * 260 + 260 := by
  have hmul : (m' + 1) * 260 ≤ (m + 1) * 260 := Nat.mul_le_mul_right 260 (Nat.succ_le_succ hm)
  omega

private theorem pr_fuel_rem {f k d : Nat} (hf : f ≥ k + d) :
    (f - k) ≥ d ∧ (∃ f', f = f' + k ∧ f' = f - k) := ⟨by omega, ⟨f - k, by omega, rfl⟩⟩

private theorem pr_fuel_ge2 {f m d f2 : Nat} (hf : f ≥ (m + 1) * 260 + 260)
    (hd : 78 + d ≤ 260) (h2 : f - 19 - 51 - 8 ≤ f2) : f2 ≥ d := by
  have hg : f - 78 ≥ d := pr_fuel_ge hf hd
  omega

private theorem pr_fuel_step1 {f m f3 : Nat} (hf : f ≥ (m + 2) * 260 + 260)
    (h3 : f - 19 - 51 - 115 ≤ f3) : f3 ≥ (m + 1) * 260 + 260 := by
  have hsub : f - 185 ≥ (m + 1) * 260 + 260 := pr_fuel_step hf m (Nat.le_refl m) (by decide)
  omega

private theorem pr_fuel_step2 {f m f2 f3 k : Nat} (hf : f ≥ (m + 2) * 260 + 260)
    (hk : 78 + k ≤ 260) (h2 : f - 19 - 51 - 8 ≤ f2) (h3 : f2 - k ≤ f3) :
    f3 ≥ (m + 1) * 260 + 260 := by
  have hsub : f - (78 + k) ≥ (m + 1) * 260 + 260 := pr_fuel_step hf m (Nat.le_refl m) hk
  omega

private structure RleDataLocs (locs : Nat → JvmVal) (lines : Array String)
    (numLines i : UInt32) (inLine : Bool) (bytesAddr : Nat) (limit p col : UInt32)
    (count : UInt64) (hasCount : Bool) (countP countCol : UInt32)
    (warnsVal runsVal : JvmVal) (startX startY : Int32) : Prop where
  l0 : locs 0 = .strArr lines
  l1 : locs 1 = .i32 numLines
  l2 : locs 2 = .i32 i
  l3 : locs 3 = .i32 (if inLine then 1 else 0)
  l4 : locs 4 = .heapRef bytesAddr
  l5 : locs 5 = .i32 limit
  l6 : locs 6 = .i32 p
  l7 : locs 7 = .i32 col
  l8 : locs 8 = .i64 count
  l10 : locs 10 = .i32 (if hasCount then 1 else 0)
  l11 : locs 11 = .i32 countP
  l12 : locs 12 = .i32 countCol
  l13 : locs 13 = warnsVal
  l14 : locs 14 = runsVal
  l15 : locs 15 = .i32 startX.toUInt32
  l16 : locs 16 = .i32 startY.toUInt32

private theorem parseRLEData_drop_0_6 :
    f_Algorithm_parseRLEData_prog =
      .aload 0 :: .ldcStr "lines" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 4 :: .ldcStr "bytes" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      f_Algorithm_parseRLEData_prog.drop 6 := by
  conv => lhs; rw [← List.drop_zero (l := f_Algorithm_parseRLEData_prog)]
  drop_prefix 6

private theorem parseRLEData_drop_6_12 :
    f_Algorithm_parseRLEData_prog.drop 6 =
      .aconstNull :: .astore 17 :: .iload 2 :: .iload 1 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: .ifge 14 ::
      f_Algorithm_parseRLEData_prog.drop 12 := by drop_prefix 6

private theorem parseRLEData_drop_12_14 :
    f_Algorithm_parseRLEData_prog.drop 12 =
      .iconst 1 :: .goto 15 :: f_Algorithm_parseRLEData_prog.drop 14 := by drop_prefix 2

private theorem parseRLEData_drop_14_26 :
    f_Algorithm_parseRLEData_prog.drop 14 =
      .iconst 0 :: .istore 18 :: .aconstNull :: .astore 19 :: .lconst 0 :: .lstore 20 ::
      .iconst 0 :: .istore 22 :: .iconst 0 :: .istore 23 :: .iload 18 :: .ifne 32 ::
      f_Algorithm_parseRLEData_prog.drop 26 := by drop_prefix 12

private theorem parseRLEData_drop_15_26 :
    f_Algorithm_parseRLEData_prog.drop 15 =
      .istore 18 :: .aconstNull :: .astore 19 :: .lconst 0 :: .lstore 20 ::
      .iconst 0 :: .istore 22 :: .iconst 0 :: .istore 23 :: .iload 18 :: .ifne 32 ::
      f_Algorithm_parseRLEData_prog.drop 26 := by drop_prefix 11

private theorem parseRLEData_drop_26_32 :
    f_Algorithm_parseRLEData_prog.drop 26 =
      .aload 13 :: .aload 14 :: .iload 15 :: .iload 16 ::
      .invokestatic "RleLeanKt" "f_Algorithm_finishRLE"
        "(Ljava/lang/Object;Ljava/lang/Object;II)Lcom/alexvanyo/composelife/model/RLEResult;" ::
      .areturn :: f_Algorithm_parseRLEData_prog.drop 32 := by drop_prefix 6

private theorem parseRLEData_drop_32_61 :
    f_Algorithm_parseRLEData_prog.drop 32 =
      .iload 3 :: .ifne 94 :: .aload 0 :: .iload 2 :: .aaload :: .dup ::
      .ldcStr "null cannot be cast to non-null type kotlin.String" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .checkcast "java/lang/String" ::
      .invokestatic "kotlin/text/StringsKt" "encodeToByteArray" "(Ljava/lang/String;)[B" ::
      .astore 24 :: .aload 0 :: .astore 25 :: .iload 1 :: .istore 26 ::
      .iload 2 :: .istore 27 :: .aload 24 :: .arraylength ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 28 ::
      .aload 13 :: .astore 29 :: .aload 14 :: .astore 30 ::
      .iload 15 :: .istore 31 :: .iload 16 :: .istore 32 ::
      f_Algorithm_parseRLEData_prog.drop 61 := by drop_prefix 29

private theorem parseRLEData_drop_61_94 :
    f_Algorithm_parseRLEData_prog.drop 61 =
      .aload 25 :: .astore 0 :: .iload 26 :: .istore 1 :: .iload 27 :: .istore 2 ::
      .iconst 1 :: .istore 3 :: .aload 24 :: .astore 4 :: .iload 28 :: .istore 5 ::
      .iconst 0 :: .istore 6 :: .iconst 0 :: .istore 7 :: .lconst 0 :: .lstore 8 ::
      .iconst 0 :: .istore 10 :: .iconst 0 :: .istore 11 :: .iconst 0 :: .istore 12 ::
      .aload 29 :: .astore 13 :: .aload 30 :: .astore 14 ::
      .iload 31 :: .istore 15 :: .iload 32 :: .istore 16 :: .goto 6 ::
      f_Algorithm_parseRLEData_prog.drop 94 := by drop_prefix 33

private theorem parseRLEData_drop_32_34 :
    f_Algorithm_parseRLEData_prog.drop 32 =
      .iload 3 :: .ifne 94 :: f_Algorithm_parseRLEData_prog.drop 34 := by drop_prefix 2

private theorem parseRLEData_drop_94_98 :
    f_Algorithm_parseRLEData_prog.drop 94 =
      .iload 6 :: .iload 5 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: .iflt 152 ::
      f_Algorithm_parseRLEData_prog.drop 98 := by drop_prefix 4

private theorem parseRLEData_drop_98_124 :
    f_Algorithm_parseRLEData_prog.drop 98 =
      .aload 0 :: .astore 24 :: .iload 1 :: .istore 25 :: .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 26 ::
      .aload 4 :: .astore 27 :: .iload 5 :: .istore 28 ::
      .aload 13 :: .astore 29 :: .aload 14 :: .astore 30 ::
      .iload 15 :: .istore 31 :: .iload 16 :: .istore 32 ::
      .aload 24 :: .astore 0 :: .iload 25 :: .istore 1 :: .iload 26 ::
      f_Algorithm_parseRLEData_prog.drop 124 := by drop_prefix 26

private theorem parseRLEData_drop_124_152 :
    f_Algorithm_parseRLEData_prog.drop 124 =
      .istore 2 :: .iconst 0 :: .istore 3 :: .aload 27 :: .astore 4 :: .iload 28 :: .istore 5 ::
      .iconst 0 :: .istore 6 :: .iconst 0 :: .istore 7 :: .lconst 0 :: .lstore 8 ::
      .iconst 0 :: .istore 10 :: .iconst 0 :: .istore 11 :: .iconst 0 :: .istore 12 ::
      .aload 29 :: .astore 13 :: .aload 30 :: .astore 14 ::
      .iload 31 :: .istore 15 :: .iload 32 :: .istore 16 :: .goto 6 ::
      f_Algorithm_parseRLEData_prog.drop 152 := by drop_prefix 28

private theorem parseRLEData_drop_152_175 :
    f_Algorithm_parseRLEData_prog.drop 152 =
      .aload 4 :: .iload 6 :: .iload 5 ::
      .invokestatic "RleLeanKt" "f_Algorithm_decodeCharAt-BltQuoY" "([BII)Lkotlin/Pair;" ::
      .astore 24 :: .aload 24 ::
      .invokevirtual "kotlin/Pair" "getFirst" "()Ljava/lang/Object;" ::
      .checkcast "kotlin/UInt" :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .istore 25 :: .aload 24 ::
      .invokevirtual "kotlin/Pair" "getSecond" "()Ljava/lang/Object;" ::
      .checkcast "kotlin/UInt" :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .istore 26 :: .lconst 0 :: .lstore 27 :: .iconst 0 :: .istore 29 ::
      .iconst 0 :: .istore 30 :: .iconst 0 :: .istore 31 ::
      f_Algorithm_parseRLEData_prog.drop 175 := by drop_prefix 23

private theorem parseRLEData_drop_175_197 :
    f_Algorithm_parseRLEData_prog.drop 175 =
      .aconstNull :: .astore 32 :: .aconstNull :: .astore 33 ::
      .iconst 0 :: .istore 34 :: .iconst 0 :: .istore 35 ::
      .iconst 0 :: .istore 36 :: .iconst 0 :: .istore 37 ::
      .iconst 0 :: .istore 38 :: .iconst 0 :: .istore 39 ::
      .iconst 0 :: .istore 40 :: .iconst 0 :: .istore 41 ::
      .iconst 0 :: .istore 42 :: f_Algorithm_parseRLEData_prog.drop 197 := by drop_prefix 22

private theorem parseRLEData_drop_197_205 :
    f_Algorithm_parseRLEData_prog.drop 197 =
      .iconst 48 :: .iload 25 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: .ifgt 230 ::
      .iload 25 :: .iconst 57 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: .ifgt 230 ::
      f_Algorithm_parseRLEData_prog.drop 205 := by drop_prefix 8

private theorem parseRLEData_drop_205_230 :
    f_Algorithm_parseRLEData_prog.drop 205 =
      .lconst 4294967296 :: .lload 8 ::
      .invokestatic "java/lang/Long" "compareUnsigned" "(JJ)I" :: .iflt 227 ::
      .lload 8 :: .lconst 10 :: .lmul ::
      .invokestatic "kotlin/ULong" "constructor-impl" "(J)J" ::
      .iload 25 :: .i2l :: .lconst 4294967295 :: .land ::
      .invokestatic "kotlin/ULong" "constructor-impl" "(J)J" ::
      .lconst 48 :: .lsub ::
      .invokestatic "kotlin/ULong" "constructor-impl" "(J)J" ::
      .ladd :: .invokestatic "kotlin/ULong" "constructor-impl" "(J)J" ::
      .lstore 43 :: .lload 43 :: .lstore 27 :: .goto 613 ::
      f_Algorithm_parseRLEData_prog.drop 227 := by drop_prefix 22

private theorem parseRLEData_drop_227_230 :
    f_Algorithm_parseRLEData_prog.drop 227 =
      .lload 8 :: .lstore 27 :: .goto 613 :: f_Algorithm_parseRLEData_prog.drop 230 := by
  drop_prefix 3

private theorem parseRLEData_drop_230_254 :
    f_Algorithm_parseRLEData_prog.drop 230 =
      .iload 25 :: .iconst 33 :: .if_icmpeq 289 ::
      .iload 25 :: .iconst 32 :: .if_icmpeq 288 ::
      .iload 25 :: .iconst 9 :: .if_icmpeq 287 ::
      .iload 25 :: .iconst 13 :: .if_icmpeq 286 ::
      .iload 10 :: .ifne 247 :: .iconst 0 :: .istore 42 :: .goto 322 ::
      .lconst 2147483647 :: .lload 8 ::
      .invokestatic "java/lang/Long" "compareUnsigned" "(JJ)I" :: .iflt 254 ::
      .iconst 0 :: .istore 42 :: .goto 322 ::
      f_Algorithm_parseRLEData_prog.drop 254 := by drop_prefix 24

private theorem parseRLEData_drop_247_254 :
    f_Algorithm_parseRLEData_prog.drop 247 =
      .lconst 2147483647 :: .lload 8 ::
      .invokestatic "java/lang/Long" "compareUnsigned" "(JJ)I" :: .iflt 254 ::
      .iconst 0 :: .istore 42 :: .goto 322 ::
      f_Algorithm_parseRLEData_prog.drop 254 := by drop_prefix 7

private theorem parseRLEData_drop_254_286 :
    f_Algorithm_parseRLEData_prog.drop 254 =
      .aload 4 :: .iload 11 :: .iload 6 ::
      .invokestatic "RleLeanKt" "f_Algorithm_asciiStringLossy-BltQuoY"
        "([BII)Ljava/lang/String;" ::
      .astore 43 ::
      .newClass "com/alexvanyo/composelife/model/RLEStatus$UnexpectedInput" :: .dup ::
      .aload 43 :: .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .iload 12 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/RLEStatus$UnexpectedInput" "<init>"
        "(Ljava/lang/String;IILkotlin/jvm/internal/DefaultConstructorMarker;)V" ::
      .astore 44 ::
      .invokestatic "RleLeanKt" "f_Algorithm_parseRLEData___closed__2"
        "()[Ljava/lang/Object;" ::
      .astore 45 :: .invokestatic "RleLeanKt" "f_Algorithm_noCells" "()[J" :: .astore 46 ::
      .newClass "com/alexvanyo/composelife/model/RLEResult" :: .dup ::
      .aload 44 :: .checkcast "com/alexvanyo/composelife/model/RLEStatus" ::
      .aload 45 :: .aload 46 :: .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/RLEResult" "<init>"
        ("(Lcom/alexvanyo/composelife/model/RLEStatus;" ++
          "[Ljava/lang/Object;[JLkotlin/jvm/internal/DefaultConstructorMarker;)V") ::
      .areturn :: f_Algorithm_parseRLEData_prog.drop 286 := by drop_prefix 32

private theorem parseRLEData_drop_286_289 :
    f_Algorithm_parseRLEData_prog.drop 286 =
      .goto 420 :: .goto 420 :: .goto 420 :: f_Algorithm_parseRLEData_prog.drop 289 := by
  drop_prefix 3

private theorem parseRLEData_drop_287_289 :
    f_Algorithm_parseRLEData_prog.drop 287 =
      .goto 420 :: .goto 420 :: f_Algorithm_parseRLEData_prog.drop 289 := by
  drop_prefix 2

private theorem parseRLEData_drop_288_289 :
    f_Algorithm_parseRLEData_prog.drop 288 =
      .goto 420 :: f_Algorithm_parseRLEData_prog.drop 289 := by
  drop_prefix 1

private theorem parseRLEData_drop_289_294 :
    f_Algorithm_parseRLEData_prog.drop 289 =
      .iload 10 :: .ifne 294 :: .aload 13 :: .astore 33 :: .goto 484 ::
      f_Algorithm_parseRLEData_prog.drop 294 := by drop_prefix 5

private theorem parseRLEData_drop_294_322 :
    f_Algorithm_parseRLEData_prog.drop 294 =
      .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 43 ::
      .iload 12 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 44 ::
      .aload 4 :: .iload 11 :: .iload 26 ::
      .invokestatic "RleLeanKt" "f_Algorithm_asciiStringLossy-BltQuoY"
        "([BII)Ljava/lang/String;" ::
      .astore 45 :: .aload 13 ::
      .newClass "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput" :: .dup ::
      .iload 43 :: .iload 44 :: .aload 45 :: .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput" "<init>"
        "(IILjava/lang/String;Lkotlin/jvm/internal/DefaultConstructorMarker;)V" ::
      .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" ::
      .astore 46 :: .aload 46 :: .astore 33 :: .goto 484 ::
      f_Algorithm_parseRLEData_prog.drop 322 := by drop_prefix 28

private theorem parseRLEData_drop_322_337 :
    f_Algorithm_parseRLEData_prog.drop 322 =
      .iload 10 :: .ifne 329 :: .iload 42 :: .istore 40 :: .iconst 1 :: .istore 41 ::
      .goto 337 ::
      .lload 8 :: .l2i :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 43 ::
      .iload 42 :: .istore 40 :: .iload 43 :: .istore 41 ::
      f_Algorithm_parseRLEData_prog.drop 337 := by drop_prefix 15

private theorem parseRLEData_drop_329_337 :
    f_Algorithm_parseRLEData_prog.drop 329 =
      .lload 8 :: .l2i :: .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 43 ::
      .iload 42 :: .istore 40 :: .iload 43 :: .istore 41 ::
      f_Algorithm_parseRLEData_prog.drop 337 := by drop_prefix 8

private theorem parseRLEData_drop_337_363 :
    f_Algorithm_parseRLEData_prog.drop 337 =
      .iload 25 :: .iconst 36 :: .if_icmpeq 357 ::
      .iload 25 :: .iconst 98 :: .if_icmpeq 350 ::
      .iload 41 :: .istore 37 :: .iload 40 :: .istore 38 :: .iconst 2 :: .istore 39 ::
      .goto 363 ::
      .iload 41 :: .istore 37 :: .iload 40 :: .istore 38 :: .iconst 1 :: .istore 39 ::
      .goto 363 ::
      .iload 41 :: .istore 37 :: .iload 40 :: .istore 38 :: .iconst 0 :: .istore 39 ::
      f_Algorithm_parseRLEData_prog.drop 363 := by drop_prefix 26

private theorem parseRLEData_drop_350_363 :
    f_Algorithm_parseRLEData_prog.drop 350 =
      .iload 41 :: .istore 37 :: .iload 40 :: .istore 38 :: .iconst 1 :: .istore 39 ::
      .goto 363 ::
      .iload 41 :: .istore 37 :: .iload 40 :: .istore 38 :: .iconst 0 :: .istore 39 ::
      f_Algorithm_parseRLEData_prog.drop 363 := by drop_prefix 13

private theorem parseRLEData_drop_357_363 :
    f_Algorithm_parseRLEData_prog.drop 357 =
      .iload 41 :: .istore 37 :: .iload 40 :: .istore 38 :: .iconst 0 :: .istore 39 ::
      f_Algorithm_parseRLEData_prog.drop 363 := by drop_prefix 6

private theorem parseRLEData_drop_363_395 :
    f_Algorithm_parseRLEData_prog.drop 363 =
      .iload 39 :: .iconst 2 :: .if_icmpeq 375 ::
      .iload 37 :: .istore 29 :: .iload 38 :: .istore 30 :: .iload 39 :: .istore 31 ::
      .aload 13 :: .astore 32 :: .goto 551 ::
      .iload 25 :: .iconst 111 :: .if_icmpeq 385 ::
      .iload 37 :: .istore 34 :: .iload 38 :: .istore 35 :: .iload 39 :: .istore 36 ::
      .goto 395 ::
      .nop :: .iload 37 :: .istore 29 :: .iconst 0 :: .istore 30 ::
      .iload 39 :: .istore 31 :: .aload 13 :: .astore 32 :: .goto 551 ::
      f_Algorithm_parseRLEData_prog.drop 395 := by drop_prefix 32

private theorem parseRLEData_drop_375_395 :
    f_Algorithm_parseRLEData_prog.drop 375 =
      .iload 25 :: .iconst 111 :: .if_icmpeq 385 ::
      .iload 37 :: .istore 34 :: .iload 38 :: .istore 35 :: .iload 39 :: .istore 36 ::
      .goto 395 ::
      .nop :: .iload 37 :: .istore 29 :: .iconst 0 :: .istore 30 ::
      .iload 39 :: .istore 31 :: .aload 13 :: .astore 32 :: .goto 551 ::
      f_Algorithm_parseRLEData_prog.drop 395 := by drop_prefix 20

private theorem parseRLEData_drop_385_395 :
    f_Algorithm_parseRLEData_prog.drop 385 =
      .nop :: .iload 37 :: .istore 29 :: .iconst 0 :: .istore 30 ::
      .iload 39 :: .istore 31 :: .aload 13 :: .astore 32 :: .goto 551 ::
      f_Algorithm_parseRLEData_prog.drop 395 := by drop_prefix 10

private theorem parseRLEData_drop_395_420 :
    f_Algorithm_parseRLEData_prog.drop 395 =
      .aload 13 ::
      .newClass "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar" :: .dup ::
      .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .iload 7 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .iload 25 :: .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar" "<init>"
        "(IIILkotlin/jvm/internal/DefaultConstructorMarker;)V" ::
      .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" ::
      .astore 43 :: .iload 34 :: .istore 29 :: .iload 35 :: .istore 30 ::
      .iload 36 :: .istore 31 :: .aload 43 :: .astore 32 :: .goto 551 ::
      f_Algorithm_parseRLEData_prog.drop 420 := by drop_prefix 25

private theorem parseRLEData_drop_420_452 :
    f_Algorithm_parseRLEData_prog.drop 420 =
      .aload 0 :: .astore 34 :: .iload 1 :: .istore 35 :: .iload 2 :: .istore 36 ::
      .aload 4 :: .astore 37 :: .iload 5 :: .istore 38 :: .iload 7 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 39 ::
      .lload 8 :: .lstore 40 :: .iload 10 :: .istore 42 :: .iload 11 :: .istore 43 ::
      .iload 12 :: .istore 44 :: .aload 13 :: .astore 45 :: .aload 14 :: .astore 46 ::
      .iload 15 :: .istore 47 :: .iload 16 :: .istore 48 :: .aload 34 ::
      f_Algorithm_parseRLEData_prog.drop 452 := by drop_prefix 32

private theorem parseRLEData_drop_452_484 :
    f_Algorithm_parseRLEData_prog.drop 452 =
      .astore 0 :: .iload 35 :: .istore 1 :: .iload 36 :: .istore 2 ::
      .iconst 1 :: .istore 3 :: .aload 37 :: .astore 4 :: .iload 38 :: .istore 5 ::
      .iload 26 :: .istore 6 :: .iload 39 :: .istore 7 :: .lload 40 :: .lstore 8 ::
      .iload 42 :: .istore 10 :: .iload 43 :: .istore 11 :: .iload 44 :: .istore 12 ::
      .aload 45 :: .astore 13 :: .aload 46 :: .astore 14 ::
      .iload 47 :: .istore 15 :: .iload 48 :: .istore 16 :: .goto 6 ::
      f_Algorithm_parseRLEData_prog.drop 484 := by drop_prefix 32

private theorem parseRLEData_drop_484_500 :
    f_Algorithm_parseRLEData_prog.drop 484 =
      .iload 26 :: .iload 5 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: .iflt 524 ::
      .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 34 ::
      .iload 34 :: .iload 1 ::
      .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: .iflt 500 ::
      .aload 33 :: .astore 17 :: .goto 777 ::
      f_Algorithm_parseRLEData_prog.drop 500 := by drop_prefix 16

private theorem parseRLEData_drop_500_524 :
    f_Algorithm_parseRLEData_prog.drop 500 =
      .aload 0 :: .iload 34 :: .aaload :: .astore 35 :: .aload 33 ::
      .newClass "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput" :: .dup ::
      .iload 2 :: .iconst 2 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .iconst 1 :: .aload 35 ::
      .ldcStr "null cannot be cast to non-null type kotlin.String" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload 35 :: .checkcast "java/lang/String" :: .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput" "<init>"
        "(IILjava/lang/String;Lkotlin/jvm/internal/DefaultConstructorMarker;)V" ::
      .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" ::
      .astore 36 :: .aload 36 :: .astore 17 :: .goto 777 ::
      f_Algorithm_parseRLEData_prog.drop 524 := by drop_prefix 24

private theorem parseRLEData_drop_524_551 :
    f_Algorithm_parseRLEData_prog.drop 524 =
      .aload 4 :: .iload 26 :: .iload 5 ::
      .invokestatic "RleLeanKt" "f_Algorithm_decodeCharAt-BltQuoY" "([BII)Lkotlin/Pair;" ::
      .astore 34 :: .aload 33 ::
      .newClass "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd" :: .dup ::
      .iload 2 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .iload 7 :: .iconst 2 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .aload 34 :: .invokevirtual "kotlin/Pair" "getFirst" "()Ljava/lang/Object;" ::
      .checkcast "kotlin/UInt" :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .aconstNull ::
      .invokespecial "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd" "<init>"
        "(IIILkotlin/jvm/internal/DefaultConstructorMarker;)V" ::
      .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" ::
      .astore 35 :: .aload 35 :: .astore 17 :: .goto 777 ::
      f_Algorithm_parseRLEData_prog.drop 551 := by drop_prefix 27

private theorem parseRLEData_drop_551_581 :
    f_Algorithm_parseRLEData_prog.drop 551 =
      .iload 7 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 33 ::
      .aload 14 :: .newClass "kotlin/Pair" :: .dup ::
      .iload 31 :: .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" ::
      .iload 29 :: .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" ::
      .invokespecial "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V" ::
      .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" ::
      .astore 34 :: .aload 0 :: .astore 35 :: .iload 1 :: .istore 36 ::
      .iload 2 :: .istore 37 :: .aload 4 :: .astore 38 :: .iload 5 :: .istore 39 ::
      .iload 15 :: .istore 40 :: .iload 16 :: .istore 41 :: .aload 35 ::
      f_Algorithm_parseRLEData_prog.drop 581 := by drop_prefix 30

private theorem parseRLEData_drop_581_613 :
    f_Algorithm_parseRLEData_prog.drop 581 =
      .astore 0 :: .iload 36 :: .istore 1 :: .iload 37 :: .istore 2 ::
      .iconst 1 :: .istore 3 :: .aload 38 :: .astore 4 :: .iload 39 :: .istore 5 ::
      .iload 26 :: .istore 6 :: .iload 33 :: .istore 7 :: .lconst 0 :: .lstore 8 ::
      .iload 30 :: .istore 10 :: .iconst 0 :: .istore 11 :: .iconst 0 :: .istore 12 ::
      .aload 32 :: .astore 13 :: .aload 34 :: .astore 14 ::
      .iload 40 :: .istore 15 :: .iload 41 :: .istore 16 :: .goto 6 ::
      f_Algorithm_parseRLEData_prog.drop 613 := by drop_prefix 32

private theorem parseRLEData_drop_613_641 :
    f_Algorithm_parseRLEData_prog.drop 613 =
      .iload 7 :: .iconst 1 :: .iadd ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 29 ::
      .iload 10 :: .ifne 630 ::
      .iload 26 :: .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" ::
      .astore 19 :: .lload 27 :: .lstore 20 :: .iload 29 :: .istore 22 ::
      .iload 6 :: .istore 23 :: .goto 639 ::
      .iload 26 :: .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" ::
      .astore 19 :: .lload 27 :: .lstore 20 :: .iload 29 :: .istore 22 ::
      .iload 11 :: .istore 23 :: .iload 10 :: .ifne 709 ::
      f_Algorithm_parseRLEData_prog.drop 641 := by drop_prefix 28

private theorem parseRLEData_drop_630_641 :
    f_Algorithm_parseRLEData_prog.drop 630 =
      .iload 26 :: .invokestatic "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" ::
      .astore 19 :: .lload 27 :: .lstore 20 :: .iload 29 :: .istore 22 ::
      .iload 11 :: .istore 23 :: .iload 10 :: .ifne 709 ::
      f_Algorithm_parseRLEData_prog.drop 641 := by drop_prefix 11

private theorem parseRLEData_drop_639_641 :
    f_Algorithm_parseRLEData_prog.drop 639 =
      .iload 10 :: .ifne 709 :: f_Algorithm_parseRLEData_prog.drop 641 := by drop_prefix 2

private theorem parseRLEData_drop_641_656 :
    f_Algorithm_parseRLEData_prog.drop 641 =
      .aload 19 :: .astore 25 :: .iconst 0 :: .istore 26 :: .aload 25 ::
      .instanceof "java/lang/Integer" :: .ifeq 653 ::
      .aload 25 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto 655 ::
      .aload 25 :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" :: .istore 24 ::
      f_Algorithm_parseRLEData_prog.drop 656 := by drop_prefix 15

private theorem parseRLEData_drop_653_656 :
    f_Algorithm_parseRLEData_prog.drop 653 =
      .aload 25 :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" :: .istore 24 ::
      f_Algorithm_parseRLEData_prog.drop 656 := by drop_prefix 3

private theorem parseRLEData_drop_656_677 :
    f_Algorithm_parseRLEData_prog.drop 656 =
      .aload 0 :: .astore 25 :: .iload 1 :: .istore 26 :: .iload 2 :: .istore 27 ::
      .aload 4 :: .astore 28 :: .iload 5 :: .istore 29 :: .iload 7 :: .istore 30 ::
      .aload 13 :: .astore 31 :: .aload 14 :: .astore 32 ::
      .iload 15 :: .istore 33 :: .iload 16 :: .istore 34 :: .aload 25 ::
      f_Algorithm_parseRLEData_prog.drop 677 := by drop_prefix 21

private theorem parseRLEData_drop_677_709 :
    f_Algorithm_parseRLEData_prog.drop 677 =
      .astore 0 :: .iload 26 :: .istore 1 :: .iload 27 :: .istore 2 ::
      .iload 18 :: .istore 3 :: .aload 28 :: .astore 4 :: .iload 29 :: .istore 5 ::
      .iload 24 :: .istore 6 :: .iload 22 :: .istore 7 :: .lload 20 :: .lstore 8 ::
      .iload 18 :: .istore 10 :: .iload 23 :: .istore 11 :: .iload 30 :: .istore 12 ::
      .aload 31 :: .astore 13 :: .aload 32 :: .astore 14 ::
      .iload 33 :: .istore 15 :: .iload 34 :: .istore 16 :: .goto 6 ::
      f_Algorithm_parseRLEData_prog.drop 709 := by drop_prefix 32

private theorem parseRLEData_drop_709_724 :
    f_Algorithm_parseRLEData_prog.drop 709 =
      .aload 19 :: .astore 25 :: .iconst 0 :: .istore 26 :: .aload 25 ::
      .instanceof "java/lang/Integer" :: .ifeq 721 ::
      .aload 25 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .goto 723 ::
      .aload 25 :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" :: .istore 24 ::
      f_Algorithm_parseRLEData_prog.drop 724 := by drop_prefix 15

private theorem parseRLEData_drop_721_724 :
    f_Algorithm_parseRLEData_prog.drop 721 =
      .aload 25 :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" :: .istore 24 ::
      f_Algorithm_parseRLEData_prog.drop 724 := by drop_prefix 3

private theorem parseRLEData_drop_724_745 :
    f_Algorithm_parseRLEData_prog.drop 724 =
      .aload 0 :: .astore 25 :: .iload 1 :: .istore 26 :: .iload 2 :: .istore 27 ::
      .aload 4 :: .astore 28 :: .iload 5 :: .istore 29 :: .iload 12 :: .istore 30 ::
      .aload 13 :: .astore 31 :: .aload 14 :: .astore 32 ::
      .iload 15 :: .istore 33 :: .iload 16 :: .istore 34 :: .aload 25 ::
      f_Algorithm_parseRLEData_prog.drop 745 := by drop_prefix 21

private theorem parseRLEData_drop_745_777 :
    f_Algorithm_parseRLEData_prog.drop 745 =
      .astore 0 :: .iload 26 :: .istore 1 :: .iload 27 :: .istore 2 ::
      .iload 18 :: .istore 3 :: .aload 28 :: .astore 4 :: .iload 29 :: .istore 5 ::
      .iload 24 :: .istore 6 :: .iload 22 :: .istore 7 :: .lload 20 :: .lstore 8 ::
      .iload 18 :: .istore 10 :: .iload 23 :: .istore 11 :: .iload 30 :: .istore 12 ::
      .aload 31 :: .astore 13 :: .aload 32 :: .astore 14 ::
      .iload 33 :: .istore 15 :: .iload 34 :: .istore 16 :: .goto 6 ::
      f_Algorithm_parseRLEData_prog.drop 777 := by drop_prefix 32

private theorem parseRLEData_drop_777_789 :
    f_Algorithm_parseRLEData_prog.drop 777 =
      .invokestatic "RleLeanKt" "f_Algorithm_parseRLEData___closed__0" "()Lkotlin/Pair;" ::
      .astore 18 :: .aload 14 :: .aload 18 ::
      .invokestatic "RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" ::
      .astore 19 :: .aload 17 :: .aload 19 :: .iload 15 :: .iload 16 ::
      .invokestatic "RleLeanKt" "f_Algorithm_finishRLE"
        "(Ljava/lang/Object;Ljava/lang/Object;II)Lcom/alexvanyo/composelife/model/RLEResult;" ::
      .areturn :: f_Algorithm_parseRLEData_prog.drop 789 := by drop_prefix 12

private theorem parseRLEData_step_head_lt
    (f : Nat) (lines : Array String) (numLines i : UInt32) (inLine : Bool)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warnsVal runsVal : JvmVal) (startX startY : Int32)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 20) (hlt : i < numLines)
    (hl : RleDataLocs locs lines numLines i inLine bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    ∃ locs',
      runJvmResFast f f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
      runJvmResFast (f - 19) f_Algorithm_parseRLEData_prog 32
        (f_Algorithm_parseRLEData_prog.drop 32) ⟨32, [], locs', jh, hp⟩ ∧
      locs' 18 = .i32 1 ∧
      RleDataLocs locs' lines numLines i inLine bytesAddr limit p col count hasCount
        countP countCol warnsVal runsVal startX startY := by
  have h19 : f - 19 = f - 19 := rfl
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 19 := ⟨f - 19, by omega⟩
  apply Exists.intro
  refine ⟨?_, ?_, ?_⟩
  · rw [hf', show f' + 19 - 19 = f' from by omega]
    rw [parseRLEData_drop_6_12]
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l2]
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l1]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
    rw [runJvmResFast_ifge_fallthrough_pr (by
      rw [compareUnsigned_sle_zero]; simp [hlt])]
    norm_res_fuel
    rw [parseRLEData_drop_12_14]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_goto]
    rw [parseRLEData_drop_15_26]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_lconst_local]; norm_res_fuel
    rw [runJvmResFast_lstore_pr]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_ifne_branch (by decide)]
  · simp [setLocal]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7, hl.l8,
        hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]

private theorem parseRLEData_step_finish
    (f : Nat) (lines : Array String) (numLines i : UInt32) (inLine : Bool)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (warnsVal runsVal : JvmVal)
    (startX startY : Int32) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 25) (hge : ¬ (i < numLines))
    (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (hl : RleDataLocs locs lines numLines i inLine bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    let res := Algorithm.finishRLE warns runs startX startY
    let enc := encodeRLEResult jh u64 res
    runJvmResFast f f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      some (enc.1, ⟨31, [enc.1],
        setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 17 .null)
          18 (.i32 0)) 19 .null) 20 (.i64 0)) 22 (.i32 0)) 23 (.i32 0),
        enc.2.1, ⟨ar, enc.2.2, asc⟩⟩) := by
  dsimp only
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 24 := ⟨f - 24, by omega⟩
  rw [hf', parseRLEData_drop_6_12]
  rw [runJvmResFast_aconstNull]; norm_res_fuel
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l2]
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l1]
  rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
  rw [runJvmResFast_ifge_branch_pr (by
    rw [compareUnsigned_sle_zero]; exact decide_eq_true hge)]
  norm_res_fuel
  rw [parseRLEData_drop_14_26]
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_aconstNull]; norm_res_fuel
  rw [runJvmResFast_astore_local]; norm_res_fuel
  rw [runJvmResFast_lconst_local]; norm_res_fuel
  rw [runJvmResFast_lstore_pr]; norm_res_fuel
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iconst_local]; norm_res_fuel
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
  rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
  rw [parseRLEData_drop_26_32]
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l13]
  rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l14]
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l15]
  rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l16]
  rw [runJvmResFast_invokestatic_step (stepStatic_finishRLE_pr hrep hruns)]; norm_res_fuel
  rw [runJvmResFast_areturn_local]

private theorem parseRLEData_step_newLine
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warnsVal runsVal : JvmVal) (startX startY : Int32)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 65) (hi_lt : i.toNat < lines.size) (hislt : i.toBitVec.slt 0#32 = false)
    (hl : RleDataLocs locs lines numLines i false bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    let line := lines[i.toNat]!
    let bytes' := line.toByteArray
    let jh' := (jh.alloc (.byteArray bytes'.data)).2
    let bytesAddr' := jh.objects.size
    ∃ locs',
      runJvmResFast f f_Algorithm_parseRLEData_prog 32
        (f_Algorithm_parseRLEData_prog.drop 32) ⟨32, [], locs, jh, hp⟩ =
      runJvmResFast (f - 62) f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs', jh', hp⟩ ∧
      RleDataLocs locs' lines numLines i true bytesAddr' bytes'.size.toUInt32 0 0
        0 false 0 0 warnsVal runsVal startX startY := by
  intro line bytes' jh' bytesAddr'
  have hget' : jh'.get? bytesAddr' = some (.byteArray bytes'.data) := by
    simp [jh', bytesAddr', Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 62 := ⟨f - 62, by omega⟩
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · rw [hf', show f' + 62 - 62 = f' from by omega]
    rw [parseRLEData_drop_32_61]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l3]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl.l0]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l2]
    rw [runJvmResFast_aaload_strArr hislt hi_lt]; norm_res_fuel
    rw [← getElem!_pos lines i.toNat hi_lt]
    rw [runJvmResFast_dup_local]; norm_res_fuel
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
    rw [runJvmResFast_checkcast_step (by rfl)]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_stringsEncodeToByteArray]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l0]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l1]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l2]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_arraylength_byteArray hget']; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l13]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l14]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l15]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l16]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [parseRLEData_drop_61_94]
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_lconst_local]; norm_res_fuel
    rw [runJvmResFast_lstore_pr]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_goto]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · dsimp only [setLocal, bytesAddr']
        rfl

private theorem parseRLEData_step_eol
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warnsVal runsVal : JvmVal) (startX startY : Int32)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 65) (hp_ge : ¬ (p < limit))
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    ∃ locs',
      runJvmResFast f f_Algorithm_parseRLEData_prog 32
        (f_Algorithm_parseRLEData_prog.drop 32) ⟨32, [], locs, jh, hp⟩ =
      runJvmResFast (f - 60) f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs', jh, hp⟩ ∧
      RleDataLocs locs' lines numLines (i + 1) false bytesAddr limit 0 0
        0 false 0 0 warnsVal runsVal startX startY := by
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 60 := ⟨f - 60, by omega⟩
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · rw [hf', show f' + 60 - 60 = f' from by omega]
    rw [parseRLEData_drop_32_34]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l3]; simp only [↓reduceIte]
    rw [runJvmResFast_ifne_branch (by decide)]
    rw [parseRLEData_drop_94_98]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l6]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l5]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
    rw [runJvmResFast_iflt_fallthrough (by
      rw [compareUnsigned_slt_zero]; exact decide_eq_false hp_ge)]
    norm_res_fuel
    rw [parseRLEData_drop_98_124]
    rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl.l0]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l1]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l2]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l4]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l5]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l13]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l14]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l15]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l16]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [parseRLEData_drop_124_152]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_lconst_local]; norm_res_fuel
    rw [runJvmResFast_lstore_pr]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_goto]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [setLocal]

private theorem parseRLEData_step_decode
    (f : Nat) (lines : Array String) (numLines i : UInt32) (bytes : ByteArray)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warnsVal runsVal : JvmVal) (startX startY : Int32)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 55) (hp_lt : p < limit) (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    let r := Algorithm.decodeCharAt bytes p limit
    ∃ locs',
      runJvmResFast f f_Algorithm_parseRLEData_prog 32
        (f_Algorithm_parseRLEData_prog.drop 32) ⟨32, [], locs, jh, hp⟩ =
      runJvmResFast (f - 51) f_Algorithm_parseRLEData_prog 197
        (f_Algorithm_parseRLEData_prog.drop 197) ⟨197, [], locs', jh, hp⟩ ∧
      locs' 18 = locs 18 ∧ locs' 25 = .i32 r.1 ∧ locs' 26 = .i32 r.2 ∧
      RleDataLocs locs' lines numLines i true bytesAddr limit p col count hasCount
        countP countCol warnsVal runsVal startX startY := by
  intro r
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 51 := ⟨f - 51, by omega⟩
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hf', show f' + 51 - 51 = f' from by omega]
    rw [parseRLEData_drop_32_34]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l3]; simp only [↓reduceIte]
    rw [runJvmResFast_ifne_branch (by decide)]
    rw [parseRLEData_drop_94_98]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l6]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l5]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
    rw [runJvmResFast_iflt_branch (by
      rw [compareUnsigned_slt_zero]; exact decide_eq_true hp_lt)]
    rw [parseRLEData_drop_152_175]
    rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl.l4]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l6]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l5]
    rw [runJvmResFast_invokestatic_step
      (stepStatic_decodeCharAt_heap (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hbytes)]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetFirst_pr]; norm_res_fuel
    rw [runJvmResFast_checkcast_step (by rfl)]; norm_res_fuel
    rw [runJvmResFast_invokevirtual_step stepVirtual_uintUnbox]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetSecond_pr]; norm_res_fuel
    rw [runJvmResFast_checkcast_step (by rfl)]; norm_res_fuel
    rw [runJvmResFast_invokevirtual_step stepVirtual_uintUnbox]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_lconst_local]; norm_res_fuel
    rw [runJvmResFast_lstore_pr]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [parseRLEData_drop_175_197]
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]
  · simp [setLocal]
  · simp [setLocal, r]
  · simp [setLocal, r]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7, hl.l8,
        hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]

private theorem parseRLEData_step_digit_613
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warnsVal runsVal : JvmVal) (startX startY : Int32)
    (nextP : UInt32) (newCount : UInt64) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 85)
    (hl18 : locs 18 = .i32 1) (hl26 : locs 26 = .i32 nextP) (hl27 : locs 27 = .i64 newCount)
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    ∃ f' locs',
      f - 82 ≤ f' ∧ f' ≤ f ∧
      runJvmResFast f f_Algorithm_parseRLEData_prog 613
        (f_Algorithm_parseRLEData_prog.drop 613) ⟨613, [], locs, jh, hp⟩ =
      runJvmResFast f' f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs', jh, hp⟩ ∧
      RleDataLocs locs' lines numLines i true bytesAddr limit nextP (col + 1)
        newCount true (if hasCount then countP else p) (if hasCount then countCol else col)
        warnsVal runsVal startX startY := by
  cases hasCount with
  | false =>
    obtain ⟨f', hf'⟩ : ∃ f', f = f' + 82 := ⟨f - 82, by omega⟩
    refine ⟨f', ?_⟩
    apply Exists.intro
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [hf', parseRLEData_drop_613_641]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l7]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_iadd_local]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l10]
      rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl26]
      rw [runJvmResFast_invokestatic_step stepStatic_uintBox_pr]; norm_res_fuel
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_lload_pr]; norm_res_fuel; simp [setLocal, hl27]
      rw [runJvmResFast_lstore_pr]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l6]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_goto]
      rw [parseRLEData_drop_639_641]
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l10]
      rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
      rw [parseRLEData_drop_641_656]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
      rw [runJvmResFast_ifeq_branch rfl]
      rw [parseRLEData_drop_653_656]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_invokevirtual_step stepVirtual_uintUnbox]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [parseRLEData_drop_656_677]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l0]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l1]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l2]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l4]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l5]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l7]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l13]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l14]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l15]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l16]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [parseRLEData_drop_677_709]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl18]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_lload_pr]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_lstore_pr]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl18]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_goto]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [setLocal]
  | true =>
    obtain ⟨f', hf'⟩ : ∃ f', f = f' + 81 := ⟨f - 81, by omega⟩
    refine ⟨f', ?_⟩
    apply Exists.intro
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [hf', parseRLEData_drop_613_641]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l7]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_iadd_local]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l10]
      rw [runJvmResFast_ifne_branch (by decide)]
      rw [parseRLEData_drop_630_641]
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl26]
      rw [runJvmResFast_invokestatic_step stepStatic_uintBox_pr]; norm_res_fuel
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_lload_pr]; norm_res_fuel; simp [setLocal, hl27]
      rw [runJvmResFast_lstore_pr]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l11]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l10]
      rw [runJvmResFast_ifne_branch (by decide)]
      rw [parseRLEData_drop_709_724]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
      rw [runJvmResFast_ifeq_branch rfl]
      rw [parseRLEData_drop_721_724]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_invokevirtual_step stepVirtual_uintUnbox]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [parseRLEData_drop_724_745]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l0]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l1]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l2]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l4]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l5]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l12]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l13]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l14]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l15]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l16]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [parseRLEData_drop_745_777]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl18]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_lload_pr]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_lstore_pr]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl18]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_goto]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [setLocal]

private theorem parseRLEData_step_digit
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warnsVal runsVal : JvmVal) (startX startY : Int32)
    (cp nextP : UInt32) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 120) (hge48 : 48 ≤ cp) (hle57 : cp ≤ 57)
    (hl18 : locs 18 = .i32 1) (hl25 : locs 25 = .i32 cp) (hl26 : locs 26 = .i32 nextP)
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    let newCount := if count > 4294967296 then count else count * 10 + (cp.toUInt64 - 48)
    ∃ f' locs',
      f - 115 ≤ f' ∧ f' ≤ f ∧
      runJvmResFast f f_Algorithm_parseRLEData_prog 197
        (f_Algorithm_parseRLEData_prog.drop 197) ⟨197, [], locs, jh, hp⟩ =
      runJvmResFast f' f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs', jh, hp⟩ ∧
      RleDataLocs locs' lines numLines i true bytesAddr limit nextP (col + 1)
        newCount true (if hasCount then countP else p) (if hasCount then countCol else col)
        warnsVal runsVal startX startY := by
  intro newCount
  have h1 : f_Algorithm_parseRLEData_prog.drop 197 = _ := parseRLEData_drop_197_205
  have hsgt1 : ((0#32 : BitVec 32).slt (if (48 : UInt32) == cp then (0 : UInt32)
      else if (48 : UInt32) < cp then 4294967295 else 1).toBitVec) = false := by
    rw [compareUnsigned_sgt_iff]; exact decide_eq_false (UInt32.not_lt.mpr hge48)
  have hsgt2 : ((0#32 : BitVec 32).slt (if cp == 57 then (0 : UInt32)
      else if cp < 57 then 4294967295 else 1).toBitVec) = false := by
    rw [compareUnsigned_sgt_iff]; exact decide_eq_false (UInt32.not_lt.mpr hle57)
  by_cases hgt : 4294967296 < count
  · have hnc : newCount = count := by simp [newCount, hgt]
    obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 15 := ⟨f - 15, by omega⟩
    let locs1 := setLocal locs 27 (.i64 count)
    have hl1 : RleDataLocs locs1 lines numLines i true bytesAddr limit p col count hasCount
        countP countCol warnsVal runsVal startX startY := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [locs1, setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7, hl.l8,
          hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]
    rcases parseRLEData_step_digit_613 f0 lines numLines i bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY nextP count locs1 jh hp (by omega)
      (by simp [locs1, setLocal, hl18]) (by simp [locs1, setLocal, hl26])
      (by simp [locs1]) hl1 with ⟨f', locs', hle, hle2, h613, hl'⟩
    refine ⟨f', locs', by omega, by omega, ?_, ?_⟩
    · rw [hf0, h1]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
      rw [runJvmResFast_ifgt_fallthrough_pr hsgt1]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
      rw [runJvmResFast_ifgt_fallthrough_pr hsgt2]; norm_res_fuel
      rw [parseRLEData_drop_205_230]
      rw [runJvmResFast_lconst_local]; norm_res_fuel
      rw [runJvmResFast_lload_pr]; norm_res_fuel; rw [hl.l8]
      rw [runJvmResFast_invokestatic_step stepStatic_longCompareUnsigned_pr]; norm_res_fuel
      rw [runJvmResFast_iflt_branch (by
        rw [longCompareUnsigned_slt_iff]; exact decide_eq_true hgt)]
      rw [parseRLEData_drop_227_230]
      rw [runJvmResFast_lload_pr]; norm_res_fuel; rw [hl.l8]
      rw [runJvmResFast_lstore_pr]; norm_res_fuel
      rw [runJvmResFast_goto]
      exact h613
    · rw [hnc]; exact hl'
  · have hnc : newCount = count * 10 + (cp.toUInt64 - 48) := by simp [newCount, hgt]
    obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 30 := ⟨f - 30, by omega⟩
    let locs1 := setLocal (setLocal locs 43 (.i64 newCount)) 27 (.i64 newCount)
    have hl1 : RleDataLocs locs1 lines numLines i true bytesAddr limit p col count hasCount
        countP countCol warnsVal runsVal startX startY := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [locs1, setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7, hl.l8,
          hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]
    rcases parseRLEData_step_digit_613 f0 lines numLines i bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY nextP newCount locs1 jh hp (by omega)
      (by simp [locs1, setLocal, hl18]) (by simp [locs1, setLocal, hl26])
      (by simp [locs1]) hl1 with ⟨f', locs', hle, hle2, h613, hl'⟩
    refine ⟨f', locs', by omega, by omega, ?_, hl'⟩
    rw [hf0, h1]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
    rw [runJvmResFast_ifgt_fallthrough_pr hsgt1]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
    rw [runJvmResFast_ifgt_fallthrough_pr hsgt2]; norm_res_fuel
    rw [parseRLEData_drop_205_230]
    rw [runJvmResFast_lconst_local]; norm_res_fuel
    rw [runJvmResFast_lload_pr]; norm_res_fuel; rw [hl.l8]
    rw [runJvmResFast_invokestatic_step stepStatic_longCompareUnsigned_pr]; norm_res_fuel
    rw [runJvmResFast_iflt_fallthrough (by
      rw [longCompareUnsigned_slt_iff]; exact decide_eq_false hgt)]
    norm_res_fuel
    rw [runJvmResFast_lload_pr]; norm_res_fuel; rw [hl.l8]
    rw [runJvmResFast_lconst_local]; norm_res_fuel
    rw [runJvmResFast_lmul_pr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_i2l_mask]
    rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor_local]; norm_res_fuel
    rw [runJvmResFast_lconst_local]; norm_res_fuel
    rw [runJvmResFast_lsub_pr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor_local]; norm_res_fuel
    rw [runJvmResFast_ladd]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_ulongCtor_local]; norm_res_fuel
    rw [runJvmResFast_lstore_pr]; norm_res_fuel
    rw [runJvmResFast_lload_pr]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_lstore_pr]; norm_res_fuel
    rw [runJvmResFast_goto]
    simpa [hnc, locs1] using h613

private theorem parseRLEData_step_to_230
    (f : Nat) (cp : UInt32) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 10) (hndig : ¬(48 ≤ cp ∧ cp ≤ 57)) (hl25 : locs 25 = .i32 cp) :
    ∃ f',
      f - 8 ≤ f' ∧ f' ≤ f ∧
      runJvmResFast f f_Algorithm_parseRLEData_prog 197
        (f_Algorithm_parseRLEData_prog.drop 197) ⟨197, [], locs, jh, hp⟩ =
      runJvmResFast f' f_Algorithm_parseRLEData_prog 230
        (f_Algorithm_parseRLEData_prog.drop 230) ⟨230, [], locs, jh, hp⟩ := by
  by_cases hlt48 : cp < 48
  · obtain ⟨f', hf'⟩ : ∃ f', f = f' + 4 := ⟨f - 4, by omega⟩
    refine ⟨f', by omega, by omega, ?_⟩
    rw [hf', parseRLEData_drop_197_205]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
    rw [runJvmResFast_ifgt_branch_pr (by
      rw [compareUnsigned_sgt_iff]; exact decide_eq_true hlt48)]
  · have hge48 : 48 ≤ cp := UInt32.not_lt.mp hlt48
    have hgt57 : 57 < cp := UInt32.lt_iff_toNat_lt.mpr
      (Nat.lt_of_not_le (fun hle => hndig ⟨hge48, UInt32.le_iff_toNat_le.mpr hle⟩))
    obtain ⟨f', hf'⟩ : ∃ f', f = f' + 8 := ⟨f - 8, by omega⟩
    refine ⟨f', by omega, by omega, ?_⟩
    rw [hf', parseRLEData_drop_197_205]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
    rw [runJvmResFast_ifgt_fallthrough_pr (by
      rw [compareUnsigned_sgt_iff]; exact decide_eq_false hlt48)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
    rw [runJvmResFast_ifgt_branch_pr (by
      rw [compareUnsigned_sgt_iff]; exact decide_eq_true hgt57)]

private theorem parseRLEData_step_bang_484
    (f : Nat) (lines : Array String) (numLines i : UInt32) (bytes : ByteArray)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns1 : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (warnsVal warnsVal1 runsVal : JvmVal)
    (startX startY : Int32) (nextP : UInt32) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 50) (hsz : numLines.toNat ≤ lines.size) (hlines31 : lines.size < 2 ^ 31)
    (_hi_lt : i < numLines) (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hrep1 : RleWarnRep warns1 warnsVal1) (hruns : RlePairRep runs runsVal)
    (hl26 : locs 26 = .i32 nextP) (hl33 : locs 33 = warnsVal1)
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    let warns2 :=
      if nextP < limit then
        warns1.push (.charAfterEnd (i + 1) (col + 2) (Algorithm.decodeCharAt bytes nextP limit).1)
      else if i + 1 < numLines then
        warns1.push (.unexpectedInput (i + 2) 1 (lines[(i + 1).toNat]!))
      else warns1
    let res := Algorithm.finishRLE warns2 (runs.push (0, 1)) startX startY
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 484
        (f_Algorithm_parseRLEData_prog.drop 484) ⟨484, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v = some res ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  intro warns2 res
  have h777 : ∀ (f1 : Nat) (locs1 : Nat → JvmVal) (jh1 : Jvm.JvmHeap AlgExt)
      (warns2 : Algorithm.GrowBuf Algorithm.RLEWarning) (wVal2 : JvmVal),
      f1 ≥ 12 → RleWarnRep warns2 wVal2 → locs1 17 = wVal2 → locs1 14 = runsVal →
      locs1 15 = .i32 startX.toUInt32 → locs1 16 = .i32 startY.toUInt32 →
      HeapExtends jh jh1 → jh1.statics = jh.statics →
      ∃ v st',
        runJvmResFast f1 f_Algorithm_parseRLEData_prog 777
          (f_Algorithm_parseRLEData_prog.drop 777) ⟨777, [], locs1, jh1, ⟨ar, u64, asc⟩⟩ =
          some (v, st') ∧
        decodeRLEResult st' v = some (Algorithm.finishRLE warns2 (runs.push (0, 1)) startX startY) ∧
        HeapExtends jh st'.jvmHeap ∧
        st'.jvmHeap.statics = jh.statics ∧
        st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
    intro f1 locs1 jh1 warns2' wVal2 hf1 hrep2 hk17 hk14 hk15 hk16 hext1 hstat1
    obtain ⟨f2, rfl⟩ : ∃ f2, f1 = f2 + 12 := ⟨f1 - 12, by omega⟩
    let res' := Algorithm.finishRLE warns2' (runs.push (0, 1)) startX startY
    let enc := encodeRLEResult jh1 u64 res'
    refine ⟨enc.1, ?_⟩
    apply Exists.intro
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [parseRLEData_drop_777_789]
      rw [runJvmResFast_invokestatic_step stepStatic_parseRLEData_closed0_pr]; norm_res_fuel
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hk14]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_u32Pair hruns)]; norm_res_fuel
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hk17]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hk15]
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hk16]
      rw [runJvmResFast_invokestatic_step
        (stepStatic_finishRLE_pr hrep2 (RlePairRep.full (runs.push (0, 1))))]; norm_res_fuel
      rw [runJvmResFast_areturn_local]
    · exact decodeRLEResult_encode_proj 788 [enc.1] _ jh1 ar u64 asc res'
    · exact heapExtends_trans hext1 (encodeRLEResult_heapExtends jh1 u64 res')
    · exact (encodeRLEResult_statics jh1 u64 res').trans hstat1
    · rfl
    · rfl
  by_cases hnp : nextP < limit
  · have hw2 : warns2 = warns1.push (.charAfterEnd (i + 1) (col + 2)
        (Algorithm.decodeCharAt bytes nextP limit).1) := by simp [warns2, hnp]
    dsimp only [res]; rw [hw2]
    let cp2 := (Algorithm.decodeCharAt bytes nextP limit).1
    let w : Algorithm.RLEWarning := .charAfterEnd (i + 1) (col + 2) cp2
    let wObj : Jvm.HeapObj AlgExt :=
      Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd"
        [("lineIndex", .i32 (i + 1)), ("columnIndex", .i32 (col + 2)), ("codePoint", .i32 cp2)]
    let jh1 := (jh.alloc wObj).2
    let wAddr := jh.objects.size
    have hw_dec : decodeRLEWarning jh1 (.heapRef wAddr) = some w := by
      simp [decodeRLEWarning, jh1, wAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc, wObj, w]
      rfl
    have hw_dec' : decodeRLEWarning { objects := jh.objects.push wObj, statics := jh.statics }
        (.heapRef jh.objects.size) = some w := hw_dec
    have hext1 : HeapExtends jh jh1 := heapExtends_alloc jh wObj
    obtain ⟨f', hf'⟩ : ∃ f', f = f' + 31 := ⟨f - 31, by omega⟩
    let wVal2 : JvmVal := .ext (.rleWarnGrowBuf (warns1.push w))
    let locs1 := setLocal (setLocal (setLocal locs 34 (.pair
      (.boxedUInt (Algorithm.decodeCharAt bytes nextP limit).1)
      (.boxedUInt (Algorithm.decodeCharAt bytes nextP limit).2))) 35 wVal2) 17 wVal2
    rcases h777 f' locs1 jh1 (warns1.push w) wVal2
      (by omega) (RleWarnRep.full _) (by simp [locs1])
      (by simp [locs1, setLocal, hl.l14])
      (by simp [locs1, setLocal, hl.l15]) (by simp [locs1, setLocal, hl.l16]) hext1 rfl with
      ⟨v, st', hrun, hdec, hext', hstat', har', hasc'⟩
    refine ⟨v, st', ?_, hdec, hext', hstat', har', hasc'⟩
    rw [hf', parseRLEData_drop_484_500]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl26]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l5]
    rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
    rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hnp)]
    rw [parseRLEData_drop_524_551]
    rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl.l4]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl26]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l5]
    rw [runJvmResFast_invokestatic_step
      (stepStatic_decodeCharAt_heap (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hbytes)]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl33]
    rw [runJvmResFast_newClass]; norm_res_fuel
    rw [runJvmResFast_dup_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l2]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l7]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_invokevirtual_step stepVirtual_pairGetFirst_pr]; norm_res_fuel
    rw [runJvmResFast_checkcast_step (by rfl)]; norm_res_fuel
    rw [runJvmResFast_invokevirtual_step stepVirtual_uintUnbox]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_invokespecial_step stepSpecial_rleWarnCharAfterEnd_init_pr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_rleWarn hrep1 hw_dec')]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_goto]
    exact hrun
  · by_cases hi1 : i + 1 < numLines
    · have hw2 : warns2 = warns1.push (.unexpectedInput (i + 2) 1 (lines[(i + 1).toNat]!)) := by
        simp [warns2, hnp, hi1]
      dsimp only [res]; rw [hw2]
      have hi1_lt : (i + 1).toNat < lines.size :=
        Nat.lt_of_lt_of_le (UInt32.lt_iff_toNat_lt.mp hi1) hsz
      have hi1_slt : (i + 1).toBitVec.slt 0#32 = false :=
        u32_slt_zero_of_lt_2_31 (Nat.lt_trans hi1_lt hlines31)
      have hi_add2 : (i + 1) + 1 = i + 2 := by
        apply UInt32.eq_of_toBitVec_eq; simp [BitVec.add_assoc]
      let lineNext := lines[(i + 1).toNat]!
      let w : Algorithm.RLEWarning := .unexpectedInput (i + 2) 1 lineNext
      let wObj : Jvm.HeapObj AlgExt :=
        Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput"
          [("lineIndex", .i32 (i + 2)), ("columnIndex", .i32 1), ("input", .str lineNext)]
      let jh1 := (jh.alloc wObj).2
      let wAddr := jh.objects.size
      have hw_dec : decodeRLEWarning jh1 (.heapRef wAddr) = some w := by
        simp [decodeRLEWarning, jh1, wAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc, wObj, w]
        rfl
      have hw_dec' : decodeRLEWarning { objects := jh.objects.push wObj, statics := jh.statics }
          (.heapRef jh.objects.size) = some w := hw_dec
      have hext1 : HeapExtends jh jh1 := heapExtends_alloc jh wObj
      obtain ⟨f', hf'⟩ : ∃ f', f = f' + 37 := ⟨f - 37, by omega⟩
      let wVal2 : JvmVal := .ext (.rleWarnGrowBuf (warns1.push w))
      let locs1 := setLocal (setLocal (setLocal (setLocal locs 34 (.i32 (i + 1)))
        35 (.str lineNext)) 36 wVal2) 17 wVal2
      rcases h777 f' locs1 jh1 (warns1.push w) wVal2
        (by omega) (RleWarnRep.full _) (by simp [locs1])
        (by simp [locs1, setLocal, hl.l14])
        (by simp [locs1, setLocal, hl.l15]) (by simp [locs1, setLocal, hl.l16]) hext1 rfl with
        ⟨v, st', hrun, hdec, hext', hstat', har', hasc'⟩
      refine ⟨v, st', ?_, hdec, hext', hstat', har', hasc'⟩
      rw [hf', parseRLEData_drop_484_500]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl26]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l5]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
      rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hnp)]
      norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l2]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_iadd_local]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l1]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
      rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hi1)]
      rw [parseRLEData_drop_500_524]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l0]
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_aaload_strArr hi1_slt hi1_lt]; norm_res_fuel
      rw [← getElem!_pos lines (i + 1).toNat hi1_lt]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl33]
      rw [runJvmResFast_newClass]; norm_res_fuel
      rw [runJvmResFast_dup_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l2]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_iadd_local]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_ldcStr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNull_local rfl)]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_checkcast_step (by rfl)]; norm_res_fuel
      rw [runJvmResFast_aconstNull]; norm_res_fuel
      rw [runJvmResFast_invokespecial_step stepSpecial_rleWarnUnexpectedInput_init_pr]
      norm_res_fuel
      rw [show lines[(i.toNat + 1) % 4294967296]! = lineNext from rfl]
      rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_rleWarn hrep1 hw_dec')]; norm_res_fuel
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_goto]
      exact hrun
    · have hw2 : warns2 = warns1 := by simp [warns2, hnp, hi1]
      dsimp only [res]; rw [hw2]
      obtain ⟨f', hf'⟩ : ∃ f', f = f' + 16 := ⟨f - 16, by omega⟩
      let locs1 := setLocal (setLocal locs 34 (.i32 (i + 1))) 17 warnsVal1
      rcases h777 f' locs1 jh warns1 warnsVal1 (by omega) hrep1
        (by simp [locs1])
        (by simp [locs1, setLocal, hl.l14]) (by simp [locs1, setLocal, hl.l15])
        (by simp [locs1, setLocal, hl.l16]) (heapExtends_refl jh) rfl with
        ⟨v, st', hrun, hdec, hext', hstat', har', hasc'⟩
      refine ⟨v, st', ?_, hdec, hext', hstat', har', hasc'⟩
      rw [hf', parseRLEData_drop_484_500]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl26]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l5]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
      rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hnp)]
      norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l2]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_iadd_local]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l1]
      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_i32]; norm_res_fuel
      rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hi1)]
      norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl33]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_goto]
      exact hrun

private theorem parseRLEData_step_bang
    (f : Nat) (lines : Array String) (numLines i : UInt32) (bytes : ByteArray)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (warnsVal runsVal : JvmVal)
    (startX startY : Int32) (nextP : UInt32) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 90) (hsz : numLines.toNat ≤ lines.size) (hlines31 : lines.size < 2 ^ 31)
    (hi_lt : i < numLines) (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (hl25 : locs 25 = .i32 33) (hl26 : locs 26 = .i32 nextP)
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    let warns1 :=
      if hasCount then
        warns.push (.unexpectedInput (i + 1) (countCol + 1)
          (Algorithm.asciiStringLossy bytes countP nextP))
      else warns
    let warns2 :=
      if nextP < limit then
        warns1.push (.charAfterEnd (i + 1) (col + 2) (Algorithm.decodeCharAt bytes nextP limit).1)
      else if i + 1 < numLines then
        warns1.push (.unexpectedInput (i + 2) 1 (lines[(i + 1).toNat]!))
      else warns1
    let res := Algorithm.finishRLE warns2 (runs.push (0, 1)) startX startY
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 230
        (f_Algorithm_parseRLEData_prog.drop 230) ⟨230, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v = some res ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  intro warns1 warns2 res
  cases hasCount with
  | false =>
    have hw1 : warns1 = warns := by simp [warns1]
    obtain ⟨f', hf'⟩ : ∃ f', f = f' + 8 := ⟨f - 8, by omega⟩
    let locs1 := setLocal locs 33 warnsVal
    have hl1 : RleDataLocs locs1 lines numLines i true bytesAddr limit p col count false
        countP countCol warnsVal runsVal startX startY := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [locs1, setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7, hl.l8,
          hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]
    rcases parseRLEData_step_bang_484 f' lines numLines i bytes bytesAddr limit p col count
      false countP countCol warns1 runs warnsVal warnsVal runsVal startX startY nextP locs1 jh ar u64
      asc (by omega) hsz hlines31 hi_lt hbytes (by rw [hw1]; exact hrep) hruns
      (by simp [locs1, setLocal, hl26]) (by simp [locs1]) hl1 with
      ⟨v, st', h484, hdec, hext, hstat, har, hasc⟩
    refine ⟨v, st', ?_, hdec, hext, hstat, har, hasc⟩
    rw [hf', parseRLEData_drop_230_254]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_branch rfl]
    rw [parseRLEData_drop_289_294]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l10]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl.l13]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_goto]
    exact h484
  | true =>
    let s := Algorithm.asciiStringLossy bytes countP nextP
    let w : Algorithm.RLEWarning := .unexpectedInput (i + 1) (countCol + 1) s
    have hw1 : warns1 = warns.push w := by simp [warns1, w, s]
    let wObj : Jvm.HeapObj AlgExt :=
      Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput"
        [("lineIndex", .i32 (i + 1)), ("columnIndex", .i32 (countCol + 1)), ("input", .str s)]
    let jh1 := (jh.alloc wObj).2
    let wAddr := jh.objects.size
    have hw_dec : decodeRLEWarning jh1 (.heapRef wAddr) = some w := by
      simp [decodeRLEWarning, jh1, wAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc, wObj, w]
      rfl
    have hw_dec' : decodeRLEWarning { objects := jh.objects.push wObj, statics := jh.statics }
        (.heapRef jh.objects.size) = some w := hw_dec
    have hext01 : HeapExtends jh jh1 := heapExtends_alloc jh wObj
    have hbytes1 : jh1.get? bytesAddr = some (.byteArray bytes.data) := hext01 bytesAddr _ hbytes
    obtain ⟨f', hf'⟩ : ∃ f', f = f' + 33 := ⟨f - 33, by omega⟩
    let wVal1 : JvmVal := .ext (.rleWarnGrowBuf (warns.push w))
    let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal locs
      43 (.i32 (i + 1))) 44 (.i32 (countCol + 1))) 45 (.str s)) 46 wVal1) 33 wVal1
    rcases parseRLEData_step_bang_484 f' lines numLines i bytes bytesAddr limit p col count
      true countP countCol warns1 runs warnsVal wVal1 runsVal startX startY nextP locs1 jh1 ar u64
      asc (by omega) hsz hlines31 hi_lt hbytes1 (by rw [hw1]; exact RleWarnRep.full _) hruns
      (by simp [locs1, setLocal, hl26]) (by simp [locs1])
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [locs1, setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7, hl.l8,
              hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]) with
      ⟨v, st', h484, hdec, hext12, hstat12, har, hasc⟩
    refine ⟨v, st', ?_, hdec, heapExtends_trans hext01 hext12, hstat12, har, hasc⟩
    rw [hf', parseRLEData_drop_230_254]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_branch rfl]
    rw [parseRLEData_drop_289_294]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l10]; simp only [↓reduceIte]
    rw [runJvmResFast_ifne_branch (by decide)]
    rw [parseRLEData_drop_294_322]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l2]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l12]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l4]
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l11]
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl26]
    rw [runJvmResFast_invokestatic_step (stepStatic_asciiStringLossy_heap_pr hbytes)]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l13]
    rw [runJvmResFast_newClass]; norm_res_fuel
    rw [runJvmResFast_dup_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_invokespecial_step stepSpecial_rleWarnUnexpectedInput_init_pr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_rleWarn hrep hw_dec')]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_goto]
    exact h484

private theorem parseRLEData_step_ws_420
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warnsVal runsVal : JvmVal) (startX startY : Int32)
    (nextP : UInt32) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 66) (hl26 : locs 26 = .i32 nextP)
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    ∃ locs',
      runJvmResFast f f_Algorithm_parseRLEData_prog 420
        (f_Algorithm_parseRLEData_prog.drop 420) ⟨420, [], locs, jh, hp⟩ =
      runJvmResFast (f - 64) f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs', jh, hp⟩ ∧
      RleDataLocs locs' lines numLines i true bytesAddr limit nextP (col + 1) count hasCount
        countP countCol warnsVal runsVal startX startY := by
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 64 := ⟨f - 64, by omega⟩
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · rw [hf', show f' + 64 - 64 = f' from by omega]
    rw [parseRLEData_drop_420_452]
    rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl.l0]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l1]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l2]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l4]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l5]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l7]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_lload_pr]; norm_res_fuel; simp [setLocal, hl.l8]
    rw [runJvmResFast_lstore_pr]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l10]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l11]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l12]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l13]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l14]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l15]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l16]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [parseRLEData_drop_452_484]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl26]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_lload_pr]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_lstore_pr]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_goto]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [setLocal]

private theorem parseRLEData_step_ws
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warnsVal runsVal : JvmVal) (startX startY : Int32)
    (cp nextP : UInt32) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 85) (hws : cp = 32 ∨ cp = 9 ∨ cp = 13)
    (hl25 : locs 25 = .i32 cp) (hl26 : locs 26 = .i32 nextP)
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    ∃ f' locs',
      f - 77 ≤ f' ∧ f' ≤ f ∧
      runJvmResFast f f_Algorithm_parseRLEData_prog 230
        (f_Algorithm_parseRLEData_prog.drop 230) ⟨230, [], locs, jh, hp⟩ =
      runJvmResFast f' f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs', jh, hp⟩ ∧
      RleDataLocs locs' lines numLines i true bytesAddr limit nextP (col + 1) count hasCount
        countP countCol warnsVal runsVal startX startY := by
  have hne33 : cp ≠ 33 := by rcases hws with rfl | rfl | rfl <;> decide
  rcases hws with rfl | rfl | rfl
  · obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 7 := ⟨f - 7, by omega⟩
    rcases parseRLEData_step_ws_420 f0 lines numLines i bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY nextP locs jh hp (by omega) hl26 hl with
      ⟨locs', h420, hl'⟩
    refine ⟨f0 - 64, locs', by omega, by omega, ?_, hl'⟩
    rw [hf0, parseRLEData_drop_230_254]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (by decide)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_branch rfl]
    rw [parseRLEData_drop_288_289]
    rw [runJvmResFast_goto]
    exact h420
  · obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 10 := ⟨f - 10, by omega⟩
    rcases parseRLEData_step_ws_420 f0 lines numLines i bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY nextP locs jh hp (by omega) hl26 hl with
      ⟨locs', h420, hl'⟩
    refine ⟨f0 - 64, locs', by omega, by omega, ?_, hl'⟩
    rw [hf0, parseRLEData_drop_230_254]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (by decide)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (by decide)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_branch rfl]
    rw [parseRLEData_drop_287_289]
    rw [runJvmResFast_goto]
    exact h420
  · obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 13 := ⟨f - 13, by omega⟩
    rcases parseRLEData_step_ws_420 f0 lines numLines i bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY nextP locs jh hp (by omega) hl26 hl with
      ⟨locs', h420, hl'⟩
    refine ⟨f0 - 64, locs', by omega, by omega, ?_, hl'⟩
    rw [hf0, parseRLEData_drop_230_254]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (by decide)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (by decide)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (by decide)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_branch rfl]
    rw [parseRLEData_drop_286_289]
    rw [runJvmResFast_goto]
    exact h420

private theorem parseRLEData_step_overflow
    (f : Nat) (lines : Array String) (numLines i : UInt32) (bytes : ByteArray)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64)
    (countP countCol : UInt32) (warnsVal runsVal : JvmVal) (startX startY : Int32)
    (cp : UInt32) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf : f ≥ 60) (hne33 : cp ≠ 33) (hne32 : cp ≠ 32) (hne9 : cp ≠ 9) (hne13 : cp ≠ 13)
    (hov : Algorithm.maxRunCount < count)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data)) (hl25 : locs 25 = .i32 cp)
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count true
      countP countCol warnsVal runsVal startX startY) :
    let s := Algorithm.asciiStringLossy bytes countP p
    let res : Algorithm.RLEResult :=
      ⟨.unexpectedInput s (i + 1) (countCol + 1), #[], Algorithm.noCells⟩
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 230
        (f_Algorithm_parseRLEData_prog.drop 230) ⟨230, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v = some res ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  intro s res
  have hmax : (2147483647 : UInt64) < count := hov
  let wArrAddr := jh.objects.size
  let jh1 := (jh.alloc (.objArray "java/lang/Object" #[])).2
  let resObj : Jvm.HeapObj AlgExt :=
    Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus (.unexpectedInput s (i + 1) (countCol + 1)))),
       ("warnings", .heapRef wArrAddr), ("cells", .ext (.u64Ref u64.length))]
  let resAddr := jh1.objects.size
  let jh2 := (jh1.alloc resObj).2
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 50 := ⟨f - 50, by omega⟩
  refine ⟨.heapRef resAddr, ?_⟩
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf', parseRLEData_drop_230_254]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne33)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne32)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne9)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne13)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l10]; simp only [↓reduceIte]
    rw [runJvmResFast_ifne_branch (by decide)]
    rw [parseRLEData_drop_247_254]
    rw [runJvmResFast_lconst_local]; norm_res_fuel
    rw [runJvmResFast_lload_pr]; norm_res_fuel; rw [hl.l8]
    rw [runJvmResFast_invokestatic_step stepStatic_longCompareUnsigned_pr]; norm_res_fuel
    rw [runJvmResFast_iflt_branch (by
      rw [longCompareUnsigned_slt_iff]; exact decide_eq_true hmax)]
    rw [parseRLEData_drop_254_286]
    rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl.l4]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l11]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l6]
    rw [runJvmResFast_invokestatic_step (stepStatic_asciiStringLossy_heap_pr hbytes)]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_newClass]; norm_res_fuel
    rw [runJvmResFast_dup_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l2]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l12]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_invokespecial_step stepSpecial_rleStatusUnexpectedInput_init_pr]
    norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_parseRLEData_closed2_pr]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_noCells_rle_local]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_newClass]; norm_res_fuel
    rw [runJvmResFast_dup_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_checkcast_step (by rfl)]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_invokespecial_step stepSpecial_rleResult_init]; norm_res_fuel
    rw [runJvmResFast_areturn_local]
    rfl
  · have hget_w : jh1.get? wArrAddr = some (.objArray "java/lang/Object" #[]) := by
      simp [jh1, wArrAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    exact rleResult_decode_of_parts (ar := ar) (u64 := u64) (asc := asc)
      (.unexpectedInput s (i + 1) (countCol + 1)) Algorithm.GrowBuf.empty (.heapRef wArrAddr)
      (some wArrAddr) ⟨rfl, #[], hget_w, rfl⟩
  · exact heapExtends_trans (heapExtends_alloc jh _) (heapExtends_alloc jh1 _)
  · rfl
  · rfl
  · rfl

private theorem parseRLEData_step_run_551
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warnsVal warnsVal' runsVal : JvmVal)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (nextP n tag : UInt32) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 65) (hruns : RlePairRep runs runsVal)
    (hl26 : locs 26 = .i32 nextP) (hl29 : locs 29 = .i32 n)
    (hl30 : locs 30 = .i32 0) (hl31 : locs 31 = .i32 tag) (hl32 : locs 32 = warnsVal')
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    let runsVal' : JvmVal := .ext (.u32PairGrowBuf (runs.push (tag, n)))
    ∃ locs',
      runJvmResFast f f_Algorithm_parseRLEData_prog 551
        (f_Algorithm_parseRLEData_prog.drop 551) ⟨551, [], locs, jh, hp⟩ =
      runJvmResFast (f - 62) f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs', jh, hp⟩ ∧
      RleDataLocs locs' lines numLines i true bytesAddr limit nextP (col + 1)
        0 false 0 0 warnsVal' runsVal' startX startY := by
  obtain ⟨f', hf'⟩ : ∃ f', f = f' + 62 := ⟨f - 62, by omega⟩
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · rw [hf', show f' + 62 - 62 = f' from by omega]
    rw [parseRLEData_drop_551_581]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l7]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_iadd_local]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l14]
    rw [runJvmResFast_newClass]; norm_res_fuel
    rw [runJvmResFast_dup_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl31]
    rw [runJvmResFast_invokestatic_step stepStatic_uintBox_pr]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl29]
    rw [runJvmResFast_invokestatic_step stepStatic_uintBox_pr]; norm_res_fuel
    rw [runJvmResFast_invokespecial_step stepSpecial_pair_init_pr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_u32Pair hruns)]; norm_res_fuel
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l0]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l1]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l2]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l4]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l5]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l15]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l16]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [parseRLEData_drop_581_613]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl26]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_lconst_local]; norm_res_fuel
    rw [runJvmResFast_lstore_pr]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl30]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl32]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_goto]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [setLocal]

private theorem parseRLEData_step_run_363
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (warnsVal runsVal : JvmVal)
    (startX startY : Int32) (cp nextP n tag : UInt32)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 105) (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (hl25 : locs 25 = .i32 cp) (hl26 : locs 26 = .i32 nextP)
    (hl37 : locs 37 = .i32 n) (hl38 : locs 38 = .i32 0) (hl39 : locs 39 = .i32 tag)
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    let warns' :=
      if tag == 2 && cp != 111 then warns.push (.unexpectedChar (i + 1) (col + 1) cp) else warns
    ∃ f' warnsVal' locs' jh',
      f - 101 ≤ f' ∧ f' ≤ f ∧
      RleWarnRep warns' warnsVal' ∧
      HeapExtends jh jh' ∧
      jh'.statics = jh.statics ∧
      runJvmResFast f f_Algorithm_parseRLEData_prog 363
        (f_Algorithm_parseRLEData_prog.drop 363) ⟨363, [], locs, jh, hp⟩ =
      runJvmResFast f' f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs', jh', hp⟩ ∧
      RleDataLocs locs' lines numLines i true bytesAddr limit nextP (col + 1)
        0 false 0 0 warnsVal' (.ext (.u32PairGrowBuf (runs.push (tag, n)))) startX startY := by
  intro warns'
  by_cases htag2 : tag == 2
  · have htag2_eq : tag = 2 := beq_iff_eq.mp htag2
    by_cases hcp111 : cp == 111
    · have hcp_eq : cp = 111 := beq_iff_eq.mp hcp111
      have hnb : (cp != 111) = false := by simp [bne, hcp111]
      have hw' : warns' = warns := by simp [warns', hnb]
      rw [hw']
      obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 16 := ⟨f - 16, by omega⟩
      let locs1 := setLocal (setLocal (setLocal (setLocal locs 29 (.i32 n)) 30 (.i32 0))
        31 (.i32 tag)) 32 warnsVal
      have hl1 : RleDataLocs locs1 lines numLines i true bytesAddr limit p col count hasCount
          countP countCol warnsVal runsVal startX startY := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [locs1, setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7, hl.l8,
            hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]
      rcases parseRLEData_step_run_551 f0 lines numLines i bytesAddr limit p col count hasCount
        countP countCol warnsVal warnsVal runsVal runs startX startY nextP n tag locs1 jh hp
        (by omega) hruns (by simp [locs1, setLocal, hl26]) (by simp [locs1, setLocal])
        (by simp [locs1, setLocal]) (by simp [locs1, setLocal]) (by simp [locs1]) hl1
        with ⟨locs', h551, hl'⟩
      refine ⟨f0 - 62, warnsVal, locs', jh, by omega, by omega, hrep, heapExtends_refl jh, rfl,
        ?_, hl'⟩
      rw [hf0, parseRLEData_drop_363_395]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl39]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_if_icmpeq_branch htag2_eq]
      rw [parseRLEData_drop_375_395]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_if_icmpeq_branch hcp_eq]
      rw [parseRLEData_drop_385_395]
      rw [runJvmResFast_nop_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl37]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl39]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l13]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_goto]
      exact h551
    · have hne111 : cp ≠ 111 := fun h => hcp111 (beq_iff_eq.mpr h)
      let w : Algorithm.RLEWarning := .unexpectedChar (i + 1) (col + 1) cp
      have htb : (tag == 2) = true := htag2
      have hnb : (cp != 111) = true := by simp [bne, hcp111]
      have hw' : warns' = warns.push w := by simp [warns', htb, hnb, w]
      rw [hw']
      let wObj : Jvm.HeapObj AlgExt :=
        Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar"
          [("lineIndex", .i32 (i + 1)), ("columnIndex", .i32 (col + 1)), ("codePoint", .i32 cp)]
      let jh1 := (jh.alloc wObj).2
      let wAddr := jh.objects.size
      have hw_dec : decodeRLEWarning jh1 (.heapRef wAddr) = some w := by
        simp [decodeRLEWarning, jh1, wAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc, wObj, w]
        rfl
      have hw_dec' : decodeRLEWarning { objects := jh.objects.push wObj, statics := jh.statics }
          (.heapRef jh.objects.size) = some w := hw_dec
      let wVal' : JvmVal := .ext (.rleWarnGrowBuf (warns.push w))
      obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 38 := ⟨f - 38, by omega⟩
      let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal locs 34 (.i32 n)) 35 (.i32 0)) 36 (.i32 tag))
        43 wVal') 29 (.i32 n)) 30 (.i32 0)) 31 (.i32 tag)) 32 wVal'
      rcases parseRLEData_step_run_551 f0 lines numLines i bytesAddr limit p col count hasCount
        countP countCol warnsVal wVal' runsVal runs startX startY nextP n tag locs1 jh1 hp
        (by omega) hruns (by simp [locs1, setLocal, hl26]) (by simp [locs1, setLocal])
        (by simp [locs1, setLocal]) (by simp [locs1, setLocal]) (by simp [locs1])
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [locs1, setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7,
                hl.l8, hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]) with
        ⟨locs', h551, hl'⟩
      refine ⟨f0 - 62, wVal', locs', jh1, by omega, by omega, RleWarnRep.full _,
        heapExtends_alloc jh wObj, rfl, ?_, hl'⟩
      rw [hf0, parseRLEData_drop_363_395]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl39]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_if_icmpeq_branch htag2_eq]
      rw [parseRLEData_drop_375_395]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne111)]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl37]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl38]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl39]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_goto]
      rw [parseRLEData_drop_395_420]
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l13]
      rw [runJvmResFast_newClass]; norm_res_fuel
      rw [runJvmResFast_dup_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l2]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_iadd_local]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l7]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_iadd_local]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl25]
      rw [runJvmResFast_aconstNull]; norm_res_fuel
      rw [runJvmResFast_invokespecial_step stepSpecial_rleWarnUnexpectedChar_init_pr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_rleWarn hrep hw_dec')]; norm_res_fuel
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal]
      rw [runJvmResFast_astore_local]; norm_res_fuel
      rw [runJvmResFast_goto]
      exact h551
  · have hne2 : tag ≠ 2 := fun h => htag2 (beq_iff_eq.mpr h)
    have htb : (tag == 2) = false := beq_false_of_ne hne2
    have hw' : warns' = warns := by simp [warns', htb]
    rw [hw']
    obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 12 := ⟨f - 12, by omega⟩
    let locs1 := setLocal (setLocal (setLocal (setLocal locs 29 (.i32 n)) 30 (.i32 0))
      31 (.i32 tag)) 32 warnsVal
    have hl1 : RleDataLocs locs1 lines numLines i true bytesAddr limit p col count hasCount
        countP countCol warnsVal runsVal startX startY := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [locs1, setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7, hl.l8,
          hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]
    rcases parseRLEData_step_run_551 f0 lines numLines i bytesAddr limit p col count hasCount
      countP countCol warnsVal warnsVal runsVal runs startX startY nextP n tag locs1 jh hp
      (by omega) hruns (by simp [locs1, setLocal, hl26]) (by simp [locs1, setLocal])
      (by simp [locs1, setLocal]) (by simp [locs1, setLocal]) (by simp [locs1]) hl1
      with ⟨locs', h551, hl'⟩
    refine ⟨f0 - 62, warnsVal, locs', jh, by omega, by omega, hrep, heapExtends_refl jh, rfl,
      ?_, hl'⟩
    rw [hf0, parseRLEData_drop_363_395]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl39]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne2)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl37]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl38]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl39]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload_local]; norm_res_fuel; simp [setLocal, hl.l13]
    rw [runJvmResFast_astore_local]; norm_res_fuel
    rw [runJvmResFast_goto]
    exact h551

private theorem parseRLEData_step_run_337
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (warnsVal runsVal : JvmVal)
    (startX startY : Int32) (cp nextP n : UInt32)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 120) (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (hl25 : locs 25 = .i32 cp) (hl26 : locs 26 = .i32 nextP)
    (hl40 : locs 40 = .i32 0) (hl41 : locs 41 = .i32 n)
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    let tag : UInt32 := if cp == 36 then 0 else if cp == 98 then 1 else 2
    let warns' :=
      if tag == 2 && cp != 111 then warns.push (.unexpectedChar (i + 1) (col + 1) cp) else warns
    ∃ f' warnsVal' locs' jh',
      f - 115 ≤ f' ∧ f' ≤ f ∧
      RleWarnRep warns' warnsVal' ∧
      HeapExtends jh jh' ∧
      jh'.statics = jh.statics ∧
      runJvmResFast f f_Algorithm_parseRLEData_prog 337
        (f_Algorithm_parseRLEData_prog.drop 337) ⟨337, [], locs, jh, hp⟩ =
      runJvmResFast f' f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs', jh', hp⟩ ∧
      RleDataLocs locs' lines numLines i true bytesAddr limit nextP (col + 1)
        0 false 0 0 warnsVal' (.ext (.u32PairGrowBuf (runs.push (tag, n)))) startX startY := by
  intro tag warns'
  by_cases h36 : cp == 36
  · have htag : tag = 0 := by simp [tag, h36]
    dsimp only [warns']; rw [htag]
    obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 9 := ⟨f - 9, by omega⟩
    let locs1 := setLocal (setLocal (setLocal locs 37 (.i32 n)) 38 (.i32 0)) 39 (.i32 0)
    rcases parseRLEData_step_run_363 f0 lines numLines i bytesAddr limit p col count hasCount
      countP countCol warns runs warnsVal runsVal startX startY cp nextP n 0 locs1 jh hp
      (by omega) hrep hruns (by simp [locs1, setLocal, hl25]) (by simp [locs1, setLocal, hl26])
      (by simp [locs1, setLocal]) (by simp [locs1, setLocal]) (by simp [locs1])
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [locs1, setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7,
              hl.l8, hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]) with
      ⟨f', warnsVal', locs', jh', hle1, hle2, hwrep, hext, hstat, h363, hl'⟩
    refine ⟨f', warnsVal', locs', jh', by omega, by omega, hwrep, hext, hstat, ?_, hl'⟩
    rw [hf0, parseRLEData_drop_337_363]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_branch (beq_iff_eq.mp h36)]
    rw [parseRLEData_drop_357_363]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl41]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl40]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    exact h363
  · have hne36 : cp ≠ 36 := fun h => h36 (beq_iff_eq.mpr h)
    by_cases h98 : cp == 98
    · have htag : tag = 1 := by simp [tag, h36, h98]
      dsimp only [warns']; rw [htag]
      obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 13 := ⟨f - 13, by omega⟩
      let locs1 := setLocal (setLocal (setLocal locs 37 (.i32 n)) 38 (.i32 0)) 39 (.i32 1)
      rcases parseRLEData_step_run_363 f0 lines numLines i bytesAddr limit p col count hasCount
        countP countCol warns runs warnsVal runsVal startX startY cp nextP n 1 locs1 jh hp
        (by omega) hrep hruns (by simp [locs1, setLocal, hl25]) (by simp [locs1, setLocal, hl26])
        (by simp [locs1, setLocal]) (by simp [locs1, setLocal]) (by simp [locs1])
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [locs1, setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7,
                hl.l8, hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]) with
        ⟨f', warnsVal', locs', jh', hle1, hle2, hwrep, hext, hstat, h363, hl'⟩
      refine ⟨f', warnsVal', locs', jh', by omega, by omega, hwrep, hext, hstat, ?_, hl'⟩
      rw [hf0, parseRLEData_drop_337_363]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne36)]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_if_icmpeq_branch (beq_iff_eq.mp h98)]
      rw [parseRLEData_drop_350_363]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl41]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl40]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_goto]
      exact h363
    · have hne98 : cp ≠ 98 := fun h => h98 (beq_iff_eq.mpr h)
      have htag : tag = 2 := by simp [tag, h36, h98]
      dsimp only [warns']; rw [htag]
      obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 13 := ⟨f - 13, by omega⟩
      let locs1 := setLocal (setLocal (setLocal locs 37 (.i32 n)) 38 (.i32 0)) 39 (.i32 2)
      rcases parseRLEData_step_run_363 f0 lines numLines i bytesAddr limit p col count hasCount
        countP countCol warns runs warnsVal runsVal startX startY cp nextP n 2 locs1 jh hp
        (by omega) hrep hruns (by simp [locs1, setLocal, hl25]) (by simp [locs1, setLocal, hl26])
        (by simp [locs1, setLocal]) (by simp [locs1, setLocal]) (by simp [locs1])
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [locs1, setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7,
                hl.l8, hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]) with
        ⟨f', warnsVal', locs', jh', hle1, hle2, hwrep, hext, hstat, h363, hl'⟩
      refine ⟨f', warnsVal', locs', jh', by omega, by omega, hwrep, hext, hstat, ?_, hl'⟩
      rw [hf0, parseRLEData_drop_337_363]
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne36)]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne98)]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; rw [hl41]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl40]
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iconst_local]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_goto]
      exact h363

private theorem parseRLEData_step_run
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytesAddr : Nat) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (warnsVal runsVal : JvmVal)
    (startX startY : Int32) (cp nextP : UInt32)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : f ≥ 155) (hne33 : cp ≠ 33) (hne32 : cp ≠ 32) (hne9 : cp ≠ 9) (hne13 : cp ≠ 13)
    (hnov : ¬(hasCount && count > Algorithm.maxRunCount))
    (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (hl25 : locs 25 = .i32 cp) (hl26 : locs 26 = .i32 nextP)
    (hl : RleDataLocs locs lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    let n : UInt32 := if hasCount then count.toUInt32 else 1
    let tag : UInt32 := if cp == 36 then 0 else if cp == 98 then 1 else 2
    let warns' :=
      if tag == 2 && cp != 111 then warns.push (.unexpectedChar (i + 1) (col + 1) cp) else warns
    ∃ f' warnsVal' locs' jh',
      f - 148 ≤ f' ∧ f' ≤ f ∧
      RleWarnRep warns' warnsVal' ∧
      HeapExtends jh jh' ∧
      jh'.statics = jh.statics ∧
      runJvmResFast f f_Algorithm_parseRLEData_prog 230
        (f_Algorithm_parseRLEData_prog.drop 230) ⟨230, [], locs, jh, hp⟩ =
      runJvmResFast f' f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs', jh', hp⟩ ∧
      RleDataLocs locs' lines numLines i true bytesAddr limit nextP (col + 1)
        0 false 0 0 warnsVal' (.ext (.u32PairGrowBuf (runs.push (tag, n)))) startX startY := by
  intro n tag warns'
  cases hasCount with
  | false =>
    have hn : n = 1 := by simp [n]
    obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 24 := ⟨f - 24, by omega⟩
    let locs1 := setLocal (setLocal (setLocal locs 42 (.i32 0)) 40 (.i32 0)) 41 (.i32 1)
    rcases parseRLEData_step_run_337 f0 lines numLines i bytesAddr limit p col count false
      countP countCol warns runs warnsVal runsVal startX startY cp nextP 1 locs1 jh hp
      (by omega) hrep hruns (by simp [locs1, setLocal, hl25]) (by simp [locs1, setLocal, hl26])
      (by simp [locs1, setLocal]) (by simp [locs1])
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [locs1, setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7,
              hl.l8, hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]) with
      ⟨f', warnsVal', locs', jh', hle1, hle2, hwrep, hext, hstat, h337, hl'⟩
    rw [hn]
    refine ⟨f', warnsVal', locs', jh', by omega, by omega, hwrep, hext, hstat, ?_, hl'⟩
    rw [hf0, parseRLEData_drop_230_254]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne33)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne32)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne9)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne13)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l10]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_goto]
    rw [parseRLEData_drop_322_337]
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l10]
    rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_goto]
    exact h337
  | true =>
    have hnotgt : ¬((2147483647 : UInt64) < count) := by
      simpa [Algorithm.maxRunCount] using hnov
    have hn : n = count.toUInt32 := by simp [n]
    obtain ⟨f0, hf0⟩ : ∃ f0, f = f0 + 31 := ⟨f - 31, by omega⟩
    let locs1 := setLocal (setLocal (setLocal (setLocal locs 42 (.i32 0))
      43 (.i32 count.toUInt32)) 40 (.i32 0)) 41 (.i32 count.toUInt32)
    rcases parseRLEData_step_run_337 f0 lines numLines i bytesAddr limit p col count true
      countP countCol warns runs warnsVal runsVal startX startY cp nextP count.toUInt32 locs1 jh hp
      (by omega) hrep hruns (by simp [locs1, setLocal, hl25]) (by simp [locs1, setLocal, hl26])
      (by simp [locs1, setLocal]) (by simp [locs1])
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [locs1, setLocal, hl.l0, hl.l1, hl.l2, hl.l3, hl.l4, hl.l5, hl.l6, hl.l7,
              hl.l8, hl.l10, hl.l11, hl.l12, hl.l13, hl.l14, hl.l15, hl.l16]) with
      ⟨f', warnsVal', locs', jh', hle1, hle2, hwrep, hext, hstat, h337, hl'⟩
    rw [hn]
    refine ⟨f', warnsVal', locs', jh', by omega, by omega, hwrep, hext, hstat, ?_, hl'⟩
    rw [hf0, parseRLEData_drop_230_254]
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne33)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne32)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne9)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl25]
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hne13)]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; rw [hl.l10]; simp only [↓reduceIte]
    rw [runJvmResFast_ifne_branch (by decide)]
    rw [parseRLEData_drop_247_254]
    rw [runJvmResFast_lconst_local]; norm_res_fuel
    rw [runJvmResFast_lload_pr]; norm_res_fuel; rw [hl.l8]
    rw [runJvmResFast_invokestatic_step stepStatic_longCompareUnsigned_pr]; norm_res_fuel
    rw [runJvmResFast_iflt_fallthrough (by
      rw [longCompareUnsigned_slt_iff]; exact decide_eq_false hnotgt)]; norm_res_fuel
    rw [runJvmResFast_iconst_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_goto]
    rw [parseRLEData_drop_322_337]
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal, hl.l10]
    rw [runJvmResFast_ifne_branch (by decide)]
    rw [parseRLEData_drop_329_337]
    rw [runJvmResFast_lload_pr]; norm_res_fuel; simp [setLocal, hl.l8]
    rw [runJvmResFast_l2i_pr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; norm_res_fuel; simp [setLocal]
    rw [runJvmResFast_istore]; norm_res_fuel
    exact h337

private def ParseRLELoopInv (m : Nat) : Prop :=
  ∀ (f : Nat) (lines : Array String) (numLines i : UInt32) (inLine : Bool)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (bytesAddr : Nat) (warnsVal runsVal : JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes),
    parseRLEDataMeasure numLines i inLine limit p ≤ m →
    f ≥ (m + 1) * 260 + 260 →
    numLines.toNat ≤ lines.size →
    lines.size < 2 ^ 31 →
    jh.get? bytesAddr = some (.byteArray bytes.data) →
    RleWarnRep warns warnsVal →
    RlePairRep runs runsVal →
    RleDataLocs locs lines numLines i inLine bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY →
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEData lines numLines i inLine bytes limit p col
          count hasCount countP countCol warns runs startX startY) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc

private theorem parseRLEData_eq_false
    (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (hilt : i < numLines) :
    Algorithm.parseRLEData lines numLines i false bytes limit p col count hasCount
      countP countCol warns runs startX startY =
    Algorithm.parseRLEData lines numLines i true lines[i.toNat]!.toByteArray
      lines[i.toNat]!.toByteArray.size.toUInt32 0 0 0 false 0 0 warns runs startX startY := by
  conv => lhs; unfold Algorithm.parseRLEData
  simp only [hilt, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]

private theorem parseRLEData_eq_eol
    (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (hilt : i < numLines) (hplt : ¬ p < limit) :
    Algorithm.parseRLEData lines numLines i true bytes limit p col count hasCount
      countP countCol warns runs startX startY =
    Algorithm.parseRLEData lines numLines (i + 1) false bytes limit 0 0 0 false 0 0
      warns runs startX startY := by
  conv => lhs; unfold Algorithm.parseRLEData
  simp only [hilt, ↓reduceDIte, hplt, ↓reduceIte]

private theorem parseRLEData_eq_digit
    (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (hilt : i < numLines) (hplt : p < limit)
    (hdig : 48 ≤ (Algorithm.decodeCharAt bytes p limit).1 ∧
      (Algorithm.decodeCharAt bytes p limit).1 ≤ 57) :
    let r := Algorithm.decodeCharAt bytes p limit
    let cp := r.1
    let newCount := if count > 4294967296 then count else count * 10 + (cp.toUInt64 - 48)
    Algorithm.parseRLEData lines numLines i true bytes limit p col count hasCount
      countP countCol warns runs startX startY =
    Algorithm.parseRLEData lines numLines i true bytes limit r.2 (col + 1) newCount true
      (if hasCount then countP else p) (if hasCount then countCol else col)
      warns runs startX startY := by
  dsimp only
  conv => lhs; unfold Algorithm.parseRLEData
  have hdigb : ((Algorithm.decodeCharAt bytes p limit).1 ≥ 48 &&
      (Algorithm.decodeCharAt bytes p limit).1 ≤ 57) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact hdig
  simp only [hilt, ↓reduceDIte, hplt, hdigb, ite_true]

private theorem parseRLEData_eq_bang
    (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (hilt : i < numLines) (hplt : p < limit)
    (hndb : ((Algorithm.decodeCharAt bytes p limit).1 ≥ 48 &&
      (Algorithm.decodeCharAt bytes p limit).1 ≤ 57) = false)
    (hbang : ((Algorithm.decodeCharAt bytes p limit).1 == 33) = true) :
    let r := Algorithm.decodeCharAt bytes p limit
    let nextP := r.2
    let warns1 := if hasCount then
      warns.push (.unexpectedInput (i + 1) (countCol + 1)
        (Algorithm.asciiStringLossy bytes countP nextP))
      else warns
    let warns2 := if nextP < limit then
      warns1.push (.charAfterEnd (i + 1) (col + 2)
        (Algorithm.decodeCharAt bytes nextP limit).1)
      else if i + 1 < numLines then
        warns1.push (.unexpectedInput (i + 2) 1 (lines[(i + 1).toNat]!))
      else warns1
    Algorithm.parseRLEData lines numLines i true bytes limit p col count hasCount
      countP countCol warns runs startX startY =
    Algorithm.finishRLE warns2 (runs.push (0, 1)) startX startY := by
  dsimp only
  conv => lhs; unfold Algorithm.parseRLEData
  simp only [hilt, ↓reduceDIte, hplt, hndb, hbang, Bool.false_eq_true, ↓reduceIte]

private theorem parseRLEData_eq_ws
    (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (hilt : i < numLines) (hplt : p < limit)
    (hndb : ((Algorithm.decodeCharAt bytes p limit).1 ≥ 48 &&
      (Algorithm.decodeCharAt bytes p limit).1 ≤ 57) = false)
    (hbang : ((Algorithm.decodeCharAt bytes p limit).1 == 33) = false)
    (hwsb : ((Algorithm.decodeCharAt bytes p limit).1 == 32 ||
      (Algorithm.decodeCharAt bytes p limit).1 == 9 ||
      (Algorithm.decodeCharAt bytes p limit).1 == 13) = true) :
    Algorithm.parseRLEData lines numLines i true bytes limit p col count hasCount
      countP countCol warns runs startX startY =
    Algorithm.parseRLEData lines numLines i true bytes limit
      (Algorithm.decodeCharAt bytes p limit).2 (col + 1) count hasCount
      countP countCol warns runs startX startY := by
  conv => lhs; unfold Algorithm.parseRLEData
  simp only [hilt, ↓reduceDIte, hplt, hndb, hbang, hwsb, Bool.false_eq_true, ↓reduceIte]

private theorem parseRLEData_eq_overflow
    (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (hilt : i < numLines) (hplt : p < limit)
    (hndb : ((Algorithm.decodeCharAt bytes p limit).1 ≥ 48 &&
      (Algorithm.decodeCharAt bytes p limit).1 ≤ 57) = false)
    (hbang : ((Algorithm.decodeCharAt bytes p limit).1 == 33) = false)
    (hwsb : ((Algorithm.decodeCharAt bytes p limit).1 == 32 ||
      (Algorithm.decodeCharAt bytes p limit).1 == 9 ||
      (Algorithm.decodeCharAt bytes p limit).1 == 13) = false)
    (hov : (hasCount && decide (count > Algorithm.maxRunCount)) = true) :
    Algorithm.parseRLEData lines numLines i true bytes limit p col count hasCount
      countP countCol warns runs startX startY =
    ⟨.unexpectedInput (Algorithm.asciiStringLossy bytes countP p) (i + 1) (countCol + 1),
      #[], Algorithm.noCells⟩ := by
  conv => lhs; unfold Algorithm.parseRLEData
  simp only [hilt, ↓reduceDIte, hplt, hndb, hbang, hwsb, hov, Bool.false_eq_true, ↓reduceIte]

private theorem parseRLEData_eq_run
    (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (hilt : i < numLines) (hplt : p < limit)
    (hndb : ((Algorithm.decodeCharAt bytes p limit).1 ≥ 48 &&
      (Algorithm.decodeCharAt bytes p limit).1 ≤ 57) = false)
    (hbang : ((Algorithm.decodeCharAt bytes p limit).1 == 33) = false)
    (hwsb : ((Algorithm.decodeCharAt bytes p limit).1 == 32 ||
      (Algorithm.decodeCharAt bytes p limit).1 == 9 ||
      (Algorithm.decodeCharAt bytes p limit).1 == 13) = false)
    (hov : (hasCount && decide (count > Algorithm.maxRunCount)) = false) :
    let r := Algorithm.decodeCharAt bytes p limit
    let cp := r.1
    let n : UInt32 := if hasCount then count.toUInt32 else 1
    let tag : UInt32 := if cp == 36 then 0 else if cp == 98 then 1 else 2
    let warns' := if tag == 2 && cp != 111 then
      warns.push (.unexpectedChar (i + 1) (col + 1) cp) else warns
    Algorithm.parseRLEData lines numLines i true bytes limit p col count hasCount
      countP countCol warns runs startX startY =
    Algorithm.parseRLEData lines numLines i true bytes limit r.2 (col + 1) 0 false 0 0
      warns' (runs.push (tag, n)) startX startY := by
  dsimp only
  conv => lhs; unfold Algorithm.parseRLEData
  simp only [hilt, ↓reduceDIte, hplt, hndb, hbang, hwsb, hov, Bool.false_eq_true, ↓reduceIte]

private theorem parseRLEData_loop_false {m : Nat} (ih : ParseRLELoopInv m)
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (bytesAddr : Nat) (warnsVal runsVal : JvmVal)
    (locs locs1 : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hm : parseRLEDataMeasure numLines i false limit p ≤ m + 1)
    (hf : f ≥ (m + 2) * 260 + 260)
    (hsz : numLines.toNat ≤ lines.size) (hlines31 : lines.size < 2 ^ 31)
    (hilt : i < numLines)
    (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (h6_32 : runJvmResFast f f_Algorithm_parseRLEData_prog 6
      (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 19) f_Algorithm_parseRLEData_prog 32
        (f_Algorithm_parseRLEData_prog.drop 32) ⟨32, [], locs1, jh, ⟨ar, u64, asc⟩⟩)
    (hl1 : RleDataLocs locs1 lines numLines i false bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEData lines numLines i false bytes limit p col
          count hasCount countP countCol warns runs startX startY) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  have hi_lt : i.toNat < lines.size := Nat.lt_of_lt_of_le (UInt32.lt_iff_toNat_lt.mp hilt) hsz
  have hi_slt : i.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (Nat.lt_trans hi_lt hlines31)
  rcases parseRLEData_step_newLine (f - 19) lines numLines i bytesAddr limit p col count
    hasCount countP countCol warnsVal runsVal startX startY locs1 jh ⟨ar, u64, asc⟩
    (pr_fuel_ge hf (by decide)) hi_lt hi_slt hl1 with ⟨locs2, h32_6, hl2⟩
  let line := lines[i.toNat]!
  let bytes' := line.toByteArray
  let jh' := (jh.alloc (.byteArray bytes'.data)).2
  let bytesAddr' := jh.objects.size
  have hget' : jh'.get? bytesAddr' = some (.byteArray bytes'.data) := by
    simp [jh', bytesAddr', Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  have hm' : parseRLEDataMeasure numLines i true bytes'.size.toUInt32 0 ≤ m :=
    Nat.le_of_lt_succ (Nat.lt_of_lt_of_le parseRLEData_measure_newLine hm)
  rcases ih (f - 19 - 62) lines numLines i true bytes' bytes'.size.toUInt32 0 0 0 false 0 0
    warns runs startX startY bytesAddr' warnsVal runsVal locs2 jh' ar u64 asc
    hm' (by rw [Nat.sub_sub]; exact pr_fuel_step hf _ (Nat.le_refl m) (by decide))
    hsz hlines31 hget' hrep hruns hl2 with
    ⟨v, st', hrun, hdec, hext12, hstat, har, hasc⟩
  refine ⟨v, st', ?_, ?_, heapExtends_trans (heapExtends_alloc jh _) hext12, hstat, har, hasc⟩
  · rw [h6_32, h32_6]; exact hrun
  · rw [hdec, parseRLEData_eq_false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hilt]

private theorem parseRLEData_loop_true_bang
    (f f2 : Nat) (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (bytesAddr : Nat) (warnsVal runsVal : JvmVal)
    (locs locs2 : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf2 : f2 ≥ 90)
    (hsz : numLines.toNat ≤ lines.size) (hlines31 : lines.size < 2 ^ 31)
    (hilt : i < numLines) (hplt : p < limit)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (h6_230 : runJvmResFast f f_Algorithm_parseRLEData_prog 6
      (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast f2 f_Algorithm_parseRLEData_prog 230
        (f_Algorithm_parseRLEData_prog.drop 230) ⟨230, [], locs2, jh, ⟨ar, u64, asc⟩⟩)
    (hl25 : locs2 25 = JvmVal.i32 (Algorithm.decodeCharAt bytes p limit).1)
    (hl26 : locs2 26 = JvmVal.i32 (Algorithm.decodeCharAt bytes p limit).2)
    (hl2 : RleDataLocs locs2 lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY)
    (hndb : ((Algorithm.decodeCharAt bytes p limit).1 ≥ 48 &&
      (Algorithm.decodeCharAt bytes p limit).1 ≤ 57) = false)
    (hbang : (Algorithm.decodeCharAt bytes p limit).1 == 33) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEData lines numLines i true bytes limit p col
          count hasCount countP countCol warns runs startX startY) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  have hcp33 : (Algorithm.decodeCharAt bytes p limit).1 = 33 := beq_iff_eq.mp hbang
  rcases parseRLEData_step_bang f2 lines numLines i bytes bytesAddr limit p col count
    hasCount countP countCol warns runs warnsVal runsVal startX startY
    (Algorithm.decodeCharAt bytes p limit).2 locs2 jh
    ar u64 asc hf2 hsz hlines31 hilt hbytes hrep hruns (by rw [hl25, hcp33]) hl26 hl2
    with ⟨v, st', h230, hdec, hext, hstat, har, hasc⟩
  refine ⟨v, st', ?_, ?_, hext, hstat, har, hasc⟩
  · rw [h6_230]; exact h230
  · rw [hdec, parseRLEData_eq_bang _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hilt hplt hndb hbang]

private theorem parseRLEData_loop_true_ws {m : Nat} (ih : ParseRLELoopInv m)
    (f f2 : Nat) (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (bytesAddr : Nat) (warnsVal runsVal : JvmVal)
    (locs locs2 : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hm : parseRLEDataMeasure numLines i true limit p ≤ m + 1)
    (hf : f ≥ (m + 2) * 260 + 260) (hf2_1 : f - 78 ≤ f2)
    (hsz : numLines.toNat ≤ lines.size) (hlines31 : lines.size < 2 ^ 31)
    (hilt : i < numLines) (hplt : p < limit)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (h6_230 : runJvmResFast f f_Algorithm_parseRLEData_prog 6
      (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast f2 f_Algorithm_parseRLEData_prog 230
        (f_Algorithm_parseRLEData_prog.drop 230) ⟨230, [], locs2, jh, ⟨ar, u64, asc⟩⟩)
    (hl25 : locs2 25 = JvmVal.i32 (Algorithm.decodeCharAt bytes p limit).1)
    (hl26 : locs2 26 = JvmVal.i32 (Algorithm.decodeCharAt bytes p limit).2)
    (hl2 : RleDataLocs locs2 lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY)
    (hndb : ((Algorithm.decodeCharAt bytes p limit).1 ≥ 48 &&
      (Algorithm.decodeCharAt bytes p limit).1 ≤ 57) = false)
    (hbang : ((Algorithm.decodeCharAt bytes p limit).1 == 33) = false)
    (hws : (Algorithm.decodeCharAt bytes p limit).1 = 32 ∨
      (Algorithm.decodeCharAt bytes p limit).1 = 9 ∨
      (Algorithm.decodeCharAt bytes p limit).1 = 13) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEData lines numLines i true bytes limit p col
          count hasCount countP countCol warns runs startX startY) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  let r := Algorithm.decodeCharAt bytes p limit
  let cp := r.1
  let nextP := r.2
  have hm' : parseRLEDataMeasure numLines i true limit nextP ≤ m :=
    Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (parseRLEData_measure_step hplt) hm)
  have hf2 : f2 ≥ 85 := pr_fuel_ge2 hf (by decide) hf2_1
  rcases parseRLEData_step_ws f2 lines numLines i bytesAddr limit p col count
    hasCount countP countCol warnsVal runsVal startX startY cp nextP locs2 jh
    ⟨ar, u64, asc⟩ hf2 hws hl25 hl26 hl2 with ⟨f3, locs3, hle1, _, h230_6, hl3⟩
  have hf3 : f3 ≥ (m + 1) * 260 + 260 := pr_fuel_step2 hf (by decide) hf2_1 hle1
  rcases ih f3 lines numLines i true bytes limit nextP (col + 1) count hasCount
    countP countCol warns runs startX startY bytesAddr warnsVal runsVal locs3 jh
    ar u64 asc hm' hf3 hsz hlines31 hbytes hrep hruns hl3 with
    ⟨v, st', hrun, hdec, hext, hstat, har, hasc⟩
  refine ⟨v, st', ?_, ?_, hext, hstat, har, hasc⟩
  · rw [h6_230, h230_6]; exact hrun
  · have hwsb : (cp == 32 || cp == 9 || cp == 13) = true := by
      dsimp only [cp, r]
      rcases hws with h | h | h <;> rw [h] <;> rfl
    rw [hdec, parseRLEData_eq_ws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hilt hplt hndb hbang hwsb]

private theorem parseRLEData_loop_true_overflow
    (f f2 : Nat) (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (bytesAddr : Nat) (warnsVal runsVal : JvmVal)
    (locs locs2 : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hf2 : f2 ≥ 60)
    (hilt : i < numLines) (hplt : p < limit)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (h6_230 : runJvmResFast f f_Algorithm_parseRLEData_prog 6
      (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast f2 f_Algorithm_parseRLEData_prog 230
        (f_Algorithm_parseRLEData_prog.drop 230) ⟨230, [], locs2, jh, ⟨ar, u64, asc⟩⟩)
    (hl25 : locs2 25 = JvmVal.i32 (Algorithm.decodeCharAt bytes p limit).1)
    (hl2 : RleDataLocs locs2 lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY)
    (hndb : ((Algorithm.decodeCharAt bytes p limit).1 ≥ 48 &&
      (Algorithm.decodeCharAt bytes p limit).1 ≤ 57) = false)
    (hbang : ((Algorithm.decodeCharAt bytes p limit).1 == 33) = false)
    (hwsb : ((Algorithm.decodeCharAt bytes p limit).1 == 32 ||
      (Algorithm.decodeCharAt bytes p limit).1 == 9 ||
      (Algorithm.decodeCharAt bytes p limit).1 == 13) = false)
    (hne33 : (Algorithm.decodeCharAt bytes p limit).1 ≠ 33)
    (hne32 : (Algorithm.decodeCharAt bytes p limit).1 ≠ 32)
    (hne9 : (Algorithm.decodeCharAt bytes p limit).1 ≠ 9)
    (hne13 : (Algorithm.decodeCharAt bytes p limit).1 ≠ 13)
    (hov : (hasCount && decide (count > Algorithm.maxRunCount)) = true) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEData lines numLines i true bytes limit p col
          count hasCount countP countCol warns runs startX startY) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  have hhc : hasCount = true := by
    cases hasCount
    · rw [Bool.false_and] at hov; exact absurd hov Bool.false_ne_true
    · rfl
  have hgt : Algorithm.maxRunCount < count := by
    rw [hhc, Bool.true_and, decide_eq_true_eq] at hov
    exact hov
  subst hhc
  rcases parseRLEData_step_overflow f2 lines numLines i bytes bytesAddr limit p col
    count countP countCol warnsVal runsVal startX startY
    (Algorithm.decodeCharAt bytes p limit).1 locs2 jh ar u64 asc
    hf2 hne33 hne32 hne9 hne13 hgt hbytes hl25 hl2 with
    ⟨v, st', h230, hdec, hext, hstat, har, hasc⟩
  refine ⟨v, st', ?_, ?_, hext, hstat, har, hasc⟩
  · rw [h6_230]; exact h230
  · rw [hdec, parseRLEData_eq_overflow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hilt hplt hndb
      hbang hwsb hov]

private theorem parseRLEData_loop_true_run {m : Nat} (ih : ParseRLELoopInv m)
    (f f2 : Nat) (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (bytesAddr : Nat) (warnsVal runsVal : JvmVal)
    (locs locs2 : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hm : parseRLEDataMeasure numLines i true limit p ≤ m + 1)
    (hf : f ≥ (m + 2) * 260 + 260) (hf2_1 : f - 78 ≤ f2)
    (hsz : numLines.toNat ≤ lines.size) (hlines31 : lines.size < 2 ^ 31)
    (hilt : i < numLines) (hplt : p < limit)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (h6_230 : runJvmResFast f f_Algorithm_parseRLEData_prog 6
      (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast f2 f_Algorithm_parseRLEData_prog 230
        (f_Algorithm_parseRLEData_prog.drop 230) ⟨230, [], locs2, jh, ⟨ar, u64, asc⟩⟩)
    (hl25 : locs2 25 = JvmVal.i32 (Algorithm.decodeCharAt bytes p limit).1)
    (hl26 : locs2 26 = JvmVal.i32 (Algorithm.decodeCharAt bytes p limit).2)
    (hl2 : RleDataLocs locs2 lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY)
    (hndb : ((Algorithm.decodeCharAt bytes p limit).1 ≥ 48 &&
      (Algorithm.decodeCharAt bytes p limit).1 ≤ 57) = false)
    (hbang : ((Algorithm.decodeCharAt bytes p limit).1 == 33) = false)
    (hwsb : ((Algorithm.decodeCharAt bytes p limit).1 == 32 ||
      (Algorithm.decodeCharAt bytes p limit).1 == 9 ||
      (Algorithm.decodeCharAt bytes p limit).1 == 13) = false)
    (hne33 : (Algorithm.decodeCharAt bytes p limit).1 ≠ 33)
    (hne32 : (Algorithm.decodeCharAt bytes p limit).1 ≠ 32)
    (hne9 : (Algorithm.decodeCharAt bytes p limit).1 ≠ 9)
    (hne13 : (Algorithm.decodeCharAt bytes p limit).1 ≠ 13)
    (hov : (hasCount && decide (count > Algorithm.maxRunCount)) = false) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEData lines numLines i true bytes limit p col
          count hasCount countP countCol warns runs startX startY) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  let r := Algorithm.decodeCharAt bytes p limit
  let cp := r.1
  let nextP := r.2
  have hm' : parseRLEDataMeasure numLines i true limit nextP ≤ m :=
    Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (parseRLEData_measure_step hplt) hm)
  have hf2 : f2 ≥ 155 := pr_fuel_ge2 hf (by decide) hf2_1
  rcases parseRLEData_step_run f2 lines numLines i bytesAddr limit p col count
    hasCount countP countCol warns runs warnsVal runsVal startX startY cp nextP
    locs2 jh ⟨ar, u64, asc⟩ hf2 hne33 hne32 hne9 hne13 (by simp [hov]) hrep hruns hl25 hl26
    hl2 with ⟨f3, warnsVal', locs3, jh', hle1, _, hwrep', hext01, hstat01, h230_6, hl3⟩
  have hbytes' : jh'.get? bytesAddr = some (.byteArray bytes.data) := hext01 bytesAddr _ hbytes
  have hf3 : f3 ≥ (m + 1) * 260 + 260 := pr_fuel_step2 hf (by decide) hf2_1 hle1
  let n : UInt32 := if hasCount then count.toUInt32 else 1
  let tag : UInt32 := if cp == 36 then 0 else if cp == 98 then 1 else 2
  let warns' := if tag == 2 && cp != 111 then
    warns.push (.unexpectedChar (i + 1) (col + 1) cp) else warns
  rcases ih f3 lines numLines i true bytes limit nextP (col + 1) 0 false 0 0
    warns' (runs.push (tag, n)) startX startY bytesAddr warnsVal'
    (.ext (.u32PairGrowBuf (runs.push (tag, n)))) locs3 jh' ar u64 asc
    hm' hf3 hsz hlines31 hbytes' hwrep' (RlePairRep.full _) hl3 with
    ⟨v, st', hrun, hdec, hext12, hstat12, har, hasc⟩
  refine ⟨v, st', ?_, ?_, heapExtends_trans hext01 hext12, hstat12.trans hstat01, har, hasc⟩
  · rw [h6_230, h230_6]; exact hrun
  · rw [hdec, parseRLEData_eq_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hilt hplt hndb hbang hwsb hov]

private theorem parseRLEData_loop_true_nondigit {m : Nat} (ih : ParseRLELoopInv m)
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (bytesAddr : Nat) (warnsVal runsVal : JvmVal)
    (locs locs2 : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hm : parseRLEDataMeasure numLines i true limit p ≤ m + 1)
    (hf : f ≥ (m + 2) * 260 + 260)
    (hsz : numLines.toNat ≤ lines.size) (hlines31 : lines.size < 2 ^ 31)
    (hilt : i < numLines) (hplt : p < limit)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (h6_197 : runJvmResFast f f_Algorithm_parseRLEData_prog 6
      (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 19 - 51) f_Algorithm_parseRLEData_prog 197
        (f_Algorithm_parseRLEData_prog.drop 197) ⟨197, [], locs2, jh, ⟨ar, u64, asc⟩⟩)
    (hl25 : locs2 25 = JvmVal.i32 (Algorithm.decodeCharAt bytes p limit).1)
    (hl26 : locs2 26 = JvmVal.i32 (Algorithm.decodeCharAt bytes p limit).2)
    (hl2 : RleDataLocs locs2 lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY)
    (hdig : ¬ (48 ≤ (Algorithm.decodeCharAt bytes p limit).1 ∧
      (Algorithm.decodeCharAt bytes p limit).1 ≤ 57)) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEData lines numLines i true bytes limit p col
          count hasCount countP countCol warns runs startX startY) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  let cp := (Algorithm.decodeCharAt bytes p limit).1
  rcases parseRLEData_step_to_230 (f - 19 - 51) cp locs2 jh ⟨ar, u64, asc⟩
    (by rw [Nat.sub_sub]; exact pr_fuel_ge hf (by decide)) hdig hl25 with
    ⟨f2, hf2_1, _, h197_230⟩
  have hndb : (cp ≥ 48 && cp ≤ 57) = false := by
    rw [Bool.and_eq_false_iff]
    by_cases h1 : 48 ≤ cp
    · exact Or.inr (decide_eq_false (fun h2 => hdig ⟨h1, h2⟩))
    · exact Or.inl (decide_eq_false h1)
  by_cases hbang : (cp == 33) = true
  · exact parseRLEData_loop_true_bang f f2 lines numLines i bytes limit p col count hasCount
      countP countCol warns runs startX startY bytesAddr warnsVal runsVal locs locs2 jh
      ar u64 asc (pr_fuel_ge2 hf (by decide) hf2_1) hsz hlines31 hilt hplt hbytes hrep hruns
      (h6_197.trans h197_230) hl25 hl26 hl2 hndb hbang
  · have hbang' : (cp == 33) = false := Bool.eq_false_iff.mpr hbang
    have hne33 : cp ≠ 33 := fun h => hbang (beq_iff_eq.mpr h)
    by_cases hws : cp = 32 ∨ cp = 9 ∨ cp = 13
    · exact parseRLEData_loop_true_ws ih f f2 lines numLines i bytes limit p col count
        hasCount countP countCol warns runs startX startY bytesAddr warnsVal runsVal
        locs locs2 jh ar u64 asc hm hf hf2_1 hsz hlines31 hilt hplt hbytes hrep hruns
        (h6_197.trans h197_230) hl25 hl26 hl2 hndb hbang' hws
    · have hne32 : cp ≠ 32 := fun h => hws (Or.inl h)
      have hne9 : cp ≠ 9 := fun h => hws (Or.inr (Or.inl h))
      have hne13 : cp ≠ 13 := fun h => hws (Or.inr (Or.inr h))
      have hwsb : (cp == 32 || cp == 9 || cp == 13) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        exact ⟨⟨hne32, hne9⟩, hne13⟩
      by_cases hov : (hasCount && decide (count > Algorithm.maxRunCount)) = true
      · exact parseRLEData_loop_true_overflow f f2 lines numLines i bytes limit p col count
          hasCount countP countCol warns runs startX startY bytesAddr warnsVal runsVal
          locs locs2 jh ar u64 asc (pr_fuel_ge2 hf (by decide) hf2_1) hilt hplt hbytes
          (h6_197.trans h197_230) hl25 hl2 hndb hbang' hwsb hne33 hne32 hne9 hne13 hov
      · exact parseRLEData_loop_true_run ih f f2 lines numLines i bytes limit p col count
          hasCount countP countCol warns runs startX startY bytesAddr warnsVal runsVal
          locs locs2 jh ar u64 asc hm hf hf2_1 hsz hlines31 hilt hplt hbytes hrep hruns
          (h6_197.trans h197_230) hl25 hl26 hl2 hndb hbang' hwsb hne33 hne32 hne9 hne13
          (Bool.eq_false_iff.mpr hov)

private theorem parseRLEData_loop_true_digit {m : Nat} (ih : ParseRLELoopInv m)
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (bytesAddr : Nat) (warnsVal runsVal : JvmVal)
    (locs locs2 : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hm : parseRLEDataMeasure numLines i true limit p ≤ m + 1)
    (hf : f ≥ (m + 2) * 260 + 260)
    (hsz : numLines.toNat ≤ lines.size) (hlines31 : lines.size < 2 ^ 31)
    (hilt : i < numLines) (hplt : p < limit)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (h6_197 : runJvmResFast f f_Algorithm_parseRLEData_prog 6
      (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 19 - 51) f_Algorithm_parseRLEData_prog 197
        (f_Algorithm_parseRLEData_prog.drop 197) ⟨197, [], locs2, jh, ⟨ar, u64, asc⟩⟩)
    (hl2_18 : locs2 18 = JvmVal.i32 1)
    (hl25 : locs2 25 = JvmVal.i32 (Algorithm.decodeCharAt bytes p limit).1)
    (hl26 : locs2 26 = JvmVal.i32 (Algorithm.decodeCharAt bytes p limit).2)
    (hl2 : RleDataLocs locs2 lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY)
    (hdig : 48 ≤ (Algorithm.decodeCharAt bytes p limit).1 ∧
      (Algorithm.decodeCharAt bytes p limit).1 ≤ 57) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEData lines numLines i true bytes limit p col
          count hasCount countP countCol warns runs startX startY) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  let r := Algorithm.decodeCharAt bytes p limit
  let cp := r.1
  let nextP := r.2
  have hm' : parseRLEDataMeasure numLines i true limit nextP ≤ m :=
    Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (parseRLEData_measure_step hplt) hm)
  rcases parseRLEData_step_digit (f - 19 - 51) lines numLines i bytesAddr limit p col
    count hasCount countP countCol warnsVal runsVal startX startY cp nextP locs2 jh
    ⟨ar, u64, asc⟩ (by rw [Nat.sub_sub]; exact pr_fuel_ge hf (by decide)) hdig.1 hdig.2
    hl2_18 hl25 hl26 hl2 with ⟨f3, locs3, hle1, _, h197_6, hl3⟩
  let newCount :=
    if count > 4294967296 then count else count * 10 + (cp.toUInt64 - 48)
  have hf3 : f3 ≥ (m + 1) * 260 + 260 := pr_fuel_step1 hf hle1
  rcases ih f3 lines numLines i true bytes limit nextP (col + 1) newCount true
    (if hasCount then countP else p) (if hasCount then countCol else col)
    warns runs startX startY bytesAddr warnsVal runsVal locs3 jh ar u64 asc
    hm' hf3 hsz hlines31 hbytes hrep hruns hl3 with
    ⟨v, st', hrun, hdec, hext, hstat, har, hasc⟩
  refine ⟨v, st', ?_, ?_, hext, hstat, har, hasc⟩
  · rw [h6_197, h197_6]; exact hrun
  · rw [hdec, parseRLEData_eq_digit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hilt hplt hdig]

private theorem parseRLEData_loop_true_eol {m : Nat} (ih : ParseRLELoopInv m)
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (bytesAddr : Nat) (warnsVal runsVal : JvmVal)
    (locs locs1 : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hm : parseRLEDataMeasure numLines i true limit p ≤ m + 1)
    (hf : f ≥ (m + 2) * 260 + 260)
    (hsz : numLines.toNat ≤ lines.size) (hlines31 : lines.size < 2 ^ 31)
    (hilt : i < numLines) (hplt : ¬ p < limit)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (h6_32 : runJvmResFast f f_Algorithm_parseRLEData_prog 6
      (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 19) f_Algorithm_parseRLEData_prog 32
        (f_Algorithm_parseRLEData_prog.drop 32) ⟨32, [], locs1, jh, ⟨ar, u64, asc⟩⟩)
    (hl1 : RleDataLocs locs1 lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEData lines numLines i true bytes limit p col
          count hasCount countP countCol warns runs startX startY) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  rcases parseRLEData_step_eol (f - 19) lines numLines i bytesAddr limit p col count
    hasCount countP countCol warnsVal runsVal startX startY locs1 jh ⟨ar, u64, asc⟩
    (pr_fuel_ge hf (by decide)) hplt hl1 with ⟨locs2, h32_6, hl2⟩
  have hm' : parseRLEDataMeasure numLines (i + 1) false limit 0 ≤ m :=
    Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (parseRLEData_measure_eol hilt) hm)
  rcases ih (f - 19 - 60) lines numLines (i + 1) false bytes limit 0 0 0 false 0 0
    warns runs startX startY bytesAddr warnsVal runsVal locs2 jh ar u64 asc
    hm' (by rw [Nat.sub_sub]; exact pr_fuel_step hf m (Nat.le_refl m) (by decide))
    hsz hlines31 hbytes hrep hruns hl2 with
    ⟨v, st', hrun, hdec, hext, hstat, har, hasc⟩
  refine ⟨v, st', ?_, ?_, hext, hstat, har, hasc⟩
  · rw [h6_32, h32_6]; exact hrun
  · rw [hdec, parseRLEData_eq_eol _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hilt hplt]

private theorem parseRLEData_loop_true {m : Nat} (ih : ParseRLELoopInv m)
    (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (limit p col : UInt32) (count : UInt64) (hasCount : Bool)
    (countP countCol : UInt32) (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (bytesAddr : Nat) (warnsVal runsVal : JvmVal)
    (locs locs1 : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hm : parseRLEDataMeasure numLines i true limit p ≤ m + 1)
    (hf : f ≥ (m + 2) * 260 + 260)
    (hsz : numLines.toNat ≤ lines.size) (hlines31 : lines.size < 2 ^ 31)
    (hilt : i < numLines)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hrep : RleWarnRep warns warnsVal) (hruns : RlePairRep runs runsVal)
    (h6_32 : runJvmResFast f f_Algorithm_parseRLEData_prog 6
      (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 19) f_Algorithm_parseRLEData_prog 32
        (f_Algorithm_parseRLEData_prog.drop 32) ⟨32, [], locs1, jh, ⟨ar, u64, asc⟩⟩)
    (hl18 : locs1 18 = JvmVal.i32 1)
    (hl1 : RleDataLocs locs1 lines numLines i true bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEData_prog 6
        (f_Algorithm_parseRLEData_prog.drop 6) ⟨6, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEData lines numLines i true bytes limit p col
          count hasCount countP countCol warns runs startX startY) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = jh.statics ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  by_cases hplt : p < limit
  · rcases parseRLEData_step_decode (f - 19) lines numLines i bytes bytesAddr limit p col
      count hasCount countP countCol warnsVal runsVal startX startY locs1 jh ⟨ar, u64, asc⟩
      (pr_fuel_ge hf (by decide)) hplt hbytes hl1 with ⟨locs2, h32_197, hl2_18, hl25, hl26, hl2⟩
    by_cases hdig : 48 ≤ (Algorithm.decodeCharAt bytes p limit).1 ∧
        (Algorithm.decodeCharAt bytes p limit).1 ≤ 57
    · exact parseRLEData_loop_true_digit ih f lines numLines i bytes limit p col count
        hasCount countP countCol warns runs startX startY bytesAddr warnsVal runsVal
        locs locs2 jh ar u64 asc hm hf hsz hlines31 hilt hplt hbytes hrep hruns
        (h6_32.trans h32_197) (hl2_18.trans hl18) hl25 hl26 hl2 hdig
    · exact parseRLEData_loop_true_nondigit ih f lines numLines i bytes limit p col count
        hasCount countP countCol warns runs startX startY bytesAddr warnsVal runsVal
        locs locs2 jh ar u64 asc hm hf hsz hlines31 hilt hplt hbytes hrep hruns
        (h6_32.trans h32_197) hl25 hl26 hl2 hdig
  · exact parseRLEData_loop_true_eol ih f lines numLines i bytes limit p col count
      hasCount countP countCol warns runs startX startY bytesAddr warnsVal runsVal
      locs locs1 jh ar u64 asc hm hf hsz hlines31 hilt hplt hbytes hrep hruns h6_32 hl1

private theorem parseRLEData_loop (m : Nat) : ParseRLELoopInv m := by
  induction m with
  | zero =>
    intro f lines numLines i inLine bytes limit p col count hasCount countP countCol
      warns runs startX startY bytesAddr warnsVal runsVal locs jh ar u64 asc
      hm hf hsz hlines31 hbytes hrep hruns hl
    exfalso
    cases inLine <;> simp only [parseRLEDataMeasure, Bool.false_eq_true, ↓reduceIte] at hm <;> omega
  | succ m ih =>
    intro f lines numLines i inLine bytes limit p col count hasCount countP countCol
      warns runs startX startY bytesAddr warnsVal runsVal locs jh ar u64 asc
      hm hf hsz hlines31 hbytes hrep hruns hl
    by_cases hilt : i < numLines
    · rcases parseRLEData_step_head_lt f lines numLines i inLine bytesAddr limit p col count
        hasCount countP countCol warnsVal runsVal startX startY locs jh ⟨ar, u64, asc⟩
        (by omega) hilt hl with ⟨locs1, h6_32, hl18, hl1⟩
      cases inLine with
      | false =>
        exact parseRLEData_loop_false ih f lines numLines i bytes limit p col count
          hasCount countP countCol warns runs startX startY bytesAddr warnsVal runsVal
          locs locs1 jh ar u64 asc hm hf hsz hlines31 hilt hrep hruns h6_32 hl1
      | true =>
        exact parseRLEData_loop_true ih f lines numLines i bytes limit p col count
          hasCount countP countCol warns runs startX startY bytesAddr warnsVal runsVal
          locs locs1 jh ar u64 asc hm hf hsz hlines31 hilt hbytes hrep hruns h6_32 hl18 hl1
    · let res := Algorithm.finishRLE warns runs startX startY
      let enc := encodeRLEResult jh u64 res
      refine ⟨enc.1, _, parseRLEData_step_finish f lines numLines i inLine bytesAddr limit p col
        count hasCount countP countCol warns runs warnsVal runsVal startX startY locs jh ar u64 asc
        (pr_fuel_ge (a := 0) hf (by decide)) hilt hrep hruns hl, ?_,
        encodeRLEResult_heapExtends jh u64 res, encodeRLEResult_statics jh u64 res, rfl, rfl⟩
      have heq : Algorithm.parseRLEData lines numLines i inLine bytes limit p col count hasCount
          countP countCol warns runs startX startY = res := by
        unfold Algorithm.parseRLEData
        simp only [hilt, ↓reduceDIte, res]
      rw [heq]
      exact decodeRLEResult_encode_proj 31 [enc.1] _ jh ar u64 asc res

theorem parseRLEData_equiv
    (lines : Array String) (numLines i : UInt32) (inLine : Bool)
    (bytes : ByteArray) (limit p col : UInt32)
    (count : UInt64) (hasCount : Bool) (countP countCol : UInt32)
    (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32))
    (startX startY : Int32)
    (bytesAddr : Nat) (warnsVal runsVal : JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hstat : jh.statics = [])
    (hsz : numLines.toNat ≤ lines.size)
    (hlines31 : lines.size < 2 ^ 31)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hrep : RleWarnRep warns warnsVal)
    (hruns : RlePairRep runs runsVal)
    (hl0 : locs 0 = .strArr lines)
    (hl1 : locs 1 = .i32 numLines)
    (hl2 : locs 2 = .i32 i)
    (hl3 : locs 3 = .i32 (if inLine then 1 else 0))
    (hl4 : locs 4 = .heapRef bytesAddr)
    (hl5 : locs 5 = .i32 limit)
    (hl6 : locs 6 = .i32 p)
    (hl7 : locs 7 = .i32 col)
    (hl8 : locs 8 = .i64 count)
    (hl10 : locs 10 = .i32 (if hasCount then 1 else 0))
    (hl11 : locs 11 = .i32 countP)
    (hl12 : locs 12 = .i32 countCol)
    (hl13 : locs 13 = warnsVal)
    (hl14 : locs 14 = runsVal)
    (hl15 : locs 15 = .i32 startX.toUInt32)
    (hl16 : locs 16 = .i32 startY.toUInt32) :
    ∃ f v st', runJvmRes f f_Algorithm_parseRLEData_prog ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeRLEResult st' v =
        some (Algorithm.parseRLEData lines numLines i inLine bytes limit p col
          count hasCount countP countCol warns runs startX startY) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.jvmHeap.statics = [] ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  let m := parseRLEDataMeasure numLines i inLine limit p
  let f := (m + 1) * 260 + 266
  have hl : RleDataLocs locs lines numLines i inLine bytesAddr limit p col count hasCount
      countP countCol warnsVal runsVal startX startY :=
    ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl10, hl11, hl12, hl13, hl14, hl15, hl16⟩
  rcases parseRLEData_loop m (f - 6) lines numLines i inLine bytes limit p col count hasCount
    countP countCol warns runs startX startY bytesAddr warnsVal runsVal locs jh ar u64 asc
    (Nat.le_refl m) (by omega) hsz hlines31 hbytes hrep hruns hl with
    ⟨v, st', hrun, hdec, hext, hst, har, hasc⟩
  refine ⟨f, v, st', ?_, hdec, hext, hst.trans hstat, har, hasc⟩
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  conv => lhs; arg 4; rw [parseRLEData_drop_0_6]
  split_res_fuel 6
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl0]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam_local rfl)]; norm_res_fuel
  rw [runJvmResFast_aload_local]; norm_res_fuel; rw [hl4]
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParam_local rfl)]; norm_res_fuel
  exact hrun

end ParseRLEData

end Algorithm.JvmVerification
