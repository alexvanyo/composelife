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

/-! ### Sub-batch 2C: Plaintext (`serializePlaintext___closed__1`, `deserializePlaintext*`) -/

theorem serializePlaintext___closed__1_equiv :
    ∃ v st', runJvmRes 30 f_Algorithm_serializePlaintext___closed__1_prog (initJvmState []) =
        some (v, st') ∧
      decodeStrArray st' v = some #["."] := by
  refine ⟨.heapRef 1, ⟨25, [.heapRef 1], setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
        0 (.str ".")) 1 (.heapRef 0)) 2 (.heapRef 1)) 3 (.heapRef 1)) 4 (.i32 0),
      ⟨#[.objArray "java/lang/Object" #[], .objArray "java/lang/Object" #[.str "."]], []⟩, {}⟩, ?_, rfl⟩
  rw [runJvmRes_of_runJvmResFast0 30 _ _ _ rfl]
  dsimp only [f_Algorithm_serializePlaintext___closed__1_prog, initJvmState, Jvm.initJvmState, List.foldl]
  rw [runJvmResFast_stepResHeapChunk 25]
  conv => lhs; arg 1; jvm_whnf_blk
  rfl

/-! #### Monotonic heap encoding & `GrowBuf PlaintextWarning` invariant -/

private def HeapExtends (h1 h2 : Jvm.JvmHeap AlgExt) : Prop :=
  ∀ i obj, h1.get? i = some obj → h2.get? i = some obj

private theorem heapExtends_refl (h : Jvm.JvmHeap AlgExt) : HeapExtends h h :=
  fun _ _ hget => hget

private theorem heapExtends_trans {h1 h2 h3 : Jvm.JvmHeap AlgExt}
    (h12 : HeapExtends h1 h2) (h23 : HeapExtends h2 h3) : HeapExtends h1 h3 :=
  fun i obj hi => h23 i obj (h12 i obj hi)

private theorem heapExtends_alloc (h : Jvm.JvmHeap AlgExt) (obj : Jvm.HeapObj AlgExt) :
    HeapExtends h (h.alloc obj).2 := by
  intro i o hget
  simp only [Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc] at hget ⊢
  have hlt : i < h.objects.size := by
    by_cases h' : i < h.objects.size
    · exact h'
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt h')] at hget
      contradiction
  rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt]
  exact hget

private theorem decodePlaintextWarning_mono {h1 h2 : Jvm.JvmHeap AlgExt}
    (hext : HeapExtends h1 h2) {v : JvmVal} {w : Algorithm.PlaintextWarning}
    (hdec : decodePlaintextWarning h1 v = some w) : decodePlaintextWarning h2 v = some w := by
  cases v with
  | heapRef a =>
    dsimp only [decodePlaintextWarning] at hdec ⊢
    cases hg : h1.get? a with
    | none => simp [hg] at hdec
    | some obj =>
      rw [hg] at hdec
      rw [hext a obj hg]
      exact hdec
  | _ => simp [decodePlaintextWarning] at hdec

private theorem mapM_decodePlaintextWarning_mono {h1 h2 : Jvm.JvmHeap AlgExt}
    (hext : HeapExtends h1 h2) {vs : List JvmVal} {ws : List Algorithm.PlaintextWarning}
    (hm : vs.mapM (decodePlaintextWarning h1) = some ws) :
    vs.mapM (decodePlaintextWarning h2) = some ws := by
  induction vs generalizing ws with
  | nil => simpa using hm
  | cons v vs ih =>
    simp only [List.mapM_cons] at hm ⊢
    cases hdv : decodePlaintextWarning h1 v with
    | none => simp [hdv] at hm
    | some w =>
      rw [decodePlaintextWarning_mono hext hdv]
      rw [hdv] at hm
      cases hrest : vs.mapM (decodePlaintextWarning h1) with
      | none => simp [hrest] at hm
      | some ws' =>
        rw [hrest] at hm
        rw [ih hrest]
        exact hm

private theorem encodePlaintextWarning_spec (h : Jvm.JvmHeap AlgExt)
    (w : Algorithm.PlaintextWarning) :
    HeapExtends h (encodePlaintextWarning h w).2 ∧
      decodePlaintextWarning (encodePlaintextWarning h w).2 (encodePlaintextWarning h w).1 = some w := by
  cases w with
  | blankLine ln =>
    refine ⟨heapExtends_alloc _ _, ?_⟩
    simp [encodePlaintextWarning, decodePlaintextWarning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup]
  | shortLine ln =>
    refine ⟨heapExtends_alloc _ _, ?_⟩
    simp [encodePlaintextWarning, decodePlaintextWarning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup]
  | unexpectedChar ln col cp =>
    refine ⟨heapExtends_alloc _ _, ?_⟩
    simp [encodePlaintextWarning, decodePlaintextWarning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup]

private theorem encodeGrowBufArray_foldl_ptWarn
    (xs : List Algorithm.PlaintextWarning) (acc : Array JvmVal)
    (h : Jvm.JvmHeap AlgExt) (pfx : List Algorithm.PlaintextWarning)
    (hpfx : acc.toList.mapM (decodePlaintextWarning h) = some pfx) :
    let step : Array JvmVal × Jvm.JvmHeap AlgExt → Algorithm.PlaintextWarning → Array JvmVal × Jvm.JvmHeap AlgExt :=
      fun p x => (p.1.push (encodePlaintextWarning p.2 x).1, (encodePlaintextWarning p.2 x).2)
    HeapExtends h (xs.foldl step (acc, h)).2 ∧
      (xs.foldl step (acc, h)).1.toList.mapM (decodePlaintextWarning (xs.foldl step (acc, h)).2) =
        some (pfx ++ xs) := by
  intro step
  induction xs generalizing acc h pfx with
  | nil => exact ⟨heapExtends_refl h, by simpa using hpfx⟩
  | cons x xs ih =>
    simp only [List.foldl_cons, step]
    have hs := encodePlaintextWarning_spec h x
    have hnext : ((acc.push (encodePlaintextWarning h x).1).toList.mapM
        (decodePlaintextWarning (encodePlaintextWarning h x).2)) = some (pfx ++ [x]) := by
      simp only [Array.toList_push, List.mapM_append, List.mapM_cons, List.mapM_nil]
      rw [mapM_decodePlaintextWarning_mono hs.1 hpfx, hs.2]
      rfl
    have hrec := ih (acc.push (encodePlaintextWarning h x).1) (encodePlaintextWarning h x).2
      (pfx ++ [x]) hnext
    refine ⟨heapExtends_trans hs.1 hrec.1, ?_⟩
    simpa [List.append_assoc, step] using hrec.2

private theorem encodeGrowBufArray_decode_ptWarn (h : Jvm.JvmHeap AlgExt)
    (b : Algorithm.GrowBuf Algorithm.PlaintextWarning) :
    let (v, h') := encodeGrowBufArray h encodePlaintextWarning b
    HeapExtends h h' ∧
      ∃ addr warnVals, v = .heapRef addr ∧ h'.get? addr = some (.objArray "java/lang/Object" warnVals) ∧
        warnVals.toList.mapM (decodePlaintextWarning h') = some b.toArray.toList := by
  dsimp only [encodeGrowBufArray]
  simp only [← Array.foldl_toList]
  have hfl := encodeGrowBufArray_foldl_ptWarn b.toArray.toList #[] h [] rfl
  dsimp only at hfl
  let res := b.toArray.toList.foldl
    (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) x =>
      (p.1.push (encodePlaintextWarning p.2 x).1, (encodePlaintextWarning p.2 x).2))
    (#[], h)
  have halloc := heapExtends_alloc res.2 (.objArray "java/lang/Object" res.1)
  refine ⟨heapExtends_trans hfl.1 halloc, res.2.objects.size, res.1, rfl, ?_, ?_⟩
  · dsimp only [res]
    simp only [Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    exact Array.getElem?_push_size
  · rw [List.nil_append] at hfl
    exact mapM_decodePlaintextWarning_mono halloc hfl.2

private inductive PtWarnRep : Algorithm.GrowBuf Algorithm.PlaintextWarning → JvmVal → Prop
  | empty (b : Algorithm.GrowBuf Algorithm.PlaintextWarning)
      (he : b.data.isEmpty = true) (hz : b.size = 0) :
      PtWarnRep b (.ext (.strGrowBuf Algorithm.GrowBuf.empty))
  | full (b : Algorithm.GrowBuf Algorithm.PlaintextWarning) :
      PtWarnRep b (.ext (.ptWarnGrowBuf b))

private theorem ptWarnRep_empty :
    PtWarnRep (Algorithm.GrowBuf.empty : Algorithm.GrowBuf Algorithm.PlaintextWarning)
      (.ext (.strGrowBuf Algorithm.GrowBuf.empty)) :=
  PtWarnRep.empty _ rfl rfl

private theorem growBuf_eq_empty_of {α : Type} {b : Algorithm.GrowBuf α}
    (he : b.data.isEmpty = true) (hz : b.size = 0) : b = Algorithm.GrowBuf.empty := by
  have hd : b.data = #[] := Array.isEmpty_iff.mp he
  rcases b with ⟨d, s⟩
  dsimp only at hd hz
  subst hd hz
  simp [Algorithm.GrowBuf.empty]

private theorem decodePlaintextWarning_not_rle_or_mc {jh : Jvm.JvmHeap AlgExt}
    {v : JvmVal} {w : Algorithm.PlaintextWarning}
    (hdec : decodePlaintextWarning jh v = some w) :
    decodeRLEWarning jh v = none ∧ decodeMacrocellWarning jh v = none := by
  cases v with
  | heapRef a =>
    dsimp only [decodePlaintextWarning] at hdec
    cases hg : jh.get? a with
    | none => simp [hg] at hdec
    | some obj =>
      rw [hg] at hdec
      cases obj with
      | «instance» cls flds =>
        by_cases h1 : cls = "com/alexvanyo/composelife/model/PlaintextWarning$BlankLine" <;>
        by_cases h2 : cls = "com/alexvanyo/composelife/model/PlaintextWarning$ShortLine" <;>
        by_cases h3 : cls = "com/alexvanyo/composelife/model/PlaintextWarning$UnexpectedChar" <;>
          simp [decodeRLEWarning, decodeMacrocellWarning, hg, h1, h2, h3] at hdec ⊢
      | _ => simp at hdec
  | _ => simp [decodePlaintextWarning] at hdec

private theorem stepStatic_growBufPush_ptWarn
    {pc : Nat} {wVal bufVal : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {b : Algorithm.GrowBuf Algorithm.PlaintextWarning} {w : Algorithm.PlaintextWarning}
    (hrep : PtWarnRep b bufVal) (hdec : decodePlaintextWarning jh wVal = some w) :
    stepInvokeStatic ⟨pc, wVal :: bufVal :: rest, locs, jh, hp⟩
      "PlaintextLeanKt" "f_Algorithm_GrowBuf_push___redArg"
      "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.ptWarnGrowBuf (b.push w)) :: rest, locs, jh, hp⟩) := by
  have hnot := decodePlaintextWarning_not_rle_or_mc hdec
  cases hrep with
  | empty he hz =>
    have hb : b = Algorithm.GrowBuf.empty := growBuf_eq_empty_of he hz
    subst hb
    cases wVal with
    | heapRef a =>
      have hstep : stepInvokeStatic
          ⟨pc, .heapRef a :: .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: rest, locs, jh, hp⟩
          "PlaintextLeanKt" "f_Algorithm_GrowBuf_push___redArg"
          "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
          (if (Algorithm.GrowBuf.empty : Algorithm.GrowBuf String).data.isEmpty &&
              (Algorithm.GrowBuf.empty : Algorithm.GrowBuf String).size == 0 then
            let ext? : Option AlgExt :=
              match decodeRLEWarning jh (.heapRef a) with
              | some w => some (.rleWarnGrowBuf (Algorithm.GrowBuf.empty.push w))
              | none =>
                match decodeMacrocellWarning jh (.heapRef a) with
                | some w => some (.mcWarnGrowBuf (Algorithm.GrowBuf.empty.push w))
                | none => (decodePlaintextWarning jh (.heapRef a)).map fun w =>
                    .ptWarnGrowBuf (Algorithm.GrowBuf.empty.push w)
            match ext? with
            | some e => .inl (some ⟨pc + 1, .ext e :: rest, locs, jh, hp⟩)
            | none => .inr none
          else .inr none) := rfl
      rw [hstep]
      simp only [show (Algorithm.GrowBuf.empty : Algorithm.GrowBuf String).data.isEmpty = true from rfl,
        show ((Algorithm.GrowBuf.empty : Algorithm.GrowBuf String).size == 0) = true from rfl,
        Bool.and_self, ↓reduceIte, hnot.1, hnot.2, hdec, Option.map_some]
    | _ => simp [decodePlaintextWarning] at hdec
  | full =>
    cases wVal with
    | heapRef a =>
      have hstep : stepInvokeStatic ⟨pc, .heapRef a :: .ext (.ptWarnGrowBuf b) :: rest, locs, jh, hp⟩
          "PlaintextLeanKt" "f_Algorithm_GrowBuf_push___redArg"
          "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
          (match decodePlaintextWarning jh (.heapRef a) with
          | some w => .inl (some ⟨pc + 1, .ext (.ptWarnGrowBuf (b.push w)) :: rest, locs, jh, hp⟩)
          | none => .inr none) := rfl
      rw [hstep, hdec]
    | _ => simp [decodePlaintextWarning] at hdec

private theorem stepStatic_growBufToArray_ptWarn
    {pc : Nat} {bufVal : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {b : Algorithm.GrowBuf Algorithm.PlaintextWarning}
    (hrep : PtWarnRep b bufVal) :
    ∃ (arrVal : JvmVal) (jh' : Jvm.JvmHeap AlgExt) (warnVals? : Option Nat),
      stepInvokeStatic ⟨pc, bufVal :: rest, locs, jh, hp⟩
        "PlaintextLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
        "(Ljava/lang/Object;)[Ljava/lang/Object;" =
        .inl (some ⟨pc + 1, arrVal :: rest, locs, jh', hp⟩) ∧
      match warnVals? with
      | none => arrVal = .strArr #[] ∧ jh' = jh ∧ b.toArray = #[]
      | some addr =>
        arrVal = .heapRef addr ∧
        ∃ warnVals, jh'.get? addr = some (.objArray "java/lang/Object" warnVals) ∧
          warnVals.toList.mapM (decodePlaintextWarning jh') = some b.toArray.toList := by
  cases hrep with
  | empty he hz =>
    have hb : b = Algorithm.GrowBuf.empty := growBuf_eq_empty_of he hz
    subst hb
    refine ⟨JvmVal.strArr #[], jh, none, rfl, rfl, rfl, by decide⟩
  | full =>
    have hdec := encodeGrowBufArray_decode_ptWarn jh b
    dsimp only at hdec
    rcases hdec with ⟨_, addr, warnVals, hv, hg, hm⟩
    refine ⟨(encodeGrowBufArray jh encodePlaintextWarning b).1,
      (encodeGrowBufArray jh encodePlaintextWarning b).2, some addr, rfl, hv, warnVals, hg, hm⟩

private theorem cellBits_u32_eq (x y : UInt32) :
    x.toUInt64 <<< ((32 : UInt32) &&& 63).toUInt64 + (y.toUInt64 &&& 4294967295) =
      Algorithm.cellBits (x.toInt32, y.toInt32) := by
  have hmask : y.toUInt64 &&& 4294967295 = y.toUInt64 := by
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i hlt64
    simp only [UInt64.toBitVec_and, BitVec.getLsbD_and, UInt32.toBitVec_toUInt64,
      BitVec.getLsbD_setWidth, hlt64, decide_true, Bool.true_and]
    rw [show UInt64.toBitVec 4294967295 = 4294967295#64 from rfl]
    by_cases hi32 : i < 32
    · have h64 : (4294967295#64).getLsbD i = true := by
        rw [BitVec.getLsbD_eq_getElem hlt64]; revert i hlt64 hi32; decide
      simp only [h64, Bool.and_true]
    · have hy64 : y.toBitVec.getLsbD i = false :=
        @BitVec.getLsbD_of_ge 32 y.toBitVec i (Nat.le_of_not_lt hi32)
      simp only [hy64, Bool.false_and]
  have hsh : ((32 : UInt32) &&& 63).toUInt64 = 32 := rfl
  rw [hsh]
  simp [Algorithm.cellBits, Algorithm.cellKey, hmask]

/-! #### Pure helper for inner row scan (`inRow = true`) -/

private def plaintextRowStep (bytes : ByteArray) (limit p col i rowIdx : UInt32)
    (warns : Algorithm.GrowBuf Algorithm.PlaintextWarning) (cells : Algorithm.U64Buf) :
    Algorithm.GrowBuf Algorithm.PlaintextWarning × Algorithm.U64Buf :=
  if hp : p < limit then
    let r := Algorithm.decodeCharAt bytes p limit
    let _ := Algorithm.decodeCharAt_next bytes p limit hp
    let cp := r.1
    if cp == 46 then
      plaintextRowStep bytes limit r.2 (col + 1) i rowIdx warns cells
    else if cp == 79 then
      plaintextRowStep bytes limit r.2 (col + 1) i rowIdx warns
        (Algorithm.U64Buf.push cells (Algorithm.cellBits (col.toInt32, rowIdx.toInt32)))
    else
      let newWarns := warns.push (.unexpectedChar (i + 1) (col + 1) cp)
      let newCells := if cp == 32 then cells
        else Algorithm.U64Buf.push cells (Algorithm.cellBits (col.toInt32, rowIdx.toInt32))
      plaintextRowStep bytes limit r.2 (col + 1) i rowIdx newWarns newCells
  else (warns, cells)
termination_by limit.toNat - p.toNat
decreasing_by
  all_goals
    (have _ := Algorithm.decodeCharAt_next bytes p limit hp
     have hlt := UInt32.lt_iff_toNat_lt.mp hp
     omega)

private theorem deserializePlaintext_loop_row_eq
    (m : Nat) (lines : Array String) (numLines i : UInt32) (bytes : ByteArray)
    (limit p col rowIdx longestIdx longestLen : UInt32) (hasLongest : Bool)
    (warns : Algorithm.GrowBuf Algorithm.PlaintextWarning) (cells : Algorithm.U64Buf)
    (hm : limit.toNat - p.toNat ≤ m) (hi : i < numLines) :
    Algorithm.deserializePlaintext.loop lines numLines i true bytes limit p col rowIdx
        longestIdx longestLen hasLongest warns cells =
      let res := plaintextRowStep bytes limit p col i rowIdx warns cells
      Algorithm.deserializePlaintext.loop lines numLines (i + 1) false bytes limit 0 0 (rowIdx + 1)
        longestIdx longestLen hasLongest res.1 res.2 := by
  induction m generalizing p col warns cells with
  | zero =>
    have hnot : ¬(p < limit) := by
      intro hp; have := UInt32.lt_iff_toNat_lt.mp hp; omega
    rw [Algorithm.deserializePlaintext.loop, plaintextRowStep]
    simp [hi, hnot]
  | succ m ih =>
    by_cases hp : p < limit
    · have hnext := Algorithm.decodeCharAt_next bytes p limit hp
      rw [Algorithm.deserializePlaintext.loop, plaintextRowStep]
      simp only [hi, ↓reduceDIte, ↓reduceIte, hp]
      split
      · exact ih _ (col + 1) warns cells (by omega)
      · split
        · exact ih _ (col + 1) warns _ (by omega)
        · exact ih _ (col + 1) _ _ (by omega)
    · rw [Algorithm.deserializePlaintext.loop, plaintextRowStep]
      simp [hi, hp]

/-! #### Row-scan JVM stepping lemmas (`pc = 9` with `inRow = true`) -/

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

private theorem setLocal_eq_self {Ext : Type} {locs : Nat → Jvm.JvmVal Ext} {idx : Nat} {v : Jvm.JvmVal Ext}
    (h : locs idx = v) : setLocal locs idx v = locs := by
  funext i; simp only [setLocal, Jvm.setLocal]; split <;> simp_all

private theorem stepInstr_istore {Ext Heap : Type} (hooks : Jvm.JvmHooks Ext Heap)
    {pc idx : Nat} {v : Jvm.JvmVal Ext} {stkRest : List (Jvm.JvmVal Ext)}
    {locs : Nat → Jvm.JvmVal Ext} {jh : Jvm.JvmHeap Ext} {hp : Heap} :
    Jvm.stepInstr hooks (.istore idx) ⟨pc, v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stkRest, Jvm.setLocal locs idx v, jh, hp⟩) := by
  unfold Jvm.stepInstr; rfl

private theorem runJvmResFast_istore {f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.istore idx :: rest) ⟨pc0, v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stkRest, setLocal locs idx v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) (stepInstr_istore algHooks) rfl

private structure PtRowLocs (locs : Nat → JvmVal) (lines : Array String)
    (numLines i : UInt32) (inRow : Bool) (bytesAddr : Nat)
    (limit p col rowIdx longestIdx longestLen : UInt32) (hasLongest : Bool)
    (warnsVal : JvmVal) (accId : Nat) : Prop where
  h0 : locs 0 = .strArr lines
  h1 : locs 1 = .i32 numLines
  h2 : locs 2 = .i32 i
  h3 : locs 3 = .i32 (if inRow then 1 else 0)
  h4 : locs 4 = .heapRef bytesAddr
  h5 : locs 5 = .i32 limit
  h6 : locs 6 = .i32 p
  h7 : locs 7 = .i32 col
  h8 : locs 8 = .i32 rowIdx
  h9 : locs 9 = .i32 longestIdx
  h10 : locs 10 = .i32 longestLen
  h11 : locs 11 = .i32 (if hasLongest then 1 else 0)
  h12 : locs 12 = warnsVal
  h13 : locs 13 = .ext (.u64Ref accId)

section
set_option maxRecDepth 2048

private theorem pt_pc9_to_417
    {f : Nat} {lines : Array String} {numLines i : UInt32} {bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen : UInt32} {hasLongest : Bool}
    {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 6 ≤ f) (hlt : i < numLines) (hlocs : PtRowLocs locs lines numLines i true bytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 9
      (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs, jh, hp⟩ =
      runJvmResFast (f - 6) f_Algorithm_deserializePlaintext_loop_prog 417
        (f_Algorithm_deserializePlaintext_loop_prog.drop 417) ⟨417, [], locs, jh, hp⟩ := by
  split_res_fuel 6
  step_drop 4
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [hlocs.h1, hlocs.h2]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt)]
  norm_res_fuel
  step_drop 2
  rw [runJvmResFast_stepResHeapChunk 1]; (conv => lhs; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont]; norm_res_fuel
  dsimp only; rw [hlocs.h3]; simp only [↓reduceIte]
  rw [runJvmResFast_ifne_branch (v := 1) (by decide)]

private theorem pt_row_exit
    {f : Nat} {lines : Array String} {numLines i : UInt32} {bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen : UInt32} {hasLongest : Bool}
    {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 61 ≤ f) (hnot : ¬(p < limit))
    (hlocs : PtRowLocs locs lines numLines i true bytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 417
        (f_Algorithm_deserializePlaintext_loop_prog.drop 417) ⟨417, [], locs, jh, hp⟩ =
        runJvmResFast (f - 61) f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs', jh, hp⟩ ∧
      PtRowLocs locs' lines numLines (i + 1) false bytesAddr
        limit 0 0 (rowIdx + 1) longestIdx longestLen hasLongest warnsVal accId := by
  cases hlocs
  apply Exists.intro
  constructor
  · split_res_fuel 61
    step_drop 4
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 5 = _›, ‹locs 6 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hnot)]
    norm_res_fuel
    step_drop 57
    rw [← setLocal_eq_self ‹locs 2 = _›, ← setLocal_eq_self ‹locs 8 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]
  · constructor <;> (try dsimp only [setLocal]) <;> simp [*]

private theorem pt_row_pre
    {f : Nat} {lines : Array String} {numLines i : UInt32} {bytesAddr : Nat}
    {bytes : ByteArray} {limit p col rowIdx longestIdx longestLen : UInt32}
    {hasLongest : Bool} {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 19 ≤ f) (hpLt : p < limit)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hlocs : PtRowLocs locs lines numLines i true bytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    let r := Algorithm.decodeCharAt bytes p limit
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 417
        (f_Algorithm_deserializePlaintext_loop_prog.drop 417) ⟨417, [], locs, jh, hp⟩ =
        runJvmResFast (f - 19) f_Algorithm_deserializePlaintext_loop_prog 493
          (f_Algorithm_deserializePlaintext_loop_prog.drop 493) ⟨493, [], locs', jh, hp⟩ ∧
      locs' 15 = .i32 r.1 ∧ locs' 16 = .i32 r.2 ∧
      PtRowLocs locs' lines numLines i true bytesAddr
        limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId := by
  cases hlocs
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_⟩
  · split_res_fuel 19
    step_drop 4
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 5 = _›, ‹locs 6 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hpLt)]
    norm_res_fuel
    step_drop 15
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 4 = _›, ‹locs 5 = _›, ‹locs 6 = _›]
    rw [runJvmResFast_invokestatic_step
      (stepStatic_decodeCharAt_heap (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hbytes)]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
    rw [runJvmResFast_stepResHeapChunk 2]; (conv => lhs; arg 1; jvm_whnf_blk)
    rw [afterResBlockChunk_cont]; norm_res_fuel; dsimp only; rfl
  · simp [setLocal]
  · simp [setLocal]
  · constructor <;> (try dsimp only [setLocal]) <;> simp [*]

private theorem pt_row_dot
    {f : Nat} {lines : Array String} {numLines i : UInt32} {bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen cp pNext : UInt32}
    {hasLongest : Bool} {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 59 ≤ f) (hcp : cp = 46)
    (h15 : locs 15 = .i32 cp) (h16 : locs 16 = .i32 pNext)
    (hlocs : PtRowLocs locs lines numLines i true bytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 493
        (f_Algorithm_deserializePlaintext_loop_prog.drop 493) ⟨493, [], locs, jh, hp⟩ =
        runJvmResFast (f - 59) f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs', jh, hp⟩ ∧
      PtRowLocs locs' lines numLines i true bytesAddr
        limit pNext (col + 1) rowIdx longestIdx longestLen hasLongest warnsVal accId := by
  cases hlocs
  apply Exists.intro
  constructor
  · split_res_fuel 59
    step_drop 3
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h15]
    rw [runJvmResFast_if_icmpeq_branch hcp]; norm_res_fuel
    step_drop 56
    rw [← setLocal_eq_self ‹locs 7 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]
  · constructor <;> (try dsimp only [setLocal]) <;> simp [*]

private theorem pt_row_alive
    {f : Nat} {lines : Array String} {numLines i : UInt32} {bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen cp pNext : UInt32}
    {hasLongest : Bool} {warnsVal : JvmVal} {accId : Nat} {acc : Array UInt64}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hf : 81 ≤ f) (hne46 : (cp == 46) = false) (hcp : cp = 79)
    (h15 : locs 15 = .i32 cp) (h16 : locs 16 = .i32 pNext)
    (hu : u64[accId]? = some acc)
    (hlocs : PtRowLocs locs lines numLines i true bytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 493
        (f_Algorithm_deserializePlaintext_loop_prog.drop 493) ⟨493, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        runJvmResFast (f - 81) f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9)
          ⟨9, [], locs', jh,
            ⟨ar, u64 ++ [Algorithm.U64Buf.push acc (Algorithm.cellBits (col.toInt32, rowIdx.toInt32))], asc⟩⟩ ∧
      PtRowLocs locs' lines numLines i true bytesAddr
        limit pNext (col + 1) rowIdx longestIdx longestLen hasLongest warnsVal u64.length := by
  have hcb := cellBits_u32_eq col rowIdx
  cases hlocs
  apply Exists.intro
  constructor
  · split_res_fuel 81
    step_drop 6
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h15]
    rw [runJvmResFast_if_icmpeq_fallthrough hne46]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h15]
    rw [runJvmResFast_if_icmpeq_branch hcp]; norm_res_fuel
    step_drop 75
    rw [← setLocal_eq_self ‹locs 7 = _›, ← setLocal_eq_self ‹locs 8 = _›, ← setLocal_eq_self ‹locs 13 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [hcb]
    rw [runJvmResFast_invokestatic_step
      (stepStatic_u64BufPush_heap (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hu)]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]
  · constructor <;> (try dsimp only [setLocal]) <;> simp [*]

private theorem pt_row_unexp_space
    {f : Nat} {lines : Array String} {numLines i : UInt32} {bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen cp pNext : UInt32}
    {hasLongest : Bool} {warns : Algorithm.GrowBuf Algorithm.PlaintextWarning}
    {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 76 ≤ f) (hne46 : (cp == 46) = false) (hne79 : (cp == 79) = false) (hcp : cp = 32)
    (h15 : locs 15 = .i32 cp) (h16 : locs 16 = .i32 pNext)
    (hw : PtWarnRep warns warnsVal)
    (hlocs : PtRowLocs locs lines numLines i true bytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    let w := Algorithm.PlaintextWarning.unexpectedChar (i + 1) (col + 1) cp
    let obj : Jvm.HeapObj AlgExt := .instance "com/alexvanyo/composelife/model/PlaintextWarning$UnexpectedChar"
      [("lineIndex", .i32 (i + 1)), ("columnIndex", .i32 (col + 1)), ("codePoint", .i32 cp)]
    let jh' := (jh.alloc obj).2
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 493
        (f_Algorithm_deserializePlaintext_loop_prog.drop 493) ⟨493, [], locs, jh, hp⟩ =
        runJvmResFast (f - 76) f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs', jh', hp⟩ ∧
      PtRowLocs locs' lines numLines i true bytesAddr
        limit pNext (col + 1) rowIdx longestIdx longestLen hasLongest
        (.ext (.ptWarnGrowBuf (warns.push w))) accId := by
  intro w obj jh'
  have hdecNew : decodePlaintextWarning jh' (.heapRef jh.objects.size) = some w := by
    simp [jh', obj, w, decodePlaintextWarning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup]
  cases hlocs
  apply Exists.intro
  constructor
  · split_res_fuel 76
    step_drop 27
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h15]
    rw [runJvmResFast_if_icmpeq_fallthrough hne46]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h15]
    rw [runJvmResFast_if_icmpeq_fallthrough hne79]; norm_res_fuel
    rw [← setLocal_eq_self ‹locs 2 = _›, ← setLocal_eq_self ‹locs 7 = _›,
      ← setLocal_eq_self ‹locs 12 = _›, ← setLocal_eq_self h15]
    heap_step_nonbranch_chunks; norm_res_fuel
    dsimp only [Jvm.JvmState.jvmHeap]
    rw [runJvmResFast_invokespecial_step rfl]; norm_res_fuel
    dsimp only [Jvm.JvmState.jvmHeap]
    have hjh' : (⟨jh.objects.push obj, jh.statics⟩ : Jvm.JvmHeap AlgExt) = jh' := rfl
    rw [hjh']
    rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_ptWarn hw hdecNew)]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_branch hcp]; norm_res_fuel
    step_drop 49
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]
  · constructor <;> (try dsimp only [setLocal, w]) <;> simp [*]

private theorem pt_row_unexp_alive
    {f : Nat} {lines : Array String} {numLines i : UInt32} {bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen cp pNext : UInt32}
    {hasLongest : Bool} {warns : Algorithm.GrowBuf Algorithm.PlaintextWarning}
    {warnsVal : JvmVal} {accId : Nat} {acc : Array UInt64} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hf : 95 ≤ f) (hne46 : (cp == 46) = false) (hne79 : (cp == 79) = false)
    (hne32 : (cp == 32) = false)
    (h15 : locs 15 = .i32 cp) (h16 : locs 16 = .i32 pNext)
    (hw : PtWarnRep warns warnsVal) (hu : u64[accId]? = some acc)
    (hlocs : PtRowLocs locs lines numLines i true bytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    let w := Algorithm.PlaintextWarning.unexpectedChar (i + 1) (col + 1) cp
    let obj : Jvm.HeapObj AlgExt := .instance "com/alexvanyo/composelife/model/PlaintextWarning$UnexpectedChar"
      [("lineIndex", .i32 (i + 1)), ("columnIndex", .i32 (col + 1)), ("codePoint", .i32 cp)]
    let jh' := (jh.alloc obj).2
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 493
        (f_Algorithm_deserializePlaintext_loop_prog.drop 493) ⟨493, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        runJvmResFast (f - 95) f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9)
          ⟨9, [], locs', jh',
            ⟨ar, u64 ++ [Algorithm.U64Buf.push acc (Algorithm.cellBits (col.toInt32, rowIdx.toInt32))], asc⟩⟩ ∧
      PtRowLocs locs' lines numLines i true bytesAddr
        limit pNext (col + 1) rowIdx longestIdx longestLen hasLongest
        (.ext (.ptWarnGrowBuf (warns.push w))) u64.length := by
  intro w obj jh'
  have hcb := cellBits_u32_eq col rowIdx
  have hdecNew : decodePlaintextWarning jh' (.heapRef jh.objects.size) = some w := by
    simp [jh', obj, w, decodePlaintextWarning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup]
  cases hlocs
  apply Exists.intro
  constructor
  · split_res_fuel 95
    step_drop 27
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h15]
    rw [runJvmResFast_if_icmpeq_fallthrough hne46]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h15]
    rw [runJvmResFast_if_icmpeq_fallthrough hne79]; norm_res_fuel
    rw [← setLocal_eq_self ‹locs 2 = _›, ← setLocal_eq_self ‹locs 7 = _›,
      ← setLocal_eq_self ‹locs 8 = _›, ← setLocal_eq_self ‹locs 12 = _›,
      ← setLocal_eq_self ‹locs 13 = _›, ← setLocal_eq_self h15]
    heap_step_nonbranch_chunks; norm_res_fuel
    dsimp only [Jvm.JvmState.jvmHeap]
    rw [runJvmResFast_invokespecial_step rfl]; norm_res_fuel
    dsimp only [Jvm.JvmState.jvmHeap]
    have hjh' : (⟨jh.objects.push obj, jh.statics⟩ : Jvm.JvmHeap AlgExt) = jh' := rfl
    rw [hjh']
    rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_ptWarn hw hdecNew)]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_if_icmpeq_fallthrough hne32]; norm_res_fuel
    step_drop 68
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [hcb]
    rw [runJvmResFast_invokestatic_step
      (stepStatic_u64BufPush_heap (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hu)]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]
  · constructor <;> (try dsimp only [setLocal, w]) <;> simp [*]

private theorem deserializePlaintext_row_jvm
    (mBytes : Nat) (f fTail : Nat) (lines : Array String) (numLines i : UInt32)
    (bytesAddr : Nat) (bytes : ByteArray)
    (limit p col rowIdx longestIdx longestLen : UInt32) (hasLongest : Bool)
    (warns : Algorithm.GrowBuf Algorithm.PlaintextWarning) (warnsVal : JvmVal)
    (accId : Nat) (acc : Algorithm.U64Buf) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hlt : i < numLines) (hm : limit.toNat - p.toNat ≤ mBytes)
    (hf : mBytes * 120 + 67 + fTail ≤ f)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hw : PtWarnRep warns warnsVal) (hu : u64[accId]? = some acc)
    (hlocs : PtRowLocs locs lines numLines i true bytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    let res := plaintextRowStep bytes limit p col i rowIdx warns acc
    ∃ f' locs' warnsVal' jh' u64',
      fTail ≤ f' ∧
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 9
        (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        runJvmResFast f' f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs', jh', ⟨ar, u64', asc⟩⟩ ∧
      PtWarnRep res.1 warnsVal' ∧
      (∃ accId', u64'[accId']? = some res.2 ∧
        PtRowLocs locs' lines numLines (i + 1) false bytesAddr
          limit 0 0 (rowIdx + 1) longestIdx longestLen hasLongest warnsVal' accId') := by
  induction mBytes generalizing f p col warns warnsVal accId acc locs jh u64 with
  | zero =>
    have hnot : ¬(p < limit) := by
      intro hp; have := UInt32.lt_iff_toNat_lt.mp hp; omega
    have hrow : plaintextRowStep bytes limit p col i rowIdx warns acc = (warns, acc) := by
      rw [plaintextRowStep]; simp [hnot]
    have hp1 := pt_pc9_to_417 (f := f) (jh := jh) (hp := ⟨ar, u64, asc⟩) (by omega) hlt hlocs
    rcases pt_row_exit (f := f - 6) (jh := jh) (hp := ⟨ar, u64, asc⟩) (by omega) hnot hlocs with
      ⟨locs', hex, hlocs'⟩
    refine ⟨f - 6 - 61, locs', warnsVal, jh, u64, by omega, ?_, ?_, accId, ?_, hlocs'⟩
    · rw [hp1, hex]
    · rw [hrow]; exact hw
    · rw [hrow]; exact hu
  | succ m ih =>
    by_cases hp : p < limit
    · have hnext := Algorithm.decodeCharAt_next bytes p limit hp
      have hmNext : limit.toNat - (Algorithm.decodeCharAt bytes p limit).2.toNat ≤ m := by omega
      have hp1 := pt_pc9_to_417 (f := f) (jh := jh) (hp := ⟨ar, u64, asc⟩) (by omega) hlt hlocs
      rcases pt_row_pre (f := f - 6) (jh := jh) (hp := ⟨ar, u64, asc⟩) (by omega) hp hbytes hlocs with
        ⟨locs1, hp2, h15, h16, hlocs1⟩
      let r := Algorithm.decodeCharAt bytes p limit
      let cp := r.1
      by_cases h46 : cp = 46
      · have hrow : plaintextRowStep bytes limit p col i rowIdx warns acc =
            plaintextRowStep bytes limit r.2 (col + 1) i rowIdx warns acc := by
          rw [plaintextRowStep]; simp [hp]; dsimp only [cp, r] at h46 ⊢; simp [h46]
        rcases pt_row_dot (f := f - 6 - 19) (jh := jh) (hp := ⟨ar, u64, asc⟩) (by omega) h46 h15 h16 hlocs1 with
          ⟨locs2, hp3, hlocs2⟩
        rcases ih (f - 6 - 19 - 59) r.2 (col + 1) warns warnsVal accId acc locs2 jh u64
            (by dsimp only [r]; exact hmNext) (by omega) hbytes hw hu hlocs2 with
          ⟨f', locs', wv', jh', u64', hf', hrec, hw', accId', hu', hlocs'⟩
        refine ⟨f', locs', wv', jh', u64', hf', ?_, ?_, accId', ?_, hlocs'⟩
        · rw [hp1, hp2, hp3]; exact hrec
        · rw [hrow]; exact hw'
        · rw [hrow]; exact hu'
      · have hne46 : (cp == 46) = false := beq_false_of_ne h46
        by_cases h79 : cp = 79
        · let acc' := Algorithm.U64Buf.push acc (Algorithm.cellBits (col.toInt32, rowIdx.toInt32))
          have hrow : plaintextRowStep bytes limit p col i rowIdx warns acc =
              plaintextRowStep bytes limit r.2 (col + 1) i rowIdx warns acc' := by
            rw [plaintextRowStep]; simp [hp]; dsimp only [cp, r, acc'] at h79 ⊢; simp [h79]
          rcases pt_row_alive (f := f - 6 - 19) (jh := jh) (ar := ar) (asc := asc)
              (by omega) hne46 h79 h15 h16 hu hlocs1 with ⟨locs2, hp3, hlocs2⟩
          rcases ih (f - 6 - 19 - 81) r.2 (col + 1) warns warnsVal u64.length acc' locs2 jh (u64 ++ [acc'])
              (by dsimp only [r]; exact hmNext) (by omega) hbytes hw (by simp [acc']) hlocs2 with
              ⟨f', locs', wv', jh', u64', hf', hrec, hw', accId', hu', hlocs'⟩
          refine ⟨f', locs', wv', jh', u64', hf', ?_, ?_, accId', ?_, hlocs'⟩
          · rw [hp1, hp2, hp3]; exact hrec
          · rw [hrow]; exact hw'
          · rw [hrow]; exact hu'
        · have hne79 : (cp == 79) = false := beq_false_of_ne h79
          let w := Algorithm.PlaintextWarning.unexpectedChar (i + 1) (col + 1) cp
          let obj : Jvm.HeapObj AlgExt := .«instance»
            "com/alexvanyo/composelife/model/PlaintextWarning$UnexpectedChar"
            [("lineIndex", .i32 (i + 1)), ("columnIndex", .i32 (col + 1)), ("codePoint", .i32 cp)]
          let jh1 := (jh.alloc obj).2
          have hbytes1 : jh1.get? bytesAddr = some (.byteArray bytes.data) :=
            heapExtends_alloc jh obj bytesAddr _ hbytes
          by_cases h32 : cp = 32
          · have hrow : plaintextRowStep bytes limit p col i rowIdx warns acc =
                plaintextRowStep bytes limit r.2 (col + 1) i rowIdx (warns.push w) acc := by
              rw [plaintextRowStep]; simp [hp]; dsimp only [cp, r, w] at h32 ⊢; simp [h32]
            rcases pt_row_unexp_space (f := f - 6 - 19) (jh := jh) (hp := ⟨ar, u64, asc⟩)
                (by omega) hne46 hne79 h32 h15 h16 hw hlocs1 with ⟨locs2, hp3, hlocs2⟩
            rcases ih (f - 6 - 19 - 76) r.2 (col + 1) (warns.push w) _ accId acc locs2 jh1 u64
                (by dsimp only [r]; exact hmNext) (by omega) hbytes1 (PtWarnRep.full _) hu hlocs2 with
                ⟨f', locs', wv', jh', u64', hf', hrec, hw', accId', hu', hlocs'⟩
            refine ⟨f', locs', wv', jh', u64', hf', ?_, ?_, accId', ?_, hlocs'⟩
            · rw [hp1, hp2, hp3]; exact hrec
            · rw [hrow]; exact hw'
            · rw [hrow]; exact hu'
          · have hne32 : (cp == 32) = false := beq_false_of_ne h32
            let acc' := Algorithm.U64Buf.push acc (Algorithm.cellBits (col.toInt32, rowIdx.toInt32))
            have hrow : plaintextRowStep bytes limit p col i rowIdx warns acc =
                plaintextRowStep bytes limit r.2 (col + 1) i rowIdx (warns.push w) acc' := by
              rw [plaintextRowStep]; simp [hp]; dsimp only [cp, r, w, acc'] at h46 h79 h32 ⊢; simp [h46, h79, h32]
            rcases pt_row_unexp_alive (f := f - 6 - 19) (jh := jh) (ar := ar) (asc := asc)
                (by omega) hne46 hne79 hne32 h15 h16 hw hu hlocs1 with ⟨locs2, hp3, hlocs2⟩
            rcases ih (f - 6 - 19 - 95) r.2 (col + 1) (warns.push w) _ u64.length acc' locs2 jh1 (u64 ++ [acc'])
                (by dsimp only [r]; exact hmNext) (by omega) hbytes1 (PtWarnRep.full _) (by simp [acc']) hlocs2 with
                ⟨f', locs', wv', jh', u64', hf', hrec, hw', accId', hu', hlocs'⟩
            refine ⟨f', locs', wv', jh', u64', hf', ?_, ?_, accId', ?_, hlocs'⟩
            · rw [hp1, hp2, hp3]; exact hrec
            · rw [hrow]; exact hw'
            · rw [hrow]; exact hu'
    · have hrow : plaintextRowStep bytes limit p col i rowIdx warns acc = (warns, acc) := by
        rw [plaintextRowStep]; simp [hp]
      have hp1 := pt_pc9_to_417 (f := f) (jh := jh) (hp := ⟨ar, u64, asc⟩) (by omega) hlt hlocs
      rcases pt_row_exit (f := f - 6) (jh := jh) (hp := ⟨ar, u64, asc⟩) (by omega) hp hlocs with
        ⟨locs', hex, hlocs'⟩
      refine ⟨f - 6 - 61, locs', warnsVal, jh, u64, by omega, ?_, ?_, accId, ?_, hlocs'⟩
      · rw [hp1, hex]
      · rw [hrow]; exact hw
      · rw [hrow]; exact hu

/-! #### Outer line loop (`inRow = false`), base exit, and top-level `deserializePlaintext` -/

private def linesMaxBytes (lines : Array String) : Nat :=
  lines.foldl (fun acc s => max acc s.toByteArray.size) 0

private theorem foldl_max_ge (xs : List String) (init x : Nat) (h : x ≤ init) :
    x ≤ xs.foldl (fun acc s => max acc s.toByteArray.size) init := by
  induction xs generalizing init with
  | nil => exact h
  | cons _ xs ih => exact ih _ (Nat.le_trans h (Nat.le_max_left _ _))

private theorem list_getElem_le_foldl_max (xs : List String) (k : Nat) (hk : k < xs.length) (init : Nat) :
    xs[k].toByteArray.size ≤ xs.foldl (fun acc s => max acc s.toByteArray.size) init := by
  induction xs generalizing k init with
  | nil => simp at hk
  | cons y ys ih =>
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero, List.foldl_cons]
      exact foldl_max_ge ys _ _ (Nat.le_max_right _ _)
    | succ k' =>
      simp only [List.getElem_cons_succ, List.foldl_cons]
      exact ih k' (by simp only [List.length_cons] at hk; omega) _

private theorem le_linesMaxBytes (lines : Array String) (k : Nat) (hk : k < lines.size) :
    lines[k].toByteArray.size ≤ linesMaxBytes lines := by
  dsimp only [linesMaxBytes]
  rw [← Array.foldl_toList]
  exact list_getElem_le_foldl_max lines.toList k hk 0

private theorem u32_slt_zero_false_of_lt {x : UInt32} (hx : x.toNat < 2 ^ 31) :
    x.toBitVec.slt 0#32 = false := by
  have hx0 : x.toBitVec.toNat < 2 ^ 31 := hx
  rw [BitVec.slt_eq_decide, BitVec.toInt_zero]
  have hle : (0 : Int) ≤ x.toBitVec.toInt := by
    rw [BitVec.toInt_eq_toNat_cond]
    split <;> omega
  exact decide_eq_false (Int.not_lt.mpr hle)

private theorem baload_u8_eq_33_of_eq {b : UInt8} (hb : b = 33) :
    UInt32.ofBitVec (b.toBitVec.signExtend 32) = 33 := by
  subst hb; decide

private theorem baload_u8_eq_33_of_ne {b : UInt8} (hb : b ≠ 33) :
    (UInt32.ofBitVec (b.toBitVec.signExtend 32) == 33) = false := by
  apply beq_false_of_ne
  intro heq
  apply hb
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h := congrArg (fun x : UInt32 => x.toBitVec.getLsbD k) heq
  have hk32 : k < 32 := by omega
  simp only [BitVec.getLsbD_signExtend, hk32, decide_true, Bool.true_and] at h
  have hk8 : k < 8 := hk
  simp only [hk8, ↓reduceIte] at h
  exact h

private theorem pt_pc9_to_28
    {f : Nat} {lines : Array String} {numLines i : UInt32} {bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen : UInt32} {hasLongest : Bool}
    {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 6 ≤ f) (hlt : i < numLines) (hlocs : PtRowLocs locs lines numLines i false bytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 9
      (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs, jh, hp⟩ =
      runJvmResFast (f - 6) f_Algorithm_deserializePlaintext_loop_prog 28
        (f_Algorithm_deserializePlaintext_loop_prog.drop 28) ⟨28, [], locs, jh, hp⟩ := by
  split_res_fuel 6
  step_drop 4
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [hlocs.h1, hlocs.h2]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt)]
  norm_res_fuel
  step_drop 2
  rw [runJvmResFast_stepResHeapChunk 1]; (conv => lhs; arg 1; jvm_whnf_blk)
  rw [afterResBlockChunk_cont]; norm_res_fuel
  dsimp only; rw [hlocs.h3]; simp only [Bool.false_eq_true, ↓reduceIte]
  exact runJvmResFast_ifne_fallthrough

private theorem pt_line_prefix
    {f : Nat} {lines : Array String} {numLines i : UInt32} {oldBytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen : UInt32} {hasLongest : Bool}
    {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 13 ≤ f) (hiLen : i.toNat < lines.size) (hiSlt : i.toBitVec.slt 0#32 = false)
    (hlocs : PtRowLocs locs lines numLines i false oldBytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    let line := lines[i.toNat]
    let bytes := line.toByteArray
    let newAddr := jh.objects.size
    let jh' := (jh.alloc (.byteArray bytes.data)).2
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 28
        (f_Algorithm_deserializePlaintext_loop_prog.drop 28) ⟨28, [], locs, jh, hp⟩ =
        runJvmResFast (f - 13) f_Algorithm_deserializePlaintext_loop_prog 41
          (f_Algorithm_deserializePlaintext_loop_prog.drop 41) ⟨41, [], locs', jh', hp⟩ ∧
      jh'.get? newAddr = some (.byteArray bytes.data) ∧
      locs' 14 = .heapRef newAddr ∧ locs' 15 = .i32 bytes.size.toUInt32 ∧
      PtRowLocs locs' lines numLines i false oldBytesAddr
        limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId := by
  intro line bytes newAddr jh'
  have hget : jh'.get? newAddr = some (.byteArray bytes.data) := by
    simp only [jh', newAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    exact Array.getElem?_push_size
  cases hlocs
  apply Exists.intro
  refine ⟨?_, hget, ?_, ?_, ?_⟩
  · split_res_fuel 13
    step_drop 13
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 0 = _›, ‹locs 2 = _›]
    (conv => lhs; arg 5; dsimp only)
    rw [runJvmResFast_aaload_strArr hiSlt hiLen]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    (conv => lhs; arg 5; dsimp only)
    rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
    (conv => lhs; arg 5; dsimp only)
    rw [runJvmResFast_invokestatic_step stepStatic_stringsEncodeToByteArray]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    (conv => lhs; arg 5; dsimp only)
    have hgetUtf : jh'.get? newAddr = some (.byteArray line.toUTF8.data) := hget
    have hjh' : (jh.alloc (.byteArray line.toUTF8.data)).2 = jh' := rfl
    rw [hjh']
    rw [runJvmResFast_arraylength_byteArray hgetUtf]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_deserializePlaintext_loop_prog, List.drop]
    rw [runJvmResFast_istore]
    simp only [Nat.reduceAdd]; rfl
  · simp [setLocal, newAddr]
  · simp [setLocal, bytes, line]
  · constructor <;> (try dsimp only [setLocal]) <;> simp [*]

private theorem pt_line_blank_push
    {f : Nat} {lines : Array String} {numLines i : UInt32} {oldBytesAddr bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen lineLimit : UInt32} {hasLongest : Bool}
    {warns : Algorithm.GrowBuf Algorithm.PlaintextWarning}
    {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 62 ≤ f) (hzero : lineLimit = 0) (hi1 : i + 1 < numLines)
    (h14 : locs 14 = .heapRef bytesAddr) (h15 : locs 15 = .i32 lineLimit)
    (hw : PtWarnRep warns warnsVal)
    (hlocs : PtRowLocs locs lines numLines i false oldBytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    let w := Algorithm.PlaintextWarning.blankLine (i + 1)
    let obj : Jvm.HeapObj AlgExt := .instance "com/alexvanyo/composelife/model/PlaintextWarning$BlankLine"
      [("lineIndex", .i32 (i + 1))]
    let jh' := (jh.alloc obj).2
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 41
        (f_Algorithm_deserializePlaintext_loop_prog.drop 41) ⟨41, [], locs, jh, hp⟩ =
        runJvmResFast (f - 62) f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs', jh', hp⟩ ∧
      PtRowLocs locs' lines numLines (i + 1) false bytesAddr
        lineLimit 0 0 rowIdx longestIdx longestLen hasLongest
        (.ext (.ptWarnGrowBuf (warns.push w))) accId := by
  intro w obj jh'
  have hdecNew : decodePlaintextWarning jh' (.heapRef jh.objects.size) = some w := by
    simp [jh', obj, w, decodePlaintextWarning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup]
  cases hlocs
  apply Exists.intro
  constructor
  · split_res_fuel 62
    step_drop 2
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h15]
    rw [runJvmResFast_ifeq_branch hzero]; norm_res_fuel
    step_drop 9
    rw [← setLocal_eq_self ‹locs 2 = _›, ← setLocal_eq_self ‹locs 1 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hi1)]
    norm_res_fuel
    step_drop 51
    rw [← setLocal_eq_self ‹locs 12 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    (conv => lhs; arg 5; dsimp only)
    dsimp only [Jvm.JvmState.jvmHeap]
    rw [runJvmResFast_invokespecial_step rfl]; norm_res_fuel
    dsimp only [Jvm.JvmState.jvmHeap]
    have hjh' : (⟨jh.objects.push obj, jh.statics⟩ : Jvm.JvmHeap AlgExt) = jh' := rfl
    rw [hjh']
    rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_ptWarn hw hdecNew)]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]
  · constructor <;> (try dsimp only [setLocal, w]) <;> simp [*]

private theorem pt_line_blank_skip
    {f : Nat} {lines : Array String} {numLines i : UInt32} {oldBytesAddr bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen lineLimit : UInt32} {hasLongest : Bool}
    {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 56 ≤ f) (hzero : lineLimit = 0) (hnot : ¬(i + 1 < numLines))
    (h14 : locs 14 = .heapRef bytesAddr) (h15 : locs 15 = .i32 lineLimit)
    (hlocs : PtRowLocs locs lines numLines i false oldBytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 41
        (f_Algorithm_deserializePlaintext_loop_prog.drop 41) ⟨41, [], locs, jh, hp⟩ =
        runJvmResFast (f - 56) f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs', jh, hp⟩ ∧
      PtRowLocs locs' lines numLines (i + 1) false bytesAddr
        lineLimit 0 0 rowIdx longestIdx longestLen hasLongest warnsVal accId := by
  cases hlocs
  apply Exists.intro
  constructor
  · split_res_fuel 56
    step_drop 2
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h15]
    rw [runJvmResFast_ifeq_branch hzero]; norm_res_fuel
    step_drop 9
    rw [← setLocal_eq_self ‹locs 2 = _›, ← setLocal_eq_self ‹locs 1 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hnot)]
    norm_res_fuel
    step_drop 45
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]
  · constructor <;> (try dsimp only [setLocal]) <;> simp [*]

private theorem pt_line_comment
    {f : Nat} {lines : Array String} {numLines i : UInt32} {oldBytesAddr bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen lineLimit : UInt32} {hasLongest : Bool}
    {warnsVal : JvmVal} {accId : Nat} {bytes : ByteArray} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 58 ≤ f) (hne0 : (lineLimit == 0) = false)
    (hpos0 : 0 < bytes.data.size) (hb33 : bytes.data[0] = 33)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (h14 : locs 14 = .heapRef bytesAddr) (h15 : locs 15 = .i32 lineLimit)
    (hlocs : PtRowLocs locs lines numLines i false oldBytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 41
        (f_Algorithm_deserializePlaintext_loop_prog.drop 41) ⟨41, [], locs, jh, hp⟩ =
        runJvmResFast (f - 58) f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs', jh, hp⟩ ∧
      PtRowLocs locs' lines numLines (i + 1) false bytesAddr
        lineLimit 0 0 rowIdx longestIdx longestLen hasLongest warnsVal accId := by
  cases hlocs
  apply Exists.intro
  constructor
  · split_res_fuel 58
    step_drop 8
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h15]
    rw [runJvmResFast_ifeq_fallthrough hne0]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h14]
    (conv => lhs; arg 5; dsimp only)
    rw [runJvmResFast_baload_byteArray (idx := 0) hbytes (by decide) hpos0]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    simp only [UInt32.toNat_zero]
    rw [runJvmResFast_if_icmpeq_branch (baload_u8_eq_33_of_eq hb33)]; norm_res_fuel
    step_drop 50
    rw [← setLocal_eq_self ‹locs 2 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]
  · constructor <;> (try dsimp only [setLocal]) <;> simp [*]

private theorem pt_line_row_hdr
    {f : Nat} {lines : Array String} {numLines i : UInt32} {oldBytesAddr bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen lineLimit : UInt32} {hasLongest : Bool}
    {warnsVal : JvmVal} {accId : Nat} {bytes : ByteArray} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 14 ≤ f) (hne0 : (lineLimit == 0) = false)
    (hpos0 : 0 < bytes.data.size) (hb33 : bytes.data[0] ≠ 33)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (h14 : locs 14 = .heapRef bytesAddr) (h15 : locs 15 = .i32 lineLimit)
    (hlocs : PtRowLocs locs lines numLines i false oldBytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    let len := Algorithm.countChars bytes lineLimit 0 0
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 41
        (f_Algorithm_deserializePlaintext_loop_prog.drop 41) ⟨41, [], locs, jh, hp⟩ =
        runJvmResFast (f - 14) f_Algorithm_deserializePlaintext_loop_prog 55
          (f_Algorithm_deserializePlaintext_loop_prog.drop 55) ⟨55, [], locs', jh, hp⟩ ∧
      locs' 14 = .heapRef bytesAddr ∧ locs' 15 = .i32 lineLimit ∧ locs' 16 = .i32 len ∧
      PtRowLocs locs' lines numLines i false oldBytesAddr
        limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId := by
  intro len
  cases hlocs
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · split_res_fuel 14
    step_drop 14
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h15]
    rw [runJvmResFast_ifeq_fallthrough hne0]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h14]
    (conv => lhs; arg 5; dsimp only)
    rw [runJvmResFast_baload_byteArray (idx := 0) hbytes (by decide) hpos0]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    simp only [UInt32.toNat_zero]
    rw [runJvmResFast_if_icmpeq_fallthrough (baload_u8_eq_33_of_ne hb33)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h14, h15]
    (conv => lhs; arg 5; dsimp only)
    rw [runJvmResFast_invokestatic_step (stepStatic_countChars_heap hbytes)]
    norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_deserializePlaintext_loop_prog, List.drop]
    rw [runJvmResFast_istore]
    simp only [Nat.reduceAdd]; rfl
  · simp [setLocal, h14]
  · simp [setLocal, h15]
  · simp [setLocal, len]
  · constructor <;> (try dsimp only [setLocal]) <;> simp [*]

private theorem pt_line_row_init
    {f : Nat} {lines : Array String} {numLines i : UInt32} {oldBytesAddr bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen lineLimit len : UInt32}
    {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 48 ≤ f)
    (h14 : locs 14 = .heapRef bytesAddr) (h15 : locs 15 = .i32 lineLimit) (h16 : locs 16 = .i32 len)
    (hlocs : PtRowLocs locs lines numLines i false oldBytesAddr
      limit p col rowIdx longestIdx longestLen false warnsVal accId) :
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 55
        (f_Algorithm_deserializePlaintext_loop_prog.drop 55) ⟨55, [], locs, jh, hp⟩ =
        runJvmResFast (f - 48) f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs', jh, hp⟩ ∧
      PtRowLocs locs' lines numLines i true bytesAddr
        lineLimit 0 0 rowIdx (i + 1) len true warnsVal accId := by
  cases hlocs
  apply Exists.intro
  constructor
  · split_res_fuel 48
    step_drop 48
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 11 = _›]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
    rw [← setLocal_eq_self ‹locs 2 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]
  · constructor <;> (try dsimp only [setLocal]) <;> simp [*]

private theorem pt_line_row_longer
    {f : Nat} {lines : Array String} {numLines i : UInt32} {oldBytesAddr bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen lineLimit len : UInt32}
    {warns : Algorithm.GrowBuf Algorithm.PlaintextWarning}
    {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 58 ≤ f) (hgt : longestLen < len)
    (h14 : locs 14 = .heapRef bytesAddr) (h15 : locs 15 = .i32 lineLimit) (h16 : locs 16 = .i32 len)
    (hw : PtWarnRep warns warnsVal)
    (hlocs : PtRowLocs locs lines numLines i false oldBytesAddr
      limit p col rowIdx longestIdx longestLen true warnsVal accId) :
    let w := Algorithm.PlaintextWarning.shortLine longestIdx
    let obj : Jvm.HeapObj AlgExt := .instance "com/alexvanyo/composelife/model/PlaintextWarning$ShortLine"
      [("lineIndex", .i32 longestIdx)]
    let jh' := (jh.alloc obj).2
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 55
        (f_Algorithm_deserializePlaintext_loop_prog.drop 55) ⟨55, [], locs, jh, hp⟩ =
        runJvmResFast (f - 58) f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs', jh', hp⟩ ∧
      PtRowLocs locs' lines numLines i true bytesAddr
        lineLimit 0 0 rowIdx (i + 1) len true (.ext (.ptWarnGrowBuf (warns.push w))) accId := by
  intro w obj jh'
  have hdecNew : decodePlaintextWarning jh' (.heapRef jh.objects.size) = some w := by
    simp [jh', obj, w, decodePlaintextWarning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup]
  cases hlocs
  apply Exists.intro
  constructor
  · split_res_fuel 58
    step_drop 2
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 11 = _›]; simp only [↓reduceIte]
    rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; norm_res_fuel
    step_drop 4
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 10 = _›, h16]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hgt)]
    norm_res_fuel
    step_drop 52
    rw [← setLocal_eq_self ‹locs 2 = _›, ← setLocal_eq_self ‹locs 9 = _›, ← setLocal_eq_self ‹locs 12 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    (conv => lhs; arg 5; dsimp only)
    dsimp only [Jvm.JvmState.jvmHeap]
    rw [runJvmResFast_invokespecial_step rfl]; norm_res_fuel
    dsimp only [Jvm.JvmState.jvmHeap]
    have hjh' : (⟨jh.objects.push obj, jh.statics⟩ : Jvm.JvmHeap AlgExt) = jh' := rfl
    rw [hjh']
    rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_ptWarn hw hdecNew)]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]
  · constructor <;> (try dsimp only [setLocal, w]) <;> simp [*]

private theorem pt_line_row_shorter
    {f : Nat} {lines : Array String} {numLines i : UInt32} {oldBytesAddr bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen lineLimit len : UInt32}
    {warns : Algorithm.GrowBuf Algorithm.PlaintextWarning}
    {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 64 ≤ f) (hnot : ¬(longestLen < len)) (hlt : len < longestLen)
    (h14 : locs 14 = .heapRef bytesAddr) (h15 : locs 15 = .i32 lineLimit) (h16 : locs 16 = .i32 len)
    (hw : PtWarnRep warns warnsVal)
    (hlocs : PtRowLocs locs lines numLines i false oldBytesAddr
      limit p col rowIdx longestIdx longestLen true warnsVal accId) :
    let w := Algorithm.PlaintextWarning.shortLine (i + 1)
    let obj : Jvm.HeapObj AlgExt := .instance "com/alexvanyo/composelife/model/PlaintextWarning$ShortLine"
      [("lineIndex", .i32 (i + 1))]
    let jh' := (jh.alloc obj).2
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 55
        (f_Algorithm_deserializePlaintext_loop_prog.drop 55) ⟨55, [], locs, jh, hp⟩ =
        runJvmResFast (f - 64) f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs', jh', hp⟩ ∧
      PtRowLocs locs' lines numLines i true bytesAddr
        lineLimit 0 0 rowIdx longestIdx longestLen true (.ext (.ptWarnGrowBuf (warns.push w))) accId := by
  intro w obj jh'
  have hdecNew : decodePlaintextWarning jh' (.heapRef jh.objects.size) = some w := by
    simp [jh', obj, w, decodePlaintextWarning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup]
  cases hlocs
  apply Exists.intro
  constructor
  · split_res_fuel 64
    step_drop 2
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 11 = _›]; simp only [↓reduceIte]
    rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; norm_res_fuel
    step_drop 4
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 10 = _›, h16]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hnot)]
    norm_res_fuel
    step_drop 4
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 10 = _›, h16]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt)]
    norm_res_fuel
    step_drop 54
    rw [← setLocal_eq_self ‹locs 2 = _›, ← setLocal_eq_self ‹locs 12 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    (conv => lhs; arg 5; dsimp only)
    dsimp only [Jvm.JvmState.jvmHeap]
    rw [runJvmResFast_invokespecial_step rfl]; norm_res_fuel
    dsimp only [Jvm.JvmState.jvmHeap]
    have hjh' : (⟨jh.objects.push obj, jh.statics⟩ : Jvm.JvmHeap AlgExt) = jh' := rfl
    rw [hjh']
    rw [runJvmResFast_invokestatic_step (stepStatic_growBufPush_ptWarn hw hdecNew)]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]
  · constructor <;> (try dsimp only [setLocal, w]) <;> simp [*]

private theorem pt_line_row_eq
    {f : Nat} {lines : Array String} {numLines i : UInt32} {oldBytesAddr bytesAddr : Nat}
    {limit p col rowIdx longestIdx longestLen lineLimit len : UInt32}
    {warnsVal : JvmVal} {accId : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 55 ≤ f) (hnot1 : ¬(longestLen < len)) (hnot2 : ¬(len < longestLen))
    (h14 : locs 14 = .heapRef bytesAddr) (h15 : locs 15 = .i32 lineLimit) (h16 : locs 16 = .i32 len)
    (hlocs : PtRowLocs locs lines numLines i false oldBytesAddr
      limit p col rowIdx longestIdx longestLen true warnsVal accId) :
    ∃ locs',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 55
        (f_Algorithm_deserializePlaintext_loop_prog.drop 55) ⟨55, [], locs, jh, hp⟩ =
        runJvmResFast (f - 55) f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs', jh, hp⟩ ∧
      PtRowLocs locs' lines numLines i true bytesAddr
        lineLimit 0 0 rowIdx longestIdx longestLen true warnsVal accId := by
  cases hlocs
  apply Exists.intro
  constructor
  · split_res_fuel 55
    step_drop 2
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 11 = _›]; simp only [↓reduceIte]
    rw [runJvmResFast_ifne_branch (v := 1) (by decide)]; norm_res_fuel
    step_drop 4
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 10 = _›, h16]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hnot1)]
    norm_res_fuel
    step_drop 4
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 10 = _›, h16]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hnot2)]
    norm_res_fuel
    step_drop 45
    rw [← setLocal_eq_self ‹locs 2 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]
  · constructor <;> (try dsimp only [setLocal]) <;> simp [*]

private theorem decodePlaintextResult_empty {st : JvmState} {addr cid : Nat} {cells : Array UInt64}
    (hres : st.jvmHeap.get? addr = some (.instance "com/alexvanyo/composelife/model/PlaintextResult"
      [("warnings", .strArr #[]), ("cells", .ext (.u64Ref cid))]))
    (hu : st.heap.u64Arrays[cid]? = some cells) :
    decodePlaintextResult st (.heapRef addr) = some ⟨#[], cells⟩ := by
  have h1 : decodePlaintextResult st (.heapRef addr) =
      (st.heap.u64Arrays[cid]?.map fun cells => ⟨#[], cells⟩) := by
    dsimp only [decodePlaintextResult]
    rw [hres]
    rfl
  rw [h1, hu]
  rfl

private theorem decodePlaintextResult_arr {st : JvmState} {addr wAddr cid : Nat}
    {warnVals : Array JvmVal} {warns : Array Algorithm.PlaintextWarning} {cells : Array UInt64}
    (hres : st.jvmHeap.get? addr = some (.instance "com/alexvanyo/composelife/model/PlaintextResult"
      [("warnings", .heapRef wAddr), ("cells", .ext (.u64Ref cid))]))
    (hw : st.jvmHeap.get? wAddr = some (.objArray "java/lang/Object" warnVals))
    (hu : st.heap.u64Arrays[cid]? = some cells)
    (hm : warnVals.toList.mapM (decodePlaintextWarning st.jvmHeap) = some warns.toList) :
    decodePlaintextResult st (.heapRef addr) = some ⟨warns, cells⟩ := by
  have h1 : decodePlaintextResult st (.heapRef addr) =
      (match st.jvmHeap.get? wAddr, st.heap.u64Arrays[cid]? with
      | some (.objArray _ warnVals), some cells =>
        (warnVals.toList.mapM (decodePlaintextWarning st.jvmHeap)).map fun ws =>
          ⟨ws.toArray, cells⟩
      | _, _ => none) := by
    dsimp only [decodePlaintextResult]
    rw [hres]
    rfl
  rw [h1, hw, hu]
  have h2 : (match some (Jvm.HeapObj.objArray "java/lang/Object" warnVals), some cells with
      | some (.objArray _ warnVals), some cells =>
        (warnVals.toList.mapM (decodePlaintextWarning st.jvmHeap)).map fun ws =>
          Algorithm.PlaintextResult.mk ws.toArray cells
      | _, _ => none) =
      ((warnVals.toList.mapM (decodePlaintextWarning st.jvmHeap)).map fun ws =>
        Algorithm.PlaintextResult.mk ws.toArray cells) := rfl
  rw [h2, hm]
  simp only [Option.map_some, Array.toArray_toList]

private theorem deserializePlaintext_base
    {f : Nat} {lines : Array String} {numLines i : UInt32} {inRow : Bool} {bytesAddr : Nat}
    {bytes : ByteArray} {limit p col rowIdx longestIdx longestLen : UInt32} {hasLongest : Bool}
    {warns : Algorithm.GrowBuf Algorithm.PlaintextWarning} {warnsVal : JvmVal}
    {accId : Nat} {acc : Algorithm.U64Buf} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hf : 17 ≤ f) (hnot : ¬(i < numLines))
    (hw : PtWarnRep warns warnsVal) (hu : u64[accId]? = some acc)
    (hlocs : PtRowLocs locs lines numLines i inRow bytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    ∃ v st',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 9
        (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodePlaintextResult st' v =
        some (Algorithm.deserializePlaintext.loop lines numLines i inRow bytes limit p col
          rowIdx longestIdx longestLen hasLongest warns acc) := by
  have hloop : Algorithm.deserializePlaintext.loop lines numLines i inRow bytes limit p col
      rowIdx longestIdx longestLen hasLongest warns acc = ⟨warns.toArray, Algorithm.U64Buf.toArray acc⟩ := by
    rw [Algorithm.deserializePlaintext.loop]; simp [hnot]
  rw [hloop]
  rcases stepStatic_growBufToArray_ptWarn (pc := 14) (rest := []) (locs := locs)
    (jh := jh) (hp := ⟨ar, u64, asc⟩) hw with ⟨arrVal, jh1, warnVals?, hgb, hmatch⟩
  cases hlocs
  have hrun : runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 9
      (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      some (.heapRef jh1.objects.size,
        ⟨25, [.heapRef jh1.objects.size],
          setLocal (setLocal locs 14 arrVal) 15 (.ext (.u64Ref u64.length)),
          (jh1.alloc (.instance "com/alexvanyo/composelife/model/PlaintextResult"
            [("warnings", arrVal), ("cells", .ext (.u64Ref u64.length))])).2,
          ⟨ar, u64 ++ [Algorithm.U64Buf.toArray acc], asc⟩⟩) := by
    split_res_fuel 17
    step_drop 4
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 1 = _›, ‹locs 2 = _›]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hnot)]
    norm_res_fuel
    step_drop 13
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 12 = _›]
    (conv => lhs; arg 5; dsimp only)
    rw [runJvmResFast_invokestatic_step hgb]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [‹locs 13 = _›]
    (conv => lhs; arg 5; dsimp only)
    rw [runJvmResFast_invokestatic_step
      (stepStatic_u64BufToArray_heap (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hu)]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    (conv => lhs; arg 5; dsimp only)
    rw [runJvmResFast_invokespecial_step rfl]; norm_res_fuel
    heap_step_nonbranch_chunks
    rfl
  refine ⟨_, _, hrun, ?_⟩
  cases warnVals? with
  | none =>
    rcases hmatch with ⟨rarr, rjh, rbw⟩
    subst rarr
    rw [rjh] at hrun
    have hext : jh1 = jh := rjh
    have hgetR : ((jh1.alloc (.instance "com/alexvanyo/composelife/model/PlaintextResult"
        [("warnings", .strArr #[]), ("cells", .ext (.u64Ref u64.length))])).2).get? jh1.objects.size =
        some (.instance "com/alexvanyo/composelife/model/PlaintextResult"
          [("warnings", .strArr #[]), ("cells", .ext (.u64Ref u64.length))]) := by
      simp [Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    have hres := decodePlaintextResult_empty (addr := jh1.objects.size) (cid := u64.length)
      (cells := Algorithm.U64Buf.toArray acc)
      (st := ⟨25, [.heapRef jh1.objects.size],
        setLocal (setLocal locs 14 (.strArr #[])) 15 (.ext (.u64Ref u64.length)),
        (jh1.alloc (.instance "com/alexvanyo/composelife/model/PlaintextResult"
          [("warnings", .strArr #[]), ("cells", .ext (.u64Ref u64.length))])).2,
        ⟨ar, u64 ++ [Algorithm.U64Buf.toArray acc], asc⟩⟩) hgetR (by simp)
    rw [rbw]
    simpa [hext] using hres
  | some wAddr =>
    rcases hmatch with ⟨rarr, warnVals, hgw, hmw⟩
    subst rarr
    have hext : HeapExtends jh1 (jh1.alloc (.instance "com/alexvanyo/composelife/model/PlaintextResult"
        [("warnings", .heapRef wAddr), ("cells", .ext (.u64Ref u64.length))])).2 :=
      heapExtends_alloc _ _
    have hgw2 := hext wAddr (.objArray "java/lang/Object" warnVals) hgw
    have hmw2 := mapM_decodePlaintextWarning_mono hext hmw
    have hgetR : ((jh1.alloc (.instance "com/alexvanyo/composelife/model/PlaintextResult"
        [("warnings", .heapRef wAddr), ("cells", .ext (.u64Ref u64.length))])).2).get? jh1.objects.size =
        some (.instance "com/alexvanyo/composelife/model/PlaintextResult"
          [("warnings", .heapRef wAddr), ("cells", .ext (.u64Ref u64.length))]) := by
      simp [Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    exact decodePlaintextResult_arr (addr := jh1.objects.size) (wAddr := wAddr) (cid := u64.length)
      (warnVals := warnVals) (warns := warns.toArray)
      (cells := Algorithm.U64Buf.toArray acc) hgetR hgw2 (by simp) hmw2

private theorem deserializePlaintext_loop_row_branch
    (lines : Array String) (numLines i : UInt32) (bytes : ByteArray)
    (limit p col rowIdx longestIdx longestLen : UInt32) (hasLongest : Bool)
    (warns : Algorithm.GrowBuf Algorithm.PlaintextWarning) (acc : Algorithm.U64Buf)
    (hi : i < numLines) (hne0 : (lines[i.toNat]!.toByteArray.size.toUInt32 == 0) = false)
    (hne33 : (lines[i.toNat]!.toByteArray.get! 0 == 33) = false) :
    let lb := lines[i.toNat]!.toByteArray
    let ll := lb.size.toUInt32
    let len := Algorithm.countChars lb ll 0 0
    Algorithm.deserializePlaintext.loop lines numLines i false bytes limit p col
      rowIdx longestIdx longestLen hasLongest warns acc =
      if !hasLongest then
        Algorithm.deserializePlaintext.loop lines numLines i true lb ll 0 0 rowIdx (i + 1) len true warns acc
      else if len > longestLen then
        Algorithm.deserializePlaintext.loop lines numLines i true lb ll 0 0 rowIdx (i + 1) len true
          (warns.push (.shortLine longestIdx)) acc
      else if len < longestLen then
        Algorithm.deserializePlaintext.loop lines numLines i true lb ll 0 0 rowIdx longestIdx longestLen true
          (warns.push (.shortLine (i + 1))) acc
      else
        Algorithm.deserializePlaintext.loop lines numLines i true lb ll 0 0 rowIdx longestIdx longestLen true
          warns acc := by
  intro lb ll len
  dsimp only [lb, ll, len]
  rw [Algorithm.deserializePlaintext.loop]
  simp only [hi, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte, hne0, hne33]
  by_cases hlt : Algorithm.countChars lb ll 0 0 < longestLen <;>
    (dsimp only [lb, ll] at hlt; simp only [hlt, ↓reduceIte])

private theorem pt_line_step_row
    {f fRem : Nat} {lines : Array String} {numLines i : UInt32}
    {oldBytesAddr bytesAddr : Nat} {bytes lineBytes : ByteArray}
    {limit p col rowIdx longestIdx longestLen lineLimit : UInt32} {hasLongest : Bool}
    {warns : Algorithm.GrowBuf Algorithm.PlaintextWarning} {warnsVal : JvmVal}
    {accId : Nat} {acc : Algorithm.U64Buf} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hi : i < numLines) (hlineLoop : lines[i.toNat]!.toByteArray = lineBytes)
    (hne0 : (lineLimit == 0) = false) (hne33B : (lineBytes.get! 0 == 33) = false)
    (hf : fRem + lineLimit.toNat * 120 + 131 ≤ f)
    (hget1 : jh.get? bytesAddr = some (.byteArray lineBytes.data))
    (h14 : locs 14 = .heapRef bytesAddr) (h15 : locs 15 = .i32 lineLimit)
    (h16 : locs 16 = .i32 (Algorithm.countChars lineBytes lineLimit 0 0))
    (hw : PtWarnRep warns warnsVal) (hu : u64[accId]? = some acc)
    (hlocs : PtRowLocs locs lines numLines i false oldBytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId)
    (hlimEq : lineLimit = lineBytes.size.toUInt32) :
    ∃ f' rowIdx' longestIdx' longestLen' hasLongest' warns' wv' accId' acc' locs' jh' u64',
      fRem ≤ f' ∧
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 55
        (f_Algorithm_deserializePlaintext_loop_prog.drop 55) ⟨55, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        runJvmResFast f' f_Algorithm_deserializePlaintext_loop_prog 9
          (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs', jh', ⟨ar, u64', asc⟩⟩ ∧
      PtWarnRep warns' wv' ∧
      u64'[accId']? = some acc' ∧
      PtRowLocs locs' lines numLines (i + 1) false bytesAddr
        lineLimit 0 0 rowIdx' longestIdx' longestLen' hasLongest' wv' accId' ∧
      Algorithm.deserializePlaintext.loop lines numLines i false bytes limit p col
        rowIdx longestIdx longestLen hasLongest warns acc =
        Algorithm.deserializePlaintext.loop lines numLines (i + 1) false lineBytes lineLimit 0 0
          rowIdx' longestIdx' longestLen' hasLongest' warns' acc' := by
  subst hlimEq
  let len := Algorithm.countChars lineBytes lineBytes.size.toUInt32 0 0
  have hbranch := deserializePlaintext_loop_row_branch lines numLines i bytes limit p col
    rowIdx longestIdx longestLen hasLongest warns acc hi
    (by simp [hlineLoop, hne0]) (by simp [hlineLoop, hne33B])
  simp only [hlineLoop] at hbranch
  cases hasLongest with
  | false =>
    rcases pt_line_row_init (f := f) (jh := jh) (hp := ⟨ar, u64, asc⟩)
        (by omega) h14 h15 h16 hlocs with ⟨locs3, hp3, hlocs3⟩
    rcases deserializePlaintext_row_jvm lineBytes.size.toUInt32.toNat (f - 48) fRem lines numLines i bytesAddr
        lineBytes lineBytes.size.toUInt32 0 0 rowIdx (i + 1) len true warns warnsVal accId acc locs3 jh
        ar u64 asc hi (Nat.le_refl _) (by omega) hget1 hw hu hlocs3 with
        ⟨f', locs4, wv4, jh4, u64_4, hf', hrowJvm, hw4, accId4, hu4, hlocs4⟩
    refine ⟨f', rowIdx + 1, i + 1, len, true, _, wv4, accId4, _, locs4, jh4, u64_4,
      hf', ?_, hw4, hu4, hlocs4, ?_⟩
    · rw [hp3, hrowJvm]
    · rw [hbranch]; simp only [Bool.not_false, ↓reduceIte]
      exact deserializePlaintext_loop_row_eq lineBytes.size.toUInt32.toNat lines numLines i lineBytes
        lineBytes.size.toUInt32 0 0 rowIdx (i + 1) len true warns acc (by simp) hi
  | true =>
    by_cases hgt : longestLen < len
    · rcases pt_line_row_longer (f := f) (jh := jh) (hp := ⟨ar, u64, asc⟩)
          (by omega) hgt h14 h15 h16 hw hlocs with ⟨locs3, hp3, hlocs3⟩
      let warns' := warns.push (.shortLine longestIdx)
      rcases deserializePlaintext_row_jvm lineBytes.size.toUInt32.toNat (f - 58) fRem lines numLines i bytesAddr
          lineBytes lineBytes.size.toUInt32 0 0 rowIdx (i + 1) len true warns' _ accId acc locs3 _
          ar u64 asc hi (Nat.le_refl _) (by omega)
          (heapExtends_alloc jh _ bytesAddr _ hget1) (PtWarnRep.full _) hu hlocs3 with
          ⟨f', locs4, wv4, jh4, u64_4, hf', hrowJvm, hw4, accId4, hu4, hlocs4⟩
      refine ⟨f', rowIdx + 1, i + 1, len, true, _, wv4, accId4, _, locs4, jh4, u64_4,
        hf', ?_, hw4, hu4, hlocs4, ?_⟩
      · rw [hp3, hrowJvm]
      · rw [hbranch]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have hgt' : len > longestLen := hgt
        simp only [len, hgt', ↓reduceIte]
        exact deserializePlaintext_loop_row_eq lineBytes.size.toUInt32.toNat lines numLines i lineBytes
          lineBytes.size.toUInt32 0 0 rowIdx (i + 1) len true warns' acc (by simp) hi
    · by_cases hltLen : len < longestLen
      · rcases pt_line_row_shorter (f := f) (jh := jh) (hp := ⟨ar, u64, asc⟩)
            (by omega) hgt hltLen h14 h15 h16 hw hlocs with ⟨locs3, hp3, hlocs3⟩
        let warns' := warns.push (.shortLine (i + 1))
        rcases deserializePlaintext_row_jvm lineBytes.size.toUInt32.toNat (f - 64) fRem lines numLines i bytesAddr
            lineBytes lineBytes.size.toUInt32 0 0 rowIdx longestIdx longestLen true warns' _ accId acc locs3 _
            ar u64 asc hi (Nat.le_refl _) (by omega)
            (heapExtends_alloc jh _ bytesAddr _ hget1) (PtWarnRep.full _) hu hlocs3 with
            ⟨f', locs4, wv4, jh4, u64_4, hf', hrowJvm, hw4, accId4, hu4, hlocs4⟩
        refine ⟨f', rowIdx + 1, longestIdx, longestLen, true, _, wv4, accId4, _, locs4, jh4, u64_4,
          hf', ?_, hw4, hu4, hlocs4, ?_⟩
        · rw [hp3, hrowJvm]
        · rw [hbranch]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have hgt' : ¬(len > longestLen) := hgt
          simp only [len, hgt', hltLen, ↓reduceIte]
          exact deserializePlaintext_loop_row_eq lineBytes.size.toUInt32.toNat lines numLines i lineBytes
            lineBytes.size.toUInt32 0 0 rowIdx longestIdx longestLen true warns' acc (by simp) hi
      · rcases pt_line_row_eq (f := f) (jh := jh) (hp := ⟨ar, u64, asc⟩)
            (by omega) hgt hltLen h14 h15 h16 hlocs with ⟨locs3, hp3, hlocs3⟩
        rcases deserializePlaintext_row_jvm lineBytes.size.toUInt32.toNat (f - 55) fRem lines numLines i bytesAddr
            lineBytes lineBytes.size.toUInt32 0 0 rowIdx longestIdx longestLen true warns warnsVal accId acc locs3 jh
            ar u64 asc hi (Nat.le_refl _) (by omega) hget1 hw hu hlocs3 with
            ⟨f', locs4, wv4, jh4, u64_4, hf', hrowJvm, hw4, accId4, hu4, hlocs4⟩
        refine ⟨f', rowIdx + 1, longestIdx, longestLen, true, _, wv4, accId4, _, locs4, jh4, u64_4,
          hf', ?_, hw4, hu4, hlocs4, ?_⟩
        · rw [hp3, hrowJvm]
        · rw [hbranch]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have hgt' : ¬(len > longestLen) := hgt
          simp only [len, hgt', hltLen, ↓reduceIte]
          exact deserializePlaintext_loop_row_eq lineBytes.size.toUInt32.toNat lines numLines i lineBytes
            lineBytes.size.toUInt32 0 0 rowIdx longestIdx longestLen true warns acc (by simp) hi

private theorem deserializePlaintext_lines_tail
    (mLines : Nat) (f : Nat) (lines : Array String) (numLines i : UInt32)
    (bytesAddr : Nat) (bytes : ByteArray)
    (limit p col rowIdx longestIdx longestLen : UInt32) (hasLongest : Bool)
    (warns : Algorithm.GrowBuf Algorithm.PlaintextWarning) (warnsVal : JvmVal)
    (accId : Nat) (acc : Algorithm.U64Buf) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hnum : numLines.toNat ≤ lines.size) (hlen31 : lines.size < 2 ^ 31)
    (hm : numLines.toNat - i.toNat ≤ mLines)
    (hf : mLines * (linesMaxBytes lines * 120 + 200) + 50 ≤ f)
    (hw : PtWarnRep warns warnsVal) (hu : u64[accId]? = some acc)
    (hlocs : PtRowLocs locs lines numLines i false bytesAddr
      limit p col rowIdx longestIdx longestLen hasLongest warnsVal accId) :
    ∃ v st',
      runJvmResFast f f_Algorithm_deserializePlaintext_loop_prog 9
        (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodePlaintextResult st' v =
        some (Algorithm.deserializePlaintext.loop lines numLines i false bytes limit p col
          rowIdx longestIdx longestLen hasLongest warns acc) := by
  induction mLines generalizing f i bytesAddr bytes limit p col rowIdx longestIdx longestLen
      hasLongest warns warnsVal accId acc locs jh u64 with
  | zero =>
    have hnot : ¬(i < numLines) := by
      intro hi; have := UInt32.lt_iff_toNat_lt.mp hi; omega
    exact deserializePlaintext_base (by omega) hnot hw hu hlocs
  | succ m ih =>
    by_cases hi : i < numLines
    · have hiNat : i.toNat < numLines.toNat := UInt32.lt_iff_toNat_lt.mp hi
      have hiLen : i.toNat < lines.size := Nat.lt_of_lt_of_le hiNat hnum
      have hi31 : i.toNat < 2 ^ 31 := Nat.lt_trans hiLen hlen31
      have hiSlt : i.toBitVec.slt 0#32 = false := u32_slt_zero_false_of_lt hi31
      have hmNext : numLines.toNat - (i + 1).toNat ≤ m := by
        rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
        omega
      have hfLine : m * (linesMaxBytes lines * 120 + 200) + (linesMaxBytes lines * 120 + 200) + 50 ≤ f := by
        have hf1 := hf
        rw [Nat.succ_mul] at hf1
        omega
      let line := lines[i.toNat]
      let lineBytes := line.toByteArray
      let lineLimit := lineBytes.size.toUInt32
      let bytesAddr1 := jh.objects.size
      let jh1 := (jh.alloc (.byteArray lineBytes.data)).2
      have hp0 := pt_pc9_to_28 (f := f) (jh := jh) (hp := ⟨ar, u64, asc⟩) (by omega) hi hlocs
      rcases pt_line_prefix (f := f - 6) (jh := jh) (hp := ⟨ar, u64, asc⟩)
          (by omega) hiLen hiSlt hlocs with ⟨locs1, hp1, hget1, h14, h15, hlocs1⟩
      have hlineLoop : lines[i.toNat]!.toByteArray = lineBytes := by
        simp [lineBytes, line, getElem!_pos, hiLen]
      by_cases hzero : lineLimit = 0
      · have hzeroB : (lineLimit == 0) = true := beq_iff_eq.mpr hzero
        by_cases hi1 : i + 1 < numLines
        · have hloopEq : Algorithm.deserializePlaintext.loop lines numLines i false bytes limit p col
              rowIdx longestIdx longestLen hasLongest warns acc =
              Algorithm.deserializePlaintext.loop lines numLines (i + 1) false lineBytes lineLimit 0 0
                rowIdx longestIdx longestLen hasLongest
                (warns.push (.blankLine (i + 1))) acc := by
            rw [Algorithm.deserializePlaintext.loop]
            simp only [hi, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte, hlineLoop]
            change (if lineLimit == 0 then _ else _) = _
            simp only [hzeroB, ↓reduceIte, hi1]
            dsimp only [lineLimit]
          rcases pt_line_blank_push (f := f - 6 - 13) (jh := jh1) (hp := ⟨ar, u64, asc⟩)
              (by omega) hzero hi1 h14 h15 hw hlocs1 with ⟨locs2, hp2, hlocs2⟩
          rcases ih (f - 6 - 13 - 62) (i + 1) bytesAddr1 lineBytes lineLimit 0 0 rowIdx
              longestIdx longestLen hasLongest _ _ accId acc locs2 _ u64 hmNext
              (by omega) (PtWarnRep.full _) hu hlocs2 with ⟨v, st', hrec, hdec⟩
          refine ⟨v, st', ?_, ?_⟩
          · rw [hp0, hp1, hp2]; exact hrec
          · rw [hloopEq]; exact hdec
        · have hloopEq : Algorithm.deserializePlaintext.loop lines numLines i false bytes limit p col
              rowIdx longestIdx longestLen hasLongest warns acc =
              Algorithm.deserializePlaintext.loop lines numLines (i + 1) false lineBytes lineLimit 0 0
                rowIdx longestIdx longestLen hasLongest warns acc := by
            rw [Algorithm.deserializePlaintext.loop]
            simp only [hi, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte, hlineLoop]
            change (if lineLimit == 0 then _ else _) = _
            simp only [hzeroB, ↓reduceIte, hi1]
            dsimp only [lineLimit]
          rcases pt_line_blank_skip (f := f - 6 - 13) (jh := jh1) (hp := ⟨ar, u64, asc⟩)
              (by omega) hzero hi1 h14 h15 hlocs1 with ⟨locs2, hp2, hlocs2⟩
          rcases ih (f - 6 - 13 - 56) (i + 1) bytesAddr1 lineBytes lineLimit 0 0 rowIdx
              longestIdx longestLen hasLongest warns warnsVal accId acc locs2 jh1 u64 hmNext
              (by omega) hw hu hlocs2 with ⟨v, st', hrec, hdec⟩
          refine ⟨v, st', ?_, ?_⟩
          · rw [hp0, hp1, hp2]; exact hrec
          · rw [hloopEq]; exact hdec
      · have hne0 : (lineLimit == 0) = false := beq_false_of_ne hzero
        have hpos0 : 0 < lineBytes.data.size := by
          rcases Nat.eq_zero_or_pos lineBytes.data.size with hsz0 | hpos
          · exfalso
            apply hzero
            dsimp only [lineLimit]
            rw [show lineBytes.size = 0 from hsz0]
            rfl
          · exact hpos
        have hb0eq : lineBytes.get! 0 = lineBytes.data[0] := by
          dsimp only [ByteArray.get!]
          exact getElem!_pos lineBytes.data 0 hpos0
        by_cases hb33 : lineBytes.data[0] = 33
        · have hloopEq : Algorithm.deserializePlaintext.loop lines numLines i false bytes limit p col
              rowIdx longestIdx longestLen hasLongest warns acc =
              Algorithm.deserializePlaintext.loop lines numLines (i + 1) false lineBytes lineLimit 0 0
                rowIdx longestIdx longestLen hasLongest warns acc := by
            rw [Algorithm.deserializePlaintext.loop]
            simp only [hi, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte, hlineLoop]
            change (if lineLimit == 0 then _ else if lineBytes.get! 0 == 33 then _ else _) = _
            simp only [hne0, hb0eq, hb33, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, lineLimit]
          rcases pt_line_comment (f := f - 6 - 13) (jh := jh1) (hp := ⟨ar, u64, asc⟩)
              (by omega) hne0 hpos0 hb33 hget1 h14 h15 hlocs1 with ⟨locs2, hp2, hlocs2⟩
          rcases ih (f - 6 - 13 - 58) (i + 1) bytesAddr1 lineBytes lineLimit 0 0 rowIdx
              longestIdx longestLen hasLongest warns warnsVal accId acc locs2 jh1 u64 hmNext
              (by omega) hw hu hlocs2 with ⟨v, st', hrec, hdec⟩
          refine ⟨v, st', ?_, ?_⟩
          · rw [hp0, hp1, hp2]; exact hrec
          · rw [hloopEq]; exact hdec
        · have hne33B : (lineBytes.get! 0 == 33) = false := by
            rw [hb0eq]; exact beq_false_of_ne hb33
          rcases pt_line_row_hdr (f := f - 6 - 13) (jh := jh1) (hp := ⟨ar, u64, asc⟩)
              (by omega) hne0 hpos0 hb33 hget1 h14 h15 hlocs1 with
              ⟨locs2, hp2, h2_14, h2_15, h2_16, hlocs2⟩
          let len := Algorithm.countChars lineBytes lineLimit 0 0
          have hlimLe : lineLimit.toNat ≤ linesMaxBytes lines := by
            have h1 : lineLimit.toNat ≤ lineBytes.size := by
              dsimp only [lineLimit]
              rw [UInt32.toNat_ofNat']
              exact Nat.mod_le _ _
            exact Nat.le_trans h1 (le_linesMaxBytes lines i.toNat hiLen)
          have hmul120 : lineLimit.toNat * 120 ≤ linesMaxBytes lines * 120 :=
            Nat.mul_le_mul_right 120 hlimLe
          rcases pt_line_step_row (f := f - 6 - 13 - 14)
              (fRem := m * (linesMaxBytes lines * 120 + 200) + 50)
              (bytesAddr := bytesAddr1) (bytes := bytes) (lineBytes := lineBytes)
              (jh := jh1) (ar := ar) (u64 := u64) (asc := asc)
              hi hlineLoop hne0 hne33B (by omega) hget1 h2_14 h2_15 h2_16 hw hu
              hlocs2 rfl with
              ⟨f', rowIdx', longestIdx', longestLen', hasLongest', warns', wv', accId', acc', locs3,
                jh3, u64_3, hf', hrow, hw', hu', hlocs3, hloopEq⟩
          rcases ih f' (i + 1) bytesAddr1 lineBytes lineLimit 0 0 rowIdx' longestIdx' longestLen'
              hasLongest' warns' wv' accId' acc' locs3 jh3 u64_3 hmNext hf' hw' hu' hlocs3 with
              ⟨v, st', htail, hdec⟩
          refine ⟨v, st', ?_, ?_⟩
          · rw [hp0, hp1, hp2, hrow]; exact htail
          · rw [hloopEq]; exact hdec
    · have hnot : ¬(i < numLines) := hi
      exact deserializePlaintext_base (by omega) hnot hw hu hlocs

theorem deserializePlaintext_loop_equiv
    (lines : Array String) (numLines i : UInt32) (inRow : Bool)
    (bytes : ByteArray) (limit p col rowIdx longestIdx longestLen : UInt32) (hasLongest : Bool)
    (warns : Algorithm.GrowBuf Algorithm.PlaintextWarning) (acc : Algorithm.U64Buf)
    (hnum : numLines.toNat ≤ lines.size) (hlen31 : lines.size < 2 ^ 31) :
    let fuel := (numLines.toNat - i.toNat) * (linesMaxBytes lines * 120 + 200) +
      (if inRow then (limit.toNat - p.toNat) * 120 + 67 else 0) + 59
    let jh0 : Jvm.JvmHeap AlgExt := ({} : Jvm.JvmHeap AlgExt).alloc (.byteArray bytes.data) |>.2
    let st0 : JvmState := { initJvmState
      [(0, .strArr lines), (1, .i32 numLines), (2, .i32 i),
       (3, .i32 (if inRow then 1 else 0)), (4, .heapRef 0), (5, .i32 limit),
       (6, .i32 p), (7, .i32 col), (8, .i32 rowIdx), (9, .i32 longestIdx),
       (10, .i32 longestLen), (11, .i32 (if hasLongest then 1 else 0)),
       (12, .ext (.ptWarnGrowBuf warns)), (13, .ext (.u64Ref 0))] [] [acc] with jvmHeap := jh0 }
    ∃ v st',
      runJvmRes fuel f_Algorithm_deserializePlaintext_loop_prog st0 = some (v, st') ∧
      decodePlaintextResult st' v =
        some (Algorithm.deserializePlaintext.loop lines numLines i inRow bytes limit p col
          rowIdx longestIdx longestLen hasLongest warns acc) := by
  intro fuel jh0 st0
  have hbytes0 : jh0.get? 0 = some (.byteArray bytes.data) := by
    simp [jh0, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  let locs0 := st0.locals
  have hlocs0 : PtRowLocs locs0 lines numLines i inRow 0 limit p col rowIdx longestIdx longestLen
      hasLongest (.ext (.ptWarnGrowBuf warns)) 0 := by
    constructor <;> simp [locs0, st0, initJvmState, Jvm.initJvmState, setLocal]
  have hpre : runJvmResFast fuel f_Algorithm_deserializePlaintext_loop_prog 0
      f_Algorithm_deserializePlaintext_loop_prog st0 =
      runJvmResFast (fuel - 9) f_Algorithm_deserializePlaintext_loop_prog 9
        (f_Algorithm_deserializePlaintext_loop_prog.drop 9) ⟨9, [], locs0, jh0, ⟨[], [acc], []⟩⟩ := by
    have h9 : fuel = (fuel - 9) + 9 := by dsimp only [fuel]; omega
    conv => lhs; arg 1; rw [h9]
    dsimp only [f_Algorithm_deserializePlaintext_loop_prog, st0, initJvmState, Jvm.initJvmState, List.foldl]
    rw [runJvmResFast_stepResHeapChunk 2]; (conv => lhs; arg 1; jvm_whnf_blk)
    rw [afterResBlockChunk_cont]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
    rw [runJvmResFast_stepResHeapChunk 2]; (conv => lhs; arg 1; jvm_whnf_blk)
    rw [afterResBlockChunk_cont]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
    rw [runJvmResFast_stepResHeapChunk 2]; (conv => lhs; arg 1; jvm_whnf_blk)
    rw [afterResBlockChunk_cont]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
    rfl
  cases inRow with
  | false =>
    rcases deserializePlaintext_lines_tail (numLines.toNat - i.toNat) (fuel - 9) lines numLines i 0 bytes
        limit p col rowIdx longestIdx longestLen hasLongest warns (.ext (.ptWarnGrowBuf warns)) 0 acc
        locs0 jh0 [] [acc] [] hnum hlen31 (Nat.le_refl _)
        (by dsimp only [fuel]; simp only [Bool.false_eq_true, ↓reduceIte]; omega)
        (PtWarnRep.full _) rfl hlocs0 with ⟨v, st', htail, hdec⟩
    refine ⟨v, st', ?_, hdec⟩
    apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    rw [hpre]
    exact htail
  | true =>
    by_cases hi : i < numLines
    · have hiNat : i.toNat < numLines.toNat := UInt32.lt_iff_toNat_lt.mp hi
      have hmNext : numLines.toNat - (i + 1).toNat ≤ numLines.toNat - i.toNat - 1 := by
        rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
        omega
      rcases deserializePlaintext_row_jvm (limit.toNat - p.toNat) (fuel - 9)
          ((numLines.toNat - i.toNat - 1) * (linesMaxBytes lines * 120 + 200) + 50)
          lines numLines i 0 bytes limit p col rowIdx longestIdx longestLen hasLongest warns
          (.ext (.ptWarnGrowBuf warns)) 0 acc locs0 jh0 [] [acc] [] hi (Nat.le_refl _)
          (by
            have hmul : (numLines.toNat - i.toNat - 1) * (linesMaxBytes lines * 120 + 200) +
                (linesMaxBytes lines * 120 + 200) =
                (numLines.toNat - i.toNat) * (linesMaxBytes lines * 120 + 200) := by
              have hpos : 1 ≤ numLines.toNat - i.toNat := by omega
              calc (numLines.toNat - i.toNat - 1) * (linesMaxBytes lines * 120 + 200) +
                  (linesMaxBytes lines * 120 + 200)
                  = (numLines.toNat - i.toNat - 1 + 1) * (linesMaxBytes lines * 120 + 200) := by
                    rw [Nat.add_mul, Nat.one_mul]
                _ = (numLines.toNat - i.toNat) * (linesMaxBytes lines * 120 + 200) := by rw [Nat.sub_add_cancel hpos]
            dsimp only [fuel]
            simp only [↓reduceIte]
            omega)
          hbytes0 (PtWarnRep.full _) rfl hlocs0 with
          ⟨f', locs1, wv1, jh1, u64_1, hf', hrowJvm, hw1, accId1, hu1, hlocs1⟩
      rcases deserializePlaintext_lines_tail (numLines.toNat - i.toNat - 1) f' lines numLines (i + 1) 0 bytes
          limit 0 0 (rowIdx + 1) longestIdx longestLen hasLongest _ wv1 accId1 _ locs1 jh1 [] u64_1 []
          hnum hlen31 hmNext hf' hw1 hu1 hlocs1 with ⟨v, st', htail, hdec⟩
      refine ⟨v, st', ?_, ?_⟩
      · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
        rw [hpre, hrowJvm]; exact htail
      · rw [deserializePlaintext_loop_row_eq (limit.toNat - p.toNat) lines numLines i bytes limit p col
          rowIdx longestIdx longestLen hasLongest warns acc (Nat.le_refl _) hi]
        exact hdec
    · rcases deserializePlaintext_base (f := fuel - 9) (u64 := [acc]) (by dsimp only [fuel]; omega) hi
          (PtWarnRep.full _) rfl hlocs0 with ⟨v, st', hbase, hdec⟩
      refine ⟨v, st', ?_, hdec⟩
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      rw [hpre]
      exact hbase

private theorem decodePlaintextResult_encode
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (res : Algorithm.PlaintextResult) :
    let (v, jh', u64s') := encodePlaintextResult jh hp.u64Arrays res
    decodePlaintextResult ⟨0, [], fun _ => .null, jh', { hp with u64Arrays := u64s' }⟩ v = some res := by
  rcases res with ⟨warns, cells⟩
  dsimp only [encodePlaintextResult]
  have hfl := encodeGrowBufArray_foldl_ptWarn warns.toList #[] jh [] rfl
  simp only [Array.foldl_toList, List.nil_append] at hfl
  let foldRes := warns.foldl
    (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) w =>
      (p.1.push (encodePlaintextWarning p.2 w).1, (encodePlaintextWarning p.2 w).2))
    (#[], jh)
  let h2 := (foldRes.2.alloc (.objArray "java/lang/Object" foldRes.1)).2
  let h3 := (h2.alloc (.instance "com/alexvanyo/composelife/model/PlaintextResult"
    [("warnings", .heapRef foldRes.2.objects.size), ("cells", .ext (.u64Ref hp.u64Arrays.length))])).2
  have hext2 : HeapExtends foldRes.2 h2 := heapExtends_alloc _ _
  have hext3 : HeapExtends h2 h3 := heapExtends_alloc _ _
  have hgetArr2 : h2.get? foldRes.2.objects.size = some (.objArray "java/lang/Object" foldRes.1) := by
    simp [h2, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  have hgetArr3 : h3.get? foldRes.2.objects.size = some (.objArray "java/lang/Object" foldRes.1) :=
    hext3 _ _ hgetArr2
  have hgetRes3 : h3.get? h2.objects.size = some (.instance "com/alexvanyo/composelife/model/PlaintextResult"
      [("warnings", .heapRef foldRes.2.objects.size), ("cells", .ext (.u64Ref hp.u64Arrays.length))]) := by
    simp [h3, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  have hmap3 : foldRes.1.toList.mapM (decodePlaintextWarning h3) = some warns.toList :=
    mapM_decodePlaintextWarning_mono (heapExtends_trans hext2 hext3) hfl.2
  exact decodePlaintextResult_arr (addr := h2.objects.size) (wAddr := foldRes.2.objects.size)
    (cid := hp.u64Arrays.length) (warnVals := foldRes.1) (warns := warns) (cells := cells)
    hgetRes3 hgetArr3 (by simp) hmap3

private theorem decodePlaintextResult_state_congr {st1 st2 : JvmState} {v : JvmVal}
    (hjh : st1.jvmHeap = st2.jvmHeap) (hu : st1.heap.u64Arrays = st2.heap.u64Arrays) :
    decodePlaintextResult st1 v = decodePlaintextResult st2 v := by
  cases st1 with
  | mk pc1 stk1 loc1 jh1 hp1 =>
    cases st2 with
    | mk pc2 stk2 loc2 jh2 hp2 =>
      cases hp1 with
      | mk ar1 u64_1 asc1 =>
        cases hp2 with
        | mk ar2 u64_2 asc2 =>
          dsimp only at hjh hu
          subst hjh hu
          rfl

private theorem decodePlaintextResult_encode_proj
    (jh : Jvm.JvmHeap AlgExt) (u : List (Array UInt64)) (res : Algorithm.PlaintextResult) :
    decodePlaintextResult ⟨0, [], fun _ => .null, (encodePlaintextResult jh u res).2.1,
      { arenas := [], u64Arrays := (encodePlaintextResult jh u res).2.2, asciiArrays := [] }⟩
      (encodePlaintextResult jh u res).1 = some res :=
  decodePlaintextResult_encode jh ⟨[], u, []⟩ res

private def ptWarns? (warnsVal : JvmVal) : Option (Algorithm.GrowBuf Algorithm.PlaintextWarning) :=
  match warnsVal with
  | .ext (.ptWarnGrowBuf b) => some b
  | .ext (.strGrowBuf b) => if b.data.isEmpty && b.size == 0 then some Algorithm.GrowBuf.empty else none
  | _ => none

private def ptDispatch (pc : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (hp : AlgHeap) (cId : Nat)
    (warnsVal : JvmVal) (hasLongest longestLen longestIdx rowIdx col p limit : UInt32)
    (bytesVal : JvmVal) (inRow i numLines : UInt32) (linesVal : JvmVal)
    (rest : List JvmVal)
    (loopFn : Array String → UInt32 → UInt32 → Bool → ByteArray → UInt32 → UInt32 → UInt32 →
      UInt32 → UInt32 → UInt32 → Bool → Algorithm.GrowBuf Algorithm.PlaintextWarning → Array UInt64 →
      Algorithm.PlaintextResult)
    (encFn : Jvm.JvmHeap AlgExt → List (Array UInt64) → Algorithm.PlaintextResult →
      JvmVal × Jvm.JvmHeap AlgExt × List (Array UInt64)) : Option JvmState ⊕ Option JvmVal :=
  let st : JvmState := ⟨pc, .ext (.u64Ref cId) :: warnsVal :: .i32 hasLongest :: .i32 longestLen :: .i32 longestIdx ::
    .i32 rowIdx :: .i32 col :: .i32 p :: .i32 limit :: bytesVal :: .i32 inRow :: .i32 i :: .i32 numLines :: linesVal :: rest, locs, jh, hp⟩
  match decodeStrArray st linesVal, decodeBytes st bytesVal, ptWarns? warnsVal, st.heap.u64Arrays[cId]? with
  | some lines', some bytes', some warns, some cells' =>
    let res := loopFn lines' numLines i (inRow != 0)
      bytes' limit p col rowIdx longestIdx longestLen
      (hasLongest != 0) warns cells'
    let (resVal, h', u64s') := encFn st.jvmHeap st.heap.u64Arrays res
    .inl (some { st with
      pc := st.pc + 1, stack := resVal :: rest,
      jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
  | _, _, _, _ => .inr none

private theorem stepStatic_match_only (pc : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (hp : AlgHeap) (cId : Nat)
    (warnsVal : JvmVal) (hasLongest longestLen longestIdx rowIdx col p limit : UInt32)
    (bytesVal : JvmVal) (inRow i numLines : UInt32) (linesVal : JvmVal)
    (rest : List JvmVal) :
    let st : JvmState := ⟨pc, .ext (.u64Ref cId) :: warnsVal :: .i32 hasLongest :: .i32 longestLen :: .i32 longestIdx ::
      .i32 rowIdx :: .i32 col :: .i32 p :: .i32 limit :: bytesVal :: .i32 inRow :: .i32 i :: .i32 numLines :: linesVal :: rest, locs, jh, hp⟩
    stepInvokeStatic st "PlaintextLeanKt" "f_Algorithm_deserializePlaintext_loop-JllRuGI"
      ("([Ljava/lang/Object;IIZ[BIIIIIIZLjava/lang/Object;[J)" ++
        "Lcom/alexvanyo/composelife/model/PlaintextResult;") =
    ptDispatch pc locs jh hp cId warnsVal hasLongest longestLen longestIdx rowIdx col p limit
      bytesVal inRow i numLines linesVal rest
      Algorithm.deserializePlaintext.loop encodePlaintextResult := rfl

private theorem pt_match_elim
    (pc : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (hp : AlgHeap) (cId : Nat)
    (warnsVal : JvmVal) (hasLongest longestLen longestIdx rowIdx col p limit : UInt32)
    (bytesVal : JvmVal) (inRow i numLines : UInt32) (linesVal : JvmVal)
    (rest : List JvmVal)
    (loopFn : Array String → UInt32 → UInt32 → Bool → ByteArray → UInt32 → UInt32 → UInt32 →
      UInt32 → UInt32 → UInt32 → Bool → Algorithm.GrowBuf Algorithm.PlaintextWarning → Array UInt64 →
      Algorithm.PlaintextResult)
    (encFn : Jvm.JvmHeap AlgExt → List (Array UInt64) → Algorithm.PlaintextResult →
      JvmVal × Jvm.JvmHeap AlgExt × List (Array UInt64))
    {lines : Array String} {bytes : ByteArray}
    {warns : Algorithm.GrowBuf Algorithm.PlaintextWarning} {cells : Algorithm.U64Buf}
    (hl : decodeStrArray ⟨pc, .ext (.u64Ref cId) :: warnsVal :: .i32 hasLongest :: .i32 longestLen :: .i32 longestIdx ::
      .i32 rowIdx :: .i32 col :: .i32 p :: .i32 limit :: bytesVal :: .i32 inRow :: .i32 i :: .i32 numLines :: linesVal :: rest, locs, jh, hp⟩
      linesVal = some lines)
    (hb : decodeBytes ⟨pc, .ext (.u64Ref cId) :: warnsVal :: .i32 hasLongest :: .i32 longestLen :: .i32 longestIdx ::
      .i32 rowIdx :: .i32 col :: .i32 p :: .i32 limit :: bytesVal :: .i32 inRow :: .i32 i :: .i32 numLines :: linesVal :: rest, locs, jh, hp⟩
      bytesVal = some bytes)
    (hw : ptWarns? warnsVal = some warns)
    (hc : hp.u64Arrays[cId]? = some cells) :
    ptDispatch pc locs jh hp cId warnsVal hasLongest longestLen longestIdx rowIdx col p limit
      bytesVal inRow i numLines linesVal rest loopFn encFn =
    (.inl (some ⟨pc + 1,
      (encFn jh hp.u64Arrays (loopFn lines numLines i (inRow != 0)
        bytes limit p col rowIdx longestIdx longestLen
        (hasLongest != 0) warns cells)).1 :: rest,
      locs,
      (encFn jh hp.u64Arrays (loopFn lines numLines i (inRow != 0)
        bytes limit p col rowIdx longestIdx longestLen
        (hasLongest != 0) warns cells)).2.1,
      { arenas := hp.arenas,
        u64Arrays := (encFn jh hp.u64Arrays (loopFn lines numLines i (inRow != 0)
          bytes limit p col rowIdx longestIdx longestLen
          (hasLongest != 0) warns cells)).2.2,
        asciiArrays := hp.asciiArrays }⟩) : Option JvmState ⊕ Option JvmVal) := by
  dsimp only [ptDispatch]
  rw [hl, hb, hw, hc]

private theorem stepStatic_deserializePlaintext_loop_heap
    {pc : Nat} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {cId : Nat} {cells : Algorithm.U64Buf}
    {warns : Algorithm.GrowBuf Algorithm.PlaintextWarning}
    {warnsVal : JvmVal} {hasLongest longestLen longestIdx rowIdx col p limit : UInt32}
    {bytesVal : JvmVal} {inRow i numLines : UInt32} {linesVal : JvmVal}
    {rest : List JvmVal} {lines : Array String} {bytes : ByteArray}
    (hc : u64[cId]? = some cells)
    (hw : ptWarns? warnsVal = some warns)
    (hl : decodeStrArray ⟨pc, .ext (.u64Ref cId) :: warnsVal :: .i32 hasLongest :: .i32 longestLen :: .i32 longestIdx ::
      .i32 rowIdx :: .i32 col :: .i32 p :: .i32 limit :: bytesVal :: .i32 inRow :: .i32 i :: .i32 numLines :: linesVal :: rest,
      locs, jh, ⟨ar, u64, asc⟩⟩ linesVal = some lines)
    (hb : decodeBytes ⟨pc, .ext (.u64Ref cId) :: warnsVal :: .i32 hasLongest :: .i32 longestLen :: .i32 longestIdx ::
      .i32 rowIdx :: .i32 col :: .i32 p :: .i32 limit :: bytesVal :: .i32 inRow :: .i32 i :: .i32 numLines :: linesVal :: rest,
      locs, jh, ⟨ar, u64, asc⟩⟩ bytesVal = some bytes) :
    stepInvokeStatic ⟨pc, .ext (.u64Ref cId) :: warnsVal :: .i32 hasLongest :: .i32 longestLen :: .i32 longestIdx ::
      .i32 rowIdx :: .i32 col :: .i32 p :: .i32 limit :: bytesVal :: .i32 inRow :: .i32 i :: .i32 numLines :: linesVal :: rest,
      locs, jh, ⟨ar, u64, asc⟩⟩ "PlaintextLeanKt" "f_Algorithm_deserializePlaintext_loop-JllRuGI"
      ("([Ljava/lang/Object;IIZ[BIIIIIIZLjava/lang/Object;[J)" ++
        "Lcom/alexvanyo/composelife/model/PlaintextResult;") =
      .inl (some ⟨pc + 1,
        (encodePlaintextResult jh u64 (Algorithm.deserializePlaintext.loop lines numLines i
          (inRow != 0) bytes limit p col rowIdx longestIdx
          longestLen (hasLongest != 0) warns cells)).1 :: rest,
        locs,
        (encodePlaintextResult jh u64 (Algorithm.deserializePlaintext.loop lines numLines i
          (inRow != 0) bytes limit p col rowIdx longestIdx
          longestLen (hasLongest != 0) warns cells)).2.1,
        ⟨ar, (encodePlaintextResult jh u64 (Algorithm.deserializePlaintext.loop lines numLines i
          (inRow != 0) bytes limit p col rowIdx longestIdx
          longestLen (hasLongest != 0) warns cells)).2.2, asc⟩⟩) :=
  Eq.trans (stepStatic_match_only pc locs jh ⟨ar, u64, asc⟩ cId
    warnsVal hasLongest longestLen longestIdx rowIdx col p limit bytesVal inRow i numLines linesVal rest)
    (pt_match_elim pc locs jh ⟨ar, u64, asc⟩ cId
      warnsVal hasLongest longestLen longestIdx rowIdx col p limit bytesVal inRow i numLines linesVal rest
      Algorithm.deserializePlaintext.loop encodePlaintextResult hl hb hw hc)

private theorem pt_enc_state_congr (pc : Nat) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (encFn : Jvm.JvmHeap AlgExt → List (Array UInt64) → Algorithm.PlaintextResult →
      JvmVal × Jvm.JvmHeap AlgExt × List (Array UInt64))
    (r1 r2 : Algorithm.PlaintextResult) (hr : r1 = r2) :
    (.inl (some ⟨pc + 1, [(encFn jh u64 r1).1], locs, (encFn jh u64 r1).2.1,
      ⟨ar, (encFn jh u64 r1).2.2, asc⟩⟩) : Option JvmState ⊕ Option JvmVal) =
    (.inl (some ⟨pc + 1, [(encFn jh u64 r2).1], locs, (encFn jh u64 r2).2.1,
      ⟨ar, (encFn jh u64 r2).2.2, asc⟩⟩) : Option JvmState ⊕ Option JvmVal) := by
  subst hr
  rfl

private theorem pt_decode_encode_proj
    (decFn : JvmState → JvmVal → Option Algorithm.PlaintextResult)
    (enc : JvmVal × Jvm.JvmHeap AlgExt × List (Array UInt64))
    (res : Algorithm.PlaintextResult)
    (h : let (v, jh', u64s') := enc
         decFn ⟨0, [], fun _ => .null, jh',
           { arenas := [], u64Arrays := u64s', asciiArrays := [] }⟩ v = some res) :
    decFn ⟨0, [], fun _ => .null, enc.2.1,
      { arenas := [], u64Arrays := enc.2.2, asciiArrays := [] }⟩ enc.1 = some res := by
  rcases enc with ⟨a, b, c⟩
  exact h

private theorem stepStatic_deserializePlaintext_loop_init
    {pc : Nat} {lines : Array String} {locs : Nat → JvmVal} :
    let jh0 : Jvm.JvmHeap AlgExt := ⟨#[Jvm.HeapObj.byteArray #[]], ({} : Jvm.JvmHeap AlgExt).statics⟩
    let enc := encodePlaintextResult jh0 [Algorithm.U64Buf.empty] (Algorithm.deserializePlaintext lines)
    stepInvokeStatic ⟨pc, [.ext (.u64Ref 0), .ext (.strGrowBuf Algorithm.GrowBuf.empty),
        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .heapRef 0,
        .i32 0, .i32 0, .i32 lines.size.toUInt32, .strArr lines],
      locs, jh0, ⟨[], [Algorithm.U64Buf.empty], []⟩⟩
      "PlaintextLeanKt" "f_Algorithm_deserializePlaintext_loop-JllRuGI"
      ("([Ljava/lang/Object;IIZ[BIIIIIIZLjava/lang/Object;[J)" ++
        "Lcom/alexvanyo/composelife/model/PlaintextResult;") =
      .inl (some ⟨pc + 1, [enc.1], locs, enc.2.1, ⟨[], enc.2.2, []⟩⟩) := by
  let jh0 : Jvm.JvmHeap AlgExt := ⟨#[Jvm.HeapObj.byteArray #[]], ({} : Jvm.JvmHeap AlgExt).statics⟩
  have hw0 : ptWarns? (.ext (.strGrowBuf Algorithm.GrowBuf.empty)) = some Algorithm.GrowBuf.empty := rfl
  have hc0 : ([Algorithm.U64Buf.empty] : List (Array UInt64))[0]? = some Algorithm.U64Buf.empty := rfl
  have hl0 : decodeStrArray ⟨pc, [.ext (.u64Ref 0), .ext (.strGrowBuf Algorithm.GrowBuf.empty),
        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .heapRef 0,
        .i32 0, .i32 0, .i32 lines.size.toUInt32, .strArr lines],
      locs, jh0, ⟨[], [Algorithm.U64Buf.empty], []⟩⟩ (.strArr lines) = some lines := rfl
  have hb0 : decodeBytes ⟨pc, [.ext (.u64Ref 0), .ext (.strGrowBuf Algorithm.GrowBuf.empty),
        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .heapRef 0,
        .i32 0, .i32 0, .i32 lines.size.toUInt32, .strArr lines],
      locs, jh0, ⟨[], [Algorithm.U64Buf.empty], []⟩⟩ (.heapRef 0) = some ⟨#[]⟩ := rfl
  have hstep := stepStatic_deserializePlaintext_loop_heap hc0 hw0 hl0 hb0
  have harg : Algorithm.deserializePlaintext.loop lines
      lines.size.toUInt32 0 (0 != 0) ⟨#[]⟩ 0 0 0 0 0 0 (0 != 0)
      Algorithm.GrowBuf.empty Algorithm.U64Buf.empty =
      Algorithm.deserializePlaintext lines := by
    simp [Algorithm.deserializePlaintext]; rfl
  exact Eq.trans hstep (pt_enc_state_congr pc locs jh0 [] [Algorithm.U64Buf.empty] []
    encodePlaintextResult _ (Algorithm.deserializePlaintext lines) harg)

private theorem pt_areturn_step {f : Nat} {prog : List JvmInstr} {pc pc0 : Nat}
    {v : JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc [.areturn] ⟨pc0, [v], locs, jh, hp⟩ =
      some (v, ⟨pc, [v], locs, jh, hp⟩) := rfl

private def ptInitJh0 : Jvm.JvmHeap AlgExt :=
  ⟨#[Jvm.HeapObj.byteArray #[]], ({} : Jvm.JvmHeap AlgExt).statics⟩

private theorem pt_loop_init_enc {pc : Nat} {lines : Array String} {locs : Nat → JvmVal} :
    stepInvokeStatic ⟨pc, [.ext (.u64Ref 0), .ext (.strGrowBuf Algorithm.GrowBuf.empty),
        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .heapRef 0,
        .i32 0, .i32 0, .i32 lines.size.toUInt32, .strArr lines],
      locs, ⟨#[Jvm.HeapObj.byteArray #[]], ({} : Jvm.JvmHeap AlgExt).statics⟩,
      ⟨[], [Algorithm.U64Buf.empty], []⟩⟩
      "PlaintextLeanKt" "f_Algorithm_deserializePlaintext_loop-JllRuGI"
      ("([Ljava/lang/Object;IIZ[BIIIIIIZLjava/lang/Object;[J)" ++
        "Lcom/alexvanyo/composelife/model/PlaintextResult;") =
      .inl (some ⟨pc + 1,
        [(encodePlaintextResult ptInitJh0 [Algorithm.U64Buf.empty]
          (Algorithm.deserializePlaintext lines)).1],
        locs,
        (encodePlaintextResult ptInitJh0 [Algorithm.U64Buf.empty]
          (Algorithm.deserializePlaintext lines)).2.1,
        ⟨[], (encodePlaintextResult ptInitJh0 [Algorithm.U64Buf.empty]
          (Algorithm.deserializePlaintext lines)).2.2, []⟩⟩) :=
  stepStatic_deserializePlaintext_loop_init

private theorem deserializePlaintext_hrun (lines : Array String) :
    ∃ (pc' : Nat) (locs' : Nat → JvmVal),
      runJvmRes 40 f_Algorithm_deserializePlaintext_prog (initJvmState [(0, .strArr lines)]) =
        some ((encodePlaintextResult ptInitJh0 [Algorithm.U64Buf.empty]
            (Algorithm.deserializePlaintext lines)).1,
          ⟨pc',
            [(encodePlaintextResult ptInitJh0 [Algorithm.U64Buf.empty]
              (Algorithm.deserializePlaintext lines)).1],
            locs',
            (encodePlaintextResult ptInitJh0 [Algorithm.U64Buf.empty]
              (Algorithm.deserializePlaintext lines)).2.1,
            ⟨[], (encodePlaintextResult ptInitJh0 [Algorithm.U64Buf.empty]
              (Algorithm.deserializePlaintext lines)).2.2, []⟩⟩) := by
  have hrep0 : Array.replicate (UInt32.toNat (0 : UInt32)) (0 : UInt8) = #[] := rfl
  have hjh0 : (({} : Jvm.JvmHeap AlgExt).alloc (Jvm.HeapObj.byteArray #[])).snd =
      ⟨#[Jvm.HeapObj.byteArray #[]], ({} : Jvm.JvmHeap AlgExt).statics⟩ := rfl
  have hto : UInt32.ofNat lines.size = lines.size.toUInt32 := rfl
  have hf11 : (11 : Nat) = 10 + 1 := rfl
  have hf10 : (10 : Nat) = 9 + 1 := rfl
  apply Exists.intro
  apply Exists.intro
  apply runJvmRes_of_runJvmResFast0 40 _ _ _ rfl
  dsimp only [f_Algorithm_deserializePlaintext_prog, initJvmState, Jvm.initJvmState, List.foldl]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
  rw [runJvmResFast_arraylength_strArr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step rfl]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
  rw [runJvmResFast_newarray_byte (by decide)]; norm_res_fuel
  conv => lhs; rw [hrep0]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_invokestatic_step (stepStatic_growBufEmpty_heap (Or.inr (Or.inr (Or.inl rfl))))]
  norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_invokestatic_step
    (stepStatic_u64BufEmpty_heap (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]
  norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 1; rw [hf11]
  conv =>
    lhs; arg 5
    dsimp only [setLocal]
    simp only [List.length_nil, List.nil_append, Array.size_empty]
    rw [hjh0, hto]
  refine Eq.trans
    (runJvmResFast_invokestatic_step (@pt_loop_init_enc 29 lines _)) ?_
  conv => lhs; arg 1; rw [hf10]
  exact pt_areturn_step

private theorem pt_equiv_finish
    (prog : List JvmInstr) (st0 : JvmState)
    (decFn : JvmState → JvmVal → Option Algorithm.PlaintextResult)
    (enc : JvmVal × Jvm.JvmHeap AlgExt × List (Array UInt64))
    (res : Algorithm.PlaintextResult)
    (hrun : ∃ (pc' : Nat) (locs' : Nat → JvmVal),
      runJvmRes 40 prog st0 = some (enc.1, ⟨pc', [enc.1], locs', enc.2.1, ⟨[], enc.2.2, []⟩⟩))
    (hcongr : ∀ pc' locs',
      decFn ⟨pc', [enc.1], locs', enc.2.1, ⟨[], enc.2.2, []⟩⟩ enc.1 =
      decFn ⟨0, [], fun _ => .null, enc.2.1, ⟨[], enc.2.2, []⟩⟩ enc.1)
    (hdec : decFn ⟨0, [], fun _ => .null, enc.2.1,
        { arenas := [], u64Arrays := enc.2.2, asciiArrays := [] }⟩ enc.1 = some res) :
    ∃ v st', runJvmRes 40 prog st0 = some (v, st') ∧ decFn st' v = some res := by
  rcases hrun with ⟨pc', locs', hrun'⟩
  refine ⟨enc.1, ⟨pc', [enc.1], locs', enc.2.1, ⟨[], enc.2.2, []⟩⟩, hrun', ?_⟩
  rw [hcongr pc' locs']
  exact hdec

theorem deserializePlaintext_equiv (lines : Array String) :
    ∃ v st',
      runJvmRes 40 f_Algorithm_deserializePlaintext_prog (initJvmState [(0, .strArr lines)]) =
        some (v, st') ∧
      decodePlaintextResult st' v = some (Algorithm.deserializePlaintext lines) :=
  pt_equiv_finish f_Algorithm_deserializePlaintext_prog (initJvmState [(0, .strArr lines)])
    decodePlaintextResult
    (encodePlaintextResult ptInitJh0 [Algorithm.U64Buf.empty] (Algorithm.deserializePlaintext lines))
    (Algorithm.deserializePlaintext lines)
    (deserializePlaintext_hrun lines)
    (fun _ _ => decodePlaintextResult_state_congr rfl rfl)
    (decodePlaintextResult_encode_proj ptInitJh0 [Algorithm.U64Buf.empty] (Algorithm.deserializePlaintext lines))

end
end Algorithm.JvmVerification
