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

/-! ### Family 6a: RLE Parsing, Comments, Header, Rule, Offset -/

def decodeOptParsedCoords (h : Jvm.JvmHeap AlgExt) : JvmVal → Option (Option Algorithm.ParsedCoords)
  | .heapRef addr =>
    match h.get? addr with
    | some (.objArray _ elems) =>
      if _ : elems.size > 0 then
        match elems[0] with
        | .boxedInt 0 => some none
        | .boxedInt 1 =>
          if _ : elems.size > 1 then
            match elems[1] with
            | .heapRef innerAddr =>
              match h.get? innerAddr with
              | some (.objArray _ inner) =>
                if _ : inner.size > 5 then
                  match inner[1], inner[5] with
                  | .boxedInt x, .boxedInt y => some (some ⟨x.toInt32, y.toInt32⟩)
                  | _, _ => none
                else none
              | _ => none
            | _ => none
          else none
        | _ => none
      else none
    | _ => none
  | _ => none

def decodeRLEResult (st : JvmState) : JvmVal → Option Algorithm.RLEResult
  | .heapRef a =>
    match st.jvmHeap.get? a with
    | some (.instance "com/alexvanyo/composelife/model/RLEResult" flds) =>
      match flds.lookup "status", flds.lookup "warnings", flds.lookup "cells" with
      | some (.ext (.rleStatus s)), some (.heapRef wAddr), some (.ext (.u64Ref cid)) =>
        match st.jvmHeap.get? wAddr, st.heap.u64Arrays[cid]? with
        | some (.objArray _ warnVals), some cells =>
          (warnVals.toList.mapM (decodeRLEWarning st.jvmHeap)).map fun ws =>
            ⟨s, ws.toArray, cells⟩
        | _, _ => none
      | some (.ext (.rleStatus s)), some (.strArr sa), some (.ext (.u64Ref cid)) =>
        if sa.isEmpty then st.heap.u64Arrays[cid]?.map fun cells => ⟨s, #[], cells⟩ else none
      | _, _, _ => none
    | _ => none
  | _ => none

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
elab "step_res_block " n:num : tactic => do
  evalTactic (← `(tactic| rw [runJvmResFast_stepResHeapChunk $n]))
  evalTactic (← `(tactic| (conv => lhs; arg 1; jvm_whnf_blk)))
  evalTactic (← `(tactic| rw [afterResBlockChunk_cont]))
  evalTactic (← `(tactic| (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)))
  evalTactic (← `(tactic| norm_res_fuel))

open Lean Elab Tactic in
local elab "drop_prefix " n:num : tactic => do
  for _ in [:n.getNat] do
    evalTactic (← `(tactic| (conv => lhs; rw [list_drop_step rfl]); try simp only [Nat.reduceAdd]))
  evalTactic (← `(tactic| try rfl))

private theorem stepStatic_uintCtor_local {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, stk, locs, jh, ⟨ar, u64, asc⟩⟩ "kotlin/UInt" "constructor-impl" "(I)I" =
      .inl (some ⟨pc + 1, stk, locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

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

private theorem decodeRLEWarning_mono {h1 h2 : Jvm.JvmHeap AlgExt}
    (hext : HeapExtends h1 h2) {v : JvmVal} {w : Algorithm.RLEWarning}
    (hdec : decodeRLEWarning h1 v = some w) : decodeRLEWarning h2 v = some w := by
  cases v with
  | allocRef cls =>
    by_cases hc : cls = "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"
    · subst hc; simpa [decodeRLEWarning] using hdec
    · simp [decodeRLEWarning, hc] at hdec
  | heapRef a =>
    dsimp only [decodeRLEWarning] at hdec ⊢
    cases hg : h1.get? a with
    | none => simp [hg] at hdec
    | some obj =>
      rw [hg] at hdec
      rw [hext a obj hg]
      exact hdec
  | _ => simp [decodeRLEWarning] at hdec

private theorem mapM_decodeRLEWarning_mono {h1 h2 : Jvm.JvmHeap AlgExt}
    (hext : HeapExtends h1 h2) {vs : List JvmVal} {ws : List Algorithm.RLEWarning}
    (hm : vs.mapM (decodeRLEWarning h1) = some ws) :
    vs.mapM (decodeRLEWarning h2) = some ws := by
  induction vs generalizing ws with
  | nil => simpa using hm
  | cons v vs ih =>
    simp only [List.mapM_cons] at hm ⊢
    cases hdv : decodeRLEWarning h1 v with
    | none => simp [hdv] at hm
    | some w =>
      rw [decodeRLEWarning_mono hext hdv]
      rw [hdv] at hm
      cases hrest : vs.mapM (decodeRLEWarning h1) with
      | none => simp [hrest] at hm
      | some ws' =>
        rw [hrest] at hm
        rw [ih hrest]
        exact hm

private theorem encodeRLEWarning_spec (h : Jvm.JvmHeap AlgExt)
    (w : Algorithm.RLEWarning) :
    HeapExtends h (encodeRLEWarning h w).2 ∧
      decodeRLEWarning (encodeRLEWarning h w).2 (encodeRLEWarning h w).1 = some w := by
  cases w with
  | emptyFile => exact ⟨heapExtends_refl h, rfl⟩
  | duplicateOffset ln x y =>
    refine ⟨heapExtends_alloc _ _, ?_⟩
    simp [encodeRLEWarning, decodeRLEWarning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup]
  | unexpectedChar ln col cp =>
    refine ⟨heapExtends_alloc _ _, ?_⟩
    simp [encodeRLEWarning, decodeRLEWarning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup]
  | unexpectedInput ln col inp =>
    refine ⟨heapExtends_alloc _ _, ?_⟩
    simp [encodeRLEWarning, decodeRLEWarning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup]
  | charAfterEnd ln col cp =>
    refine ⟨heapExtends_alloc _ _, ?_⟩
    simp [encodeRLEWarning, decodeRLEWarning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup]

private theorem encodeGrowBufArray_foldl_rleWarn
    (xs : List Algorithm.RLEWarning) (acc : Array JvmVal)
    (h : Jvm.JvmHeap AlgExt) (pfx : List Algorithm.RLEWarning)
    (hpfx : acc.toList.mapM (decodeRLEWarning h) = some pfx) :
    let step : Array JvmVal × Jvm.JvmHeap AlgExt → Algorithm.RLEWarning → Array JvmVal × Jvm.JvmHeap AlgExt :=
      fun p x => (p.1.push (encodeRLEWarning p.2 x).1, (encodeRLEWarning p.2 x).2)
    HeapExtends h (xs.foldl step (acc, h)).2 ∧
      (xs.foldl step (acc, h)).1.toList.mapM (decodeRLEWarning (xs.foldl step (acc, h)).2) =
        some (pfx ++ xs) := by
  intro step
  induction xs generalizing acc h pfx with
  | nil => exact ⟨heapExtends_refl h, by simpa using hpfx⟩
  | cons x xs ih =>
    simp only [List.foldl_cons, step]
    have hs := encodeRLEWarning_spec h x
    have hnext : ((acc.push (encodeRLEWarning h x).1).toList.mapM
        (decodeRLEWarning (encodeRLEWarning h x).2)) = some (pfx ++ [x]) := by
      simp only [Array.toList_push, List.mapM_append, List.mapM_cons, List.mapM_nil]
      rw [mapM_decodeRLEWarning_mono hs.1 hpfx, hs.2]
      rfl
    have hrec := ih (acc.push (encodeRLEWarning h x).1) (encodeRLEWarning h x).2
      (pfx ++ [x]) hnext
    refine ⟨heapExtends_trans hs.1 hrec.1, ?_⟩
    simpa [List.append_assoc, step] using hrec.2

private theorem encodeGrowBufArray_decode_rleWarn (h : Jvm.JvmHeap AlgExt)
    (b : Algorithm.GrowBuf Algorithm.RLEWarning) :
    let (v, h') := encodeGrowBufArray h encodeRLEWarning b
    HeapExtends h h' ∧
      ∃ addr warnVals, v = .heapRef addr ∧ h'.get? addr = some (.objArray "java/lang/Object" warnVals) ∧
        warnVals.toList.mapM (decodeRLEWarning h') = some b.toArray.toList := by
  dsimp only [encodeGrowBufArray]
  have hfl := encodeGrowBufArray_foldl_rleWarn b.toArray.toList #[] h [] rfl
  dsimp only at hfl
  let stepFn : Array JvmVal × Jvm.JvmHeap AlgExt → Algorithm.RLEWarning →
      Array JvmVal × Jvm.JvmHeap AlgExt :=
    fun p x => (p.1.push (encodeRLEWarning p.2 x).1, (encodeRLEWarning p.2 x).2)
  let foldRes := b.toArray.foldl stepFn (#[], h)
  have hfold_eq : foldRes = b.toArray.toList.foldl stepFn (#[], h) := by
    simp only [foldRes, ← Array.foldl_toList]
  have hfl1 : HeapExtends h foldRes.2 := by rw [hfold_eq]; exact hfl.1
  have hfl2 : foldRes.1.toList.mapM (decodeRLEWarning foldRes.2) = some b.toArray.toList := by
    rw [hfold_eq]; simpa [stepFn] using hfl.2
  have halloc := heapExtends_alloc foldRes.2 (.objArray "java/lang/Object" foldRes.1)
  refine ⟨heapExtends_trans hfl1 halloc, foldRes.2.objects.size, foldRes.1, rfl,
    jvmHeap_get?_alloc_self _ _, mapM_decodeRLEWarning_mono halloc hfl2⟩

theorem decodeRLEResult_encode
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (res : Algorithm.RLEResult) :
    let (v, jh', u64s') := encodeRLEResult jh hp.u64Arrays res
    decodeRLEResult ⟨0, [], fun _ => .null, jh', { hp with u64Arrays := u64s' }⟩ v = some res := by
  rcases res with ⟨status, warns, cells⟩
  dsimp only [encodeRLEResult]
  have hfl := encodeGrowBufArray_foldl_rleWarn warns.toList #[] jh [] rfl
  dsimp only at hfl
  let stepFn : Array JvmVal × Jvm.JvmHeap AlgExt → Algorithm.RLEWarning →
      Array JvmVal × Jvm.JvmHeap AlgExt :=
    fun p w => (p.1.push (encodeRLEWarning p.2 w).1, (encodeRLEWarning p.2 w).2)
  let foldRes := warns.foldl stepFn (#[], jh)
  have hfold_eq : foldRes = warns.toList.foldl stepFn (#[], jh) := by
    simp only [foldRes, ← Array.foldl_toList]
  have hm1 : foldRes.1.toList.mapM (decodeRLEWarning foldRes.2) = some warns.toList := by
    rw [hfold_eq]
    simpa [stepFn] using hfl.2
  let h2 := (foldRes.2.alloc (.objArray "java/lang/Object" foldRes.1)).2
  let wAddr := foldRes.2.objects.size
  have hget_w2 : h2.get? wAddr = some (.objArray "java/lang/Object" foldRes.1) :=
    jvmHeap_get?_alloc_self _ _
  let rObj : Jvm.HeapObj AlgExt := .instance "com/alexvanyo/composelife/model/RLEResult"
    [("status", .ext (.rleStatus status)), ("warnings", .heapRef wAddr),
      ("cells", .ext (.u64Ref hp.u64Arrays.length))]
  have hext23 := heapExtends_alloc h2 rObj
  let h3 := (h2.alloc rObj).2
  let resAddr := h2.objects.size
  have hget_r3 : h3.get? resAddr = some rObj := jvmHeap_get?_alloc_self _ _
  have hget_w3 : h3.get? wAddr = some (.objArray "java/lang/Object" foldRes.1) :=
    hext23 wAddr _ hget_w2
  have hm3 : foldRes.1.toList.mapM (decodeRLEWarning h3) = some warns.toList :=
    mapM_decodeRLEWarning_mono (heapExtends_trans (heapExtends_alloc _ _) hext23) hm1
  have hu64 : (hp.u64Arrays ++ [cells])[hp.u64Arrays.length]? = some cells := by simp
  change decodeRLEResult ⟨0, [], fun _ => .null, h3, { hp with u64Arrays := hp.u64Arrays ++ [cells] }⟩
      (.heapRef resAddr) = some ⟨status, warns, cells⟩
  dsimp only [decodeRLEResult]
  rw [hget_r3]
  simp only [rObj, List.lookup, beq_self_eq_true]
  rw [show ("warnings" == "status") = false from by decide,
    show ("cells" == "status") = false from by decide,
    show ("cells" == "warnings") = false from by decide]
  dsimp only
  rw [hget_w3, hu64]
  simp [hm3]

inductive RleWarnRep : Algorithm.GrowBuf Algorithm.RLEWarning → JvmVal → Prop
  | empty (b : Algorithm.GrowBuf Algorithm.RLEWarning)
      (he : b.data.isEmpty = true) (hz : b.size = 0) :
      RleWarnRep b (.ext (.strGrowBuf Algorithm.GrowBuf.empty))
  | full (b : Algorithm.GrowBuf Algorithm.RLEWarning) :
      RleWarnRep b (.ext (.rleWarnGrowBuf b))

theorem rleWarnRep_empty :
    RleWarnRep (Algorithm.GrowBuf.empty : Algorithm.GrowBuf Algorithm.RLEWarning)
      (.ext (.strGrowBuf Algorithm.GrowBuf.empty)) :=
  RleWarnRep.empty _ rfl rfl

private theorem growBuf_eq_empty_of {α : Type} {b : Algorithm.GrowBuf α}
    (he : b.data.isEmpty = true) (hz : b.size = 0) : b = Algorithm.GrowBuf.empty := by
  have hd : b.data = #[] := Array.isEmpty_iff.mp he
  rcases b with ⟨d, s⟩
  dsimp only at hd hz
  subst hd hz
  simp [Algorithm.GrowBuf.empty]

theorem stepStatic_growBufPush_rleWarn
    {pc : Nat} {wVal bufVal : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {b : Algorithm.GrowBuf Algorithm.RLEWarning} {w : Algorithm.RLEWarning}
    (hrep : RleWarnRep b bufVal) (hdec : decodeRLEWarning jh wVal = some w) :
    stepInvokeStatic ⟨pc, wVal :: bufVal :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
      "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.rleWarnGrowBuf (b.push w)) :: rest, locs, jh, hp⟩) := by
  cases hrep with
  | empty he hz =>
    have hb : b = Algorithm.GrowBuf.empty := growBuf_eq_empty_of he hz
    subst hb
    cases wVal with
    | allocRef cls =>
      have hstep : stepInvokeStatic
          ⟨pc, .allocRef cls :: .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: rest, locs, jh, hp⟩
          "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
          "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
          (if (Algorithm.GrowBuf.empty : Algorithm.GrowBuf String).data.isEmpty &&
              (Algorithm.GrowBuf.empty : Algorithm.GrowBuf String).size == 0 then
            let ext? : Option AlgExt :=
              match decodeRLEWarning jh (.allocRef cls) with
              | some w => some (.rleWarnGrowBuf (Algorithm.GrowBuf.empty.push w))
              | none =>
                match decodeMacrocellWarning jh (.allocRef cls) with
                | some w => some (.mcWarnGrowBuf (Algorithm.GrowBuf.empty.push w))
                | none => (decodePlaintextWarning jh (.allocRef cls)).map fun w =>
                    .ptWarnGrowBuf (Algorithm.GrowBuf.empty.push w)
            match ext? with
            | some e => .inl (some ⟨pc + 1, .ext e :: rest, locs, jh, hp⟩)
            | none => .inr none
          else .inr none) := rfl
      rw [hstep]
      simp only [show (Algorithm.GrowBuf.empty : Algorithm.GrowBuf String).data.isEmpty = true from rfl,
        show ((Algorithm.GrowBuf.empty : Algorithm.GrowBuf String).size == 0) = true from rfl,
        Bool.and_self, ↓reduceIte, hdec]
    | heapRef a =>
      have hstep : stepInvokeStatic
          ⟨pc, .heapRef a :: .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: rest, locs, jh, hp⟩
          "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
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
        Bool.and_self, ↓reduceIte, hdec]
    | _ => simp [decodeRLEWarning] at hdec
  | full =>
    cases wVal with
    | allocRef cls =>
      have hstep : stepInvokeStatic
          ⟨pc, .allocRef cls :: .ext (.rleWarnGrowBuf b) :: rest, locs, jh, hp⟩
          "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
          "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
          (match decodeRLEWarning jh (.allocRef cls) with
          | some w => .inl (some ⟨pc + 1, .ext (.rleWarnGrowBuf (b.push w)) :: rest, locs, jh, hp⟩)
          | none => .inr none) := rfl
      rw [hstep, hdec]
    | heapRef a =>
      have hstep : stepInvokeStatic
          ⟨pc, .heapRef a :: .ext (.rleWarnGrowBuf b) :: rest, locs, jh, hp⟩
          "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_GrowBuf_push___redArg"
          "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
          (match decodeRLEWarning jh (.heapRef a) with
          | some w => .inl (some ⟨pc + 1, .ext (.rleWarnGrowBuf (b.push w)) :: rest, locs, jh, hp⟩)
          | none => .inr none) := rfl
      rw [hstep, hdec]
    | _ => simp [decodeRLEWarning] at hdec

theorem stepStatic_growBufToArray_rleWarn
    {pc : Nat} {bufVal : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {b : Algorithm.GrowBuf Algorithm.RLEWarning}
    (hrep : RleWarnRep b bufVal) :
    ∃ (arrVal : JvmVal) (jh' : Jvm.JvmHeap AlgExt) (warnVals? : Option Nat),
      stepInvokeStatic ⟨pc, bufVal :: rest, locs, jh, hp⟩
        "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
        "(Ljava/lang/Object;)[Ljava/lang/Object;" =
        .inl (some ⟨pc + 1, arrVal :: rest, locs, jh', hp⟩) ∧
      match warnVals? with
      | none => arrVal = .strArr #[] ∧ jh' = jh ∧ b.toArray = #[]
      | some addr =>
        arrVal = .heapRef addr ∧
        ∃ warnVals, jh'.get? addr = some (.objArray "java/lang/Object" warnVals) ∧
          warnVals.toList.mapM (decodeRLEWarning jh') = some b.toArray.toList := by
  cases hrep with
  | empty he hz =>
    have hb : b = Algorithm.GrowBuf.empty := growBuf_eq_empty_of he hz
    subst hb
    refine ⟨JvmVal.strArr #[], jh, none, rfl, rfl, rfl, rfl⟩
  | full =>
    have hdec := encodeGrowBufArray_decode_rleWarn jh b
    dsimp only at hdec
    rcases hdec with ⟨_, addr, warnVals, hv, hg, hm⟩
    exists (encodeGrowBufArray jh encodeRLEWarning b).1,
      (encodeGrowBufArray jh encodeRLEWarning b).2, some addr
    exact ⟨rfl, hv, warnVals, hg, hm⟩

private theorem stepStatic_scanDigitSet_heap
    {pc : Nat} {mask p limit : UInt32} {addr : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .i32 mask :: .i32 p :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_scanDigitSet-7IvYBaQ" "([BIII)Lkotlin/Pair;" =
      let r := Algorithm.scanDigitSet ⟨elems⟩ limit p mask
      .inl (some ⟨pc + 1, .pair (.boxedUInt r.1) (.boxedUInt r.2) :: rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 mask :: .i32 p :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_scanDigitSet-7IvYBaQ" "([BIII)Lkotlin/Pair;" =
      match decodeBytes ⟨pc, .i32 mask :: .i32 p :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩
          (.heapRef addr) with
      | some bytes =>
        let r := Algorithm.scanDigitSet bytes limit p mask
        .inl (some ⟨pc + 1, .pair (.boxedUInt r.1) (.boxedUInt r.2) :: rest, locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn]; simp only [decodeBytes, hget]

private theorem stepStatic_parseUInt32At_heap
    {pc : Nat} {limit pos : UInt32} {addr : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .i32 limit :: .i32 pos :: .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseUInt32At-BltQuoY" "([BII)Ljava/lang/Object;" =
      let optPair := (Algorithm.parseUInt32At ⟨elems⟩ pos limit).map fun r =>
        (.boxedUInt r.val, .boxedUInt r.next)
      let (res, h') := encodeOptScalarPair jh optPair
      .inl (some ⟨pc + 1, res :: rest, locs, h', hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 limit :: .i32 pos :: .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseUInt32At-BltQuoY" "([BII)Ljava/lang/Object;" =
      match decodeBytes ⟨pc, .i32 limit :: .i32 pos :: .heapRef addr :: rest, locs, jh, hp⟩
          (.heapRef addr) with
      | some bytes =>
        let optPair := (Algorithm.parseUInt32At bytes pos limit).map
          fun (r : Algorithm.ParsedUInt32) => (JvmVal.boxedUInt r.val, JvmVal.boxedUInt r.next)
        let (res, h') := encodeOptScalarPair jh optPair
        .inl (some ⟨pc + 1, res :: rest, locs, h', hp⟩)
      | none => .inr none := rfl
  rw [hfn]; simp only [decodeBytes, hget]

private theorem stepStatic_parseRLEOffset_heap
    {pc : Nat} {addr : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEOffset" "([B)Ljava/lang/Object;" =
      let optPair := (Algorithm.parseRLEOffset ⟨elems⟩).map fun r =>
        (.boxedInt r.x.toUInt32, .boxedInt r.y.toUInt32)
      let (res, h') := encodeOptScalarPair jh optPair
      .inl (some ⟨pc + 1, res :: rest, locs, h', hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEOffset" "([B)Ljava/lang/Object;" =
      match decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) with
      | some bytes =>
        let optPair := (Algorithm.parseRLEOffset bytes).map
          fun (r : Algorithm.ParsedCoords) => (.boxedInt r.x.toUInt32, .boxedInt r.y.toUInt32)
        let (res, h') := encodeOptScalarPair jh optPair
        .inl (some ⟨pc + 1, res :: rest, locs, h', hp⟩)
      | none => .inr none := rfl
  rw [hfn]; simp only [decodeBytes, hget]

private theorem stepStatic_parseRLEHeader_heap
    {pc : Nat} {addr : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEHeader" "([B)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.parseRLEHeader ⟨elems⟩) :: rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEHeader" "([B)I" =
      match decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) with
      | some bytes => .inl (some ⟨pc + 1, .i32 (Algorithm.parseRLEHeader bytes) :: rest, locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn]; simp only [decodeBytes, hget]

private theorem stepStatic_checkRLERule_heap
    {pc : Nat} {limit pos : UInt32} {addr : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .i32 limit :: .i32 pos :: .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_checkRLERule-BltQuoY" "([BII)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.checkRLERule ⟨elems⟩ pos limit) :: rest,
        locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 limit :: .i32 pos :: .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_checkRLERule-BltQuoY" "([BII)I" =
      match decodeBytes ⟨pc, .i32 limit :: .i32 pos :: .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) with
      | some bytes =>
        .inl (some ⟨pc + 1, .i32 (Algorithm.checkRLERule bytes pos limit) :: rest,
          locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn]; simp only [decodeBytes, hget]

private theorem stepStatic_noCells_rle
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩ "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_noCells" "()[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref hp.u64Arrays.length) :: rest, locs, jh,
        { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.noCells] }⟩) := rfl

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

private def u8Sext (b : UInt8) : UInt32 :=
  UInt32.ofBitVec (b.toBitVec.signExtend 32)

private theorem u8Sext_eq_u32 {b : UInt8} {c : UInt32} (h : b.toNat = c.toNat) (hc : c.toNat < 128) :
    u8Sext b = c := by
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
  simp only [u8Sext, UInt32.toBitVec_ofBitVec, hsw]
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  exact hbt.trans h

private theorem u8Sext_beq_false (b : UInt8) (c : UInt32) (hne : b.toNat ≠ c.toNat) (hc : c.toNat < 128) :
    (u8Sext b == c) = false := by
  cases he : u8Sext b == c
  · rfl
  · have hb_eq : u8Sext b = c := LawfulBEq.eq_of_beq he
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
      simp only [u8Sext, hsw, UInt32.toNat_ofBitVec, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt hblt] at h2
      exact absurd h2 hne
    · have hu31 : (u8Sext b).toBitVec.getLsbD 31 = true := by
        simp [u8Sext, BitVec.getLsbD_signExtend, hm]
      have hc31 : c.toBitVec.getLsbD 31 = false := by
        rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
        have hct : c.toBitVec.toNat < 2 ^ 31 := by simpa using Nat.lt_trans hc (by decide)
        exact Nat.testBit_lt_two_pow hct
      have hcontra := congrArg (fun x : UInt32 => x.toBitVec.getLsbD 31) hb_eq
      rw [hu31, hc31] at hcontra
      contradiction

private theorem byteArray_get_eq_getBang (bytes : ByteArray) {idx : Nat} (hlt : idx < bytes.data.size) :
    bytes.data[idx] = bytes.get! idx := by
  simp only [ByteArray.get!]
  exact (getElem!_pos bytes.data idx hlt).symm

private theorem u32_ofNat_lt_of_lt {n : Nat} (hlt : n < 2 ^ 31) :
    (UInt32.ofNat n).toNat = n ∧ (UInt32.ofNat n).toNat < 2 ^ 31 := by
  have h1 : (UInt32.ofNat n).toNat = n := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  exact ⟨h1, by omega⟩

private theorem compareUnsigned_sle_zero (a b : UInt32) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.sle 0#32 = decide (a ≤ b) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b <;> simp [h1, h2]
    · exact Nat.le_of_lt h2
    · have hne : a ≠ b := fun he => h1 (beq_iff_eq.mpr he)
      rw [UInt32.lt_iff_toNat_lt] at h2 ⊢
      have hne' : a.toNat ≠ b.toNat := fun he => hne (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq he))
      omega

private theorem skipSpaces_le (bytes : ByteArray) (pos limit : UInt32) (hle : pos ≤ limit) :
    Algorithm.skipSpaces bytes pos limit ≤ limit := by
  induction hfuel : (limit.toNat - pos.toNat) generalizing pos with
  | zero =>
    have hnot : ¬(pos < limit) := by
      intro hlt; have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    rw [Algorithm.skipSpaces]; simp [hnot, hle]
  | succ m ih =>
    by_cases hp : pos < limit
    · rw [Algorithm.skipSpaces]; simp only [hp, ↓reduceDIte]
      split
      · have hp1 : pos + 1 ≤ limit := by
          rw [UInt32.le_iff_toNat_le, UInt32.toNat_add, UInt32.toNat_one]
          have := UInt32.lt_iff_toNat_lt.mp hp
          have := UInt32.toNat_lt limit
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        have hdiff : limit.toNat - (pos + 1).toNat = m := by
          rw [UInt32.toNat_add, UInt32.toNat_one]
          have := UInt32.lt_iff_toNat_lt.mp hp
          have := UInt32.toNat_lt limit
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        exact ih (pos + 1) hp1 hdiff
      · exact hle
    · rw [Algorithm.skipSpaces]; simp [hp, hle]

private theorem runJvmResFast_tableswitch {f pc dflt : Nat} {low : Int32} {targets : List Nat}
    {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.tableswitch low targets dflt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      let tgt := Jvm.tableswitchTarget v low targets dflt
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  unfold runJvmResFast; rw [Jvm.runJvmResFast.eq_def]; rfl

/-! #### 1. `f_Algorithm_parseRLEOffset_prog` -/

section ParseRLEOffset
set_option maxRecDepth 2048

private theorem jvmHeap_alloc_fst (h : Jvm.JvmHeap AlgExt) (o : Jvm.HeapObj AlgExt) :
    (h.alloc o).1 = h.objects.size := rfl

private theorem runJvmResFast_iconst {f pc : Nat} {prog rest : List JvmInstr} {c : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.iconst c :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 c :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_astore {f pc idx : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.astore idx :: rest) ⟨pc, v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_aload {f pc idx : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.aload idx :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_intValueOf {f pc : Nat} {prog rest : List JvmInstr} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc
        (.invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" :: rest)
        ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .boxedInt v :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem parseRLEOffset_retNone_body
    {f pc st_loc : Nat} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 12 ≤ f)
    (hdrop : f_Algorithm_parseRLEOffset_prog.drop pc =
      .iconst 1 :: .anewarray "java/lang/Object" :: .astore st_loc :: .aload st_loc ::
      .iconst 0 :: .iconst 0 ::
      .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" ::
      .aastore :: .aload st_loc :: .astore (st_loc - 1) :: .aload (st_loc - 1) ::
      .areturn :: f_Algorithm_parseRLEOffset_prog.drop (pc + 12)) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEOffset_prog pc (f_Algorithm_parseRLEOffset_prog.drop pc)
          ⟨pc, stk, locs, jh, hp⟩ = some (v, st') ∧
      decodeOptParsedCoords st'.jvmHeap v = some none := by
  let a0 : Array JvmVal := Array.replicate 1 .null
  let jh0 := (jh.alloc (.objArray "java/lang/Object" a0)).2
  let a1 := a0.set 0 (.boxedInt 0) (by simp [a0])
  let jh1 := jh0.set jh.objects.size (.objArray "java/lang/Object" a1)
  have hjh0 : jh0.get? jh.objects.size = some (.objArray "java/lang/Object" a0) :=
    jvmHeap_get?_alloc_self _ _
  have hjh1 : jh1 = (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2 := by
    cases jh with
    | mk objs stat =>
      dsimp only [jh1, jh0, Jvm.JvmHeap.set, Jvm.JvmHeap.alloc]
      simp only [Array.size_push, Nat.lt_succ_self, ↓reduceDIte]
      congr 1
      apply Array.ext
      · simp
      · intro k hk1 hk2
        by_cases hk : k = objs.size
        · subst hk; simp only [Array.getElem_set_self, Array.getElem_push, Nat.lt_irrefl, ↓reduceDIte]; rfl
        · have hkj : k < (objs.push (Jvm.HeapObj.objArray "java/lang/Object" a0)).size := by
            simp only [Array.size_push] at hk2 ⊢; exact hk2
          rw [Array.getElem_set_ne (h' := by simp only [Array.size_push]; exact Nat.lt_succ_self _)
            (pj := hkj) (h := Ne.symm hk)]
          have hk_lt : k < objs.size := by simp only [Array.size_push] at hk2; omega
          rw [Array.getElem_push_lt hk_lt, Array.getElem_push_lt hk_lt]
  have hrun :
      runJvmResFast f f_Algorithm_parseRLEOffset_prog pc (f_Algorithm_parseRLEOffset_prog.drop pc)
        ⟨pc, stk, locs, jh, hp⟩ =
      some (.heapRef jh.objects.size,
        ⟨pc + 11, .heapRef jh.objects.size :: stk,
          setLocal (setLocal locs st_loc (.heapRef jh.objects.size)) (st_loc - 1) (.heapRef jh.objects.size),
          jh1, hp⟩) := by
    rw [hdrop]
    split_res_fuel 12
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_anewarray_obj (by decide), show (1 : UInt32).toNat = 1 from rfl]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload]; simp only [setLocal, ↓reduceIte]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_intValueOf]; norm_res_fuel
    rw [show pc + 1 + 1 + 1 + 1 + 1 + 1 + 1 = pc + 7 by omega]
    rw [runJvmResFast_aastore (idx := 0) hjh0 (by decide) (by decide)]; norm_res_fuel
    rw [runJvmResFast_aload]; simp only [setLocal, ↓reduceIte]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload]; simp only [setLocal, ↓reduceIte]; norm_res_fuel
    rw [show pc + 7 + 1 + 1 + 1 + 1 = pc + 11 by omega]
    rfl
  refine ⟨_, _, hrun, ?_⟩
  rw [hjh1]
  dsimp only [decodeOptParsedCoords]
  rw [jvmHeap_get?_alloc_self]
  simp

private theorem parseRLEOffset_retSome_body
    {f : Nat} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {x y : Int32} (hx : locs 5 = .i32 x.toUInt32) (hy : locs 10 = .i32 y.toUInt32)
    (hf : 46 ≤ f) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseRLEOffset_prog 294
        (.iconst 2 :: f_Algorithm_parseRLEOffset_prog.drop 295)
        ⟨294, [], locs, jh, hp⟩ = some (v, st') ∧
      decodeOptParsedCoords st'.jvmHeap v = some (some ⟨x, y⟩) := by
  let ao0 : Array JvmVal := Array.replicate 2 .null
  let jho0 := (jh.alloc (.objArray "java/lang/Object" ao0)).2
  let ao1 := ao0.set 0 (.boxedInt 1) (by decide)
  let jho1 := jho0.set jh.objects.size (.objArray "java/lang/Object" ao1)
  let ai0 : Array JvmVal := Array.replicate 6 .null
  let jhi0 := (jho1.alloc (.objArray "java/lang/Object" ai0)).2
  let ai1 := ai0.set 0 (.boxedInt 0) (by decide)
  let jhi1 := jhi0.set jho1.objects.size (.objArray "java/lang/Object" ai1)
  let ai2 := ai1.set 1 (.boxedInt x.toUInt32) (by decide)
  let jhi2 := jhi1.set jho1.objects.size (.objArray "java/lang/Object" ai2)
  let ai3 := ai2.set 2 .null (by simp [ai2, ai1, ai0])
  let jhi3 := jhi2.set jho1.objects.size (.objArray "java/lang/Object" ai3)
  let ai4 := ai3.set 3 .null (by simp [ai3, ai2, ai1, ai0])
  let jhi4 := jhi3.set jho1.objects.size (.objArray "java/lang/Object" ai4)
  let ai5 := ai4.set 4 .null (by simp [ai4, ai3, ai2, ai1, ai0])
  let jhi5 := jhi4.set jho1.objects.size (.objArray "java/lang/Object" ai5)
  let ai6 := ai5.set 5 (.boxedInt y.toUInt32) (by simp [ai5, ai4, ai3, ai2, ai1, ai0])
  let jhi6 := jhi5.set jho1.objects.size (.objArray "java/lang/Object" ai6)
  let ao2 := ao1.set 1 (.heapRef jho1.objects.size) (by decide)
  have ho_sz : jho1.objects.size = jh.objects.size + 1 := by
    simp [jho1, jho0, Jvm.JvmHeap.set, Jvm.JvmHeap.alloc]
  have hgo0 : jho0.get? jh.objects.size = some (.objArray "java/lang/Object" ao0) :=
    jvmHeap_get?_alloc_self _ _
  have hgi0 : jhi0.get? jho1.objects.size = some (.objArray "java/lang/Object" ai0) :=
    jvmHeap_get?_alloc_self _ _
  have hgi1 : jhi1.get? jho1.objects.size = some (.objArray "java/lang/Object" ai1) :=
    jvmHeap_get?_set_self hgi0
  have hgi2 : jhi2.get? jho1.objects.size = some (.objArray "java/lang/Object" ai2) :=
    jvmHeap_get?_set_self hgi1
  have hgi3 : jhi3.get? jho1.objects.size = some (.objArray "java/lang/Object" ai3) :=
    jvmHeap_get?_set_self hgi2
  have hgi4 : jhi4.get? jho1.objects.size = some (.objArray "java/lang/Object" ai4) :=
    jvmHeap_get?_set_self hgi3
  have hgi5 : jhi5.get? jho1.objects.size = some (.objArray "java/lang/Object" ai5) :=
    jvmHeap_get?_set_self hgi4
  have hgo1 : jhi6.get? jh.objects.size = some (.objArray "java/lang/Object" ao1) := by
    have hne : jh.objects.size ≠ jho1.objects.size := by omega
    simp only [jhi6, jhi5, jhi4, jhi3, jhi2, jhi1]
    iterate 6 rw [jvmHeap_get?_set_ne _ _ hne]
    rw [jvmHeap_get?_alloc_lt _ _ (by simp [jho1, jho0, Jvm.JvmHeap.set, Jvm.JvmHeap.alloc])]
    exact jvmHeap_get?_set_self hgo0
  apply Exists.intro (.heapRef jh.objects.size)
  apply Exists.intro _
  constructor
  · split_res_fuel 46
    rw [runJvmResFast_iconst]; norm_res_fuel
    step_drop 1
    rw [runJvmResFast_anewarray_obj (by decide), show (2 : UInt32).toNat = 2 from rfl]; norm_res_fuel
    step_drop 6
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_aastore (idx := 0) hgo0 (by decide) (by decide)]
    simp only [show (0 : UInt32).toNat = 0 from rfl]; norm_res_fuel
    step_drop 4
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_anewarray_obj (by decide), show (6 : UInt32).toNat = 6 from rfl]; norm_res_fuel
    step_drop 6
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_aastore (idx := 0) hgi0 (by decide) (by decide)]
    simp only [show (0 : UInt32).toNat = 0 from rfl]; norm_res_fuel
    step_drop 5
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [hx, runJvmResFast_intValueOf]; norm_res_fuel
    rw [runJvmResFast_aastore (idx := 1) hgi1 (by decide) (by decide)]
    simp only [show (1 : UInt32).toNat = 1 from rfl]; norm_res_fuel
    step_drop 4
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_aastore (idx := 2) hgi2 (by decide) (by simp [ai2, ai1, ai0])]
    simp only [show (2 : UInt32).toNat = 2 from rfl]; norm_res_fuel
    step_drop 4
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_aastore (idx := 3) hgi3 (by decide) (by simp [ai3, ai2, ai1, ai0])]
    simp only [show (3 : UInt32).toNat = 3 from rfl]; norm_res_fuel
    step_drop 4
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_aastore (idx := 4) hgi4 (by decide) (by simp [ai4, ai3, ai2, ai1, ai0])]
    simp only [show (4 : UInt32).toNat = 4 from rfl]; norm_res_fuel
    step_drop 5
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [hy, runJvmResFast_intValueOf]; norm_res_fuel
    rw [runJvmResFast_aastore (idx := 5) hgi5 (by decide) (by simp [ai5, ai4, ai3, ai2, ai1, ai0])]
    simp only [show (5 : UInt32).toNat = 5 from rfl]; norm_res_fuel
    step_drop 2
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_aastore (idx := 1) hgo1 (by decide) (by decide)]
    simp only [show (1 : UInt32).toNat = 1 from rfl]; norm_res_fuel
    step_drop 4
    rw [runJvmResFast_aload]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload]
    simp only [setLocal, ↓reduceIte]
    norm_res_fuel
    rfl
  · dsimp only [decodeOptParsedCoords]
    rw [jvmHeap_get?_set_self hgo1]
    simp only [Array.size_set, Array.size_replicate, Nat.reduceGT, ↓reduceDIte, Array.getElem_set_self]
    rw [Array.getElem_set_ne (pj := by simp) (h := (by decide : (1 : Nat) ≠ 0)),
      Array.getElem_set_self]
    rw [jvmHeap_get?_set_ne _ _ (by rw [ho_sz]; omega), jvmHeap_get?_set_self hgi5]
    simp [show x.toUInt32.toInt32 = x from rfl, show y.toUInt32.toInt32 = y from rfl]

theorem parseRLEOffset_equiv (bytes : ByteArray) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bytesAddr : Nat) (hget : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hlen31 : bytes.data.size < 2 ^ 31) :
    ∃ v st', runJvmRes 250 f_Algorithm_parseRLEOffset_prog
        ⟨0, [], setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr), jh, hp⟩ = some (v, st') ∧
      decodeOptParsedCoords st'.jvmHeap v = some (Algorithm.parseRLEOffset bytes) := by
  have hlim := u32_ofNat_lt_of_lt hlen31
  let limit := UInt32.ofNat bytes.data.size
  suffices h : ∃ v st',
      runJvmResFast 250 f_Algorithm_parseRLEOffset_prog 0 f_Algorithm_parseRLEOffset_prog
        ⟨0, [], setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr), jh, hp⟩ = some (v, st') ∧
      decodeOptParsedCoords st'.jvmHeap v = some (Algorithm.parseRLEOffset bytes) by
    rcases h with ⟨v, st', hrun, hdec⟩
    exact ⟨v, st', by rw [runJvmRes_of_runJvmResFast0 250 _ _ _ rfl]; exact hrun, hdec⟩
  unfold Algorithm.parseRLEOffset
  have h0_10 : runJvmResFast 250 f_Algorithm_parseRLEOffset_prog 0 f_Algorithm_parseRLEOffset_prog
      ⟨0, [], setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr), jh, hp⟩ =
      runJvmResFast 240 f_Algorithm_parseRLEOffset_prog 10
        (.iflt 52 :: f_Algorithm_parseRLEOffset_prog.drop 11)
        ⟨10, [.i32 (if limit == 3 then 0 else if limit < 3 then 4294967295 else 1)],
          setLocal (setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr)) 1 (.i32 limit), jh, hp⟩ := by
    rw [show f_Algorithm_parseRLEOffset_prog = f_Algorithm_parseRLEOffset_prog.drop 0 from rfl]
    split_res_fuel 10
    step_drop 5
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_arraylength_byteArray hget]; norm_res_fuel
    step_drop 6
    heap_step_nonbranch_chunks
    rfl
  by_cases hlt3 : limit < 3
  · have hr : Algorithm.parseRLEOffset bytes = none := by
      unfold Algorithm.parseRLEOffset
      dsimp only
      have hlt_b : (decide (bytes.size.toUInt32 < 3)) = true :=
        decide_eq_true (by simpa [limit] using hlt3)
      rw [hlt_b]
      simp
    rcases parseRLEOffset_retNone_body (f := 239) (pc := 52) (st_loc := 3)
        (stk := []) (locs := setLocal (setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr)) 1 (.i32 limit))
        (jh := jh) (hp := hp) (by omega) rfl with ⟨v, st', hrun, hdec⟩
    refine ⟨v, st', ?_, by rw [← hr] at hdec; exact hdec⟩
    rw [h0_10]
    split_res_fuel 1
    rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt3)]
    exact hrun
  · have hge3 : 3 ≤ bytes.data.size := by
      have h3 : (3 : UInt32) ≤ limit := UInt32.not_lt.mp hlt3
      rw [UInt32.le_iff_toNat_le, hlim.1] at h3
      exact h3
    have h0_lt : 0 < bytes.data.size := by omega
    have h1_lt : 1 < bytes.data.size := by omega
    have h2_lt : 2 < bytes.data.size := by omega
    have h10_16 : runJvmResFast 240 f_Algorithm_parseRLEOffset_prog 10
        (.iflt 52 :: f_Algorithm_parseRLEOffset_prog.drop 11)
        ⟨10, [.i32 (if limit == 3 then 0 else if limit < 3 then 4294967295 else 1)],
          setLocal (setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr)) 1 (.i32 limit), jh, hp⟩ =
        runJvmResFast 234 f_Algorithm_parseRLEOffset_prog 16
          (.if_icmpeq 29 :: f_Algorithm_parseRLEOffset_prog.drop 17)
          ⟨16, [.i32 35, .i32 (u8Sext (bytes.get! 0))],
            setLocal (setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr)) 1 (.i32 limit), jh, hp⟩ := by
      split_res_fuel 6
      rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hlt3)]
      norm_res_fuel
      step_drop 3
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_baload_byteArray (idx := 0) hget (by decide) h0_lt]; norm_res_fuel
      step_drop 3
      heap_step_nonbranch_chunks
      simp only [UInt32.toNat_zero, byteArray_get_eq_getBang bytes h0_lt]
      rfl
    by_cases hb0 : bytes.get! 0 = 35
    · have hb0_u : u8Sext (bytes.get! 0) = 35 :=
        u8Sext_eq_u32 (by simp [hb0]) (by decide)
      have h16_36 : runJvmResFast 234 f_Algorithm_parseRLEOffset_prog 16
          (.if_icmpeq 29 :: f_Algorithm_parseRLEOffset_prog.drop 17)
          ⟨16, [.i32 35, .i32 (u8Sext (bytes.get! 0))],
            setLocal (setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr)) 1 (.i32 limit), jh, hp⟩ =
          runJvmResFast 226 f_Algorithm_parseRLEOffset_prog 36
            (.if_icmpeq 64 :: f_Algorithm_parseRLEOffset_prog.drop 37)
            ⟨36, [.i32 82, .i32 (u8Sext (bytes.get! 1))],
              setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr)) 1 (.i32 limit))
                2 (.i32 (u8Sext (bytes.get! 1))), jh, hp⟩ := by
        split_res_fuel 8
        rw [runJvmResFast_if_icmpeq_branch hb0_u]; norm_res_fuel
        step_drop 3
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_baload_byteArray (idx := 1) hget (by decide) h1_lt]; norm_res_fuel
        step_drop 5
        heap_step_nonbranch_chunks
        simp only [UInt32.toNat_one, byteArray_get_eq_getBang bytes h1_lt]
        rfl
      by_cases hb1 : bytes.get! 1 = 82 ∨ bytes.get! 1 = 80
      · have h36_69 : ∃ f69, 217 ≤ f69 ∧ runJvmResFast 226 f_Algorithm_parseRLEOffset_prog 36
            (.if_icmpeq 64 :: f_Algorithm_parseRLEOffset_prog.drop 37)
            ⟨36, [.i32 82, .i32 (u8Sext (bytes.get! 1))],
              setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr)) 1 (.i32 limit))
                2 (.i32 (u8Sext (bytes.get! 1))), jh, hp⟩ =
            runJvmResFast f69 f_Algorithm_parseRLEOffset_prog 69
              (.if_icmpeq 82 :: f_Algorithm_parseRLEOffset_prog.drop 70)
              ⟨69, [.i32 32, .i32 (u8Sext (bytes.get! 2))],
                setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr)) 1 (.i32 limit))
                  2 (.i32 (u8Sext (bytes.get! 1))), jh, hp⟩ := by
          rcases hb1 with hb1 | hb1
          · refine ⟨220, by omega, ?_⟩
            split_res_fuel 6
            rw [runJvmResFast_if_icmpeq_branch (u8Sext_eq_u32 (by simp [hb1]) (by decide))]; norm_res_fuel
            step_drop 3
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_baload_byteArray (idx := 2) hget (by decide) h2_lt]; norm_res_fuel
            step_drop 3
            heap_step_nonbranch_chunks
            simp only [show (2 : UInt32).toNat = 2 from rfl,
              byteArray_get_eq_getBang bytes h2_lt]
            rfl
          · have hne82 : (u8Sext (bytes.get! 1) == 82) = false :=
              u8Sext_beq_false _ _ (by simp [hb1]) (by decide)
            refine ⟨217, by omega, ?_⟩
            split_res_fuel 9
            rw [runJvmResFast_if_icmpeq_fallthrough hne82]; norm_res_fuel
            step_drop 3
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_if_icmpeq_branch (u8Sext_eq_u32 (by simp [hb1]) (by decide))]; norm_res_fuel
            step_drop 3
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_baload_byteArray (idx := 2) hget (by decide) h2_lt]; norm_res_fuel
            step_drop 3
            heap_step_nonbranch_chunks
            simp only [show (2 : UInt32).toNat = 2 from rfl,
              byteArray_get_eq_getBang bytes h2_lt]
            rfl
        rcases h36_69 with ⟨f69, hf69, h36_69⟩
        by_cases hb2 : bytes.get! 2 = 32
        · have hb2_u : u8Sext (bytes.get! 2) = 32 := u8Sext_eq_u32 (by simp [hb2]) (by decide)
          let locs2 : Nat → JvmVal :=
            setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr)) 1 (.i32 limit)) 2
              (.i32 (u8Sext (bytes.get! 1)))
          let p1 := Algorithm.parseInt32At bytes 3 limit
          let opt1 : Option (JvmVal × JvmVal) := match p1 with
            | none => none
            | some r => some (JvmVal.boxedInt r.val.toUInt32, JvmVal.boxedUInt r.next)
          let enc1 := encodeOptScalarPair jh opt1
          have h69_99 : runJvmResFast f69 f_Algorithm_parseRLEOffset_prog 69
              (.if_icmpeq 82 :: f_Algorithm_parseRLEOffset_prog.drop 70)
              ⟨69, [.i32 32, .i32 (u8Sext (bytes.get! 2))], locs2, jh, hp⟩ =
              runJvmResFast (f69 - 18) f_Algorithm_parseRLEOffset_prog 99
                (.tableswitch 0 [100, 112] 346 :: f_Algorithm_parseRLEOffset_prog.drop 100)
                ⟨99, [.i32 (match p1 with | none => 0 | some _ => 1)],
                  setLocal locs2 2 enc1.1, enc1.2, hp⟩ := by
            split_res_fuel 18
            rw [runJvmResFast_if_icmpeq_branch hb2_u]; norm_res_fuel
            step_drop 4
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_invokestatic_step
              (stepStatic_parseInt32At_heap (Or.inr (Or.inr rfl)) hget)]
            norm_res_fuel
            rw [show Algorithm.parseInt32At ⟨bytes.data⟩ 3 (UInt32.ofNat bytes.data.size) = p1 from rfl]
            cases hpi1 : p1 <;> (
              simp only [opt1, enc1, encodeOptScalarPair, hpi1, Option.map]
              step_drop 6; heap_step_nonbranch_chunks; norm_res_fuel
              simp only [jvmHeap_alloc_fst]
              rw [runJvmResFast_checkcast_objArray (jvmHeap_get?_alloc_self _ _) (Or.inl rfl)]
              norm_res_fuel; step_drop 2; heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_aaload (idx := 0) (jvmHeap_get?_alloc_self _ _) (by decide) (by simp)]
              norm_res_fuel; step_drop 4; heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
              norm_res_fuel; step_drop 2; heap_step_nonbranch_chunks; rfl)
          have hlt3_b : decide (limit < 3) = false := decide_eq_false hlt3
          have hb1_neq : (bytes.get! 1 != 82 && bytes.get! 1 != 80) = false := by
            rcases hb1 with h | h <;> simp [h]
          cases hp1 : p1 with
          | none =>
            have hp1' : Algorithm.parseInt32At bytes 3 limit = none := hp1
            have hrle : Algorithm.parseRLEOffset bytes = none := by
              unfold Algorithm.parseRLEOffset
              rw [show bytes.size.toUInt32 = limit from rfl]
              simp only [hlt3_b, hb0, bne_self_eq_false, hb1_neq, hb2, Bool.or_self,
                Bool.false_eq_true, ↓reduceIte, hp1']
            rcases parseRLEOffset_retNone_body (f := f69 - 18 - 1) (pc := 100) (st_loc := 5)
                (stk := []) (locs := setLocal locs2 2 enc1.1) (jh := enc1.2) (hp := hp)
                (by omega) rfl with ⟨v, st', hrun, hdec⟩
            refine ⟨v, st', ?_, ?_⟩
            · rw [h0_10, h10_16, h16_36, h36_69, h69_99, hp1]
              split_res_fuel 1
              rw [runJvmResFast_tableswitch,
                show Jvm.tableswitchTarget 0 0 [100, 112] 346 = 100 from by decide]
              exact hrun
            · change decodeOptParsedCoords st'.jvmHeap v = some (Algorithm.parseRLEOffset bytes)
              rw [hrle]; exact hdec
          | some r1 =>
            have hp1' : Algorithm.parseInt32At bytes 3 limit = some r1 := hp1
            have hget_outer1 : enc1.2.get? (jh.objects.size + 1) =
                some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef jh.objects.size]) := by
              have hsz : (jh.alloc (.objArray "java/lang/Object"
                  #[.boxedInt 0, .boxedInt r1.val.toUInt32, .null, .null, .null,
                    .boxedUInt r1.next])).2.objects.size = jh.objects.size + 1 := by
                simp [Jvm.JvmHeap.alloc]
              dsimp only [enc1, opt1, encodeOptScalarPair]
              rw [hp1, ← hsz]
              exact jvmHeap_get?_alloc_self _ _
            have hget_inner1 : enc1.2.get? jh.objects.size =
                some (.objArray "java/lang/Object"
                  #[.boxedInt 0, .boxedInt r1.val.toUInt32, .null, .null, .null, .boxedUInt r1.next]) := by
              have hlt : jh.objects.size < (jh.alloc (.objArray "java/lang/Object"
                  #[.boxedInt 0, .boxedInt r1.val.toUInt32, .null, .null, .null,
                    .boxedUInt r1.next])).2.objects.size := by
                simp [Jvm.JvmHeap.alloc]
              dsimp only [enc1, opt1, encodeOptScalarPair]
              rw [hp1]
              rw [jvmHeap_get?_alloc_lt _ _ hlt, jvmHeap_get?_alloc_self]
            have hget_bytes1 : enc1.2.get? bytesAddr = some (.byteArray bytes.data) := by
              have hex1 := heapExtends_alloc jh
                (.objArray "java/lang/Object"
                  #[.boxedInt 0, .boxedInt r1.val.toUInt32, .null, .null, .null, .boxedUInt r1.next])
              have hex2 := heapExtends_alloc
                (jh.alloc (.objArray "java/lang/Object"
                  #[.boxedInt 0, .boxedInt r1.val.toUInt32, .null, .null, .null, .boxedUInt r1.next])).2
                (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef jh.objects.size])
              dsimp only [enc1, opt1, encodeOptScalarPair]
              rw [hp1]
              exact heapExtends_trans hex1 hex2 bytesAddr _ hget
            let locs3 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
              (setLocal locs2 2 enc1.1) 4 (.heapRef jh.objects.size))
              6 (.boxedInt r1.val.toUInt32)) 7 (.i32 0))
              5 (.i32 r1.val.toUInt32)) 7 (.boxedUInt r1.next))
              8 (.i32 0)) 6 (.i32 r1.next)
            have henc1_fst : enc1.1 = .heapRef (jh.objects.size + 1) := by
              simp [enc1, opt1, encodeOptScalarPair, hp1, Jvm.JvmHeap.alloc]
            have h99_166 : runJvmResFast (f69 - 18) f_Algorithm_parseRLEOffset_prog 99
                (.tableswitch 0 [100, 112] 346 :: f_Algorithm_parseRLEOffset_prog.drop 100)
                ⟨99, [.i32 1], setLocal locs2 2 enc1.1, enc1.2, hp⟩ =
                runJvmResFast (f69 - 18 - 46) f_Algorithm_parseRLEOffset_prog 166
                  (.iflt 179 :: f_Algorithm_parseRLEOffset_prog.drop 167)
                  ⟨166, [.i32 (if r1.next == limit then 0 else if r1.next < limit then 4294967295 else 1)],
                    locs3, enc1.2, hp⟩ := by
              split_res_fuel 47
              rw [runJvmResFast_tableswitch,
                show Jvm.tableswitchTarget 1 0 [100, 112] 346 = 112 from by decide]
              norm_res_fuel
              step_drop 2
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [show encodeOptScalarPair jh
                    (match Algorithm.parseInt32At bytes 3 (UInt32.ofNat bytes.data.size) with
                    | none => none
                    | some r => some (JvmVal.boxedInt r.val.toUInt32, JvmVal.boxedUInt r.next)) = enc1 from rfl]
              simp only [henc1_fst]
              rw [runJvmResFast_checkcast_objArray hget_outer1 (Or.inl rfl)]; norm_res_fuel
              step_drop 2
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_aaload (idx := 1) hget_outer1 (by decide) (by simp)]; norm_res_fuel
              step_drop 6
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_checkcast_objArray hget_inner1 (Or.inl rfl)]; norm_res_fuel
              step_drop 2
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_aaload (idx := 1) hget_inner1 (by decide) (by simp)]; norm_res_fuel
              step_drop 5
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_instanceof_step (res := 0) (by rfl)]; norm_res_fuel
              step_drop 1
              rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
              step_drop 5
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
              step_drop 4
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_checkcast_objArray hget_inner1 (Or.inl rfl)]; norm_res_fuel
              step_drop 2
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_aaload (idx := 5) hget_inner1 (by decide) (by simp)]; norm_res_fuel
              step_drop 5
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_instanceof_step (res := 0) (by rfl)]; norm_res_fuel
              step_drop 1
              rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
              step_drop 5
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]; norm_res_fuel
              step_drop 6
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [← henc1_fst, show f69 - 18 - 47 + 1 = f69 - 18 - 46 by omega]
              simp only [show (1 : UInt32).toNat = 1 from rfl, show (5 : UInt32).toNat = 5 from rfl]
              rfl
            by_cases hr1n : r1.next < limit
            · have hr1n_lt : r1.next.toNat < bytes.data.size := by
                rw [← hlim.1]; exact UInt32.lt_iff_toNat_lt.mp hr1n
              have hr1n_slt : r1.next.toBitVec.slt 0#32 = false :=
                u32_slt_zero_of_lt_2_31 (by omega)
              have h166_184 : runJvmResFast (f69 - 18 - 46) f_Algorithm_parseRLEOffset_prog 166
                    (.iflt 179 :: f_Algorithm_parseRLEOffset_prog.drop 167)
                    ⟨166, [.i32 (if r1.next == limit then 0 else if r1.next < limit then 4294967295 else 1)],
                      locs3, enc1.2, hp⟩ =
                    runJvmResFast (f69 - 18 - 46 - 6) f_Algorithm_parseRLEOffset_prog 184
                      (.if_icmpeq 197 :: f_Algorithm_parseRLEOffset_prog.drop 185)
                      ⟨184, [.i32 32, .i32 (u8Sext (bytes.get! r1.next.toNat))],
                        locs3, enc1.2, hp⟩ := by
                split_res_fuel 7
                rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hr1n)]
                norm_res_fuel
                step_drop 3
                heap_step_nonbranch_chunks; norm_res_fuel
                rw [runJvmResFast_baload_byteArray hget_bytes1 hr1n_slt hr1n_lt]; norm_res_fuel
                step_drop 3
                heap_step_nonbranch_chunks; norm_res_fuel
                simp only [byteArray_get_eq_getBang bytes hr1n_lt]
                rw [show (f69 - 18 - 46 - 7) + 1 = f69 - 18 - 46 - 6 by omega]
                rfl
              by_cases hb_sp : bytes.get! r1.next.toNat = 32
              · have hb_sp_u : u8Sext (bytes.get! r1.next.toNat) = 32 :=
                  u8Sext_eq_u32 (by simp [hb_sp]) (by decide)
                let p2 := Algorithm.parseInt32At bytes (r1.next + 1) limit
                let opt2 : Option (JvmVal × JvmVal) := match p2 with
                  | none => none
                  | some r => some (JvmVal.boxedInt r.val.toUInt32, JvmVal.boxedUInt r.next)
                let enc2 := encodeOptScalarPair enc1.2 opt2
                have h184_217 : runJvmResFast (f69 - 18 - 46 - 6) f_Algorithm_parseRLEOffset_prog 184
                      (.if_icmpeq 197 :: f_Algorithm_parseRLEOffset_prog.drop 185)
                      ⟨184, [.i32 32, .i32 (u8Sext (bytes.get! r1.next.toNat))], locs3, enc1.2, hp⟩ =
                      runJvmResFast (f69 - 18 - 46 - 6 - 21) f_Algorithm_parseRLEOffset_prog 217
                        (.tableswitch 0 [218, 230] 340 :: f_Algorithm_parseRLEOffset_prog.drop 218)
                        ⟨217, [.i32 (match p2 with | none => 0 | some _ => 1)],
                          setLocal locs3 7 enc2.1, enc2.2, hp⟩ := by
                  split_res_fuel 21
                  rw [runJvmResFast_if_icmpeq_branch hb_sp_u]; norm_res_fuel
                  step_drop 7
                  heap_step_nonbranch_chunks; norm_res_fuel
                  rw [runJvmResFast_invokestatic_step
                    (stepStatic_parseInt32At_heap (Or.inr (Or.inr rfl)) hget_bytes1)]
                  norm_res_fuel
                  rw [show Algorithm.parseInt32At ⟨bytes.data⟩ (r1.next + 1)
                      (UInt32.ofNat bytes.data.size) = p2 from rfl]
                  cases hpi2 : p2 <;> (
                    simp only [opt2, enc2, encodeOptScalarPair, hpi2, Option.map]
                    step_drop 6; heap_step_nonbranch_chunks; norm_res_fuel
                    simp only [jvmHeap_alloc_fst]
                    rw [runJvmResFast_checkcast_objArray (jvmHeap_get?_alloc_self _ _) (Or.inl rfl)]
                    norm_res_fuel; step_drop 2; heap_step_nonbranch_chunks; norm_res_fuel
                    rw [runJvmResFast_aaload (idx := 0) (jvmHeap_get?_alloc_self _ _) (by decide) (by simp)]
                    norm_res_fuel; step_drop 4; heap_step_nonbranch_chunks; norm_res_fuel
                    rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
                    norm_res_fuel; step_drop 2; heap_step_nonbranch_chunks; rfl)
                cases hp2 : p2 with
                | none =>
                  have hp2' : Algorithm.parseInt32At bytes (r1.next + 1) limit = none := hp2
                  have hrle : Algorithm.parseRLEOffset bytes = none := by
                    unfold Algorithm.parseRLEOffset
                    rw [show bytes.size.toUInt32 = limit from rfl]
                    simp only [hlt3_b, hb0, bne_self_eq_false, hb1_neq, hb2, Bool.or_self,
                      Bool.false_eq_true, ↓reduceIte, hp1', decide_eq_true hr1n, hb_sp, beq_self_eq_true,
                      Bool.true_and, hp2']
                  rcases parseRLEOffset_retNone_body (f := f69 - 18 - 46 - 6 - 21 - 1) (pc := 218) (st_loc := 10)
                      (stk := []) (locs := setLocal locs3 7 enc2.1) (jh := enc2.2) (hp := hp)
                      (by omega) rfl with ⟨v, st', hrun, hdec⟩
                  refine ⟨v, st', ?_, ?_⟩
                  · rw [h0_10, h10_16, h16_36, h36_69, h69_99]; rw [hp1]; rw [h99_166, h166_184, h184_217, hp2]
                    split_res_fuel 1
                    rw [runJvmResFast_tableswitch,
                      show Jvm.tableswitchTarget 0 0 [218, 230] 340 = 218 from by decide]
                    exact hrun
                  · change decodeOptParsedCoords st'.jvmHeap v = some (Algorithm.parseRLEOffset bytes)
                    rw [hrle]; exact hdec
                | some r2 =>
                  have hp2' : Algorithm.parseInt32At bytes (r1.next + 1) limit = some r2 := hp2
                  have hget_outer2 : enc2.2.get? (enc1.2.objects.size + 1) =
                      some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef enc1.2.objects.size]) := by
                    have hsz : (enc1.2.alloc (.objArray "java/lang/Object"
                        #[.boxedInt 0, .boxedInt r2.val.toUInt32, .null, .null, .null,
                          .boxedUInt r2.next])).2.objects.size = enc1.2.objects.size + 1 := by
                      simp [Jvm.JvmHeap.alloc]
                    dsimp only [enc2, opt2, encodeOptScalarPair]
                    rw [hp2, ← hsz]
                    exact jvmHeap_get?_alloc_self _ _
                  have hget_inner2 : enc2.2.get? enc1.2.objects.size =
                      some (.objArray "java/lang/Object"
                        #[.boxedInt 0, .boxedInt r2.val.toUInt32, .null, .null, .null, .boxedUInt r2.next]) := by
                    have hlt : enc1.2.objects.size < (enc1.2.alloc (.objArray "java/lang/Object"
                        #[.boxedInt 0, .boxedInt r2.val.toUInt32, .null, .null, .null,
                          .boxedUInt r2.next])).2.objects.size := by
                      simp [Jvm.JvmHeap.alloc]
                    dsimp only [enc2, opt2, encodeOptScalarPair]
                    rw [hp2]
                    rw [jvmHeap_get?_alloc_lt _ _ hlt, jvmHeap_get?_alloc_self]
                  let locs4 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
                    (setLocal locs3 7 enc2.1) 9 (.heapRef enc1.2.objects.size))
                    11 (.boxedInt r2.val.toUInt32)) 12 (.i32 0))
                    10 (.i32 r2.val.toUInt32)) 11 (.boxedUInt r2.next))
                    12 (.i32 0)
                  have henc2_fst : enc2.1 = .heapRef (enc1.2.objects.size + 1) := by
                    simp [enc2, opt2, encodeOptScalarPair, hp2, Jvm.JvmHeap.alloc]
                  have h217_281 : runJvmResFast (f69 - 18 - 46 - 6 - 21) f_Algorithm_parseRLEOffset_prog 217
                      (.tableswitch 0 [218, 230] 340 :: f_Algorithm_parseRLEOffset_prog.drop 218)
                      ⟨217, [.i32 1], setLocal locs3 7 enc2.1, enc2.2, hp⟩ =
                      runJvmResFast (f69 - 18 - 46 - 6 - 21 - 43) f_Algorithm_parseRLEOffset_prog 281
                        (.if_icmpeq 294 :: f_Algorithm_parseRLEOffset_prog.drop 282)
                        ⟨281, [.i32 limit, .i32 r2.next], locs4, enc2.2, hp⟩ := by
                    split_res_fuel 44
                    rw [runJvmResFast_tableswitch,
                      show Jvm.tableswitchTarget 1 0 [218, 230] 340 = 230 from by decide]
                    norm_res_fuel
                    step_drop 2
                    heap_step_nonbranch_chunks; norm_res_fuel
                    rw [show encodeOptScalarPair enc1.2
                          (match Algorithm.parseInt32At bytes (r1.next + 1)
                              (UInt32.ofNat bytes.data.size) with
                          | none => none
                          | some r => some (JvmVal.boxedInt r.val.toUInt32, JvmVal.boxedUInt r.next)) =
                        enc2 from rfl]
                    simp only [henc2_fst]
                    rw [runJvmResFast_checkcast_objArray hget_outer2 (Or.inl rfl)]; norm_res_fuel
                    step_drop 2
                    heap_step_nonbranch_chunks; norm_res_fuel
                    rw [runJvmResFast_aaload (idx := 1) hget_outer2 (by decide) (by simp)]; norm_res_fuel
                    step_drop 6
                    heap_step_nonbranch_chunks; norm_res_fuel
                    rw [runJvmResFast_checkcast_objArray hget_inner2 (Or.inl rfl)]; norm_res_fuel
                    step_drop 2
                    heap_step_nonbranch_chunks; norm_res_fuel
                    rw [runJvmResFast_aaload (idx := 1) hget_inner2 (by decide) (by simp)]; norm_res_fuel
                    step_drop 5
                    heap_step_nonbranch_chunks; norm_res_fuel
                    rw [runJvmResFast_instanceof_step (res := 0) (by rfl)]; norm_res_fuel
                    step_drop 1
                    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
                    step_drop 5
                    heap_step_nonbranch_chunks; norm_res_fuel
                    rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
                    step_drop 4
                    heap_step_nonbranch_chunks; norm_res_fuel
                    rw [runJvmResFast_checkcast_objArray hget_inner2 (Or.inl rfl)]; norm_res_fuel
                    step_drop 2
                    heap_step_nonbranch_chunks; norm_res_fuel
                    rw [runJvmResFast_aaload (idx := 5) hget_inner2 (by decide) (by simp)]; norm_res_fuel
                    step_drop 5
                    heap_step_nonbranch_chunks; norm_res_fuel
                    rw [runJvmResFast_instanceof_step (res := 0) (by rfl)]; norm_res_fuel
                    step_drop 1
                    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
                    step_drop 5
                    heap_step_nonbranch_chunks; norm_res_fuel
                    rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]; norm_res_fuel
                    step_drop 3
                    heap_step_nonbranch_chunks; norm_res_fuel
                    rw [← henc2_fst, show f69 - 18 - 46 - 6 - 21 - 44 + 1 = f69 - 18 - 46 - 6 - 21 - 43 by omega]
                    simp only [show (1 : UInt32).toNat = 1 from rfl, show (5 : UInt32).toNat = 5 from rfl]
                    rfl
                  by_cases hr2n : r2.next = limit
                  · have hfin_res : Algorithm.parseRLEOffset bytes = some ⟨r1.val, r2.val⟩ := by
                      unfold Algorithm.parseRLEOffset
                      rw [show bytes.size.toUInt32 = limit from rfl]
                      simp only [hlt3_b, hb0, bne_self_eq_false, hb1_neq, hb2, Bool.or_self,
                        Bool.false_eq_true, ↓reduceIte, hp1', decide_eq_true hr1n, hb_sp, beq_self_eq_true,
                        Bool.true_and, hp2', hr2n]
                    have hloc5 : locs4 5 = .i32 r1.val.toUInt32 := by simp [locs4, locs3, setLocal]
                    have hloc10 : locs4 10 = .i32 r2.val.toUInt32 := by simp [locs4, locs3, setLocal]
                    rcases parseRLEOffset_retSome_body (f := f69 - 18 - 46 - 6 - 21 - 43 - 1)
                        hloc5 hloc10 (by omega) with ⟨v, st', hrun, hdec⟩
                    refine ⟨v, st', ?_, ?_⟩
                    · rw [h0_10, h10_16, h16_36, h36_69, h69_99]; rw [hp1]
                      rw [h99_166, h166_184, h184_217]; rw [hp2]; rw [h217_281]
                      split_res_fuel 1
                      rw [runJvmResFast_if_icmpeq_branch hr2n]
                      exact hrun
                    · change decodeOptParsedCoords st'.jvmHeap v = some (Algorithm.parseRLEOffset bytes)
                      rw [hfin_res]; exact hdec
                  · have hne_r2 : (r2.next == limit) = false := by
                      cases hbeq : r2.next == limit
                      · rfl
                      · exact absurd (LawfulBEq.eq_of_beq hbeq) hr2n
                    have hrle : Algorithm.parseRLEOffset bytes = none := by
                      unfold Algorithm.parseRLEOffset
                      rw [show bytes.size.toUInt32 = limit from rfl]
                      simp only [hlt3_b, hb0, bne_self_eq_false, hb1_neq, hb2, Bool.or_self,
                        Bool.false_eq_true, ↓reduceIte, hp1', decide_eq_true hr1n, hb_sp, beq_self_eq_true,
                        Bool.true_and, hp2', hne_r2, Bool.false_eq_true]
                    rcases parseRLEOffset_retNone_body (f := f69 - 18 - 46 - 6 - 21 - 43 - 1) (pc := 282)
                        (st_loc := 12) (stk := []) (locs := locs4) (jh := enc2.2) (hp := hp) (by omega) rfl with
                      ⟨v, st', hrun, hdec⟩
                    refine ⟨v, st', ?_, ?_⟩
                    · rw [h0_10, h10_16, h16_36, h36_69, h69_99]
                      rw [hp1, h99_166, h166_184, h184_217, hp2, h217_281]
                      split_res_fuel 1
                      rw [runJvmResFast_if_icmpeq_fallthrough hne_r2]
                      exact hrun
                    · change decodeOptParsedCoords st'.jvmHeap v = some (Algorithm.parseRLEOffset bytes)
                      rw [hrle]; exact hdec
              · have hb_sp_b : (bytes.get! r1.next.toNat == 32) = false := by
                  cases hbeq : bytes.get! r1.next.toNat == 32
                  · rfl
                  · exact absurd (LawfulBEq.eq_of_beq hbeq) hb_sp
                have hrle : Algorithm.parseRLEOffset bytes = none := by
                  unfold Algorithm.parseRLEOffset
                  rw [show bytes.size.toUInt32 = limit from rfl]
                  simp only [hlt3_b, hb0, bne_self_eq_false, hb1_neq, hb2, Bool.or_self,
                    Bool.false_eq_true, ↓reduceIte, hp1', decide_eq_true hr1n, hb_sp_b, Bool.and_false]
                rcases parseRLEOffset_retNone_body (f := f69 - 18 - 46 - 6 - 1) (pc := 185) (st_loc := 8)
                    (stk := []) (locs := locs3) (jh := enc1.2) (hp := hp) (by omega) rfl with
                  ⟨v, st', hrun, hdec⟩
                refine ⟨v, st', ?_, ?_⟩
                · rw [h0_10, h10_16, h16_36, h36_69, h69_99]; rw [hp1]; rw [h99_166, h166_184]
                  split_res_fuel 1
                  rw [runJvmResFast_if_icmpeq_fallthrough (u8Sext_beq_false (bytes.get! r1.next.toNat) 32
                    (fun h => hb_sp (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))) (by decide))]
                  exact hrun
                · change decodeOptParsedCoords st'.jvmHeap v = some (Algorithm.parseRLEOffset bytes)
                  rw [hrle]; exact hdec
            · have hrle : Algorithm.parseRLEOffset bytes = none := by
                unfold Algorithm.parseRLEOffset
                rw [show bytes.size.toUInt32 = limit from rfl]
                simp only [hlt3_b, hb0, bne_self_eq_false, hb1_neq, hb2, Bool.or_self,
                  Bool.false_eq_true, ↓reduceIte, hp1', decide_eq_false hr1n, Bool.false_and]
              rcases parseRLEOffset_retNone_body (f := f69 - 18 - 46 - 1) (pc := 167) (st_loc := 8)
                  (stk := []) (locs := locs3) (jh := enc1.2) (hp := hp) (by omega) rfl with
                ⟨v, st', hrun, hdec⟩
              refine ⟨v, st', ?_, ?_⟩
              · rw [h0_10, h10_16, h16_36, h36_69, h69_99]; rw [hp1]; rw [h99_166]
                split_res_fuel 1
                rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hr1n)]
                exact hrun
              · change decodeOptParsedCoords st'.jvmHeap v = some (Algorithm.parseRLEOffset bytes)
                rw [hrle]; exact hdec
        · rcases parseRLEOffset_retNone_body (f := f69 - 1) (pc := 70) (st_loc := 3)
              (stk := []) (locs := setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr))
                1 (.i32 limit)) 2 (.i32 (u8Sext (bytes.get! 1))))
              (jh := jh) (hp := hp) (by omega) rfl with ⟨v, st', hrun, hdec⟩
          refine ⟨v, st', ?_, ?_⟩
          · rw [h0_10, h10_16, h16_36, h36_69]
            split_res_fuel 1
            rw [runJvmResFast_if_icmpeq_fallthrough (u8Sext_beq_false (bytes.get! 2) 32
              (fun h => hb2 (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))) (by decide))]
            exact hrun
          · have hb2_b : (bytes.get! 2 != 32) = true := bne_iff_ne.mpr hb2
            simp [hb2_b]; exact hdec
      · have hne82 : (u8Sext (bytes.get! 1) == 82) = false := u8Sext_beq_false (bytes.get! 1) 82
          (fun h => hb1 (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))) (by decide)
        have hne80 : (u8Sext (bytes.get! 1) == 80) = false := u8Sext_beq_false (bytes.get! 1) 80
          (fun h => hb1 (Or.inr (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))) (by decide)
        rcases parseRLEOffset_retNone_body (f := 222) (pc := 40) (st_loc := 4)
            (stk := []) (locs := setLocal (setLocal (setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr))
              1 (.i32 limit)) 2 (.i32 (u8Sext (bytes.get! 1))))
            (jh := jh) (hp := hp) (by omega) rfl with ⟨v, st', hrun, hdec⟩
        refine ⟨v, st', ?_, ?_⟩
        · rw [h0_10, h10_16, h16_36]
          split_res_fuel 4
          rw [runJvmResFast_if_icmpeq_fallthrough hne82]; norm_res_fuel
          step_drop 3
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_if_icmpeq_fallthrough hne80]
          exact hrun
        · have hb1_82 : (bytes.get! 1 != 82) = true := bne_iff_ne.mpr (fun h => hb1 (Or.inl h))
          have hb1_80 : (bytes.get! 1 != 80) = true := bne_iff_ne.mpr (fun h => hb1 (Or.inr h))
          simp [hb1_82, hb1_80]; exact hdec
    · have hne35 : (u8Sext (bytes.get! 0) == 35) = false := u8Sext_beq_false (bytes.get! 0) 35
        (fun h => hb0 (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))) (by decide)
      rcases parseRLEOffset_retNone_body (f := 233) (pc := 17) (st_loc := 3)
          (stk := []) (locs := setLocal (setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr)) 1 (.i32 limit))
          (jh := jh) (hp := hp) (by omega) rfl with ⟨v, st', hrun, hdec⟩
      refine ⟨v, st', ?_, ?_⟩
      · rw [h0_10, h10_16]
        split_res_fuel 1
        rw [runJvmResFast_if_icmpeq_fallthrough hne35]
        exact hrun
      · have hb0_b : (bytes.get! 0 != 35) = true := bne_iff_ne.mpr hb0
        simp [hb0_b]; exact hdec

end ParseRLEOffset

/-! #### 2. `f_Algorithm_checkRLERule_prog` -/

section CheckRLERule
set_option maxRecDepth 2048

private theorem runJvmResFast_ireturn {f pc : Nat} {prog rest : List JvmInstr} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.ireturn :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      some (.i32 v, ⟨pc, .i32 v :: stk, locs, jh, hp⟩) := by
  unfold runJvmResFast; rw [Jvm.runJvmResFast.eq_def]; rfl

private theorem runJvmResFast_iconst_ireturn {f pc : Nat} {prog rest : List JvmInstr} {c : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 2) prog pc (.iconst c :: .ireturn :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      some (.i32 c, ⟨pc + 1, .i32 c :: stk, locs, jh, hp⟩) := by
  rw [show f + 2 = (f + 1) + 1 from rfl, runJvmResFast_iconst, runJvmResFast_ireturn]

private def checkRLERule_part3_val (bytes : ByteArray) (limit s2 first : UInt32) (hasLetters : Bool) : UInt32 :=
  let (e2, second) := Algorithm.scanDigitSet bytes limit s2 0
  if e2 == s2 || Algorithm.skipSpaces bytes e2 limit != limit then 2
  else
    let (birth, survival) := if hasLetters then (first, second) else (second, first)
    if birth == 8 && survival == 12 then 0 else 3

private def checkRLERule_part2_val (bytes : ByteArray) (limit s1 : UInt32) (hasLetters : Bool) : UInt32 :=
  let (e1, first) := Algorithm.scanDigitSet bytes limit s1 0
  if e1 == s1 || !(e1 < limit) || bytes.get! e1.toNat != 47 then 2
  else
    let lettersOk := !hasLetters ||
      (e1 + 1 < limit && Algorithm.isLetterByte (bytes.get! (e1 + 1).toNat) 115)
    if !lettersOk then 2
    else
      let s2 := if hasLetters then e1 + 2 else e1 + 1
      checkRLERule_part3_val bytes limit s2 first hasLetters

private theorem checkRLERule_part3
    {f : Nat} {bytes : ByteArray} {bytesAddr : Nat} {limit s2 first : UInt32}
    {hasLetters : Bool} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 44 ≤ f) (hstat : jh.statics = [])
    (hget : jh.get? bytesAddr = some (.byteArray bytes.data))
    (h0 : locs 0 = .heapRef bytesAddr) (h2 : locs 2 = .i32 limit)
    (h6 : locs 6 = .i32 (if hasLetters then 1 else 0))
    (h7 : locs 7 = .i32 first) (h8 : locs 8 = .i32 s2) :
    ∃ st', runJvmResFast f f_Algorithm_checkRLERule_prog 187
      (.invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_scanDigitSet-7IvYBaQ" "([BIII)Lkotlin/Pair;" ::
        f_Algorithm_checkRLERule_prog.drop 188)
      ⟨187, [.i32 0, .i32 s2, .i32 limit, .heapRef bytesAddr], locs, jh, hp⟩ =
      some (.i32 (checkRLERule_part3_val bytes limit s2 first hasLetters), st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  let r2 := Algorithm.scanDigitSet bytes limit s2 0
  let e2 := r2.1
  let second := r2.2
  let locs1 := setLocal (setLocal (setLocal locs 9 (.pair (.boxedUInt e2) (.boxedUInt second)))
    10 (.i32 e2)) 11 (.i32 second)
  have h187_201 : runJvmResFast f f_Algorithm_checkRLERule_prog 187
      (.invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_scanDigitSet-7IvYBaQ" "([BIII)Lkotlin/Pair;" ::
        f_Algorithm_checkRLERule_prog.drop 188)
      ⟨187, [.i32 0, .i32 s2, .i32 limit, .heapRef bytesAddr], locs, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 14) f_Algorithm_checkRLERule_prog 201
        (.if_icmpeq 224 :: f_Algorithm_checkRLERule_prog.drop 202)
        ⟨201, [.i32 s2, .i32 e2], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
    split_res_fuel 15
    rw [runJvmResFast_invokestatic_step (stepStatic_scanDigitSet_heap hget)]
    norm_res_fuel
    step_drop 14
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_checkcast_boxedUInt (hcls := Or.inl rfl)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_checkcast_boxedUInt (hcls := Or.inl rfl)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [show f - 15 + 1 = f - 14 from by omega, h8]
  by_cases he2 : e2 = s2
  · have he2_b : (e2 == s2) = true := beq_iff_eq.mpr he2
    have hret : checkRLERule_part3_val bytes limit s2 first hasLetters = 2 := by
      simp only [checkRLERule_part3_val, e2, r2, he2_b, Bool.true_or, ↓reduceIte]
    rw [hret]
    apply Exists.intro _; constructor
    · rw [h187_201]
      split_res_fuel 3
      rw [runJvmResFast_if_icmpeq_branch he2]; norm_res_fuel
      step_drop 2
      rw [runJvmResFast_iconst_ireturn]
    · exact ⟨rfl, rfl⟩
  · have he2_b : (e2 == s2) = false := beq_false_of_ne he2
    let p2 := Algorithm.skipSpaces bytes e2 limit
    let locs2 := setLocal locs1 12 (.i32 p2)
    have h201_209 : runJvmResFast (f - 14) f_Algorithm_checkRLERule_prog 201
        (.if_icmpeq 224 :: f_Algorithm_checkRLERule_prog.drop 202)
        ⟨201, [.i32 s2, .i32 e2], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
        runJvmResFast (f - 22) f_Algorithm_checkRLERule_prog 209
          (.if_icmpeq 212 :: f_Algorithm_checkRLERule_prog.drop 210)
          ⟨209, [.i32 limit, .i32 p2], locs2, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
      split_res_fuel 9
      rw [runJvmResFast_if_icmpeq_fallthrough he2_b]; norm_res_fuel
      step_drop 3
      heap_step_nonbranch_chunks
      rw [h0, h2]
      rw [runJvmResFast_invokestatic_step (stepStatic_skipSpaces_heap (by decide) hget)]
      norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [show f - 14 - 9 + 1 = f - 22 from by omega, h2]; rfl
    by_cases hp2 : p2 = limit
    · have hp2_b : (p2 != limit) = false := by simp [hp2]
      let birth := if hasLetters then first else second
      let survival := if hasLetters then second else first
      have hb_eq : (if hasLetters then (first, second) else (second, first)).1 = birth := by
        cases hasLetters <;> rfl
      have hs_eq : (if hasLetters then (first, second) else (second, first)).2 = survival := by
        cases hasLetters <;> rfl
      have h209_228 : ∃ locs3, locs3 3 = .i32 birth ∧ locs3 4 = .i32 survival ∧
          runJvmResFast (f - 22) f_Algorithm_checkRLERule_prog 209
            (.if_icmpeq 212 :: f_Algorithm_checkRLERule_prog.drop 210)
            ⟨209, [.i32 limit, .i32 p2], locs2, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast (f - 32) f_Algorithm_checkRLERule_prog 228
              (.if_icmpeq 231 :: f_Algorithm_checkRLERule_prog.drop 229)
              ⟨228, [.i32 8, .i32 birth], locs3, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
        cases hL : hasLetters
        · have h6_0 : locs 6 = .i32 0 := by simp [h6, hL]
          have hbirth : birth = second := by simp [birth, hL]
          refine ⟨setLocal (setLocal locs2 3 (.i32 second)) 4 (.i32 first),
            by simp [setLocal, birth, hL], by simp [setLocal, survival, hL], ?_⟩
          split_res_fuel 11
          rw [runJvmResFast_if_icmpeq_branch hp2]; norm_res_fuel
          step_drop 2
          heap_step_nonbranch_chunks
          rw [h6_0]; dsimp only
          rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
          step_drop 5
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [show f - 22 - 11 + 1 = f - 32 from by omega, h7, hbirth]; rfl
        · have h6_1 : locs 6 = .i32 1 := by simp [h6, hL]
          have hbirth : birth = first := by simp [birth, hL]
          refine ⟨setLocal (setLocal locs2 3 (.i32 first)) 4 (.i32 second),
            by simp [setLocal, birth, hL], by simp [setLocal, survival, hL], ?_⟩
          split_res_fuel 11
          rw [runJvmResFast_if_icmpeq_branch hp2]; norm_res_fuel
          step_drop 2
          heap_step_nonbranch_chunks
          rw [h6_1]; dsimp only
          rw [runJvmResFast_ifne_branch (by decide)]; norm_res_fuel
          step_drop 5
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [show f - 22 - 11 + 1 = f - 32 from by omega, h7, hbirth]; rfl
      rcases h209_228 with ⟨locs3, h3_3, h4_3, h209_228⟩
      by_cases hbth : birth = 8
      · have hbth_b : (birth == 8) = true := beq_iff_eq.mpr hbth
        have h228_233 : runJvmResFast (f - 32) f_Algorithm_checkRLERule_prog 228
            (.if_icmpeq 231 :: f_Algorithm_checkRLERule_prog.drop 229)
            ⟨228, [.i32 8, .i32 birth], locs3, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast (f - 35) f_Algorithm_checkRLERule_prog 233
              (.if_icmpeq 236 :: f_Algorithm_checkRLERule_prog.drop 234)
              ⟨233, [.i32 12, .i32 survival], locs3, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
          split_res_fuel 4
          rw [runJvmResFast_if_icmpeq_branch hbth]; norm_res_fuel
          step_drop 2
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [show f - 32 - 4 + 1 = f - 35 from by omega, h4_3]; rfl
        by_cases hsur : survival = 12
        · have hsur_b : (survival == 12) = true := beq_iff_eq.mpr hsur
          have hret : checkRLERule_part3_val bytes limit s2 first hasLetters = 0 := by
            dsimp only [checkRLERule_part3_val]
            change (if (e2 == s2 || (p2 != limit)) = true then 2 else
              if (if hasLetters = true then (first, second) else (second, first)).1 == 8 &&
                 (if hasLetters = true then (first, second) else (second, first)).2 == 12
              then 0 else 3) = 0
            rw [he2_b, hp2_b, Bool.false_or, hb_eq, hs_eq, hbth_b, hsur_b]; rfl
          rw [hret]
          apply Exists.intro _; constructor
          · rw [h187_201, h201_209, h209_228, h228_233]
            split_res_fuel 3
            rw [runJvmResFast_if_icmpeq_branch hsur]; norm_res_fuel
            step_drop 2
            rw [runJvmResFast_iconst_ireturn]
          · exact ⟨rfl, rfl⟩
        · have hsur_b : (survival == 12) = false := beq_false_of_ne hsur
          have hret : checkRLERule_part3_val bytes limit s2 first hasLetters = 3 := by
            dsimp only [checkRLERule_part3_val]
            change (if (e2 == s2 || (p2 != limit)) = true then 2 else
              if (if hasLetters = true then (first, second) else (second, first)).1 == 8 &&
                 (if hasLetters = true then (first, second) else (second, first)).2 == 12
              then 0 else 3) = 3
            rw [he2_b, hp2_b, Bool.false_or, hb_eq, hs_eq, hbth_b, hsur_b]; rfl
          rw [hret]
          apply Exists.intro _; constructor
          · rw [h187_201, h201_209, h209_228, h228_233]
            split_res_fuel 3
            rw [runJvmResFast_if_icmpeq_fallthrough hsur_b]; norm_res_fuel
            step_drop 2
            rw [runJvmResFast_iconst_ireturn]
          · exact ⟨rfl, rfl⟩
      · have hbth_b : (birth == 8) = false := beq_false_of_ne hbth
        have hret : checkRLERule_part3_val bytes limit s2 first hasLetters = 3 := by
          dsimp only [checkRLERule_part3_val]
          change (if (e2 == s2 || (p2 != limit)) = true then 2 else
            if (if hasLetters = true then (first, second) else (second, first)).1 == 8 &&
               (if hasLetters = true then (first, second) else (second, first)).2 == 12
            then 0 else 3) = 3
          rw [he2_b, hp2_b, Bool.false_or, hb_eq, hbth_b]; rfl
        rw [hret]
        apply Exists.intro _; constructor
        · rw [h187_201, h201_209, h209_228]
          split_res_fuel 3
          rw [runJvmResFast_if_icmpeq_fallthrough hbth_b]; norm_res_fuel
          step_drop 2
          rw [runJvmResFast_iconst_ireturn]
        · exact ⟨rfl, rfl⟩
    · have hne_p2 : (p2 != limit) = true := bne_iff_ne.mpr hp2
      have hret : checkRLERule_part3_val bytes limit s2 first hasLetters = 2 := by
        simp only [checkRLERule_part3_val, e2, r2, p2, he2_b, hne_p2, Bool.false_or, ↓reduceIte]
      rw [hret]
      apply Exists.intro _; constructor
      · rw [h187_201, h201_209]
        split_res_fuel 3
        rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hp2)]; norm_res_fuel
        step_drop 2
        rw [runJvmResFast_iconst_ireturn]
      · exact ⟨rfl, rfl⟩

private theorem checkRLERule_h143_187
    {f : Nat} {bytesAddr : Nat} {limit e1 first : UInt32}
    {locs3 : Nat → JvmVal} {objs : Array (Jvm.HeapObj AlgExt)} {hp : AlgHeap}
    (hf : 40 ≤ f) (h0 : locs3 0 = .heapRef bytesAddr) (h2 : locs3 2 = .i32 limit)
    (h16 : locs3 16 = .i32 e1) (h17 : locs3 17 = .i32 first)
    {bS : UInt8} (h19 : locs3 19 = .i32 (u8Sext bS))
    (hbS : Algorithm.isLetterByte bS 115 = true) :
    ∃ f187 locs5, f - 31 ≤ f187 ∧
      runJvmResFast f f_Algorithm_checkRLERule_prog 143
        (.if_icmpeq 158 :: f_Algorithm_checkRLERule_prog.drop 144)
        ⟨143, [.i32 115, .i32 (u8Sext bS)], locs3, ⟨objs, []⟩, hp⟩ =
        runJvmResFast f187 f_Algorithm_checkRLERule_prog 187
          (.invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_scanDigitSet-7IvYBaQ" "([BIII)Lkotlin/Pair;" ::
            f_Algorithm_checkRLERule_prog.drop 188)
          ⟨187, [.i32 0, .i32 (e1 + 2), .i32 limit, .heapRef bytesAddr],
            locs5, ⟨objs, []⟩, hp⟩ ∧
      locs5 0 = .heapRef bytesAddr ∧ locs5 2 = .i32 limit ∧
      locs5 6 = .i32 1 ∧ locs5 7 = .i32 first ∧ locs5 8 = .i32 (e1 + 2) := by
  rcases hp with ⟨ar, u64, asc⟩
  have hbS_cases : bS = 115 ∨ bS = 83 := by simpa [Algorithm.isLetterByte] using hbS
  rcases hbS_cases with hbS115 | hbS83
  · have hu115 : u8Sext bS = 115 := u8Sext_eq_u32 (by simp [hbS115]) (by decide)
    apply Exists.intro (f - 28); apply Exists.intro _
    constructor; · omega
    constructor
    · split_res_fuel 29
      rw [runJvmResFast_if_icmpeq_branch hu115]; norm_res_fuel
      step_drop 9
      step_res_block 8
      rw [runJvmResFast_goto]; norm_res_fuel
      step_drop 19
      step_res_block 1
      rw [h16]
      heap_step_nonbranch_chunks; norm_res_fuel
      simp only [show f - 29 + 1 = f - 28 from by omega, h0, h2]
      congr 2
    · simp [setLocal, h0, h2, h17]
  · have hne115 : (u8Sext bS == 115) = false :=
      u8Sext_beq_false bS 115 (by simp [hbS83]) (by decide)
    have hu83 : u8Sext bS = 83 := u8Sext_eq_u32 (by simp [hbS83]) (by decide)
    apply Exists.intro (f - 31); apply Exists.intro _
    constructor; · omega
    constructor
    · split_res_fuel 32
      rw [runJvmResFast_if_icmpeq_fallthrough hne115]; norm_res_fuel
      step_drop 3
      heap_step_nonbranch_chunks; norm_res_fuel
      (conv => lhs; arg 5; arg 1; change 146)
      rw [h19]
      rw [runJvmResFast_if_icmpeq_branch hu83]; norm_res_fuel
      step_drop 9
      step_res_block 8
      rw [runJvmResFast_goto]; norm_res_fuel
      step_drop 19
      step_res_block 1
      rw [h16]
      heap_step_nonbranch_chunks; norm_res_fuel
      simp only [show f - 32 + 1 = f - 31 from by omega, h0, h2]
      congr 2
    · simp [setLocal, h0, h2, h17]

private theorem checkRLERule_part2
    {f : Nat} {bytes : ByteArray} {bytesAddr : Nat} {limit s1 : UInt32}
    {hasLetters : Bool} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 130 ≤ f) (hstat : jh.statics = [])
    (hget : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hlim : limit.toNat ≤ bytes.data.size) (hlim31 : limit.toNat < 2 ^ 31)
    (h0 : locs 0 = .heapRef bytesAddr) (h2 : locs 2 = .i32 limit)
    (h13 : locs 13 = .i32 (if hasLetters then 1 else 0))
    (h14 : locs 14 = .i32 s1) :
    ∃ st', runJvmResFast f f_Algorithm_checkRLERule_prog 79
      (.invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_scanDigitSet-7IvYBaQ" "([BIII)Lkotlin/Pair;" ::
        f_Algorithm_checkRLERule_prog.drop 80)
      ⟨79, [.i32 0, .i32 s1, .i32 limit, .heapRef bytesAddr], locs, jh, hp⟩ =
      some (.i32 (checkRLERule_part2_val bytes limit s1 hasLetters), st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  let r1 := Algorithm.scanDigitSet bytes limit s1 0
  let e1 := r1.1
  let first := r1.2
  let locs1 := setLocal (setLocal (setLocal locs 15 (.pair (.boxedUInt e1) (.boxedUInt first)))
    16 (.i32 e1)) 17 (.i32 first)
  have h79_93 : runJvmResFast f f_Algorithm_checkRLERule_prog 79
      (.invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_scanDigitSet-7IvYBaQ" "([BIII)Lkotlin/Pair;" ::
        f_Algorithm_checkRLERule_prog.drop 80)
      ⟨79, [.i32 0, .i32 s1, .i32 limit, .heapRef bytesAddr], locs, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 14) f_Algorithm_checkRLERule_prog 93
        (.if_icmpeq 167 :: f_Algorithm_checkRLERule_prog.drop 94)
        ⟨93, [.i32 s1, .i32 e1], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
    split_res_fuel 15
    rw [runJvmResFast_invokestatic_step (stepStatic_scanDigitSet_heap hget)]
    norm_res_fuel
    step_drop 14
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_checkcast_boxedUInt (hcls := Or.inl rfl)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_checkcast_boxedUInt (hcls := Or.inl rfl)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    simp only [show f - 15 + 1 = f - 14 from by omega, h14]
    congr 2
  by_cases he1 : e1 = s1
  · have hret : checkRLERule_part2_val bytes limit s1 hasLetters = 2 := by
      simp only [checkRLERule_part2_val, e1, r1, beq_iff_eq.mpr he1, Bool.true_or, ↓reduceIte]
    rw [hret]
    apply Exists.intro _; constructor
    · rw [h79_93]
      split_res_fuel 3
      rw [runJvmResFast_if_icmpeq_branch he1]; norm_res_fuel
      step_drop 2
      rw [runJvmResFast_iconst_ireturn]
    · exact ⟨rfl, rfl⟩
  · have he1_b : (e1 == s1) = false := beq_false_of_ne he1
    have h93_97 : runJvmResFast (f - 14) f_Algorithm_checkRLERule_prog 93
        (.if_icmpeq 167 :: f_Algorithm_checkRLERule_prog.drop 94)
        ⟨93, [.i32 s1, .i32 e1], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
        runJvmResFast (f - 18) f_Algorithm_checkRLERule_prog 97
          (.iflt 100 :: f_Algorithm_checkRLERule_prog.drop 98)
          ⟨97, [.i32 (if e1 == limit then 0 else if e1 < limit then 4294967295 else 1)],
            locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
      split_res_fuel 5
      rw [runJvmResFast_if_icmpeq_fallthrough he1_b]; norm_res_fuel
      step_drop 4
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [h2]; heap_step_nonbranch_chunks; norm_res_fuel
      (conv => lhs; arg 5; arg 1; change 97)
      simp only [show f - 14 - 5 + 1 = f - 18 from by omega]
      congr 2
    by_cases he1_lim : e1 < limit
    · have he1_toNat : e1.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp he1_lim
      have he1_slt : e1.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
      have he1_lt_sz : e1.toNat < bytes.data.size := by omega
      have h97_105 : runJvmResFast (f - 18) f_Algorithm_checkRLERule_prog 97
          (.iflt 100 :: f_Algorithm_checkRLERule_prog.drop 98)
          ⟨97, [.i32 (if e1 == limit then 0 else if e1 < limit then 4294967295 else 1)],
            locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
          runJvmResFast (f - 24) f_Algorithm_checkRLERule_prog 105
            (.if_icmpeq 108 :: f_Algorithm_checkRLERule_prog.drop 106)
            ⟨105, [.i32 47, .i32 (u8Sext (bytes.get! e1.toNat))], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
        split_res_fuel 7
        rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true he1_lim)]
        norm_res_fuel
        step_drop 3
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [h0]
        rw [runJvmResFast_baload_byteArray (idx := e1) hget he1_slt he1_lt_sz]; norm_res_fuel
        step_drop 3
        heap_step_nonbranch_chunks; norm_res_fuel
        (conv => lhs; rw [show f - 18 - 7 + 1 = f - 24 from by omega,
          byteArray_get_eq_getBang bytes he1_lt_sz])
        congr 2
      by_cases hb_slash : bytes.get! e1.toNat = 47
      · have hslash_u : u8Sext (bytes.get! e1.toNat) = 47 :=
          u8Sext_eq_u32 (by simp [hb_slash]) (by decide)
        have hslash_b : (bytes.get! e1.toNat != 47) = false := by simp [hb_slash]
        have hnot_lim : (!(e1 < limit)) = false := by simp [he1_lim]
        cases hasLetters
        · have h13_1 : locs 13 = .i32 0 := by simp [h13]
          let locs2 := setLocal (setLocal (setLocal (setLocal (setLocal locs1 18 (.i32 (e1 + 1)))
            5 (.i32 0)) 6 (.i32 0)) 7 (.i32 first)) 8 (.i32 (e1 + 1))
          have h105_187 : runJvmResFast (f - 24) f_Algorithm_checkRLERule_prog 105
              (.if_icmpeq 108 :: f_Algorithm_checkRLERule_prog.drop 106)
              ⟨105, [.i32 47, .i32 (u8Sext (bytes.get! e1.toNat))], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
              runJvmResFast (f - 45) f_Algorithm_checkRLERule_prog 187
                (.invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_scanDigitSet-7IvYBaQ" "([BIII)Lkotlin/Pair;" ::
                  f_Algorithm_checkRLERule_prog.drop 188)
                ⟨187, [.i32 0, .i32 (e1 + 1), .i32 limit, .heapRef bytesAddr],
                  locs2, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
            split_res_fuel 22
            rw [runJvmResFast_if_icmpeq_branch hslash_u]; norm_res_fuel
            step_drop 2
            heap_step_nonbranch_chunks
            rw [h13_1]; dsimp only
            rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
            step_drop 14
            step_res_block 3
            rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
            step_res_block 9
            rw [runJvmResFast_goto]; norm_res_fuel
            step_drop 5
            heap_step_nonbranch_chunks; norm_res_fuel
            simp only [show f - 24 - 22 + 1 = f - 45 from by omega, h0, h2]
            congr 2
          rcases checkRLERule_part3 (f := f - 45) (bytes := bytes) (bytesAddr := bytesAddr)
              (limit := limit) (s2 := e1 + 1) (first := first) (hasLetters := false)
              (locs := locs2) (jh := ⟨objs, []⟩) (hp := ⟨ar, u64, asc⟩) (by omega) rfl hget
              (by simp [locs2, locs1, setLocal, h0]) (by simp [locs2, locs1, setLocal, h2])
              (by simp [locs2, setLocal]) (by simp [locs2, setLocal])
              (by simp [locs2, setLocal]) with
            ⟨st', hrun3, hjh3, hhp3⟩
          have hret_eq : checkRLERule_part2_val bytes limit s1 false =
              checkRLERule_part3_val bytes limit (e1 + 1) first false := by
            simp only [checkRLERule_part2_val, r1, e1, first, he1_b, hnot_lim, hslash_b,
              Bool.false_or, Bool.false_eq_true, Bool.not_false, Bool.true_or, Bool.not_true,
              ↓reduceIte]
          refine ⟨st', ?_, hjh3, hhp3⟩
          rw [hret_eq, h79_93, h93_97, h97_105, h105_187]
          exact hrun3
        · have h13_1 : locs 13 = .i32 1 := by simp [h13]
          let locs2 := setLocal locs1 18 (.i32 (e1 + 1))
          have h105_132 : runJvmResFast (f - 24) f_Algorithm_checkRLERule_prog 105
              (.if_icmpeq 108 :: f_Algorithm_checkRLERule_prog.drop 106)
              ⟨105, [.i32 47, .i32 (u8Sext (bytes.get! e1.toNat))], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
              runJvmResFast (f - 35) f_Algorithm_checkRLERule_prog 132
                (.iflt 135 :: f_Algorithm_checkRLERule_prog.drop 133)
                ⟨132, [.i32 (if e1 + 1 == limit then 0 else if e1 + 1 < limit then 4294967295 else 1)],
                  locs2, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
            split_res_fuel 12
            rw [runJvmResFast_if_icmpeq_branch hslash_u]; norm_res_fuel
            step_drop 2
            heap_step_nonbranch_chunks
            rw [h13_1]; dsimp only
            rw [runJvmResFast_ifne_branch (by decide)]; norm_res_fuel
            step_drop 9
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [h2]; heap_step_nonbranch_chunks; norm_res_fuel
            simp only [show f - 24 - 12 + 1 = f - 35 from by omega]
            congr 2
          by_cases he1p1_lim : e1 + 1 < limit
          · have he1p1_toNat : (e1 + 1).toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp he1p1_lim
            have he1p1_slt : (e1 + 1).toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
            have he1p1_lt_sz : (e1 + 1).toNat < bytes.data.size := by omega
            let bS := bytes.get! (e1 + 1).toNat
            let locs3 := setLocal locs2 19 (.i32 (u8Sext bS))
            have h132_143 : runJvmResFast (f - 35) f_Algorithm_checkRLERule_prog 132
                (.iflt 135 :: f_Algorithm_checkRLERule_prog.drop 133)
                ⟨132, [.i32 (if e1 + 1 == limit then 0 else if e1 + 1 < limit then 4294967295 else 1)],
                  locs2, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
                runJvmResFast (f - 44) f_Algorithm_checkRLERule_prog 143
                  (.if_icmpeq 158 :: f_Algorithm_checkRLERule_prog.drop 144)
                  ⟨143, [.i32 115, .i32 (u8Sext bS)], locs3, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
              split_res_fuel 10
              rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true he1p1_lim)]
              norm_res_fuel
              step_drop 4
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [h0]
              rw [runJvmResFast_baload_byteArray (idx := e1 + 1) hget he1p1_slt he1p1_lt_sz]; norm_res_fuel
              step_drop 5
              heap_step_nonbranch_chunks; norm_res_fuel
              (conv => lhs; rw [show f - 35 - 10 + 1 = f - 44 from by omega,
                byteArray_get_eq_getBang bytes he1p1_lt_sz])
              congr 2
            by_cases hbS : Algorithm.isLetterByte bS 115 = true
            · have h143_187 := checkRLERule_h143_187 (f := f - 44)
                  (bytesAddr := bytesAddr) (limit := limit) (e1 := e1) (first := first)
                  (locs3 := locs3) (objs := objs) (hp := ⟨ar, u64, asc⟩) (by omega)
                  (by simp [locs3, locs2, locs1, setLocal, h0])
                  (by simp [locs3, locs2, locs1, setLocal, h2])
                  (by simp [locs3, locs2, locs1, setLocal])
                  (by simp [locs3, locs2, locs1, setLocal])
                  (by simp [locs3, setLocal]) hbS
              rcases h143_187 with ⟨f187, locs5, hf187, h143_187, h0_5, h2_5, h6_5, h7_5, h8_5⟩
              rcases checkRLERule_part3 (f := f187) (bytes := bytes) (bytesAddr := bytesAddr)
                  (limit := limit) (s2 := e1 + 2) (first := first) (hasLetters := true)
                  (locs := locs5) (jh := ⟨objs, []⟩) (hp := ⟨ar, u64, asc⟩) (by omega) rfl hget
                  h0_5 h2_5 h6_5 h7_5 h8_5 with ⟨st', hrun3, hjh3, hhp3⟩
              have hret_eq : checkRLERule_part2_val bytes limit s1 true =
                  checkRLERule_part3_val bytes limit (e1 + 2) first true := by
                simp only [checkRLERule_part2_val, r1, e1, first, he1_b, hnot_lim, hslash_b,
                  decide_eq_true he1p1_lim, bS, hbS, Bool.true_and, Bool.false_or,
                  Bool.false_eq_true, Bool.not_true, ↓reduceIte]
              refine ⟨st', ?_, hjh3, hhp3⟩
              rw [hret_eq, h79_93, h93_97, h97_105, h105_132, h132_143, h143_187]
              exact hrun3
            · have hbS_false : Algorithm.isLetterByte bS 115 = false := Bool.eq_false_iff.mpr hbS
              have hne115 : (u8Sext bS == 115) = false := u8Sext_beq_false bS 115 (by
                intro h
                have : bS = 115 := UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)
                simp [Algorithm.isLetterByte, this] at hbS_false) (by decide)
              have hne83 : (u8Sext bS == 83) = false := u8Sext_beq_false bS 83 (by
                intro h
                have : bS = 83 := UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)
                simp [Algorithm.isLetterByte, this] at hbS_false) (by decide)
              have hret : checkRLERule_part2_val bytes limit s1 true = 2 := by
                simp only [checkRLERule_part2_val, r1, e1, he1_b, hnot_lim, hslash_b, he1p1_lim, bS,
                  hbS_false, Bool.false_eq_true, Bool.not_true, Bool.and_false,
                  Bool.or_self, Bool.not_false, ↓reduceIte]
              rw [hret]
              apply Exists.intro _; constructor
              · rw [h79_93, h93_97, h97_105, h105_132, h132_143]
                split_res_fuel 6
                rw [runJvmResFast_if_icmpeq_fallthrough hne115]; norm_res_fuel
                step_drop 3
                heap_step_nonbranch_chunks
                rw [runJvmResFast_if_icmpeq_fallthrough hne83]; norm_res_fuel
                step_drop 2
                rw [runJvmResFast_iconst_ireturn]
              · exact ⟨rfl, rfl⟩
          · have hret : checkRLERule_part2_val bytes limit s1 true = 2 := by
              simp only [checkRLERule_part2_val, r1, e1, he1_b, hnot_lim, hslash_b,
                decide_eq_false he1p1_lim, Bool.false_eq_true, Bool.not_true,
                Bool.false_and, Bool.not_false, Bool.or_self, ↓reduceIte]
            rw [hret]
            apply Exists.intro _; constructor
            · rw [h79_93, h93_97, h97_105, h105_132]
              split_res_fuel 3
              rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false he1p1_lim)]
              norm_res_fuel
              step_drop 2
              rw [runJvmResFast_iconst_ireturn]
            · exact ⟨rfl, rfl⟩
      · have hslash_b : (bytes.get! e1.toNat != 47) = true := bne_iff_ne.mpr hb_slash
        have hne47 : (u8Sext (bytes.get! e1.toNat) == 47) = false := u8Sext_beq_false _ 47
          (fun h => hb_slash (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))) (by decide)
        have hret : checkRLERule_part2_val bytes limit s1 hasLetters = 2 := by
          simp only [checkRLERule_part2_val, r1, e1, he1_b, he1_lim, hslash_b, Bool.or_true, ↓reduceIte]
        rw [hret]
        apply Exists.intro _; constructor
        · rw [h79_93, h93_97, h97_105]
          split_res_fuel 3
          rw [runJvmResFast_if_icmpeq_fallthrough hne47]; norm_res_fuel
          step_drop 2
          rw [runJvmResFast_iconst_ireturn]
        · exact ⟨rfl, rfl⟩
    · have hnot_lim : (!(e1 < limit)) = true := by simp [he1_lim]
      have hret : checkRLERule_part2_val bytes limit s1 hasLetters = 2 := by
        simp only [checkRLERule_part2_val, r1, e1, he1_b, hnot_lim, Bool.false_or, Bool.true_or, ↓reduceIte]
      rw [hret]
      apply Exists.intro _; constructor
      · rw [h79_93, h93_97]
        split_res_fuel 3
        rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false he1_lim)]
        norm_res_fuel
        step_drop 2
        rw [runJvmResFast_iconst_ireturn]
      · exact ⟨rfl, rfl⟩

private theorem checkRLERule_h0_37 {f : Nat} (bytes : ByteArray) (pos limit : UInt32) (bytesAddr : Nat)
    (objs : Array (Jvm.HeapObj AlgExt)) (hp : AlgHeap)
    (hf : 40 ≤ f) (hbytes : ({ objects := objs, statics := [] } : Jvm.JvmHeap AlgExt).get? bytesAddr =
      some (.byteArray bytes.data)) :
    let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (fun _ => .null)
      0 (.heapRef bytesAddr)) 1 (.i32 pos)) 2 (.i32 limit)
    let p0 := Algorithm.skipSpaces bytes pos limit
    let locs1 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
      locs0 3 (.i32 0)) 4 (.i32 0)) 5 (.i32 0)) 6 (.i32 0)) 7 (.i32 0)) 8 (.i32 0))
      9 (.i32 0)) 10 (.i32 0)) 11 (.i32 0)) 12 (.i32 0)) 13 (.i32 0)) 14 (.i32 0))
      15 (.i32 p0)) 16 (.i32 0)
    runJvmResFast f f_Algorithm_checkRLERule_prog 0 f_Algorithm_checkRLERule_prog
      ⟨0, [], locs0, ⟨objs, []⟩, hp⟩ =
      runJvmResFast (f - 37) f_Algorithm_checkRLERule_prog 37
        (.iflt 43 :: f_Algorithm_checkRLERule_prog.drop 38)
        ⟨37, [.i32 (if p0 == limit then 0 else if p0 < limit then 4294967295 else 1)],
          locs1, ⟨objs, []⟩, hp⟩ := by
  intro locs0 p0 locs1
  rcases hp with ⟨ar, u64, asc⟩
  split_res_fuel 38
  conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_checkRLERule_prog)]
  step_drop 3
  step_res_block 2
  (conv => lhs; arg 5; arg 2; simp only [locs0, setLocal])
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]; norm_res_fuel
  step_drop 28
  step_res_block 27
  (conv => lhs; arg 5; arg 2; simp only [locs0, setLocal])
  rw [runJvmResFast_invokestatic_step (stepStatic_skipSpaces_heap (by decide) hbytes)]
  norm_res_fuel
  step_drop 7
  step_res_block 5
  (conv => lhs; arg 5; arg 2; simp only [locs0, setLocal])
  heap_step_nonbranch_chunks; norm_res_fuel
  simp only [show f - 38 + 1 = f - 37 from by omega]
  congr 2

private theorem checkRLERule_h51_79
    {f : Nat} {limit p0 : UInt32} {bytesAddr : Nat} {b0 : UInt8}
    {locs2 : Nat → JvmVal} {objs : Array (Jvm.HeapObj AlgExt)} {hp : AlgHeap}
    (hf : 30 ≤ f) (h0 : locs2 0 = .heapRef bytesAddr) (h2 : locs2 2 = .i32 limit)
    (h15 : locs2 15 = .i32 p0) (h17 : locs2 17 = .i32 (u8Sext b0)) :
    let hasLetters := Algorithm.isLetterByte b0 98
    let s1 := if hasLetters then p0 + 1 else p0
    ∃ f79 locs3, f - 21 ≤ f79 ∧
      runJvmResFast f f_Algorithm_checkRLERule_prog 51
        (.if_icmpeq 63 :: f_Algorithm_checkRLERule_prog.drop 52)
        ⟨51, [.i32 98, .i32 (u8Sext b0)], locs2, ⟨objs, []⟩, hp⟩ =
        runJvmResFast f79 f_Algorithm_checkRLERule_prog 79
          (.invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_scanDigitSet-7IvYBaQ" "([BIII)Lkotlin/Pair;" ::
            f_Algorithm_checkRLERule_prog.drop 80)
          ⟨79, [.i32 0, .i32 s1, .i32 limit, .heapRef bytesAddr],
            locs3, ⟨objs, []⟩, hp⟩ ∧
      locs3 0 = .heapRef bytesAddr ∧ locs3 2 = .i32 limit ∧
      locs3 13 = .i32 (if hasLetters then 1 else 0) ∧ locs3 14 = .i32 s1 := by
  intro hasLetters s1
  rcases hp with ⟨ar, u64, asc⟩
  by_cases hb0 : hasLetters = true
  · have hb0_cases : b0 = 98 ∨ b0 = 66 := by simpa [hasLetters, Algorithm.isLetterByte] using hb0
    have hs1_eq : s1 = p0 + 1 := by simp [s1, hb0]
    rcases hb0_cases with hb98 | hb66
    · have hu98 : u8Sext b0 = 98 := u8Sext_eq_u32 (by simp [hb98]) (by decide)
      apply Exists.intro (f - 17); apply Exists.intro _
      constructor; · omega
      constructor
      · split_res_fuel 18
        rw [runJvmResFast_if_icmpeq_branch hu98]; norm_res_fuel
        step_drop 6
        step_res_block 3
        rw [h15]
        step_res_block 2
        rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
        step_drop 11
        step_res_block 10
        simp only [show f - 18 + 1 = f - 17 from by omega, h0, h2, hs1_eq]
        congr 2
      · simp [setLocal, h0, h2, hb0, hs1_eq]
    · have hne98 : (u8Sext b0 == 98) = false := u8Sext_beq_false b0 98 (by simp [hb66]) (by decide)
      have hu66 : u8Sext b0 = 66 := u8Sext_eq_u32 (by simp [hb66]) (by decide)
      apply Exists.intro (f - 21); apply Exists.intro _
      constructor; · omega
      constructor
      · split_res_fuel 22
        rw [runJvmResFast_if_icmpeq_fallthrough hne98]; norm_res_fuel
        step_drop 3
        heap_step_nonbranch_chunks; norm_res_fuel
        (conv => lhs; arg 5; arg 1; change 54)
        rw [h17]
        rw [runJvmResFast_if_icmpeq_branch hu66]; norm_res_fuel
        step_drop 3
        step_res_block 2
        rw [runJvmResFast_goto]; norm_res_fuel
        step_drop 4
        step_res_block 1
        rw [h15]
        step_res_block 2
        rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
        step_drop 11
        step_res_block 10
        simp only [show f - 22 + 1 = f - 21 from by omega, h0, h2, hs1_eq]
        congr 2
      · simp [setLocal, h0, h2, hb0, hs1_eq]
  · have hb0_false : hasLetters = false := Bool.eq_false_iff.mpr hb0
    have hne98 : (u8Sext b0 == 98) = false := u8Sext_beq_false b0 98 (by
      intro h
      have : b0 = 98 := UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)
      simp [hasLetters, Algorithm.isLetterByte, this] at hb0_false) (by decide)
    have hne66 : (u8Sext b0 == 66) = false := u8Sext_beq_false b0 66 (by
      intro h
      have : b0 = 66 := UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)
      simp [hasLetters, Algorithm.isLetterByte, this] at hb0_false) (by decide)
    have hs1_eq : s1 = p0 := by simp [s1, hb0_false]
    apply Exists.intro (f - 13); apply Exists.intro _
    constructor; · omega
    constructor
    · split_res_fuel 14
      rw [runJvmResFast_if_icmpeq_fallthrough hne98]; norm_res_fuel
      step_drop 3
      heap_step_nonbranch_chunks; norm_res_fuel
      (conv => lhs; arg 5; arg 1; change 54)
      rw [h17]
      rw [runJvmResFast_if_icmpeq_fallthrough hne66]; norm_res_fuel
      step_drop 5
      step_res_block 4
      rw [runJvmResFast_goto]; norm_res_fuel
      step_drop 5
      heap_step_nonbranch_chunks; norm_res_fuel
      simp only [show f - 14 + 1 = f - 13 from by omega, h0, h2, h15, hs1_eq]
      congr 2
    · simp [setLocal, h0, h2, hb0_false, hs1_eq]

private theorem checkRLERule_part1 {f : Nat} (bytes : ByteArray) (pos limit : UInt32) (bytesAddr : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hf : 230 ≤ f) (hstat : jh.statics = [])
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hlim : limit.toNat ≤ bytes.data.size) (hlim31 : limit.toNat < 2 ^ 31) :
    ∃ st', runJvmResFast f f_Algorithm_checkRLERule_prog 0 f_Algorithm_checkRLERule_prog
        ⟨0, [], setLocal (setLocal (setLocal (fun (_ : Nat) => (.null : JvmVal))
          0 (.heapRef bytesAddr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
        some (.i32 (Algorithm.checkRLERule bytes pos limit), st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (fun _ => .null)
    0 (.heapRef bytesAddr)) 1 (.i32 pos)) 2 (.i32 limit)
  let p0 := Algorithm.skipSpaces bytes pos limit
  let locs1 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
    (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
    locs0 3 (.i32 0)) 4 (.i32 0)) 5 (.i32 0)) 6 (.i32 0)) 7 (.i32 0)) 8 (.i32 0))
    9 (.i32 0)) 10 (.i32 0)) 11 (.i32 0)) 12 (.i32 0)) 13 (.i32 0)) 14 (.i32 0))
    15 (.i32 p0)) 16 (.i32 0)
  have h0_37 : runJvmResFast f f_Algorithm_checkRLERule_prog 0 f_Algorithm_checkRLERule_prog
      ⟨0, [], locs0, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (f - 37) f_Algorithm_checkRLERule_prog 37
        (.iflt 43 :: f_Algorithm_checkRLERule_prog.drop 38)
        ⟨37, [.i32 (if p0 == limit then 0 else if p0 < limit then 4294967295 else 1)],
          locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ :=
    checkRLERule_h0_37 (f := f) bytes pos limit bytesAddr objs ⟨ar, u64, asc⟩
      (by omega) hbytes
  by_cases hp0 : p0 < limit
  · have hp0_toNat : p0.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hp0
    have hp0_slt : p0.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
    have hp0_lt_sz : p0.toNat < bytes.data.size := by omega
    let b0 := bytes.get! p0.toNat
    let locs2 := setLocal locs1 17 (.i32 (u8Sext b0))
    have h37_51 : runJvmResFast (f - 37) f_Algorithm_checkRLERule_prog 37
        (.iflt 43 :: f_Algorithm_checkRLERule_prog.drop 38)
        ⟨37, [.i32 (if p0 == limit then 0 else if p0 < limit then 4294967295 else 1)],
          locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
        runJvmResFast (f - 46) f_Algorithm_checkRLERule_prog 51
          (.if_icmpeq 63 :: f_Algorithm_checkRLERule_prog.drop 52)
          ⟨51, [.i32 98, .i32 (u8Sext b0)], locs2, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
      split_res_fuel 10
      rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hp0)]
      norm_res_fuel
      step_drop 4
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_baload_byteArray (idx := p0) hbytes hp0_slt hp0_lt_sz]; norm_res_fuel
      step_drop 5
      heap_step_nonbranch_chunks; norm_res_fuel
      (conv => lhs; rw [show f - 37 - 10 + 1 = f - 46 from by omega,
        byteArray_get_eq_getBang bytes hp0_lt_sz])
      congr 2
    let hasLetters := Algorithm.isLetterByte b0 98
    let s1 := if hasLetters then p0 + 1 else p0
    have h51_79 := checkRLERule_h51_79 (f := f - 46) (limit := limit) (p0 := p0)
      (bytesAddr := bytesAddr) (b0 := b0) (locs2 := locs2) (objs := objs) (hp := ⟨ar, u64, asc⟩)
      (by omega) (by simp [locs2, locs1, locs0, setLocal])
      (by simp [locs2, locs1, locs0, setLocal]) (by simp [locs2, locs1, setLocal])
      (by simp [locs2, setLocal])
    rcases h51_79 with ⟨f79, locs3, hf79, h51_79, h0_3, h2_3, h13_3, h14_3⟩
    rcases checkRLERule_part2 (f := f79) (bytes := bytes) (bytesAddr := bytesAddr)
        (limit := limit) (s1 := s1) (hasLetters := hasLetters) (locs := locs3)
        (jh := ⟨objs, []⟩) (hp := ⟨ar, u64, asc⟩) (by omega) rfl hbytes hlim hlim31
        h0_3 h2_3 h13_3 h14_3 with ⟨st', hrun2, hjh2, hhp2⟩
    have hret_eq : Algorithm.checkRLERule bytes pos limit =
        checkRLERule_part2_val bytes limit s1 hasLetters := by
      have hdec_hp0 : decide (Algorithm.skipSpaces bytes pos limit < limit) = true :=
        decide_eq_true hp0
      rw [Algorithm.checkRLERule]
      simp only [hdec_hp0, Bool.true_and, p0, b0, hasLetters, s1,
        checkRLERule_part2_val, checkRLERule_part3_val,
        Algorithm.birth3Mask, Algorithm.survival23Mask]
    dsimp only [hasLetters, s1] at hrun2
    refine ⟨st', ?_, hjh2, hhp2⟩
    rw [hret_eq]
    (conv => lhs; arg 5; arg 3; change locs0)
    rw [h0_37, h37_51, h51_79]
    exact hrun2
  · let locs2 := setLocal (setLocal locs1 13 (.i32 0)) 14 (.i32 p0)
    have h37_79 : runJvmResFast (f - 37) f_Algorithm_checkRLERule_prog 37
        (.iflt 43 :: f_Algorithm_checkRLERule_prog.drop 38)
        ⟨37, [.i32 (if p0 == limit then 0 else if p0 < limit then 4294967295 else 1)],
          locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
        runJvmResFast (f - 47) f_Algorithm_checkRLERule_prog 79
          (.invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_scanDigitSet-7IvYBaQ" "([BIII)Lkotlin/Pair;" ::
            f_Algorithm_checkRLERule_prog.drop 80)
          ⟨79, [.i32 0, .i32 p0, .i32 limit, .heapRef bytesAddr],
            locs2, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
      split_res_fuel 11
      rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hp0)]
      norm_res_fuel
      step_drop 5
      step_res_block 4
      rw [runJvmResFast_goto]; norm_res_fuel
      step_drop 5
      step_res_block 4
      (conv => lhs; rw [show f - 37 - 11 + 1 = f - 47 from by omega])
    rcases checkRLERule_part2 (f := f - 47) (bytes := bytes) (bytesAddr := bytesAddr)
        (limit := limit) (s1 := p0) (hasLetters := false) (locs := locs2)
        (jh := ⟨objs, []⟩) (hp := ⟨ar, u64, asc⟩) (by omega) rfl hbytes hlim hlim31
        (by simp [locs2, locs1, locs0, setLocal]) (by simp [locs2, locs1, locs0, setLocal])
        (by simp [locs2, setLocal]) (by simp [locs2, setLocal]) with
      ⟨st', hrun2, hjh2, hhp2⟩
    have hret_eq : Algorithm.checkRLERule bytes pos limit =
        checkRLERule_part2_val bytes limit p0 false := by
      have hdec_hp0 : decide (Algorithm.skipSpaces bytes pos limit < limit) = false :=
        decide_eq_false hp0
      rw [Algorithm.checkRLERule]
      simp only [hdec_hp0, Bool.false_and, Bool.false_eq_true, ↓reduceIte, p0,
        checkRLERule_part2_val, checkRLERule_part3_val,
        Algorithm.birth3Mask, Algorithm.survival23Mask]
    refine ⟨st', ?_, hjh2, hhp2⟩
    rw [hret_eq]
    (conv => lhs; arg 5; arg 3; change locs0)
    rw [h0_37, h37_79]
    exact hrun2

theorem checkRLERule_equiv (bytes : ByteArray) (pos limit : UInt32) (bytesAddr : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = [])
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hlim : limit.toNat ≤ bytes.data.size) (hlim31 : limit.toNat < 2 ^ 31) :
    ∃ st', runJvmRes 250 f_Algorithm_checkRLERule_prog
        ⟨0, [], setLocal (setLocal (setLocal (fun (_ : Nat) => (.null : JvmVal))
          0 (.heapRef bytesAddr)) 1 (.i32 pos)) 2 (.i32 limit), jh, hp⟩ =
        some (.i32 (Algorithm.checkRLERule bytes pos limit), st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  rcases checkRLERule_part1 (f := 250) bytes pos limit bytesAddr jh hp
      (by omega) hstat hbytes hlim hlim31 with ⟨st', hrun, hjh, hhp⟩
  exact ⟨st', runJvmRes_of_runJvmResFast0 _ _ _ _ rfl hrun, hjh, hhp⟩

end CheckRLERule

/-! #### 3. `parseRLEHeader___lam__0`, `parseRLEHeader___lam__1`, `parseRLEHeader` -/

private theorem runJvmResFast_areturn {f pc : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.areturn :: rest) ⟨pc, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  unfold runJvmResFast; rw [Jvm.runJvmResFast.eq_def]; rfl

private theorem runJvmResFast_istore {f pc idx : Nat} {prog rest : List JvmInstr} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.istore idx :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, setLocal locs idx (.i32 v), jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_iload {f pc idx : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.iload idx :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_aconstNull {f pc : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.aconstNull :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .null :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_ldcStr {f pc : Nat} {s : String} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.ldcStr s :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .str s :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem u8_eq_of_toNat_eq {a b : UInt8} (h : a.toNat = b.toNat) : a = b := by
  cases a with | ofBitVec ab =>
  cases b with | ofBitVec bb =>
  simp only [UInt8.toNat] at h
  congr 1; exact BitVec.eq_of_toNat_eq h

private theorem runJvmResFast_aconstNull_areturn {f pc : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 2) prog pc (.aconstNull :: .areturn :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      some (.null, ⟨pc + 1, .null :: stk, locs, jh, hp⟩) := by
  rw [show f + 2 = (f + 1) + 1 from rfl, runJvmResFast_aconstNull, runJvmResFast_areturn]

private theorem runJvmResFast_nop_local {f pc : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.nop :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_iadd_local {f pc : Nat} {prog rest : List JvmInstr} {a b : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.iadd :: rest) ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 (a + b) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_isub_local {f pc : Nat} {prog rest : List JvmInstr} {a b : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.isub :: rest) ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 (a - b) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem stepStatic_compareUnsigned_local {pc : Nat} {a b : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩
      "java/lang/Integer" "compareUnsigned" "(II)I" =
      .inl (some ⟨pc + 1, .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: stk,
        locs, jh, hp⟩) := rfl

private theorem stepStatic_ubyteCtor_local {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩ "kotlin/UByte" "constructor-impl" "(B)B" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

private theorem stepStatic_uintBox_local {pc : Nat} {v : UInt32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 v :: stk, locs, jh, hp⟩ "kotlin/UInt" "box-impl" "(I)Lkotlin/UInt;" =
      .inl (some ⟨pc + 1, .boxedUInt v :: stk, locs, jh, hp⟩) := rfl

private theorem stepStatic_parseRLEHeader_lam0_heap
    {pc : Nat} {ch pos limit : UInt32} {addr : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .i32 ch :: .i32 pos :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEHeader___lam__0-XwsRtWc" "([BIIB)Lkotlin/UInt;" =
      let p' := Algorithm.skipSpaces ⟨elems⟩ pos limit
      let res :=
        if p' < limit && elems[p'.toNat]! == ch.toUInt8 then
          .boxedUInt (p' + 1)
        else .null
      .inl (some ⟨pc + 1, res :: rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 ch :: .i32 pos :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEHeader___lam__0-XwsRtWc" "([BIIB)Lkotlin/UInt;" =
      match decodeBytes ⟨pc, .i32 ch :: .i32 pos :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩
          (.heapRef addr) with
      | some bytes =>
        let p' := Algorithm.skipSpaces bytes pos limit
        let res :=
          if p' < limit && bytes.data[p'.toNat]! == ch.toUInt8 then
            .boxedUInt (p' + 1)
          else .null
        .inl (some ⟨pc + 1, res :: rest, locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn]; simp only [decodeBytes, hget]

private theorem stepStatic_parseRLEHeader_lam1_heap
    {pc : Nat} {pos limit : UInt32} {addr : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .i32 pos :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEHeader___lam__1-BltQuoY" "([BII)Lkotlin/UInt;" =
      let p' := Algorithm.skipSpaces ⟨elems⟩ pos limit
      let res := match Algorithm.parseUInt32At ⟨elems⟩ p' limit with
        | some r => .boxedUInt r.next
        | none => .null
      .inl (some ⟨pc + 1, res :: rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 pos :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEHeader___lam__1-BltQuoY" "([BII)Lkotlin/UInt;" =
      match decodeBytes ⟨pc, .i32 pos :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩
          (.heapRef addr) with
      | some bytes =>
        let p' := Algorithm.skipSpaces bytes pos limit
        let res := match Algorithm.parseUInt32At bytes p' limit with
          | some r => .boxedUInt r.next
          | none => .null
        .inl (some ⟨pc + 1, res :: rest, locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn]; simp only [decodeBytes, hget]

private theorem lam0_h0_11 (bytes : ByteArray) (limit pos : UInt32) (ch : UInt8)
    (bytesAddr : Nat) (objs : Array (Jvm.HeapObj AlgExt))
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hbytes : (⟨objs, []⟩ : Jvm.JvmHeap AlgExt).get? bytesAddr = some (.byteArray bytes.data)) :
    let p' := Algorithm.skipSpaces bytes pos limit
    let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (fun _ => .null)
      0 (.heapRef bytesAddr)) 1 (.i32 limit)) 2 (.i32 pos)) 3 (.i32 ch.toUInt32)
    runJvmResFast 35 f_Algorithm_parseRLEHeader___lam__0_prog 0
        f_Algorithm_parseRLEHeader___lam__0_prog ⟨0, [], locs0, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast 24 f_Algorithm_parseRLEHeader___lam__0_prog 11
        (.iflt 14 :: f_Algorithm_parseRLEHeader___lam__0_prog.drop 12)
        ⟨11, [.i32 (if p' == limit then 0 else if p' < limit then 4294967295 else 1)],
          setLocal locs0 4 (.i32 p'), ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
  intro p' locs0
  split_res_fuel 12
  conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_parseRLEHeader___lam__0_prog)]
  step_drop 3
  rw [runJvmResFast_aload]; norm_res_fuel
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  (conv => lhs; arg 5; arg 2; simp [locs0, setLocal])
  rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
  norm_res_fuel
  step_drop 4
  rw [runJvmResFast_aload]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  (conv => lhs; arg 5; arg 2; simp [locs0, setLocal])
  rw [runJvmResFast_invokestatic_step (stepStatic_skipSpaces_heap (by decide) hbytes)]
  norm_res_fuel
  step_drop 5
  rw [runJvmResFast_istore]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  (conv => lhs; arg 5; arg 2; simp [locs0, setLocal])
  rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_local]

private theorem lam0_h11_19 (bytes : ByteArray) (limit pos : UInt32) (ch : UInt8)
    (bytesAddr : Nat) (objs : Array (Jvm.HeapObj AlgExt))
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes)
    (hbytes : (⟨objs, []⟩ : Jvm.JvmHeap AlgExt).get? bytesAddr = some (.byteArray bytes.data))
    (hp' : Algorithm.skipSpaces bytes pos limit < limit)
    (hp'_slt : (Algorithm.skipSpaces bytes pos limit).toBitVec.slt 0#32 = false)
    (hp'_lt_sz : (Algorithm.skipSpaces bytes pos limit).toNat < bytes.data.size) :
    let p' := Algorithm.skipSpaces bytes pos limit
    let b := bytes.get! p'.toNat
    let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (fun _ => .null)
      0 (.heapRef bytesAddr)) 1 (.i32 limit)) 2 (.i32 pos)) 3 (.i32 ch.toUInt32)
    runJvmResFast 24 f_Algorithm_parseRLEHeader___lam__0_prog 11
        (.iflt 14 :: f_Algorithm_parseRLEHeader___lam__0_prog.drop 12)
        ⟨11, [.i32 (if p' == limit then 0 else if p' < limit then 4294967295 else 1)],
          setLocal locs0 4 (.i32 p'), ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast 18 f_Algorithm_parseRLEHeader___lam__0_prog 19
        (.if_icmpeq 22 :: f_Algorithm_parseRLEHeader___lam__0_prog.drop 20)
        ⟨19, [.i32 ch.toUInt32, .i32 (u8Sext b)],
          setLocal locs0 4 (.i32 p'), ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
  intro p' b locs0
  split_res_fuel 8
  rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true hp')]
  norm_res_fuel
  step_drop 3
  rw [runJvmResFast_aload]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  (conv => lhs; arg 5; arg 2; simp [locs0, setLocal])
  rw [runJvmResFast_baload_byteArray (idx := p') hbytes hp'_slt hp'_lt_sz]; norm_res_fuel
  step_drop 3
  rw [runJvmResFast_invokestatic_step stepStatic_ubyteCtor_local]; norm_res_fuel
  rw [runJvmResFast_iload]; norm_res_fuel
  (conv => lhs; arg 5; arg 2; simp [locs0, setLocal])
  rw [byteArray_get_eq_getBang bytes hp'_lt_sz]
  dsimp only [b, p']
  congr 2

theorem parseRLEHeader_lam0_equiv (bytes : ByteArray) (limit pos : UInt32) (ch : UInt8)
    (bytesAddr : Nat) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = [])
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hlim : limit.toNat ≤ bytes.data.size) (hlim31 : limit.toNat < 2 ^ 31)
    (hch : ch.toNat < 128) :
    let p' := Algorithm.skipSpaces bytes pos limit
    let expected :=
      if p' < limit && bytes.get! p'.toNat == ch then .boxedUInt (p' + 1) else .null
    ∃ st', runJvmRes 35 f_Algorithm_parseRLEHeader___lam__0_prog
        ⟨0, [], setLocal (setLocal (setLocal (setLocal (fun (_ : Nat) => (.null : JvmVal))
          0 (.heapRef bytesAddr)) 1 (.i32 limit)) 2 (.i32 pos)) 3 (.i32 ch.toUInt32), jh, hp⟩ =
        some (expected, st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  intro p' expected
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (fun _ => .null)
    0 (.heapRef bytesAddr)) 1 (.i32 limit)) 2 (.i32 pos)) 3 (.i32 ch.toUInt32)
  have h0_11 := lam0_h0_11 bytes limit pos ch bytesAddr objs ar u64 asc hbytes
  by_cases hp' : p' < limit
  · have hp'_toNat : p'.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hp'
    have hp'_slt : p'.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
    have hp'_lt_sz : p'.toNat < bytes.data.size := by omega
    let b := bytes.get! p'.toNat
    have h11_19 := lam0_h11_19 bytes limit pos ch bytesAddr objs ar u64 asc hbytes hp' hp'_slt hp'_lt_sz
    by_cases hbc : b = ch
    · have hu : u8Sext b = ch.toUInt32 := u8Sext_eq_u32 (by simp [hbc]) hch
      have hexp : expected = .boxedUInt (p' + 1) := by simp [expected, hp', b, hbc]
      apply Exists.intro
      constructor
      · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
        rw [hexp, h0_11, h11_19]
        split_res_fuel 7
        rw [runJvmResFast_if_icmpeq_branch hu]; norm_res_fuel
        step_drop 6
        rw [runJvmResFast_iload]; norm_res_fuel
        simp only [setLocal, ↓reduceIte]
        rw [runJvmResFast_iconst]; norm_res_fuel
        rw [runJvmResFast_iadd_local]; norm_res_fuel
        rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
        rw [runJvmResFast_invokestatic_step stepStatic_uintBox_local]; norm_res_fuel
        rw [runJvmResFast_areturn]
      · constructor <;> rfl
    · have hne : (u8Sext b == ch.toUInt32) = false :=
        u8Sext_beq_false b ch.toUInt32 (fun h => hbc (u8_eq_of_toNat_eq (by
          simpa [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] using h))) hch
      have hbc_f : (b == ch) = false := beq_false_of_ne hbc
      have hexp : expected = .null := by simp [expected, hp', b, hbc_f]
      apply Exists.intro
      constructor
      · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
        rw [hexp, h0_11, h11_19]
        split_res_fuel 3
        rw [runJvmResFast_if_icmpeq_fallthrough hne]; norm_res_fuel
        step_drop 2
        rw [runJvmResFast_aconstNull_areturn]
      · constructor <;> rfl
  · have hexp : expected = .null := by simp [expected, hp']
    apply Exists.intro
    constructor
    · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      rw [hexp, h0_11]
      split_res_fuel 3
      rw [runJvmResFast_iflt_fallthrough (by rw [compareUnsigned_slt_zero]; exact decide_eq_false hp')]
      norm_res_fuel
      step_drop 2
      rw [runJvmResFast_aconstNull_areturn]
    · constructor <;> rfl

theorem parseRLEHeader_lam1_equiv (bytes : ByteArray) (limit pos : UInt32) (bytesAddr : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = [])
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data)) :
    let p' := Algorithm.skipSpaces bytes pos limit
    let expected := match Algorithm.parseUInt32At bytes p' limit with
      | some r => .boxedUInt r.next
      | none => .null
    ∃ st', runJvmRes 60 f_Algorithm_parseRLEHeader___lam__1_prog
        ⟨0, [], setLocal (setLocal (setLocal (fun (_ : Nat) => (.null : JvmVal))
          0 (.heapRef bytesAddr)) 1 (.i32 limit)) 2 (.i32 pos), jh, hp⟩ =
        some (expected, st') ∧
      HeapExtends jh st'.jvmHeap ∧ st'.heap = hp := by
  intro p' expected
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (fun _ => .null)
    0 (.heapRef bytesAddr)) 1 (.i32 limit)) 2 (.i32 pos)
  let jh0 : Jvm.JvmHeap AlgExt := ⟨objs, []⟩
  let optPair : Option (JvmVal × JvmVal) :=
    (Algorithm.parseUInt32At bytes p' limit).map fun r =>
      (JvmVal.boxedUInt r.val, JvmVal.boxedUInt r.next)
  let pairRes := encodeOptScalarPair jh0 optPair
  let jh1 := pairRes.2
  let locs1 := setLocal (setLocal locs0 3 (.i32 p')) 4 pairRes.1
  have h0_12 : runJvmResFast 60 f_Algorithm_parseRLEHeader___lam__1_prog 0
      f_Algorithm_parseRLEHeader___lam__1_prog ⟨0, [], locs0, jh0, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast 48 f_Algorithm_parseRLEHeader___lam__1_prog 12
        (.astore 4 :: f_Algorithm_parseRLEHeader___lam__1_prog.drop 13)
        ⟨12, [pairRes.1], setLocal locs0 3 (.i32 p'), jh1, ⟨ar, u64, asc⟩⟩ := by
    split_res_fuel 13
    conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_parseRLEHeader___lam__1_prog)]
    step_drop 3
    step_res_block 2
    (conv => lhs; arg 5; arg 2; simp only [locs0, setLocal])
    rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
    norm_res_fuel
    step_drop 4
    step_res_block 3
    (conv => lhs; arg 5; arg 2; simp only [locs0, setLocal])
    rw [runJvmResFast_invokestatic_step (stepStatic_skipSpaces_heap (by decide) hbytes)]
    norm_res_fuel
    step_drop 5
    step_res_block 4
    (conv => lhs; arg 5; arg 2; simp only [locs0, setLocal])
    rw [runJvmResFast_invokestatic_step (stepStatic_parseUInt32At_heap hbytes)]; norm_res_fuel
    rfl
  cases hparse : Algorithm.parseUInt32At bytes p' limit with
  | none =>
    have hpair1 : pairRes.1 = .heapRef jh0.objects.size := by
      simp [pairRes, optPair, hparse, encodeOptScalarPair, Jvm.JvmHeap.alloc]
    have hjh1_get : jh1.get? jh0.objects.size = some (.objArray "java/lang/Object" #[.boxedInt 0]) := by
      simp only [jh1, pairRes, optPair, hparse, encodeOptScalarPair]
      exact jvmHeap_get?_alloc_self _ _
    have hext : HeapExtends jh0 jh1 := by
      simp only [jh1, pairRes, optPair, hparse, encodeOptScalarPair]
      exact heapExtends_alloc _ _
    have hexp : expected = .null := by simp [expected, hparse]
    apply Exists.intro
    constructor
    · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      rw [hexp, h0_12]
      split_res_fuel 17
      step_drop 13
      rw [hpair1]
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_checkcast_objArray hjh1_get (Or.inl rfl)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_aaload hjh1_get (by decide) (by decide)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_tableswitch]; norm_res_fuel
      dsimp only [Jvm.tableswitchTarget]
      step_drop 2
      rw [runJvmResFast_aconstNull_areturn]
    · exact ⟨hext, rfl⟩
  | some r =>
    let innerObj : Jvm.HeapObj AlgExt := .objArray "java/lang/Object"
      #[.boxedInt 0, .boxedUInt r.val, .null, .null, .null, .boxedUInt r.next]
    let jhInner := (jh0.alloc innerObj).2
    let innerAddr := jh0.objects.size
    let outerObj : Jvm.HeapObj AlgExt := .objArray "java/lang/Object"
      #[.boxedInt 1, .heapRef innerAddr]
    have hpair1 : pairRes.1 = .heapRef jhInner.objects.size := by
      simp [pairRes, optPair, hparse, encodeOptScalarPair, Jvm.JvmHeap.alloc, jhInner]
    have hext0i : HeapExtends jh0 jhInner := heapExtends_alloc _ _
    have hextio : HeapExtends jhInner jh1 := by
      simp only [jh1, pairRes, optPair, hparse, encodeOptScalarPair]
      exact heapExtends_alloc _ _
    have hext : HeapExtends jh0 jh1 := heapExtends_trans hext0i hextio
    have hjh1_outer : jh1.get? jhInner.objects.size = some (.objArray "java/lang/Object"
        #[.boxedInt 1, .heapRef innerAddr]) := by
      simp only [jh1, pairRes, optPair, hparse, encodeOptScalarPair]
      exact jvmHeap_get?_alloc_self _ _
    have hjh1_inner : jh1.get? innerAddr = some (.objArray "java/lang/Object"
        #[.boxedInt 0, .boxedUInt r.val, .null, .null, .null, .boxedUInt r.next]) :=
      hextio innerAddr innerObj (jvmHeap_get?_alloc_self _ _)
    have hexp : expected = .boxedUInt r.next := by simp [expected, hparse]
    apply Exists.intro
    constructor
    · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      rw [hexp, h0_12]
      step_drop 13
      rw [hpair1]
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_checkcast_objArray hjh1_outer (Or.inl rfl)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_aaload (idx := 0) hjh1_outer (by decide) (by simp)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_tableswitch]; norm_res_fuel
      dsimp only [Jvm.tableswitchTarget]
      step_drop 18
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_checkcast_objArray hjh1_outer (Or.inl rfl)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_aaload (idx := 1) hjh1_outer (by decide) (by simp)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_checkcast_objArray hjh1_inner (Or.inl rfl)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_aaload (idx := 5) hjh1_inner (by decide) (by simp)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
      rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
      step_drop 8
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_checkcast_boxedUInt (Or.inl rfl)]; norm_res_fuel
      conv => lhs; rw [runJvmResFast_invokevirtual_step (by rfl)]
      norm_res_fuel
      conv => lhs; rw [runJvmResFast_invokestatic_step stepStatic_uintBox]
      norm_res_fuel
      rw [runJvmResFast_areturn]
    · exact ⟨hext, rfl⟩

private theorem expectCond_eq (c1 c2 : Bool) (v : UInt32) (h : c1 = c2) :
    (if c1 = true then (JvmVal.boxedUInt v : JvmVal) else JvmVal.null) =
    (match (if c2 = true then some v else none) with
      | some r => (JvmVal.boxedUInt r : JvmVal) | none => JvmVal.null) := by
  cases c1 <;> cases c2 <;> simp_all

private theorem parseRLEHeader_unboxUInt {f pc t1 t2 : Nat} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 10 ≤ f) (htne : t1 ≠ t2)
    (hdrop : f_Algorithm_parseRLEHeader_prog.drop pc =
      .astore t1 :: .iconst 0 :: .istore t2 :: .aload t1 ::
      .instanceof "java/lang/Integer" :: .ifeq (pc + 11) ::
      .aload t1 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .goto (pc + 13) :: .aload t1 :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      f_Algorithm_parseRLEHeader_prog.drop (pc + 13)) :
    ∃ locs',
      runJvmResFast f f_Algorithm_parseRLEHeader_prog pc (f_Algorithm_parseRLEHeader_prog.drop pc)
        ⟨pc, .boxedUInt v :: stk, locs, jh, hp⟩ =
        runJvmResFast (f - 8) f_Algorithm_parseRLEHeader_prog (pc + 13)
          (f_Algorithm_parseRLEHeader_prog.drop (pc + 13))
          ⟨pc + 13, .i32 v :: stk, locs', jh, hp⟩ ∧
      (∀ k, k ≠ t1 → k ≠ t2 → locs' k = locs k) := by
  rcases hp with ⟨ar, u64, asc⟩
  apply Exists.intro (setLocal (setLocal locs t1 (.boxedUInt v)) t2 (.i32 0))
  constructor
  · rw [hdrop]
    split_res_fuel 9
    rw [runJvmResFast_astore, runJvmResFast_iconst, runJvmResFast_istore, runJvmResFast_aload]
    norm_res_fuel
    (conv => lhs; arg 5; arg 2; simp only [setLocal, beq_iff_eq, htne, ↓reduceIte])
    rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
    have hdrop11 : f_Algorithm_parseRLEHeader_prog.drop (pc + 11) =
        .aload t1 :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
        f_Algorithm_parseRLEHeader_prog.drop (pc + 13) := by
      have h11 : f_Algorithm_parseRLEHeader_prog.drop (pc + 11) =
          (f_Algorithm_parseRLEHeader_prog.drop pc).drop 11 := by
        rw [List.drop_drop, Nat.add_comm]
      rw [h11, hdrop]; rfl
    rw [hdrop11]
    rw [runJvmResFast_aload]; norm_res_fuel
    (conv => lhs; arg 5; arg 2; simp only [setLocal, beq_iff_eq, htne, ↓reduceIte])
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [show f - 9 + 1 = f - 8 from by omega]
  · intro k h1 h2; simp [setLocal, h1, h2]

private theorem parseRLEHeader_stepExpectChar {f pc src t1 t2 dst : Nat} {ch : UInt8}
    {bytes : ByteArray} {bytesAddr : Nat} {limit : UInt32} {optPos : Option UInt32}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 35 ≤ f) (ht1 : 2 ≤ t1) (ht2 : 2 ≤ t2) (hdst : 2 ≤ dst) (htne : t1 ≠ t2)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (h0 : locs 0 = .heapRef bytesAddr) (h1 : locs 1 = .i32 limit)
    (hsrc : locs src = match optPos with | some p => .boxedUInt p | none => .null)
    (hdrop : f_Algorithm_parseRLEHeader_prog.drop pc =
      .aload src :: .ifnonnull (pc + 4) :: .iconst 2 :: .ireturn ::
      .aload 0 :: .iload 1 :: .aload src ::
      .astore t1 :: .iconst 0 :: .istore t2 :: .aload t1 ::
      .instanceof "java/lang/Integer" :: .ifeq (pc + 18) ::
      .aload t1 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .goto (pc + 20) :: .aload t1 :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .iconst ch.toUInt32 ::
      .invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEHeader___lam__0-XwsRtWc" "([BIIB)Lkotlin/UInt;" ::
      .astore dst :: f_Algorithm_parseRLEHeader_prog.drop (pc + 23)) :
    match optPos with
    | none =>
      ∃ st', runJvmResFast f f_Algorithm_parseRLEHeader_prog pc
          (f_Algorithm_parseRLEHeader_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          some (.i32 2, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp
    | some p =>
      let q := Algorithm.skipSpaces bytes p limit
      let nextOpt : Option UInt32 :=
        if q < limit && bytes.get! q.toNat == ch then some (q + 1) else none
      ∃ locs',
        runJvmResFast f f_Algorithm_parseRLEHeader_prog pc
            (f_Algorithm_parseRLEHeader_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          runJvmResFast (f - 16) f_Algorithm_parseRLEHeader_prog (pc + 23)
            (f_Algorithm_parseRLEHeader_prog.drop (pc + 23)) ⟨pc + 23, [], locs', jh, hp⟩ ∧
        locs' 0 = .heapRef bytesAddr ∧ locs' 1 = .i32 limit ∧
        locs' dst = (match nextOpt with | some r => .boxedUInt r | none => .null) := by
  have h20 : f_Algorithm_parseRLEHeader_prog.drop (pc + 7 + 13) =
      .iconst ch.toUInt32 ::
      .invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEHeader___lam__0-XwsRtWc" "([BIIB)Lkotlin/UInt;" ::
      .astore dst :: f_Algorithm_parseRLEHeader_prog.drop (pc + 23) := by
    have hx : f_Algorithm_parseRLEHeader_prog.drop (pc + 7 + 13) =
        (f_Algorithm_parseRLEHeader_prog.drop pc).drop 20 := by
      rw [List.drop_drop]
    rw [hx, hdrop]; rfl
  have hdrop_unbox : f_Algorithm_parseRLEHeader_prog.drop (pc + 7) =
      .astore t1 :: .iconst 0 :: .istore t2 :: .aload t1 ::
      .instanceof "java/lang/Integer" :: .ifeq (pc + 7 + 11) ::
      .aload t1 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .goto (pc + 7 + 13) :: .aload t1 :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      f_Algorithm_parseRLEHeader_prog.drop (pc + 7 + 13) := by
    have h7 : f_Algorithm_parseRLEHeader_prog.drop (pc + 7) =
        (f_Algorithm_parseRLEHeader_prog.drop pc).drop 7 := by rw [List.drop_drop, Nat.add_comm]
    rw [h7, hdrop, h20]
    simp only [List.drop_succ_cons, List.drop_zero,
      show pc + 18 = pc + 7 + 11 from by omega,
      show pc + 20 = pc + 7 + 13 from by omega]
  cases optPos with
  | none =>
    apply Exists.intro
    constructor
    · rw [hdrop]
      split_res_fuel 5
      rw [runJvmResFast_aload]; norm_res_fuel
      rw [hsrc, runJvmResFast_ifnonnull_fallthrough]; norm_res_fuel
      rw [runJvmResFast_iconst_ireturn]
    · constructor <;> rfl
  | some p =>
    dsimp only
    rcases parseRLEHeader_unboxUInt (f := f - 5) (pc := pc + 7) (t1 := t1) (t2 := t2)
        (v := p) (stk := [.i32 limit, .heapRef bytesAddr])
        (locs := locs) (jh := jh) (hp := hp) (by omega) htne hdrop_unbox with
      ⟨locs1, hunbox, hlocs1⟩
    rcases hp with ⟨ar, u64, asc⟩
    let q := Algorithm.skipSpaces bytes p limit
    let nextOpt : Option UInt32 :=
      if q < limit && bytes.get! q.toNat == ch then some (q + 1) else none
    let resVal : JvmVal := match nextOpt with | some r => .boxedUInt r | none => .null
    refine ⟨setLocal locs1 dst resVal, ?_, ?_, ?_, by
        simp only [setLocal, ↓reduceIte]; rfl⟩
    · rw [hdrop]
      split_res_fuel 6
      rw [runJvmResFast_aload]; norm_res_fuel
      rw [hsrc, runJvmResFast_ifnonnull_branch rfl]; norm_res_fuel
      have hdrop4 : f_Algorithm_parseRLEHeader_prog.drop (pc + 4) =
          .aload 0 :: .iload 1 :: .aload src :: f_Algorithm_parseRLEHeader_prog.drop (pc + 7) := by
        have h4 : f_Algorithm_parseRLEHeader_prog.drop (pc + 4) =
            (f_Algorithm_parseRLEHeader_prog.drop pc).drop 4 := by rw [List.drop_drop, Nat.add_comm]
        have h7 : f_Algorithm_parseRLEHeader_prog.drop (pc + 7) =
            (f_Algorithm_parseRLEHeader_prog.drop pc).drop 7 := by rw [List.drop_drop, Nat.add_comm]
        rw [h4, h7, hdrop]; rfl
      rw [hdrop4]
      split_res_fuel 4
      rw [runJvmResFast_aload, runJvmResFast_iload, runJvmResFast_aload]; norm_res_fuel
      (conv => lhs; arg 5; arg 2; simp only [h0, h1, hsrc])
      rw [show f - 6 + 4 - 4 + 1 = f - 5 from by omega,
        show pc + 4 + 1 + 1 + 1 = pc + 7 from by omega, hunbox]
      rw [h20]
      split_res_fuel 4
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (stepStatic_parseRLEHeader_lam0_heap hbytes)]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [show f - 5 - 8 - 4 + 1 = f - 16 from by omega,
        show pc + 7 + 13 + 1 + 1 + 1 = pc + 23 from by omega]
      have hch_rt : ch.toUInt32.toUInt8 = ch := u8_eq_of_toNat_eq (by
        rw [UInt32.toNat_toUInt8, UInt8.toNat_toUInt32]
        exact Nat.mod_eq_of_lt (UInt8.toNat_lt ch))
      dsimp only [resVal, nextOpt, q]
      simp only [hch_rt]
      exact congrArg (fun x => runJvmResFast (f - 16) f_Algorithm_parseRLEHeader_prog (pc + 23)
          (f_Algorithm_parseRLEHeader_prog.drop (pc + 23)) ⟨pc + 23, [], setLocal locs1 dst x, jh, ⟨ar, u64, asc⟩⟩)
        (expectCond_eq _ _ _ rfl)
    · simp only [setLocal, ite_eq_right (by omega : ¬0 = dst), hlocs1 0 (by omega) (by omega), h0]
    · simp only [setLocal, ite_eq_right (by omega : ¬1 = dst), hlocs1 1 (by omega) (by omega), h1]

private theorem parseRLEHeader_stepExpectNum {f pc src t1 t2 dst : Nat}
    {bytes : ByteArray} {bytesAddr : Nat} {limit : UInt32} {optPos : Option UInt32}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 35 ≤ f) (ht1 : 2 ≤ t1) (ht2 : 2 ≤ t2) (hdst : 2 ≤ dst) (htne : t1 ≠ t2)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (h0 : locs 0 = .heapRef bytesAddr) (h1 : locs 1 = .i32 limit)
    (hsrc : locs src = match optPos with | some p => .boxedUInt p | none => .null)
    (hdrop : f_Algorithm_parseRLEHeader_prog.drop pc =
      .aload src :: .ifnonnull (pc + 4) :: .iconst 2 :: .ireturn ::
      .aload 0 :: .iload 1 :: .aload src ::
      .astore t1 :: .iconst 0 :: .istore t2 :: .aload t1 ::
      .instanceof "java/lang/Integer" :: .ifeq (pc + 18) ::
      .aload t1 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .goto (pc + 20) :: .aload t1 :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      .invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEHeader___lam__1-BltQuoY" "([BII)Lkotlin/UInt;" ::
      .astore dst :: f_Algorithm_parseRLEHeader_prog.drop (pc + 22)) :
    match optPos with
    | none =>
      ∃ st', runJvmResFast f f_Algorithm_parseRLEHeader_prog pc
          (f_Algorithm_parseRLEHeader_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          some (.i32 2, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp
    | some p =>
      let q := Algorithm.skipSpaces bytes p limit
      let nextOpt : Option UInt32 :=
        match Algorithm.parseUInt32At bytes q limit with | some r => some r.next | none => none
      ∃ locs',
        runJvmResFast f f_Algorithm_parseRLEHeader_prog pc
            (f_Algorithm_parseRLEHeader_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          runJvmResFast (f - 15) f_Algorithm_parseRLEHeader_prog (pc + 22)
            (f_Algorithm_parseRLEHeader_prog.drop (pc + 22)) ⟨pc + 22, [], locs', jh, hp⟩ ∧
        locs' 0 = .heapRef bytesAddr ∧ locs' 1 = .i32 limit ∧
        locs' dst = (match nextOpt with | some r => .boxedUInt r | none => .null) := by
  have h20 : f_Algorithm_parseRLEHeader_prog.drop (pc + 7 + 13) =
      .invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEHeader___lam__1-BltQuoY" "([BII)Lkotlin/UInt;" ::
      .astore dst :: f_Algorithm_parseRLEHeader_prog.drop (pc + 22) := by
    have hx : f_Algorithm_parseRLEHeader_prog.drop (pc + 7 + 13) =
        (f_Algorithm_parseRLEHeader_prog.drop pc).drop 20 := by
      rw [List.drop_drop]
    rw [hx, hdrop]; rfl
  have hdrop_unbox : f_Algorithm_parseRLEHeader_prog.drop (pc + 7) =
      .astore t1 :: .iconst 0 :: .istore t2 :: .aload t1 ::
      .instanceof "java/lang/Integer" :: .ifeq (pc + 7 + 11) ::
      .aload t1 :: .checkcast "java/lang/Number" ::
      .invokevirtual "java/lang/Number" "intValue" "()I" ::
      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
      .goto (pc + 7 + 13) :: .aload t1 :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      f_Algorithm_parseRLEHeader_prog.drop (pc + 7 + 13) := by
    have h7 : f_Algorithm_parseRLEHeader_prog.drop (pc + 7) =
        (f_Algorithm_parseRLEHeader_prog.drop pc).drop 7 := by rw [List.drop_drop, Nat.add_comm]
    rw [h7, hdrop, h20]
    simp only [List.drop_succ_cons, List.drop_zero,
      show pc + 18 = pc + 7 + 11 from by omega,
      show pc + 20 = pc + 7 + 13 from by omega]
  cases optPos with
  | none =>
    apply Exists.intro
    constructor
    · rw [hdrop]
      split_res_fuel 5
      rw [runJvmResFast_aload]; norm_res_fuel
      rw [hsrc, runJvmResFast_ifnonnull_fallthrough]; norm_res_fuel
      rw [runJvmResFast_iconst_ireturn]
    · constructor <;> rfl
  | some p =>
    dsimp only
    rcases parseRLEHeader_unboxUInt (f := f - 5) (pc := pc + 7) (t1 := t1) (t2 := t2)
        (v := p) (stk := [.i32 limit, .heapRef bytesAddr])
        (locs := locs) (jh := jh) (hp := hp) (by omega) htne hdrop_unbox with
      ⟨locs1, hunbox, hlocs1⟩
    rcases hp with ⟨ar, u64, asc⟩
    let q := Algorithm.skipSpaces bytes p limit
    let nextOpt : Option UInt32 :=
      match Algorithm.parseUInt32At bytes q limit with | some r => some r.next | none => none
    let resVal : JvmVal := match nextOpt with | some r => .boxedUInt r | none => .null
    refine ⟨setLocal locs1 dst resVal, ?_, ?_, ?_, by
        simp only [setLocal, ↓reduceIte]; rfl⟩
    · rw [hdrop]
      split_res_fuel 6
      rw [runJvmResFast_aload]; norm_res_fuel
      rw [hsrc, runJvmResFast_ifnonnull_branch rfl]; norm_res_fuel
      have hdrop4 : f_Algorithm_parseRLEHeader_prog.drop (pc + 4) =
          .aload 0 :: .iload 1 :: .aload src :: f_Algorithm_parseRLEHeader_prog.drop (pc + 7) := by
        have h4 : f_Algorithm_parseRLEHeader_prog.drop (pc + 4) =
            (f_Algorithm_parseRLEHeader_prog.drop pc).drop 4 := by rw [List.drop_drop, Nat.add_comm]
        have h7 : f_Algorithm_parseRLEHeader_prog.drop (pc + 7) =
            (f_Algorithm_parseRLEHeader_prog.drop pc).drop 7 := by rw [List.drop_drop, Nat.add_comm]
        rw [h4, h7, hdrop]; rfl
      rw [hdrop4]
      split_res_fuel 4
      rw [runJvmResFast_aload, runJvmResFast_iload, runJvmResFast_aload]; norm_res_fuel
      (conv => lhs; arg 5; arg 2; simp only [h0, h1, hsrc])
      rw [show f - 6 + 4 - 4 + 1 = f - 5 from by omega,
        show pc + 4 + 1 + 1 + 1 = pc + 7 from by omega, hunbox]
      rw [h20]
      split_res_fuel 3
      rw [runJvmResFast_invokestatic_step (stepStatic_parseRLEHeader_lam1_heap hbytes)]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [show f - 5 - 8 - 3 + 1 = f - 15 from by omega,
        show pc + 7 + 13 + 1 + 1 = pc + 22 from by omega]
      simp only [resVal, nextOpt, q]
      cases Algorithm.parseUInt32At bytes (Algorithm.skipSpaces bytes p limit) limit <;> rfl
    · simp only [setLocal, ite_eq_right (by omega : ¬0 = dst), hlocs1 0 (by omega) (by omega), h0]
    · simp only [setLocal, ite_eq_right (by omega : ¬1 = dst), hlocs1 1 (by omega) (by omega), h1]

private theorem parseRLEHeader_if_letter {f pc locIdx : Nat} {b ch : UInt8} {tgt : Nat}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 15 ≤ f) (hch : ch.toNat < 128) (hch32 : 32 ≤ ch.toNat)
    (hloc : locs locIdx = .i32 (u8Sext b))
    (hdrop : f_Algorithm_parseRLEHeader_prog.drop pc =
      .iload locIdx :: .iconst ch.toUInt32 :: .if_icmpeq tgt ::
      .iload locIdx :: .iconst (ch - 32).toUInt32 :: .if_icmpeq tgt ::
      .iconst 2 :: .ireturn :: f_Algorithm_parseRLEHeader_prog.drop (pc + 8)) :
    if Algorithm.isLetterByte b ch then
      runJvmResFast f f_Algorithm_parseRLEHeader_prog pc (f_Algorithm_parseRLEHeader_prog.drop pc)
        ⟨pc, [], locs, jh, hp⟩ =
        runJvmResFast (if b == ch then f - 3 else f - 6) f_Algorithm_parseRLEHeader_prog tgt
          (f_Algorithm_parseRLEHeader_prog.drop tgt) ⟨tgt, [], locs, jh, hp⟩
    else
      ∃ st', runJvmResFast f f_Algorithm_parseRLEHeader_prog pc
          (f_Algorithm_parseRLEHeader_prog.drop pc) ⟨pc, [], locs, jh, hp⟩ =
          some (.i32 2, st') ∧ st'.jvmHeap = jh ∧ st'.heap = hp := by
  have hsub_toNat : (ch - 32).toNat = ch.toNat - 32 := by
    rw [UInt8.toNat_sub, show (32 : UInt8).toNat = 32 from rfl]; omega
  have hch_lo : (ch - 32).toNat < 128 := by omega
  by_cases hlet : Algorithm.isLetterByte b ch = true
  · simp only [hlet, ↓reduceIte]
    have hcases : b = ch ∨ b = ch - 32 := by simpa [Algorithm.isLetterByte] using hlet
    rcases hcases with rfl | rfl
    · have hu : u8Sext b = b.toUInt32 := u8Sext_eq_u32 rfl hch
      have hbeq : (b == b) = true := beq_self_eq_true b
      simp only [hbeq, ↓reduceIte]
      rw [hdrop]
      split_res_fuel 4
      rw [runJvmResFast_iload, runJvmResFast_iconst]; norm_res_fuel
      (conv => lhs; arg 5; arg 2; simp only [hloc])
      rw [runJvmResFast_if_icmpeq_branch hu]; norm_res_fuel
      rw [show f - 4 + 1 = f - 3 from by omega]
    · by_cases heq : ch - 32 = ch
      · have : False := by
          have := congrArg UInt8.toNat heq
          omega
        contradiction
      · have hne1 : (u8Sext (ch - 32) == ch.toUInt32) = false :=
          u8Sext_beq_false (ch - 32) ch.toUInt32
            (by rw [hsub_toNat, UInt8.toNat_toUInt32]; omega) hch
        have hu2 : u8Sext (ch - 32) = (ch - 32).toUInt32 := u8Sext_eq_u32 rfl hch_lo
        have hbeq : (ch - 32 == ch) = false := beq_false_of_ne heq
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        rw [hdrop]
        split_res_fuel 7
        rw [runJvmResFast_iload, runJvmResFast_iconst]; norm_res_fuel
        (conv => lhs; arg 5; arg 2; simp only [hloc])
        rw [runJvmResFast_if_icmpeq_fallthrough hne1]; norm_res_fuel
        rw [runJvmResFast_iload, runJvmResFast_iconst]; norm_res_fuel
        (conv => lhs; arg 5; arg 2; simp only [hloc])
        rw [runJvmResFast_if_icmpeq_branch hu2]; norm_res_fuel
        rw [show f - 7 + 1 = f - 6 from by omega]
  · have hlet_f : Algorithm.isLetterByte b ch = false := Bool.eq_false_iff.mpr hlet
    simp only [hlet_f, Bool.false_eq_true, ↓reduceIte]
    have hne1 : (u8Sext b == ch.toUInt32) = false := u8Sext_beq_false b ch.toUInt32 (fun h => by
      have h1 : b.toNat = ch.toNat := by
        simpa [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] using h
      have h2 : b = ch := u8_eq_of_toNat_eq h1
      simp [Algorithm.isLetterByte, h2] at hlet_f) hch
    have hne2 : (u8Sext b == (ch - 32).toUInt32) = false := u8Sext_beq_false b (ch - 32).toUInt32
      (fun h => by
        have h1 : b.toNat = (ch - 32).toNat := by
          rw [UInt8.toNat_toUInt32] at h; exact h
        have h2 : b = ch - 32 := u8_eq_of_toNat_eq h1
        simp [Algorithm.isLetterByte, h2] at hlet_f) hch_lo
    apply Exists.intro
    constructor
    · rw [hdrop]
      split_res_fuel 9
      rw [runJvmResFast_iload, runJvmResFast_iconst]; norm_res_fuel
      (conv => lhs; arg 5; arg 2; simp only [hloc])
      rw [runJvmResFast_if_icmpeq_fallthrough hne1]; norm_res_fuel
      rw [runJvmResFast_iload, runJvmResFast_iconst]; norm_res_fuel
      (conv => lhs; arg 5; arg 2; simp only [hloc])
      rw [runJvmResFast_if_icmpeq_fallthrough hne2]; norm_res_fuel
      rw [runJvmResFast_iconst_ireturn]
    · constructor <;> rfl

theorem parseRLEHeader_equiv (bytes : ByteArray) (bytesAddr : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = [])
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hsz : bytes.data.size < 2 ^ 31) :
    ∃ st', runJvmRes 350 f_Algorithm_parseRLEHeader_prog
        ⟨0, [], setLocal (fun (_ : Nat) => (.null : JvmVal)) 0 (.heapRef bytesAddr), jh, hp⟩ =
        some (.i32 (Algorithm.parseRLEHeader bytes), st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  let jh0 : Jvm.JvmHeap AlgExt := ⟨objs, []⟩
  let hp0 : AlgHeap := ⟨ar, u64, asc⟩
  let limit : UInt32 := bytes.size.toUInt32
  have hlim_eq : limit.toNat = bytes.data.size := by
    simp only [limit, ByteArray.size, UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hlim31 : limit.toNat < 2 ^ 31 := by omega
  let expect (p : UInt32) (c : UInt8) : Option UInt32 :=
    let q := Algorithm.skipSpaces bytes p limit
    if q < limit && bytes.get! q.toNat == c then some (q + 1) else none
  let expectNum (p : UInt32) : Option UInt32 :=
    match Algorithm.parseUInt32At bytes (Algorithm.skipSpaces bytes p limit) limit with
    | some r => some r.next
    | none => none
  have h0_13 : runJvmResFast 350 f_Algorithm_parseRLEHeader_prog 0 f_Algorithm_parseRLEHeader_prog
      ⟨0, [], setLocal (fun _ => .null) 0 (.heapRef bytesAddr), jh0, hp0⟩ =
      runJvmResFast 337 f_Algorithm_parseRLEHeader_prog 13
        (f_Algorithm_parseRLEHeader_prog.drop 13)
        ⟨13, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef bytesAddr))
          1 (.i32 limit)) 2 (match expect 0 120 with | some r => .boxedUInt r | none => .null),
          jh0, hp0⟩ := by
    split_res_fuel 14
    conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_parseRLEHeader_prog)]
    step_drop 3
    step_res_block 2
    (conv => lhs; arg 5; arg 2; simp only [setLocal])
    rw [runJvmResFast_invokestatic_step (stepStatic_checkNotNullParameter rfl)]
    norm_res_fuel
    step_drop 2
    step_res_block 1
    rw [runJvmResFast_arraylength_byteArray hbytes]; norm_res_fuel
    step_drop 7
    step_res_block 1
    rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
    step_res_block 5
    (conv => lhs; arg 5; arg 2; simp only [setLocal])
    rw [runJvmResFast_invokestatic_step (stepStatic_parseRLEHeader_lam0_heap hbytes)]
    norm_res_fuel
    step_drop 2
    rw [runJvmResFast_astore]; norm_res_fuel
    have h13 : f_Algorithm_parseRLEHeader_prog.drop 13 =
        .aload 2 :: f_Algorithm_parseRLEHeader_prog.drop 14 := by
      unfold f_Algorithm_parseRLEHeader_prog; rfl
    rw [h13]
    dsimp only [expect]
    simp only [show (120 : UInt32).toUInt8 = (120 : UInt8) from by decide]
    exact congrArg (fun x => runJvmResFast 337 f_Algorithm_parseRLEHeader_prog 13
        (.aload 2 :: f_Algorithm_parseRLEHeader_prog.drop 14)
        ⟨13, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef bytesAddr)) 1 (.i32 limit)) 2 x, jh0, hp0⟩)
      (expectCond_eq _ _ _ rfl)
  let optHdr : Option UInt32 :=
    expect 0 120 >>= fun p1 =>
    expect p1 61 >>= fun p2 =>
    expectNum p2 >>= fun p3 =>
    expect p3 44 >>= fun p4 =>
    expect p4 121 >>= fun p5 =>
    expect p5 61 >>= fun p6 =>
    expectNum p6
  have hhdr_eq : Algorithm.parseRLEHeader bytes =
      match optHdr with
      | none => 2
      | some p =>
        let q := Algorithm.skipSpaces bytes p limit
        if q == limit then 0
        else match expect q 44 with
          | none => 2
          | some p1 =>
            let r := Algorithm.skipSpaces bytes p1 limit
            if r + 4 ≤ limit && limit - r ≥ 4 &&
                Algorithm.isLetterByte (bytes.get! r.toNat) 114 &&
                Algorithm.isLetterByte (bytes.get! (r + 1).toNat) 117 &&
                Algorithm.isLetterByte (bytes.get! (r + 2).toNat) 108 &&
                Algorithm.isLetterByte (bytes.get! (r + 3).toNat) 101 then
              match expect (r + 4) 61 with
              | none => 2
              | some p2 => Algorithm.checkRLERule bytes p2 limit
            else 2 := by
    rw [Algorithm.parseRLEHeader]
    dsimp only [optHdr, limit]
    simp only [Bind.bind, Option.bind_assoc]
    rfl
  rw [hhdr_eq]
  let locs0 := setLocal (setLocal (setLocal (fun (_ : Nat) => (.null : JvmVal)) 0 (.heapRef bytesAddr))
    1 (.i32 limit)) 2 (match expect 0 120 with | some r => .boxedUInt r | none => .null)
  cases he1 : expect 0 120 with
  | none =>
    have hopt : optHdr = none := by dsimp only [optHdr]; rw [he1]; rfl
    rw [hopt]; dsimp only
    have hs1 := parseRLEHeader_stepExpectChar (f := 337) (pc := 13) (src := 2) (t1 := 4) (t2 := 5)
      (dst := 3) (ch := 61) (bytes := bytes) (bytesAddr := bytesAddr) (limit := limit)
      (optPos := none) (locs := locs0) (jh := jh0) (hp := hp0) (by omega)
      (by decide) (by decide) (by decide) (by decide) hbytes (by simp [locs0, setLocal])
      (by simp [locs0, setLocal]) (by simp [locs0, setLocal, he1]) (by drop_prefix 23)
    rcases hs1 with ⟨st', hrun, hjh, hhp⟩
    refine ⟨st', ?_, hjh, hhp⟩
    apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    rw [h0_13]; exact hrun
  | some p1 =>
    have hs1 := parseRLEHeader_stepExpectChar (f := 337) (pc := 13) (src := 2) (t1 := 4) (t2 := 5)
      (dst := 3) (ch := 61) (bytes := bytes) (bytesAddr := bytesAddr) (limit := limit)
      (optPos := some p1) (locs := locs0) (jh := jh0) (hp := hp0) (by omega)
      (by decide) (by decide) (by decide) (by decide) hbytes (by simp [locs0, setLocal])
      (by simp [locs0, setLocal]) (by simp [locs0, setLocal, he1]) (by drop_prefix 23)
    rcases hs1 with ⟨locs1, hr1, hl1_0, hl1_1, hl1_3⟩
    change locs1 3 = match expect p1 61 with | some r => .boxedUInt r | none => .null at hl1_3
    cases he2 : expect p1 61 with
    | none =>
      have hopt : optHdr = none := by
        dsimp only [optHdr, Bind.bind, Option.bind]; rw [he1]; dsimp only; rw [he2]
      rw [hopt]; dsimp only
      have hs2 := parseRLEHeader_stepExpectNum (f := 321) (pc := 36) (src := 3) (t1 := 5) (t2 := 6)
        (dst := 4) (bytes := bytes) (bytesAddr := bytesAddr) (limit := limit)
        (optPos := none) (locs := locs1) (jh := jh0) (hp := hp0) (by omega)
        (by decide) (by decide) (by decide) (by decide) hbytes hl1_0 hl1_1
        (by rw [hl1_3, he2]) (by drop_prefix 22)
      rcases hs2 with ⟨st', hrun, hjh, hhp⟩
      refine ⟨st', ?_, hjh, hhp⟩
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      rw [h0_13, hr1]; exact hrun
    | some p2 =>
      have hs2 := parseRLEHeader_stepExpectNum (f := 321) (pc := 36) (src := 3) (t1 := 5) (t2 := 6)
        (dst := 4) (bytes := bytes) (bytesAddr := bytesAddr) (limit := limit)
        (optPos := some p2) (locs := locs1) (jh := jh0) (hp := hp0) (by omega)
        (by decide) (by decide) (by decide) (by decide) hbytes hl1_0 hl1_1
        (by rw [hl1_3, he2]) (by drop_prefix 22)
      rcases hs2 with ⟨locs2, hr2, hl2_0, hl2_1, hl2_4⟩
      change locs2 4 = match expectNum p2 with | some r => .boxedUInt r | none => .null at hl2_4
      cases he3 : expectNum p2 with
      | none =>
        have hopt : optHdr = none := by
          dsimp only [optHdr, Bind.bind, Option.bind]
          rw [he1]; dsimp only; rw [he2]; dsimp only; rw [he3]
        rw [hopt]; dsimp only
        have hs3 := parseRLEHeader_stepExpectChar (f := 306) (pc := 58) (src := 4) (t1 := 6) (t2 := 7)
          (dst := 5) (ch := 44) (bytes := bytes) (bytesAddr := bytesAddr) (limit := limit)
          (optPos := none) (locs := locs2) (jh := jh0) (hp := hp0) (by omega)
          (by decide) (by decide) (by decide) (by decide) hbytes hl2_0 hl2_1
          (by rw [hl2_4, he3]) (by drop_prefix 23)
        rcases hs3 with ⟨st', hrun, hjh, hhp⟩
        refine ⟨st', ?_, hjh, hhp⟩
        apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
        rw [h0_13, hr1, hr2]; exact hrun
      | some p3 =>
        have hs3 := parseRLEHeader_stepExpectChar (f := 306) (pc := 58) (src := 4) (t1 := 6) (t2 := 7)
          (dst := 5) (ch := 44) (bytes := bytes) (bytesAddr := bytesAddr) (limit := limit)
          (optPos := some p3) (locs := locs2) (jh := jh0) (hp := hp0) (by omega)
          (by decide) (by decide) (by decide) (by decide) hbytes hl2_0 hl2_1
          (by rw [hl2_4, he3]) (by drop_prefix 23)
        rcases hs3 with ⟨locs3, hr3, hl3_0, hl3_1, hl3_5⟩
        change locs3 5 = match expect p3 44 with | some r => .boxedUInt r | none => .null at hl3_5
        cases he4 : expect p3 44 with
        | none =>
          have hopt : optHdr = none := by
            dsimp only [optHdr, Bind.bind, Option.bind]
            rw [he1]; dsimp only; rw [he2]; dsimp only; rw [he3]; dsimp only; rw [he4]
          rw [hopt]; dsimp only
          have hs4 := parseRLEHeader_stepExpectChar (f := 290) (pc := 81) (src := 5) (t1 := 7) (t2 := 8)
            (dst := 6) (ch := 121) (bytes := bytes) (bytesAddr := bytesAddr) (limit := limit)
            (optPos := none) (locs := locs3) (jh := jh0) (hp := hp0) (by omega)
            (by decide) (by decide) (by decide) (by decide) hbytes hl3_0 hl3_1
            (by rw [hl3_5, he4]) (by drop_prefix 23)
          rcases hs4 with ⟨st', hrun, hjh, hhp⟩
          refine ⟨st', ?_, hjh, hhp⟩
          apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
          rw [h0_13, hr1, hr2, hr3]; exact hrun
        | some p4 =>
          have hs4 := parseRLEHeader_stepExpectChar (f := 290) (pc := 81) (src := 5) (t1 := 7) (t2 := 8)
            (dst := 6) (ch := 121) (bytes := bytes) (bytesAddr := bytesAddr) (limit := limit)
            (optPos := some p4) (locs := locs3) (jh := jh0) (hp := hp0) (by omega)
            (by decide) (by decide) (by decide) (by decide) hbytes hl3_0 hl3_1
            (by rw [hl3_5, he4]) (by drop_prefix 23)
          rcases hs4 with ⟨locs4, hr4, hl4_0, hl4_1, hl4_6⟩
          change locs4 6 = match expect p4 121 with | some r => .boxedUInt r | none => .null at hl4_6
          cases he5 : expect p4 121 with
          | none =>
            have hopt : optHdr = none := by
              dsimp only [optHdr, Bind.bind, Option.bind]
              rw [he1]; dsimp only; rw [he2]; dsimp only; rw [he3]; dsimp only
              rw [he4]; dsimp only; rw [he5]
            rw [hopt]; dsimp only
            have hs5 := parseRLEHeader_stepExpectChar (f := 274) (pc := 104) (src := 6) (t1 := 8) (t2 := 9)
              (dst := 7) (ch := 61) (bytes := bytes) (bytesAddr := bytesAddr) (limit := limit)
              (optPos := none) (locs := locs4) (jh := jh0) (hp := hp0) (by omega)
              (by decide) (by decide) (by decide) (by decide) hbytes hl4_0 hl4_1
              (by rw [hl4_6, he5]) (by drop_prefix 23)
            rcases hs5 with ⟨st', hrun, hjh, hhp⟩
            refine ⟨st', ?_, hjh, hhp⟩
            apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
            rw [h0_13, hr1, hr2, hr3, hr4]; exact hrun
          | some p5 =>
            have hs5 := parseRLEHeader_stepExpectChar (f := 274) (pc := 104) (src := 6) (t1 := 8) (t2 := 9)
              (dst := 7) (ch := 61) (bytes := bytes) (bytesAddr := bytesAddr) (limit := limit)
              (optPos := some p5) (locs := locs4) (jh := jh0) (hp := hp0) (by omega)
              (by decide) (by decide) (by decide) (by decide) hbytes hl4_0 hl4_1
              (by rw [hl4_6, he5]) (by drop_prefix 23)
            rcases hs5 with ⟨locs5, hr5, hl5_0, hl5_1, hl5_7⟩
            change locs5 7 = match expect p5 61 with | some r => .boxedUInt r | none => .null at hl5_7
            cases he6 : expect p5 61 with
            | none =>
              have hopt : optHdr = none := by
                dsimp only [optHdr, Bind.bind, Option.bind]
                rw [he1]; dsimp only; rw [he2]; dsimp only; rw [he3]; dsimp only
                rw [he4]; dsimp only; rw [he5]; dsimp only; rw [he6]
              rw [hopt]; dsimp only
              have hs6 := parseRLEHeader_stepExpectNum (f := 258) (pc := 127) (src := 7) (t1 := 9) (t2 := 10)
                (dst := 8) (bytes := bytes) (bytesAddr := bytesAddr) (limit := limit)
                (optPos := none) (locs := locs5) (jh := jh0) (hp := hp0) (by omega)
                (by decide) (by decide) (by decide) (by decide) hbytes hl5_0 hl5_1
                (by rw [hl5_7, he6]) (by drop_prefix 22)
              rcases hs6 with ⟨st', hrun, hjh, hhp⟩
              refine ⟨st', ?_, hjh, hhp⟩
              apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
              rw [h0_13, hr1, hr2, hr3, hr4, hr5]; exact hrun
            | some p6 =>
              have hs6 := parseRLEHeader_stepExpectNum (f := 258) (pc := 127) (src := 7) (t1 := 9) (t2 := 10)
                (dst := 8) (bytes := bytes) (bytesAddr := bytesAddr) (limit := limit)
                (optPos := some p6) (locs := locs5) (jh := jh0) (hp := hp0) (by omega)
                (by decide) (by decide) (by decide) (by decide) hbytes hl5_0 hl5_1
                (by rw [hl5_7, he6]) (by drop_prefix 22)
              rcases hs6 with ⟨locs6, hr6, hl6_0, hl6_1, hl6_8⟩
              change locs6 8 = match expectNum p6 with | some r => .boxedUInt r | none => .null at hl6_8
              cases he7 : expectNum p6 with
              | none =>
                have hopt : optHdr = none := by
                  dsimp only [optHdr, Bind.bind, Option.bind]
                  rw [he1]; dsimp only; rw [he2]; dsimp only; rw [he3]; dsimp only
                  rw [he4]; dsimp only; rw [he5]; dsimp only; rw [he6]; dsimp only; rw [he7]
                rw [hopt]; dsimp only
                apply Exists.intro
                constructor
                · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                  rw [h0_13, hr1, hr2, hr3, hr4, hr5, hr6]
                  have hdrop149 : f_Algorithm_parseRLEHeader_prog.drop 149 =
                      .aload 8 :: .ifnonnull 153 :: .iconst 2 :: .ireturn ::
                      f_Algorithm_parseRLEHeader_prog.drop 153 := by drop_prefix 4
                  rw [hdrop149]
                  split_res_fuel 5
                  rw [runJvmResFast_aload]; norm_res_fuel
                  rw [hl6_8, he7, runJvmResFast_ifnonnull_fallthrough]; norm_res_fuel
                  rw [runJvmResFast_iconst_ireturn]
                · constructor <;> rfl
              | some p7 =>
                have hopt : optHdr = some p7 := by
                  dsimp only [optHdr, Bind.bind, Option.bind]
                  rw [he1]; dsimp only; rw [he2]; dsimp only; rw [he3]; dsimp only
                  rw [he4]; dsimp only; rw [he5]; dsimp only; rw [he6]; dsimp only; rw [he7]
                rw [hopt]; dsimp only
                let q := Algorithm.skipSpaces bytes p7 limit
                have hdrop149 : f_Algorithm_parseRLEHeader_prog.drop 149 =
                    .aload 8 :: .ifnonnull 153 :: .iconst 2 :: .ireturn :: .aload 0 ::
                    f_Algorithm_parseRLEHeader_prog.drop 154 := by drop_prefix 5
                have hdrop155 : f_Algorithm_parseRLEHeader_prog.drop 155 =
                    .astore 10 :: .iconst 0 :: .istore 11 :: .aload 10 ::
                    .instanceof "java/lang/Integer" :: .ifeq (155 + 11) ::
                    .aload 10 :: .checkcast "java/lang/Number" ::
                    .invokevirtual "java/lang/Number" "intValue" "()I" ::
                    .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
                    .goto (155 + 13) :: .aload 10 :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
                    f_Algorithm_parseRLEHeader_prog.drop (155 + 13) := by drop_prefix 13
                rcases parseRLEHeader_unboxUInt (f := 239) (pc := 155) (t1 := 10) (t2 := 11)
                    (v := p7) (stk := [.heapRef bytesAddr]) (locs := locs6) (jh := jh0) (hp := hp0)
                    (by omega) (by decide) hdrop155 with ⟨locs7, hunbox7, hlocs7⟩
                let locs8 := setLocal locs7 9 (.i32 q)
                have h149_171 : runJvmResFast 243 f_Algorithm_parseRLEHeader_prog 149
                    (f_Algorithm_parseRLEHeader_prog.drop 149) ⟨149, [], locs6, jh0, hp0⟩ =
                    runJvmResFast 228 f_Algorithm_parseRLEHeader_prog 171
                      (.iload 9 :: .iload 1 :: .if_icmpeq 315 :: f_Algorithm_parseRLEHeader_prog.drop 174)
                      ⟨171, [], locs8, jh0, hp0⟩ := by
                  rw [hdrop149]
                  rw [runJvmResFast_aload]; norm_res_fuel
                  rw [hl6_8, he7, runJvmResFast_ifnonnull_branch rfl]; norm_res_fuel
                  have h153 : f_Algorithm_parseRLEHeader_prog.drop 153 =
                      .aload 0 :: .aload 8 :: f_Algorithm_parseRLEHeader_prog.drop 155 := by drop_prefix 2
                  rw [h153]
                  rw [runJvmResFast_aload]; norm_res_fuel
                  rw [runJvmResFast_aload]; norm_res_fuel
                  (conv => lhs; arg 5; arg 2; simp only [hl6_0, hl6_8, he7])
                  rw [hunbox7]
                  have h168 : f_Algorithm_parseRLEHeader_prog.drop (155 + 13) =
                      .iload 1 ::
                      .invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" ::
                      .istore 9 :: .iload 9 :: .iload 1 :: .if_icmpeq 315 ::
                      f_Algorithm_parseRLEHeader_prog.drop 174 := by drop_prefix 6
                  rw [h168]
                  rw [runJvmResFast_iload]; norm_res_fuel
                  rw [hlocs7 1 (by decide) (by decide), hl6_1]
                  rw [runJvmResFast_invokestatic_step (stepStatic_skipSpaces_heap (by decide) hbytes)]
                  norm_res_fuel
                  rw [runJvmResFast_istore]
                by_cases hqlim : q = limit
                · have hbeq : (q == limit) = true := beq_iff_eq.mpr hqlim
                  dsimp only [q] at hbeq
                  simp only [hbeq, ↓reduceIte]
                  apply Exists.intro
                  constructor
                  · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                    rw [h0_13, hr1, hr2, hr3, hr4, hr5, hr6, h149_171]
                    split_res_fuel 4
                    step_res_block 2
                    (conv => lhs; arg 5; arg 2; simp only [locs8, setLocal,
                      hlocs7 1 (by decide) (by decide), hl6_1])
                    rw [runJvmResFast_if_icmpeq_branch hqlim]; norm_res_fuel
                    have h315 : f_Algorithm_parseRLEHeader_prog.drop 315 =
                        [.iconst 0, .ireturn] := by drop_prefix 2
                    rw [h315, runJvmResFast_iconst_ireturn]
                  · constructor <;> rfl
                · have hbne : (q == limit) = false := beq_false_of_ne hqlim
                  dsimp only [q] at hbne
                  simp only [hbne, Bool.false_eq_true, ↓reduceIte]
                  have hlocs8_0 : locs8 0 = .heapRef bytesAddr := by
                    simp [locs8, setLocal, hlocs7 0 (by decide) (by decide), hl6_0]
                  have hlocs8_1 : locs8 1 = .i32 limit := by
                    simp [locs8, setLocal, hlocs7 1 (by decide) (by decide), hl6_1]
                  have hlocs8_9 : locs8 9 = .i32 q := by simp [locs8, setLocal]
                  have h171_180 : runJvmResFast 228 f_Algorithm_parseRLEHeader_prog 171
                      (.iload 9 :: .iload 1 :: .if_icmpeq 315 :: f_Algorithm_parseRLEHeader_prog.drop 174)
                      ⟨171, [], locs8, jh0, hp0⟩ =
                      runJvmResFast 219 f_Algorithm_parseRLEHeader_prog 180
                        (f_Algorithm_parseRLEHeader_prog.drop 180)
                        ⟨180, [], setLocal locs8 10 (match expect q 44 with
                          | some r => .boxedUInt r | none => .null), jh0, hp0⟩ := by
                    split_res_fuel 10
                    rw [runJvmResFast_iload]; norm_res_fuel
                    simp only [setLocal]
                    rw [runJvmResFast_iload]; norm_res_fuel
                    simp only [setLocal]
                    rw [hlocs7 1 (by decide) (by decide), hl6_1]
                    change runJvmResFast (228 - 10 + 8) f_Algorithm_parseRLEHeader_prog 173
                      (.if_icmpeq 315 :: f_Algorithm_parseRLEHeader_prog.drop 174)
                      ⟨173, [.i32 limit, .i32 q], setLocal locs7 9 (.i32 q), jh0, hp0⟩ = _
                    rw [runJvmResFast_if_icmpeq_fallthrough hbne]; norm_res_fuel
                    step_drop 6
                    rw [runJvmResFast_aload]; norm_res_fuel
                    simp [setLocal]
                    rw [hlocs7 0 (by decide) (by decide), hl6_0]
                    rw [runJvmResFast_iload]; norm_res_fuel
                    simp [setLocal]
                    rw [hlocs7 1 (by decide) (by decide), hl6_1]
                    rw [runJvmResFast_iload]; norm_res_fuel
                    simp [setLocal]
                    rw [runJvmResFast_iconst]; norm_res_fuel
                    rw [runJvmResFast_invokestatic_step (stepStatic_parseRLEHeader_lam0_heap hbytes)]
                    norm_res_fuel
                    rw [runJvmResFast_astore]; norm_res_fuel
                    dsimp only [expect]
                    simp only [ByteArray.get!,
                      show (44 : UInt32).toUInt8 = (44 : UInt8) from by decide]
                    split
                    · next hc =>
                      have hc' : (decide (skipSpaces bytes q limit < limit) &&
                          (bytes.data[(skipSpaces bytes q limit).toNat]! == 44)) = true := hc
                      simp only [hc', ↓reduceIte]; rfl
                    · next hc =>
                      have hc' : (decide (skipSpaces bytes q limit < limit) &&
                          (bytes.data[(skipSpaces bytes q limit).toNat]! == 44)) = false :=
                        Bool.eq_false_iff.mpr hc
                      simp only [hc', Bool.false_eq_true, ↓reduceIte]; rfl
                  cases he8 : expect q 44 with
                  | none =>
                    apply Exists.intro
                    constructor
                    · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                      rw [h0_13, hr1, hr2, hr3, hr4, hr5, hr6, h149_171, h171_180]
                      have h180 : f_Algorithm_parseRLEHeader_prog.drop 180 =
                          .aload 10 :: .ifnonnull 184 :: .iconst 2 :: .ireturn ::
                          f_Algorithm_parseRLEHeader_prog.drop 184 := by drop_prefix 4
                      rw [h180]
                      split_res_fuel 5
                      rw [runJvmResFast_aload]; norm_res_fuel
                      have hset10 : setLocal locs8 10
                          (match expect q 44 with | some r => .boxedUInt r | none => .null) 10 = .null := by
                        simp [setLocal, he8]
                      rw [hset10]
                      rw [runJvmResFast_ifnonnull_fallthrough]; norm_res_fuel
                      rw [runJvmResFast_iconst_ireturn]
                    · constructor <;> rfl
                  | some p_comma =>
                    have hp_comma_le : p_comma ≤ limit := by
                      dsimp only [expect] at he8
                      split at he8
                      · simp only [Option.some.injEq] at he8
                        subst p_comma
                        have hlt : Algorithm.skipSpaces bytes q limit < limit := by
                          rename_i hc
                          exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hc).1
                        rw [UInt32.le_iff_toNat_le, UInt32.toNat_add, UInt32.toNat_one]
                        have := UInt32.lt_iff_toNat_lt.mp hlt
                        rw [Nat.mod_eq_of_lt (by omega)]; omega
                      · cases he8
                    let r := Algorithm.skipSpaces bytes p_comma limit
                    have hr_le : r ≤ limit := skipSpaces_le bytes p_comma limit hp_comma_le
                    have h186 : f_Algorithm_parseRLEHeader_prog.drop 186 =
                        .astore 12 :: .iconst 0 :: .istore 13 :: .aload 12 ::
                        .instanceof "java/lang/Integer" :: .ifeq (186 + 11) ::
                        .aload 12 :: .checkcast "java/lang/Number" ::
                        .invokevirtual "java/lang/Number" "intValue" "()I" ::
                        .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
                        .goto (186 + 13) :: .aload 12 :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
                        f_Algorithm_parseRLEHeader_prog.drop (186 + 13) := by drop_prefix 13
                    rcases parseRLEHeader_unboxUInt (f := 215) (pc := 186) (t1 := 12) (t2 := 13)
                        (v := p_comma) (stk := [.heapRef bytesAddr])
                        (locs := setLocal locs8 10 (.boxedUInt p_comma)) (jh := jh0) (hp := hp0)
                        (by omega) (by decide) h186 with ⟨locs9, hunbox9, hlocs9⟩
                    let locs10 := setLocal (setLocal locs9 11 (.i32 r)) 12 (.i32 (r + 4))
                    have h180_210 : runJvmResFast 219 f_Algorithm_parseRLEHeader_prog 180
                        (f_Algorithm_parseRLEHeader_prog.drop 180)
                        ⟨180, [], setLocal locs8 10 (match expect q 44 with
                          | some r => .boxedUInt r | none => .null), jh0, hp0⟩ =
                        runJvmResFast 196 f_Algorithm_parseRLEHeader_prog 210
                          (.ifle 213 :: f_Algorithm_parseRLEHeader_prog.drop 211)
                          ⟨210, [.i32 (if r + 4 == limit then 0 else if r + 4 < limit then 4294967295 else 1)],
                            locs10, jh0, hp0⟩ := by
                      have h180 : f_Algorithm_parseRLEHeader_prog.drop 180 =
                          .aload 10 :: .ifnonnull 184 :: .iconst 2 :: .ireturn ::
                          f_Algorithm_parseRLEHeader_prog.drop 184 := by drop_prefix 4
                      rw [h180, he8]
                      rw [runJvmResFast_aload]; norm_res_fuel
                      simp only [setLocal]
                      rw [runJvmResFast_ifnonnull_branch rfl]; norm_res_fuel
                      have h184 : f_Algorithm_parseRLEHeader_prog.drop 184 =
                          .aload 0 :: .aload 10 :: f_Algorithm_parseRLEHeader_prog.drop 186 := by drop_prefix 2
                      rw [h184]
                      rw [runJvmResFast_aload]; norm_res_fuel
                      simp [setLocal]
                      rw [hlocs7 0 (by decide) (by decide), hl6_0]
                      rw [runJvmResFast_aload]; norm_res_fuel
                      simp [setLocal]
                      change runJvmResFast 215 f_Algorithm_parseRLEHeader_prog 186
                        (f_Algorithm_parseRLEHeader_prog.drop 186)
                        ⟨186, [.boxedUInt p_comma, .heapRef bytesAddr],
                          setLocal locs8 10 (.boxedUInt p_comma), jh0, hp0⟩ = _
                      rw [hunbox9]
                      have h199 : f_Algorithm_parseRLEHeader_prog.drop (186 + 13) =
                          .iload 1 ::
                          .invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" ::
                          .istore 11 :: .iload 11 :: .iconst 4 :: .iadd ::
                          .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: .istore 12 ::
                          .iload 12 :: .iload 1 ::
                          .invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" ::
                          .ifle 213 :: f_Algorithm_parseRLEHeader_prog.drop 211 := by drop_prefix 11
                      rw [h199]
                      split_res_fuel 12
                      rw [runJvmResFast_iload]; norm_res_fuel
                      rw [hlocs9 1 (by decide) (by decide)]; simp [setLocal]; rw [hlocs8_1]
                      rw [runJvmResFast_invokestatic_step (stepStatic_skipSpaces_heap (by decide) hbytes)]
                      norm_res_fuel
                      rw [runJvmResFast_istore]; norm_res_fuel
                      rw [runJvmResFast_iload]; norm_res_fuel
                      simp [setLocal]
                      rw [runJvmResFast_iconst]; norm_res_fuel
                      rw [runJvmResFast_iadd_local]; norm_res_fuel
                      rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
                      rw [runJvmResFast_istore]; norm_res_fuel
                      rw [runJvmResFast_iload]; norm_res_fuel
                      simp [setLocal]
                      rw [runJvmResFast_iload]; norm_res_fuel
                      (conv =>
                        lhs; arg 5; arg 2; simp [setLocal]
                        rw [hlocs9 1 (by decide) (by decide)]; simp [setLocal]; rw [hlocs8_1])
                      rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_local]; norm_res_fuel
                      simp only [beq_iff_eq]
                      rfl
                    have hl10_0 : locs10 0 = .heapRef bytesAddr := by
                      simp [locs10, setLocal, hlocs9 0 (by decide) (by decide),
                        show (0 : Nat) ≠ 10 from by decide, hlocs8_0]
                    have hl10_1 : locs10 1 = .i32 limit := by
                      simp [locs10, setLocal, hlocs9 1 (by decide) (by decide),
                        show (1 : Nat) ≠ 10 from by decide, hlocs8_1]
                    have hl10_11 : locs10 11 = .i32 r := by simp [locs10, setLocal]
                    have hl10_12 : locs10 12 = .i32 (r + 4) := by simp [locs10, setLocal]
                    by_cases h_r4 : r + 4 ≤ limit
                    · have h190_219 : runJvmResFast 196 f_Algorithm_parseRLEHeader_prog 210
                          (.ifle 213 :: f_Algorithm_parseRLEHeader_prog.drop 211)
                          ⟨210, [.i32 (if r + 4 == limit then 0 else if r + 4 < limit then 4294967295 else 1)],
                            locs10, jh0, hp0⟩ =
                          runJvmResFast 189 f_Algorithm_parseRLEHeader_prog 219
                            (.ifle 222 :: f_Algorithm_parseRLEHeader_prog.drop 220)
                            ⟨219, [.i32 (if 4 == limit - r then 0 else if 4 < limit - r then 4294967295 else 1)],
                              locs10, jh0, hp0⟩ := by
                        split_res_fuel 9
                        rw [runJvmResFast_ifle_branch (by rw [compareUnsigned_sle_zero]; exact decide_eq_true h_r4)]
                        norm_res_fuel
                        step_drop 7
                        rw [runJvmResFast_iconst]; norm_res_fuel
                        rw [runJvmResFast_iload]; norm_res_fuel
                        simp [setLocal]
                        rw [hlocs9 1 (by decide) (by decide)]; simp [setLocal]; rw [hlocs8_1]
                        rw [runJvmResFast_iload]; norm_res_fuel
                        simp [setLocal]
                        rw [runJvmResFast_isub_local]; norm_res_fuel
                        rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
                        rw [runJvmResFast_invokestatic_step stepStatic_compareUnsigned_local]; norm_res_fuel
                        simp only [beq_iff_eq]
                        rfl
                      by_cases hlimr : 4 ≤ limit - r
                      · have hr_toNat : r.toNat + 4 ≤ limit.toNat := by
                          have hlt : r.toNat ≤ limit.toNat := UInt32.le_iff_toNat_le.mp hr_le
                          have hsub : (limit - r).toNat = limit.toNat - r.toNat :=
                            UInt32.toNat_sub_of_le limit r hr_le
                          have h4l := UInt32.le_iff_toNat_le.mp hlimr
                          rw [hsub] at h4l
                          have h4v : (4 : UInt32).toNat = 4 := by decide
                          rw [h4v] at h4l; omega
                        have hb0_slt : r.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt_2_31 (by omega)
                        have hb1_slt : (r + 1).toBitVec.slt 0#32 = false := by
                          apply u32_slt_zero_of_lt_2_31
                          rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]; omega
                        have hb2_slt : (r + 2).toBitVec.slt 0#32 = false := by
                          apply u32_slt_zero_of_lt_2_31
                          rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from by decide,
                            Nat.mod_eq_of_lt (by omega)]; omega
                        have hb3_slt : (r + 3).toBitVec.slt 0#32 = false := by
                          apply u32_slt_zero_of_lt_2_31
                          rw [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from by decide,
                            Nat.mod_eq_of_lt (by omega)]; omega
                        have hb0_sz : r.toNat < bytes.data.size := by omega
                        have hb1_sz : (r + 1).toNat < bytes.data.size := by
                          rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]; omega
                        have hb2_sz : (r + 2).toNat < bytes.data.size := by
                          rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 from by decide,
                            Nat.mod_eq_of_lt (by omega)]; omega
                        have hb3_sz : (r + 3).toNat < bytes.data.size := by
                          rw [UInt32.toNat_add, show (3 : UInt32).toNat = 3 from by decide,
                            Nat.mod_eq_of_lt (by omega)]; omega
                        have h219_228 : runJvmResFast 189 f_Algorithm_parseRLEHeader_prog 219
                            (.ifle 222 :: f_Algorithm_parseRLEHeader_prog.drop 220)
                            ⟨219, [.i32 (if 4 == limit - r then 0 else if 4 < limit - r then 4294967295 else 1)],
                              locs10, jh0, hp0⟩ =
                            runJvmResFast 182 f_Algorithm_parseRLEHeader_prog 228
                              (f_Algorithm_parseRLEHeader_prog.drop 228)
                              ⟨228, [], setLocal locs10 13 (.i32 (u8Sext (bytes.get! r.toNat))), jh0, hp0⟩ := by
                          split_res_fuel 8
                          rw [runJvmResFast_ifle_branch (by rw [compareUnsigned_sle_zero]; exact decide_eq_true hlimr)]
                          norm_res_fuel
                          step_drop 6
                          rw [show (189 - 8 + 7 : Nat) = (189 - 8 + 6) + 1 from by decide]
                          rw [runJvmResFast_nop_local]; norm_res_fuel
                          change runJvmResFast (189 - 8 + 6) f_Algorithm_parseRLEHeader_prog 223
                            (.aload 0 :: .iload 11 :: .baload ::
                              .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" ::
                              .istore 13 :: f_Algorithm_parseRLEHeader_prog.drop 228)
                            ⟨223, [], locs10, jh0, hp0⟩ = _
                          rw [runJvmResFast_aload]; norm_res_fuel
                          simp [setLocal]
                          rw [hlocs9 0 (by decide) (by decide)]; simp [setLocal]; rw [hlocs8_0]
                          rw [runJvmResFast_iload]; norm_res_fuel
                          simp [setLocal]
                          rw [runJvmResFast_baload_byteArray (idx := r) hbytes hb0_slt hb0_sz]; norm_res_fuel
                          rw [runJvmResFast_invokestatic_step stepStatic_ubyteCtor_local]; norm_res_fuel
                          rw [runJvmResFast_istore]; norm_res_fuel
                          rw [byteArray_get_eq_getBang bytes hb0_sz]
                          rfl
                        have hc0 := parseRLEHeader_if_letter (f := 182) (pc := 228) (locIdx := 13)
                          (b := bytes.get! r.toNat) (ch := 114) (tgt := 236)
                          (locs := setLocal locs10 13 (.i32 (u8Sext (bytes.get! r.toNat))))
                          (jh := jh0) (hp := hp0) (by omega) (by decide) (by decide)
                          (by simp [setLocal]) (by drop_prefix 8)
                        have hcond : (decide (r + 4 ≤ limit) && decide (limit - r ≥ 4)) = true := by
                          simp [h_r4, hlimr]
                        dsimp only [r] at hcond
                        simp only [hcond, Bool.true_and]
                        by_cases hl_r : Algorithm.isLetterByte (bytes.get! r.toNat) 114 = true
                        · simp only [hl_r, ↓reduceIte] at hc0 ⊢
                          obtain ⟨f1, hf1_def⟩ : ∃ x, x =
                              (if bytes.get! r.toNat == 114 then 182 - 3 else 182 - 6) := ⟨_, rfl⟩
                          rw [← hf1_def] at hc0
                          have hf1_ge : 176 ≤ f1 := by rw [hf1_def]; split <;> omega
                          let locs11 := setLocal locs10 13 (.i32 (u8Sext (bytes.get! r.toNat)))
                          let locs12 := setLocal locs11 13 (.i32 (u8Sext (bytes.get! (r + 1).toNat)))
                          have h236_245 : runJvmResFast f1 f_Algorithm_parseRLEHeader_prog 236
                              (f_Algorithm_parseRLEHeader_prog.drop 236) ⟨236, [], locs11, jh0, hp0⟩ =
                              runJvmResFast (f1 - 9) f_Algorithm_parseRLEHeader_prog 245
                                (f_Algorithm_parseRLEHeader_prog.drop 245) ⟨245, [], locs12, jh0, hp0⟩ := by
                            have h236 : f_Algorithm_parseRLEHeader_prog.drop 236 =
                                .nop :: .aload 0 :: .iload 11 :: .iconst 1 :: .iadd ::
                                .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
                                .baload :: .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" ::
                                .istore 13 :: f_Algorithm_parseRLEHeader_prog.drop 245 := by drop_prefix 9
                            rw [h236]
                            split_res_fuel 10
                            rw [show (f1 - 10 + 10 : Nat) = (f1 - 10 + 9) + 1 from by omega]
                            rw [runJvmResFast_nop_local]; norm_res_fuel
                            change runJvmResFast (f1 - 10 + 9) f_Algorithm_parseRLEHeader_prog 237
                              (.aload 0 :: .iload 11 :: .iconst 1 :: .iadd ::
                                .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
                                .baload :: .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" ::
                                .istore 13 :: f_Algorithm_parseRLEHeader_prog.drop 245)
                              ⟨237, [], locs11, jh0, hp0⟩ = _
                            rw [runJvmResFast_aload]; norm_res_fuel
                            simp [setLocal]
                            rw [hlocs9 0 (by decide) (by decide)]; simp [setLocal]; rw [hlocs8_0]
                            rw [runJvmResFast_iload]; norm_res_fuel
                            simp [setLocal]
                            rw [runJvmResFast_iconst]; norm_res_fuel
                            rw [runJvmResFast_iadd_local]; norm_res_fuel
                            rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
                            rw [runJvmResFast_baload_byteArray (idx := r + 1) hbytes hb1_slt hb1_sz]
                            norm_res_fuel
                            rw [runJvmResFast_invokestatic_step stepStatic_ubyteCtor_local]; norm_res_fuel
                            rw [runJvmResFast_istore]; norm_res_fuel
                            rw [byteArray_get_eq_getBang bytes hb1_sz]
                            rw [hf1_def, show (if bytes.get! r.toNat == 114 then 182 - 3 else 182 - 6) - 10 + 1 =
                              (if bytes.get! r.toNat == 114 then 182 - 3 else 182 - 6) - 9 from by split <;> omega]
                            rw [← hf1_def]
                            rfl
                          have hc1 := parseRLEHeader_if_letter (f := f1 - 9) (pc := 245) (locIdx := 13)
                            (b := bytes.get! (r + 1).toNat) (ch := 117) (tgt := 253)
                            (locs := locs12) (jh := jh0) (hp := hp0) (by omega) (by decide) (by decide)
                            (by simp [locs12, setLocal]) (by drop_prefix 8)
                          by_cases hl_u : Algorithm.isLetterByte (bytes.get! (r + 1).toNat) 117 = true
                          · simp only [hl_u, ↓reduceIte] at hc1 ⊢
                            obtain ⟨f2, hf2_def⟩ : ∃ x, x =
                                (if bytes.get! (r + 1).toNat == 117 then f1 - 9 - 3 else f1 - 9 - 6) :=
                              ⟨_, rfl⟩
                            rw [← hf2_def] at hc1
                            have hf2_ge : 160 ≤ f2 := by rw [hf2_def]; split <;> omega
                            let locs13 := setLocal locs12 14 (.i32 (u8Sext (bytes.get! (r + 2).toNat)))
                            have h253_262 : runJvmResFast f2 f_Algorithm_parseRLEHeader_prog 253
                                (f_Algorithm_parseRLEHeader_prog.drop 253) ⟨253, [], locs12, jh0, hp0⟩ =
                                runJvmResFast (f2 - 9) f_Algorithm_parseRLEHeader_prog 262
                                  (f_Algorithm_parseRLEHeader_prog.drop 262) ⟨262, [], locs13, jh0, hp0⟩ := by
                              have h253 : f_Algorithm_parseRLEHeader_prog.drop 253 =
                                  .nop :: .aload 0 :: .iload 11 :: .iconst 2 :: .iadd ::
                                  .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
                                  .baload :: .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" ::
                                  .istore 14 :: f_Algorithm_parseRLEHeader_prog.drop 262 := by drop_prefix 9
                              rw [h253]
                              split_res_fuel 10
                              rw [show (f2 - 10 + 10 : Nat) = (f2 - 10 + 9) + 1 from by omega]
                              rw [runJvmResFast_nop_local]; norm_res_fuel
                              change runJvmResFast (f2 - 10 + 9) f_Algorithm_parseRLEHeader_prog 254
                                (.aload 0 :: .iload 11 :: .iconst 2 :: .iadd ::
                                  .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
                                  .baload :: .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" ::
                                  .istore 14 :: f_Algorithm_parseRLEHeader_prog.drop 262)
                                ⟨254, [], locs12, jh0, hp0⟩ = _
                              rw [runJvmResFast_aload]; norm_res_fuel
                              simp [setLocal]
                              rw [hlocs9 0 (by decide) (by decide)]; simp [setLocal]; rw [hlocs8_0]
                              rw [runJvmResFast_iload]; norm_res_fuel
                              simp [setLocal]
                              rw [runJvmResFast_iconst]; norm_res_fuel
                              rw [runJvmResFast_iadd_local]; norm_res_fuel
                              rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
                              rw [runJvmResFast_baload_byteArray (idx := r + 2) hbytes hb2_slt hb2_sz]
                              norm_res_fuel
                              rw [runJvmResFast_invokestatic_step stepStatic_ubyteCtor_local]; norm_res_fuel
                              rw [runJvmResFast_istore]; norm_res_fuel
                              rw [byteArray_get_eq_getBang bytes hb2_sz]
                              rw [hf2_def]
                              rw [show (if bytes.get! (r + 1).toNat == 117 then f1 - 9 - 3 else f1 - 9 - 6) - 10 + 1 =
                                  (if bytes.get! (r + 1).toNat == 117 then f1 - 9 - 3 else f1 - 9 - 6) - 9 from by
                                split <;> omega]
                              rw [← hf2_def]
                              rfl
                            have hc2 := parseRLEHeader_if_letter (f := f2 - 9) (pc := 262) (locIdx := 14)
                              (b := bytes.get! (r + 2).toNat) (ch := 108) (tgt := 270)
                              (locs := locs13) (jh := jh0) (hp := hp0) (by omega) (by decide) (by decide)
                              (by simp [locs13, setLocal]) (by drop_prefix 8)
                            by_cases hl_l : Algorithm.isLetterByte (bytes.get! (r + 2).toNat) 108 = true
                            · simp only [hl_l, ↓reduceIte] at hc2 ⊢
                              obtain ⟨f3, hf3_def⟩ : ∃ x, x =
                                  (if bytes.get! (r + 2).toNat == 108 then f2 - 9 - 3 else f2 - 9 - 6) :=
                                ⟨_, rfl⟩
                              rw [← hf3_def] at hc2
                              have hf3_ge : 145 ≤ f3 := by rw [hf3_def]; split <;> omega
                              let locs14 := setLocal locs13 15 (.i32 (u8Sext (bytes.get! (r + 3).toNat)))
                              have h270_279 : runJvmResFast f3 f_Algorithm_parseRLEHeader_prog 270
                                  (f_Algorithm_parseRLEHeader_prog.drop 270) ⟨270, [], locs13, jh0, hp0⟩ =
                                  runJvmResFast (f3 - 9) f_Algorithm_parseRLEHeader_prog 279
                                    (f_Algorithm_parseRLEHeader_prog.drop 279) ⟨279, [], locs14, jh0, hp0⟩ := by
                                have h270 : f_Algorithm_parseRLEHeader_prog.drop 270 =
                                    .nop :: .aload 0 :: .iload 11 :: .iconst 3 :: .iadd ::
                                    .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
                                    .baload :: .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" ::
                                    .istore 15 :: f_Algorithm_parseRLEHeader_prog.drop 279 := by drop_prefix 9
                                rw [h270]
                                split_res_fuel 10
                                rw [show (f3 - 10 + 10 : Nat) = (f3 - 10 + 9) + 1 from by omega]
                                rw [runJvmResFast_nop_local]; norm_res_fuel
                                change runJvmResFast (f3 - 10 + 9) f_Algorithm_parseRLEHeader_prog 271
                                  (.aload 0 :: .iload 11 :: .iconst 3 :: .iadd ::
                                    .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
                                    .baload :: .invokestatic "kotlin/UByte" "constructor-impl" "(B)B" ::
                                    .istore 15 :: f_Algorithm_parseRLEHeader_prog.drop 279)
                                  ⟨271, [], locs13, jh0, hp0⟩ = _
                                rw [runJvmResFast_aload]; norm_res_fuel
                                simp [setLocal]
                                rw [hlocs9 0 (by decide) (by decide)]; simp [setLocal]; rw [hlocs8_0]
                                rw [runJvmResFast_iload]; norm_res_fuel
                                simp [setLocal]
                                rw [runJvmResFast_iconst]; norm_res_fuel
                                rw [runJvmResFast_iadd_local]; norm_res_fuel
                                rw [runJvmResFast_invokestatic_step stepStatic_uintCtor_local]; norm_res_fuel
                                rw [runJvmResFast_baload_byteArray (idx := r + 3) hbytes hb3_slt hb3_sz]
                                norm_res_fuel
                                rw [runJvmResFast_invokestatic_step stepStatic_ubyteCtor_local]; norm_res_fuel
                                rw [runJvmResFast_istore]; norm_res_fuel
                                rw [byteArray_get_eq_getBang bytes hb3_sz]
                                rw [hf3_def]
                                rw [show (if bytes.get! (r + 2).toNat == 108 then f2 - 9 - 3 else f2 - 9 - 6) - 10 + 1 =
                                    (if bytes.get! (r + 2).toNat == 108 then f2 - 9 - 3 else f2 - 9 - 6) - 9 from by
                                  split <;> omega]
                                rw [← hf3_def]
                                rfl
                              have hc3 := parseRLEHeader_if_letter (f := f3 - 9) (pc := 279) (locIdx := 15)
                                (b := bytes.get! (r + 3).toNat) (ch := 101) (tgt := 287)
                                (locs := locs14) (jh := jh0) (hp := hp0) (by omega) (by decide) (by decide)
                                (by simp [locs14, setLocal]) (by drop_prefix 8)
                              by_cases hl_e : Algorithm.isLetterByte (bytes.get! (r + 3).toNat) 101 = true
                              · simp only [hl_e, ↓reduceIte] at hc3 ⊢
                                obtain ⟨f4, hf4_def⟩ : ∃ x, x =
                                    (if bytes.get! (r + 3).toNat == 101 then f3 - 9 - 3 else f3 - 9 - 6) :=
                                  ⟨_, rfl⟩
                                rw [← hf4_def] at hc3
                                have hf4_ge : 130 ≤ f4 := by rw [hf4_def]; split <;> omega
                                let locs15 := setLocal locs14 16 (match expect (r + 4) 61 with
                                  | some r => .boxedUInt r | none => .null)
                                have h287_293 : runJvmResFast f4 f_Algorithm_parseRLEHeader_prog 287
                                    (f_Algorithm_parseRLEHeader_prog.drop 287) ⟨287, [], locs14, jh0, hp0⟩ =
                                    runJvmResFast (f4 - 6) f_Algorithm_parseRLEHeader_prog 293
                                      (f_Algorithm_parseRLEHeader_prog.drop 293) ⟨293, [], locs15, jh0, hp0⟩ := by
                                  have h287 : f_Algorithm_parseRLEHeader_prog.drop 287 =
                                      .aload 0 :: .iload 1 :: .iload 12 :: .iconst 61 ::
                                      .invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_parseRLEHeader___lam__0-XwsRtWc"
                                        "([BIIB)Lkotlin/UInt;" ::
                                      .astore 16 :: f_Algorithm_parseRLEHeader_prog.drop 293 := by drop_prefix 6
                                  rw [h287]
                                  split_res_fuel 6
                                  rw [runJvmResFast_aload]; norm_res_fuel
                                  simp [setLocal]
                                  rw [hlocs9 0 (by decide) (by decide)]; simp [setLocal]; rw [hlocs8_0]
                                  rw [runJvmResFast_iload]; norm_res_fuel
                                  simp [setLocal]
                                  rw [hlocs9 1 (by decide) (by decide)]; simp [setLocal]; rw [hlocs8_1]
                                  rw [runJvmResFast_iload]; norm_res_fuel
                                  simp [setLocal]
                                  rw [runJvmResFast_iconst]; norm_res_fuel
                                  rw [runJvmResFast_invokestatic_step (stepStatic_parseRLEHeader_lam0_heap hbytes)]
                                  norm_res_fuel
                                  rw [runJvmResFast_astore]; norm_res_fuel
                                  have hv_eq : (if (decide (skipSpaces ⟨bytes.data⟩ (r + 4) limit < limit) &&
                                      (bytes.data[(skipSpaces ⟨bytes.data⟩ (r + 4) limit).toNat]! ==
                                        (61 : UInt32).toUInt8)) = true
                                      then JvmVal.boxedUInt (skipSpaces ⟨bytes.data⟩ (r + 4) limit + 1)
                                      else (.null : JvmVal)) =
                                      (match expect (r + 4) 61 with
                                      | some r => .boxedUInt r | none => (.null : JvmVal)) := by
                                    have hb : (⟨bytes.data⟩ : ByteArray) = bytes := by cases bytes; rfl
                                    rw [hb]
                                    dsimp only [expect]
                                    rw [show (61 : UInt32).toUInt8 =
                                        (61 : UInt8) from by decide,
                                      show bytes.data[(skipSpaces bytes (r + 4) limit).toNat]! =
                                        bytes.get! (skipSpaces bytes (r + 4) limit).toNat from rfl]
                                    cases decide (skipSpaces bytes (r + 4) limit < limit) &&
                                        (bytes.get! (skipSpaces bytes (r + 4) limit).toNat == 61) <;> rfl
                                  exact congrArg (fun v => runJvmResFast (f4 - 6) f_Algorithm_parseRLEHeader_prog 293
                                    (f_Algorithm_parseRLEHeader_prog.drop 293)
                                    ⟨293, [], setLocal locs14 16 v, jh0, hp0⟩) hv_eq
                                have he9_ex : (if (decide (skipSpaces bytes (r + 4) limit < limit) &&
                                    bytes.get! (skipSpaces bytes (r + 4) limit).toNat == 61) = true
                                    then some (skipSpaces bytes (r + 4) limit + 1) else none) =
                                    expect (r + 4) 61 := rfl
                                have hlet_true : (Algorithm.isLetterByte (bytes.get! r.toNat) 114 &&
                                    Algorithm.isLetterByte (bytes.get! (r + 1).toNat) 117 &&
                                    Algorithm.isLetterByte (bytes.get! (r + 2).toNat) 108 &&
                                    Algorithm.isLetterByte (bytes.get! (r + 3).toNat) 101) = true := by
                                  simp only [hl_r, hl_u, hl_l, hl_e]; rfl
                                dsimp only [r] at hlet_true
                                simp only [hlet_true, ↓reduceIte]
                                cases he9 : expect (r + 4) 61 with
                                | none =>
                                  apply Exists.intro
                                  constructor
                                  · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                                    rw [h0_13, hr1, hr2, hr3, hr4, hr5, hr6, h149_171, h171_180,
                                      h180_210, h190_219, h219_228, hc0, h236_245, hc1, h253_262, hc2,
                                      h270_279, hc3, h287_293]
                                    have h293 : f_Algorithm_parseRLEHeader_prog.drop 293 =
                                        .aload 16 :: .ifnonnull 297 :: .iconst 2 :: .ireturn ::
                                        f_Algorithm_parseRLEHeader_prog.drop 297 := by drop_prefix 4
                                    rw [h293]
                                    split_res_fuel 4
                                    rw [runJvmResFast_aload]; norm_res_fuel
                                    simp only [setLocal, ite_true]
                                    rw [he9_ex, he9]
                                    rw [runJvmResFast_ifnonnull_fallthrough]; norm_res_fuel
                                    rw [runJvmResFast_iconst_ireturn]
                                  · constructor <;> rfl
                                | some p8 =>
                                  have h299 : f_Algorithm_parseRLEHeader_prog.drop 299 =
                                      .astore 17 :: .iconst 0 :: .istore 18 :: .aload 17 ::
                                      .instanceof "java/lang/Integer" :: .ifeq (299 + 11) ::
                                      .aload 17 :: .checkcast "java/lang/Number" ::
                                      .invokevirtual "java/lang/Number" "intValue" "()I" ::
                                      .invokestatic "kotlin/UInt" "constructor-impl" "(I)I" ::
                                      .goto (299 + 13) :: .aload 17 ::
                                      .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
                                      f_Algorithm_parseRLEHeader_prog.drop (299 + 13) := by drop_prefix 13
                                  rcases parseRLEHeader_unboxUInt (f := f4 - 6 - 4) (pc := 299)
                                      (t1 := 17) (t2 := 18) (v := p8) (stk := [.heapRef bytesAddr])
                                      (locs := setLocal locs14 16 (.boxedUInt p8)) (jh := jh0) (hp := hp0)
                                      (by omega) (by decide) h299 with ⟨locs16, hunbox16, hlocs16⟩
                                  apply Exists.intro
                                  constructor
                                  · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                                    rw [h0_13, hr1, hr2, hr3, hr4, hr5, hr6, h149_171, h171_180,
                                      h180_210, h190_219, h219_228, hc0, h236_245, hc1, h253_262, hc2,
                                      h270_279, hc3, h287_293]
                                    have h293 : f_Algorithm_parseRLEHeader_prog.drop 293 =
                                        .aload 16 :: .ifnonnull 297 :: .iconst 2 :: .ireturn ::
                                        f_Algorithm_parseRLEHeader_prog.drop 297 := by drop_prefix 4
                                    rw [h293]
                                    split_res_fuel 4
                                    rw [runJvmResFast_aload]; norm_res_fuel
                                    simp only [setLocal, ite_true]
                                    rw [he9_ex, he9]
                                    rw [runJvmResFast_ifnonnull_branch rfl]; norm_res_fuel
                                    have h297 : f_Algorithm_parseRLEHeader_prog.drop 297 =
                                        .aload 0 :: .aload 16 ::
                                        f_Algorithm_parseRLEHeader_prog.drop 299 := by drop_prefix 2
                                    rw [h297]
                                    rw [runJvmResFast_aload]; norm_res_fuel
                                    simp [setLocal]
                                    rw [hlocs9 0 (by decide) (by decide)]; simp [setLocal]; rw [hlocs8_0]
                                    rw [runJvmResFast_aload]; norm_res_fuel
                                    simp only [setLocal, ite_true]
                                    change runJvmResFast (f4 - 6 - 4) f_Algorithm_parseRLEHeader_prog 299
                                      (f_Algorithm_parseRLEHeader_prog.drop 299)
                                      ⟨299, [.boxedUInt p8, .heapRef bytesAddr],
                                        setLocal locs14 16 (.boxedUInt p8), jh0, hp0⟩ = _
                                    rw [hunbox16]
                                    have h312 : f_Algorithm_parseRLEHeader_prog.drop (299 + 13) =
                                        .iload 1 ::
                                        .invokestatic "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_checkRLERule-BltQuoY" "([BII)I" ::
                                        .ireturn :: f_Algorithm_parseRLEHeader_prog.drop 315 := by drop_prefix 3
                                    rw [h312]
                                    split_res_fuel 4
                                    rw [runJvmResFast_iload]; norm_res_fuel
                                    have h16_1 : locs16 1 = .i32 limit := by
                                      simp [hlocs16 1 (by decide) (by decide), locs14, locs13,
                                        locs12, locs11, setLocal, hl10_1]
                                    rw [h16_1]
                                    rw [runJvmResFast_invokestatic_step (stepStatic_checkRLERule_heap hbytes)]
                                    norm_res_fuel
                                    rw [runJvmResFast_ireturn]
                                  · constructor <;> rfl
                              · have hl_ef : Algorithm.isLetterByte (bytes.get! (r + 3).toNat) 101 = false :=
                                  Bool.eq_false_iff.mpr hl_e
                                rw [hl_ef] at hc3
                                simp only [Bool.false_eq_true, ↓reduceIte] at hc3
                                dsimp only [r] at hl_ef
                                rw [hl_ef]
                                simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                                rcases hc3 with ⟨st', hrun, hjh, hhp⟩
                                refine ⟨st', ?_, hjh, hhp⟩
                                apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                                rw [h0_13, hr1, hr2, hr3, hr4, hr5, hr6, h149_171, h171_180,
                                  h180_210, h190_219, h219_228, hc0, h236_245, hc1, h253_262, hc2,
                                  h270_279]; exact hrun
                            · have hl_lf : Algorithm.isLetterByte (bytes.get! (r + 2).toNat) 108 = false :=
                                Bool.eq_false_iff.mpr hl_l
                              rw [hl_lf] at hc2
                              simp only [Bool.false_eq_true, ↓reduceIte] at hc2
                              dsimp only [r] at hl_lf
                              rw [hl_lf]
                              simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                              rcases hc2 with ⟨st', hrun, hjh, hhp⟩
                              refine ⟨st', ?_, hjh, hhp⟩
                              apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                              rw [h0_13, hr1, hr2, hr3, hr4, hr5, hr6, h149_171, h171_180,
                                h180_210, h190_219, h219_228, hc0, h236_245, hc1, h253_262]; exact hrun
                          · have hl_uf : Algorithm.isLetterByte (bytes.get! (r + 1).toNat) 117 = false :=
                              Bool.eq_false_iff.mpr hl_u
                            rw [hl_uf] at hc1
                            simp only [Bool.false_eq_true, ↓reduceIte] at hc1
                            dsimp only [r] at hl_uf
                            rw [hl_uf]
                            simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                            rcases hc1 with ⟨st', hrun, hjh, hhp⟩
                            refine ⟨st', ?_, hjh, hhp⟩
                            apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                            rw [h0_13, hr1, hr2, hr3, hr4, hr5, hr6, h149_171, h171_180,
                              h180_210, h190_219, h219_228, hc0, h236_245]; exact hrun
                        · have hl_rf : Algorithm.isLetterByte (bytes.get! r.toNat) 114 = false :=
                            Bool.eq_false_iff.mpr hl_r
                          rw [hl_rf] at hc0
                          simp only [Bool.false_eq_true, ↓reduceIte] at hc0
                          dsimp only [r] at hl_rf
                          rw [hl_rf]
                          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                          rcases hc0 with ⟨st', hrun, hjh, hhp⟩
                          refine ⟨st', ?_, hjh, hhp⟩
                          apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                          rw [h0_13, hr1, hr2, hr3, hr4, hr5, hr6, h149_171, h171_180,
                            h180_210, h190_219, h219_228]; exact hrun
                      · have hlimr_f : decide (limit - r ≥ 4) = false := decide_eq_false hlimr
                        dsimp only [r] at hlimr_f
                        simp only [hlimr_f, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                        apply Exists.intro
                        constructor
                        · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                          rw [h0_13, hr1, hr2, hr3, hr4, hr5, hr6, h149_171, h171_180,
                            h180_210, h190_219]
                          split_res_fuel 3
                          rw [runJvmResFast_ifle_fallthrough
                            (by rw [compareUnsigned_sle_zero]; exact decide_eq_false hlimr)]
                          norm_res_fuel
                          have h220 : f_Algorithm_parseRLEHeader_prog.drop 220 =
                              .iconst 2 :: .ireturn :: f_Algorithm_parseRLEHeader_prog.drop 222 := by drop_prefix 2
                          rw [h220]
                          rw [runJvmResFast_iconst_ireturn]
                        · constructor <;> rfl
                    · have hr4_f : decide (r + 4 ≤ limit) = false := decide_eq_false h_r4
                      dsimp only [r] at hr4_f
                      simp only [hr4_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                      apply Exists.intro
                      constructor
                      · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                        rw [h0_13, hr1, hr2, hr3, hr4, hr5, hr6, h149_171, h171_180, h180_210]
                        split_res_fuel 3
                        rw [runJvmResFast_ifle_fallthrough (by rw [compareUnsigned_sle_zero]; exact hr4_f)]
                        norm_res_fuel
                        have h211 : f_Algorithm_parseRLEHeader_prog.drop 211 =
                            .iconst 2 :: .ireturn :: f_Algorithm_parseRLEHeader_prog.drop 213 := by drop_prefix 2
                        rw [h211]
                        rw [runJvmResFast_iconst_ireturn]
                      · constructor <;> rfl

/-! #### 4. `deserializeRLE___closed__0`, `deserializeRLE___closed__1`, `parseRLEData___closed__2` -/

private theorem stepStatic_checkNotNullExprVal
    {pc : Nat} {msg : JvmVal} {addr : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, msg :: .heapRef addr :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullExpressionValue" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, hp⟩) := rfl

theorem deserializeRLE_closed0_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hstat : jh.statics = []) :
    let arrAddr := jh.objects.size + 1
    ∃ st', runJvmRes 35 f_Algorithm_deserializeRLE___closed__0_prog
        ⟨0, [], fun _ => .null, jh, hp⟩ = some (.heapRef arrAddr, st') ∧
      st'.jvmHeap.get? arrAddr =
        some (.objArray "java/lang/Object"
          #[.allocRef "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"]) ∧
      HeapExtends jh st'.jvmHeap ∧ st'.heap = hp := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  let jh0 : Jvm.JvmHeap AlgExt := ⟨objs, []⟩
  let jh1 := (jh0.alloc (.objArray "java/lang/Object" #[])).2
  let a0 := jh0.objects.size
  have hget1 : jh1.get? a0 = some (.objArray "java/lang/Object" #[]) :=
    jvmHeap_get?_alloc_self _ _
  let jh2 := (jh1.alloc (.objArray "java/lang/Object" #[.null])).2
  let a1 := jh1.objects.size
  have ha1_eq : a1 = jh0.objects.size + 1 := by simp [a1, jh1, Jvm.JvmHeap.alloc]
  have hget2 : jh2.get? a1 = some (.objArray "java/lang/Object" #[.null]) :=
    jvmHeap_get?_alloc_self _ _
  have hget1_2 : jh2.get? a0 = some (.objArray "java/lang/Object" #[]) :=
    heapExtends_alloc jh1 _ a0 _ hget1
  let jh3 := jh2.set a1 (.objArray "java/lang/Object"
    #[.allocRef "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"])
  have hget3 : jh3.get? a1 = some (.objArray "java/lang/Object"
      #[.allocRef "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"]) :=
    jvmHeap_get?_set_self hget2
  have hext : HeapExtends jh0 jh3 := by
    intro i o hgi
    have hlt : i < jh0.objects.size := by
      simp only [Jvm.JvmHeap.get?] at hgi
      by_cases h' : i < jh0.objects.size
      · exact h'
      · rw [Array.getElem?_eq_none (Nat.le_of_not_lt h')] at hgi
        contradiction
    have hne : i ≠ a1 := by omega
    rw [jvmHeap_get?_set_ne _ _ hne]
    exact heapExtends_trans (heapExtends_alloc _ _) (heapExtends_alloc _ _) i o hgi
  apply Exists.intro
  constructor
  · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_deserializeRLE___closed__0_prog)]
    step_drop 4
    rw [runJvmResFast_getstatic_step rfl rfl]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_anewarray_obj (by decide), show (0 : UInt32).toNat = 0 from rfl]; norm_res_fuel
    rw [show Array.replicate 0 (JvmVal.null : JvmVal) = #[] from rfl]
    step_drop 7
    heap_step_nonbranch_chunks; norm_res_fuel; dsimp only
    dsimp only [jh1, jh0, a0] at hget1
    rw [runJvmResFast_arraylength_obj hget1]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel; dsimp only
    rw [runJvmResFast_invokestatic_step (stepStatic_arraysCopyOf_obj (by decide) hget1)]
    norm_res_fuel
    dsimp only [jh1, jh0, a0, a1] at hget1_2 hget2
    change runJvmResFast 24 f_Algorithm_deserializeRLE___closed__0_prog (10 + 1)
        (List.drop 11 f_Algorithm_deserializeRLE___closed__0_prog)
        ⟨10 + 1, [.heapRef jh1.objects.size],
          setLocal (setLocal (fun _ => .null) 0
            (.allocRef "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"))
            1 (.heapRef objs.size),
          jh2, hp⟩ = _
    step_drop 15
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_checkNotNullExprVal]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel; dsimp only
    rw [runJvmResFast_arraylength_obj hget1_2]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [show UInt32.ofNat (#[] : Array JvmVal).size = (0 : UInt32) from rfl]
    rw [runJvmResFast_aastore (idx := 0) hget2 (by decide) (by decide)]
    simp only [show (0 : UInt32).toNat = 0 from rfl]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [show ({ objects := objs } : Jvm.JvmHeap AlgExt) = jh0 from rfl]
    rw [show (jh0.alloc (Jvm.HeapObj.objArray "java/lang/Object" #[])).snd.objects.size = a1 from rfl]
    rw [show #[JvmVal.null].set 0 (.allocRef "com/alexvanyo/composelife/model/RLEWarning$EmptyFile") =
      #[.allocRef "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"] from rfl]
    rw [← (show a1 = objs.size + 1 from ha1_eq)]
  · rw [← (show a1 = objs.size + 1 from ha1_eq)]; exact ⟨hget3, hext, rfl⟩

private theorem stepStatic_deserializeRLE_closed0_heap
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_deserializeRLE___closed__0" "()[Ljava/lang/Object;" =
      let (addr, h') := jh.alloc (.objArray "java/lang/Object"
        #[.allocRef "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"])
      .inl (some ⟨pc + 1, .heapRef addr :: rest, locs, h', hp⟩) := rfl

private theorem stepSpecial_rleResult_init
    {pc : Nat} {marker cells warns status : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, marker :: cells :: warns :: status ::
        .allocRef "com/alexvanyo/composelife/model/RLEResult" ::
        .allocRef "com/alexvanyo/composelife/model/RLEResult" :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RLEResult" "<init>"
  "(Lcom/alexvanyo/composelife/model/RLEStatus;[Ljava/lang/Object;[JLkotlin/jvm/internal/DefaultConstructorMarker;)V" =
      let (addr, h') := jh.alloc (.instance "com/alexvanyo/composelife/model/RLEResult"
        [("status", status), ("warnings", warns), ("cells", cells)])
      .inl (some ⟨pc + 1, .heapRef addr :: rest, locs, h', hp⟩) := rfl

theorem deserializeRLE_closed1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hstat : jh.statics = []) :
    ∃ v st', runJvmRes 25 f_Algorithm_deserializeRLE___closed__1_prog
        ⟨0, [], fun _ => .null, jh, hp⟩ = some (v, st') ∧
      decodeRLEResult st' v = some ⟨.emptyFile, #[.emptyFile], #[]⟩ ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.heap = { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.noCells] } := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  let jh0 : Jvm.JvmHeap AlgExt := ⟨objs, []⟩
  let warnArrObj : Jvm.HeapObj AlgExt :=
    .objArray "java/lang/Object" #[.allocRef "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"]
  let jh1 := (jh0.alloc warnArrObj).2
  let warnAddr := jh0.objects.size
  let resObj : Jvm.HeapObj AlgExt := .instance "com/alexvanyo/composelife/model/RLEResult"
    [("status", .ext (.rleStatus .emptyFile)), ("warnings", .heapRef warnAddr),
      ("cells", .ext (.u64Ref hp.u64Arrays.length))]
  let jh2 := (jh1.alloc resObj).2
  let resAddr := jh1.objects.size
  let hp1 : AlgHeap := { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.noCells] }
  let locs2 := setLocal (setLocal (fun _ => (.null : JvmVal))
    0 (.ext (.u64Ref hp.u64Arrays.length))) 1 (.heapRef warnAddr)
  let stFinal : JvmState := ⟨12, [.heapRef resAddr], locs2, jh2, hp1⟩
  have hrun : runJvmRes 25 f_Algorithm_deserializeRLE___closed__1_prog
      ⟨0, [], fun _ => .null, jh0, hp⟩ = some (.heapRef resAddr, stFinal) := by
    apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    split_res_fuel 14
    conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_deserializeRLE___closed__1_prog)]
    step_drop 13
    rw [runJvmResFast_invokestatic_step stepStatic_noCells_rle]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step stepStatic_deserializeRLE_closed0_heap]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_checkcast_step (by rfl)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_invokespecial_step stepSpecial_rleResult_init]; norm_res_fuel
    rw [runJvmResFast_areturn]
    rfl
  refine ⟨.heapRef resAddr, stFinal, hrun, ?_, ?_, rfl⟩
  · have hgetRes : jh2.get? resAddr = some resObj := jvmHeap_get?_alloc_self _ _
    have hgetWarn : jh2.get? warnAddr = some warnArrObj :=
      heapExtends_alloc jh1 resObj warnAddr warnArrObj (jvmHeap_get?_alloc_self _ _)
    have hu64 : hp1.u64Arrays[hp.u64Arrays.length]? = some Algorithm.noCells := by
      simp [hp1]
    simp only [decodeRLEResult, stFinal, hgetRes, resObj, List.lookup]
    simp [hgetWarn, warnArrObj, hu64, decodeRLEWarning, Algorithm.noCells]
  · exact heapExtends_trans (heapExtends_alloc _ _) (heapExtends_alloc _ _)

theorem parseRLEData_closed2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ st', runJvmRes 10 f_Algorithm_parseRLEData___closed__2_prog ⟨0, [], fun _ => .null, jh, hp⟩ =
        some (.heapRef jh.objects.size, st') ∧
      st'.jvmHeap = (jh.alloc (.objArray "java/lang/Object" #[])).2 ∧ st'.heap = hp := by
  apply Exists.intro
  constructor
  · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    split_res_fuel 4
    conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_parseRLEData___closed__2_prog)]
    step_drop 3
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_anewarray_obj (by decide), show (0 : UInt32).toNat = 0 from rfl]; norm_res_fuel
    rw [runJvmResFast_areturn]
  · constructor <;> rfl

end Algorithm.JvmVerification
