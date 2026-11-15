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
import JvmSemantics
import proofs.JvmEquiv.Infra
import proofs.JvmEquiv.FlatInfra
import proofs.JvmEquiv.HeapInfra
import proofs.JvmEquiv.SharedStep
import proofs.JvmEquiv.StepExt

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode
set_option Elab.async false

/-! ### Life105 Codec Equivalence (`Family4`) -/

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

local macro "norm_fuel_nz" : tactic =>
  `(tactic| (conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]))

/-! #### Heap Extension, `Life105` Decoders, and Private Static Helpers -/

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

private theorem decodeLife105Warning_mono {h1 h2 : Jvm.JvmHeap AlgExt}
    (hext : HeapExtends h1 h2) {v : JvmVal} {w : Algorithm.Life105Warning}
    (hdec : decodeLife105Warning h1 v = some w) : decodeLife105Warning h2 v = some w := by
  cases v with
  | allocRef cls =>
    dsimp only [decodeLife105Warning] at hdec ⊢
    by_cases hc : cls = "com/alexvanyo/composelife/model/Life105Warning$EmptyFile"
    · subst hc; exact hdec
    · simp [hc] at hdec
  | heapRef a =>
    dsimp only [decodeLife105Warning] at hdec ⊢
    cases hg : h1.get? a with
    | none => simp [hg] at hdec
    | some obj =>
      rw [hg] at hdec
      rw [hext a obj hg]
      exact hdec
  | _ => simp [decodeLife105Warning] at hdec

private theorem foldlM_decodeLife105Warning_mono {h1 h2 : Jvm.JvmHeap AlgExt}
    (hext : HeapExtends h1 h2) (elems : Array JvmVal) (acc ws : Array Algorithm.Life105Warning)
    (hm : elems.foldlM (fun a v => (decodeLife105Warning h1 v).map a.push) acc = some ws) :
    elems.foldlM (fun a v => (decodeLife105Warning h2 v).map a.push) acc = some ws := by
  rw [← Array.foldlM_toList] at hm ⊢
  suffices h : ∀ (l : List JvmVal) (a ws : Array Algorithm.Life105Warning),
      l.foldlM (fun a v => (decodeLife105Warning h1 v).map a.push) a = some ws →
      l.foldlM (fun a v => (decodeLife105Warning h2 v).map a.push) a = some ws from
    h elems.toList acc ws hm
  intro l
  induction l with
  | nil => intro a ws hnil; simpa using hnil
  | cons v vs ih =>
    intro a ws hcons
    simp only [List.foldlM_cons] at hcons ⊢
    cases hdv : decodeLife105Warning h1 v with
    | none => simp [hdv] at hcons
    | some w =>
      rw [decodeLife105Warning_mono hext hdv]
      rw [hdv] at hcons
      exact ih (a.push w) ws hcons

private theorem encodeLife105Warning_spec (h : Jvm.JvmHeap AlgExt)
    (w : Algorithm.Life105Warning) :
    HeapExtends h (encodeLife105Warning h w).2 ∧
      decodeLife105Warning (encodeLife105Warning h w).2 (encodeLife105Warning h w).1 = some w := by
  cases w with
  | emptyFile => exact ⟨heapExtends_refl h, rfl⟩
  | unexpectedInput inp ln col =>
    refine ⟨heapExtends_alloc _ _, ?_⟩
    simp [encodeLife105Warning, decodeLife105Warning, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc,
      List.lookup, Jvm.JvmVal.asI32]

private def decodeLife105Status (h : Jvm.JvmHeap AlgExt) : JvmVal → Option Algorithm.Life105Status
  | .allocRef "com/alexvanyo/composelife/model/Life105Status$Ok" => some .ok
  | .allocRef "com/alexvanyo/composelife/model/Life105Status$RuleNotSupported" => some .ruleNotSupported
  | .heapRef addr =>
    match h.get? addr with
    | some (.instance "com/alexvanyo/composelife/model/Life105Status$InvalidHeader" flds) =>
      match flds.lookup "line" with
      | some (.str line) => some (.invalidHeader line)
      | _ => none
    | some (.instance "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput" flds) =>
      match flds.lookup "input", flds.lookup "lineIndex", flds.lookup "columnIndex" with
      | some (.str inp), some ln, some col => some (.unexpectedInput inp ln.asI32 col.asI32)
      | _, _, _ => none
    | _ => none
  | _ => none

private def decodeLife105Result (st : JvmState) : JvmVal → Option Algorithm.Life105Result
  | .heapRef addr =>
    match st.jvmHeap.get? addr with
    | some (.instance "com/alexvanyo/composelife/model/Life105Result" flds) =>
      match flds.lookup "status", flds.lookup "warnings", flds.lookup "cells" with
      | some statusVal, some warnsVal, some (.ext (.u64Ref cId)) =>
        match decodeLife105Status st.jvmHeap statusVal, st.heap.u64Arrays[cId]? with
        | some status, some cells =>
          let warnsOpt : Option (Array Algorithm.Life105Warning) := match warnsVal with
            | .strArr xs => if xs.isEmpty then some #[] else none
            | .heapRef wAddr =>
              match st.jvmHeap.get? wAddr with
              | some (.objArray _ elems) =>
                elems.foldlM (fun acc v => (decodeLife105Warning st.jvmHeap v).map acc.push) #[]
              | _ => none
            | _ => none
          warnsOpt.map fun warns => ⟨status, warns, cells⟩
        | _, _ => none
      | _, _, _ => none
    | _ => none
  | _ => none

private theorem decodeLife105Status_mono {h1 h2 : Jvm.JvmHeap AlgExt}
    (hext : HeapExtends h1 h2) {v : JvmVal} {s : Algorithm.Life105Status}
    (hdec : decodeLife105Status h1 v = some s) : decodeLife105Status h2 v = some s := by
  cases v with
  | allocRef cls =>
    dsimp only [decodeLife105Status] at hdec ⊢
    by_cases hc1 : cls = "com/alexvanyo/composelife/model/Life105Status$Ok"
    · subst hc1; exact hdec
    · by_cases hc2 : cls = "com/alexvanyo/composelife/model/Life105Status$RuleNotSupported"
      · subst hc2; exact hdec
      · simp [hc1, hc2] at hdec
  | heapRef a =>
    dsimp only [decodeLife105Status] at hdec ⊢
    cases hg : h1.get? a with
    | none => simp [hg] at hdec
    | some obj =>
      rw [hg] at hdec
      rw [hext a obj hg]
      exact hdec
  | _ => simp [decodeLife105Status] at hdec

private theorem encodeLife105Warnings_foldl_spec
    (ws : List Algorithm.Life105Warning) (acc : Array JvmVal)
    (h : Jvm.JvmHeap AlgExt) (pfx : Array Algorithm.Life105Warning)
    (hpfx : acc.foldlM (fun a v => (decodeLife105Warning h v).map a.push) #[] = some pfx) :
    let step : Array JvmVal × Jvm.JvmHeap AlgExt → Algorithm.Life105Warning →
        Array JvmVal × Jvm.JvmHeap AlgExt :=
      fun (a, ch) w => let (wv, nh) := encodeLife105Warning ch w; (a.push wv, nh)
    HeapExtends h (ws.foldl step (acc, h)).2 ∧
      (ws.foldl step (acc, h)).1.foldlM
        (fun a v => (decodeLife105Warning (ws.foldl step (acc, h)).2 v).map a.push) #[] =
        some (pfx ++ ws.toArray) := by
  intro step
  induction ws generalizing acc h pfx with
  | nil => exact ⟨heapExtends_refl h, by simpa using hpfx⟩
  | cons w ws ih =>
    simp only [List.foldl_cons, step]
    have hs := encodeLife105Warning_spec h w
    have hacc_mono := foldlM_decodeLife105Warning_mono hs.1 acc #[] pfx hpfx
    have hnext : (acc.push (encodeLife105Warning h w).1).foldlM
        (fun a v => (decodeLife105Warning (encodeLife105Warning h w).2 v).map a.push) #[] =
        some (pfx.push w) := by
      rw [← Array.foldlM_toList, Array.toList_push, List.foldlM_append]
      have h1 : acc.toList.foldlM
          (fun a v => (decodeLife105Warning (encodeLife105Warning h w).2 v).map a.push) #[] = some pfx := by
        rwa [Array.foldlM_toList]
      rw [h1]
      simp [hs.2]
    have hrec := ih (acc.push (encodeLife105Warning h w).1) (encodeLife105Warning h w).2
      (pfx.push w) hnext
    refine ⟨heapExtends_trans hs.1 hrec.1, ?_⟩
    have hlist : (pfx.push w ++ ws.toArray).toList = (pfx ++ (w :: ws).toArray).toList := by simp
    have hpush_app : pfx.push w ++ ws.toArray = pfx ++ (w :: ws).toArray := by
      rw [← @Array.toArray_toList _ (pfx.push w ++ ws.toArray),
        ← @Array.toArray_toList _ (pfx ++ (w :: ws).toArray), hlist]
    rw [← hpush_app]
    exact hrec.2

private theorem encodeLife105Result_spec_aux
    (jh h1 : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (statusVal : JvmVal)
    (st : Algorithm.Life105Status) (warns : Array Algorithm.Life105Warning) (cells : Array UInt64)
    (_hext1 : HeapExtends jh h1) (hstDec : decodeLife105Status h1 statusVal = some st) :
    let step : Array JvmVal × Jvm.JvmHeap AlgExt → Algorithm.Life105Warning →
        Array JvmVal × Jvm.JvmHeap AlgExt :=
      fun (a, ch) w => let (wv, nh) := encodeLife105Warning ch w; (a.push wv, nh)
    let p2 := warns.foldl step (#[], h1)
    let p3 := p2.2.alloc (.objArray "java/lang/Object" p2.1)
    let cId := hp.u64Arrays.length
    let u64s' := hp.u64Arrays ++ [cells]
    let p4 := p3.2.alloc (.instance "com/alexvanyo/composelife/model/Life105Result"
      [("status", statusVal), ("warnings", .heapRef p3.1), ("cells", .ext (.u64Ref cId))])
    decodeLife105Result ⟨0, [], fun _ => .null, p4.2, { hp with u64Arrays := u64s' }⟩ (.heapRef p4.1) =
      some ⟨st, warns, cells⟩ := by
  dsimp only
  let step : Array JvmVal × Jvm.JvmHeap AlgExt → Algorithm.Life105Warning →
      Array JvmVal × Jvm.JvmHeap AlgExt :=
    fun (a, ch) w => let (wv, nh) := encodeLife105Warning ch w; (a.push wv, nh)
  let p2 := warns.foldl step (#[], h1)
  let p3 := p2.2.alloc (.objArray "java/lang/Object" p2.1)
  let cId := hp.u64Arrays.length
  let u64s' := hp.u64Arrays ++ [cells]
  let p4 := p3.2.alloc (.instance "com/alexvanyo/composelife/model/Life105Result"
    [("status", statusVal), ("warnings", .heapRef p3.1), ("cells", .ext (.u64Ref cId))])
  have hfold := encodeLife105Warnings_foldl_spec warns.toList #[] h1 #[] rfl
  have hfold_eq : warns.foldl step (#[], h1) = warns.toList.foldl step (#[], h1) :=
    (Array.foldl_toList step).symm
  have hext2 : HeapExtends h1 p2.2 := by
    dsimp only [p2]; rw [hfold_eq]; exact hfold.1
  have hdec2 : p2.1.foldlM (fun a v => (decodeLife105Warning p2.2 v).map a.push) #[] = some warns := by
    have h := hfold.2
    simp only [Array.empty_append, Array.toArray_toList] at h
    dsimp only [p2]; rw [hfold_eq]; exact h
  have hext3 : HeapExtends h1 p3.2 := heapExtends_trans hext2 (heapExtends_alloc _ _)
  have hext4 : HeapExtends p3.2 p4.2 := heapExtends_alloc _ _
  have hresGet : p4.2.get? p4.1 =
      some (.instance "com/alexvanyo/composelife/model/Life105Result"
        [("status", statusVal), ("warnings", .heapRef p3.1), ("cells", .ext (.u64Ref cId))]) := by
    simp [p4, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  have hwArrGet : p4.2.get? p3.1 = some (.objArray "java/lang/Object" p2.1) := by
    apply hext4
    simp [p3, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  have hstFin := decodeLife105Status_mono (heapExtends_trans hext3 hext4) hstDec
  have hwFin := foldlM_decodeLife105Warning_mono
    (heapExtends_trans (heapExtends_alloc _ _) hext4) p2.1 #[] warns hdec2
  have hu64 : u64s'[cId]? = some cells := by
    dsimp only [u64s', cId]
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  dsimp only [p2, p3, p4, step, cId, u64s'] at hresGet hwArrGet hstFin hwFin hu64
  dsimp only [decodeLife105Result]
  rw [hresGet]
  simp [List.lookup, hstFin, hwArrGet, hwFin]

private theorem decodeLife105Result_encode
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (res : Algorithm.Life105Result) :
    let (v, jh', u64s') := encodeLife105Result jh hp.u64Arrays res
    decodeLife105Result ⟨0, [], fun _ => .null, jh', { hp with u64Arrays := u64s' }⟩ v = some res := by
  rcases res with ⟨st, warns, cells⟩
  cases st with
  | ok =>
    exact encodeLife105Result_spec_aux jh jh hp (.allocRef "com/alexvanyo/composelife/model/Life105Status$Ok")
      .ok warns cells (heapExtends_refl jh) rfl
  | ruleNotSupported =>
    exact encodeLife105Result_spec_aux jh jh hp
      (.allocRef "com/alexvanyo/composelife/model/Life105Status$RuleNotSupported")
      .ruleNotSupported warns cells (heapExtends_refl jh) rfl
  | invalidHeader line =>
    let p := jh.alloc (.instance "com/alexvanyo/composelife/model/Life105Status$InvalidHeader" [("line", .str line)])
    exact encodeLife105Result_spec_aux jh p.2 hp (.heapRef p.1) (.invalidHeader line) warns cells
      (heapExtends_alloc _ _) (by simp [p, decodeLife105Status, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc])
  | unexpectedInput inp ln col =>
    let p := jh.alloc (.instance "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput"
      [("input", .str inp), ("lineIndex", .i32 ln), ("columnIndex", .i32 col)])
    exact encodeLife105Result_spec_aux jh p.2 hp (.heapRef p.1) (.unexpectedInput inp ln col) warns cells
      (heapExtends_alloc _ _)
      (by simp [p, decodeLife105Status, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc, List.lookup, Jvm.JvmVal.asI32])

private def decodeOptParsedCoords (jh : Jvm.JvmHeap AlgExt) :
    JvmVal → Option (Option Algorithm.ParsedCoords)
  | .heapRef outerAddr =>
    match jh.get? outerAddr with
    | some (.objArray _ elems) =>
      match elems.toList with
      | [.boxedInt 0] => some none
      | [.boxedInt 1, .heapRef innerAddr] =>
        match jh.get? innerAddr with
        | some (.objArray _ inner) =>
          match inner.toList with
          | [.boxedInt 0, .boxedInt xv, .null, .null, .null, .boxedInt yv] =>
            some (some ⟨xv.toInt32, yv.toInt32⟩)
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

private theorem decodeOptParsedCoords_some
    {jh : Jvm.JvmHeap AlgExt} {outerAddr innerAddr : Nat} {x y : Int32}
    (ho : jh.get? outerAddr = some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr]))
    (hi : jh.get? innerAddr =
      some (.objArray "java/lang/Object"
        #[.boxedInt 0, .boxedInt x.toUInt32, .null, .null, .null, .boxedInt y.toUInt32])) :
    decodeOptParsedCoords jh (.heapRef outerAddr) = some (some ⟨x, y⟩) := by
  simp only [decodeOptParsedCoords, ho, hi, Int32.toInt32_toUInt32]

private theorem stepStatic_checkNotNull_heap
    {pc : Nat} {msg obj : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hnull : obj.isNull = false) :
    stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      (if obj.isNull then .inr none else .inl (some ⟨pc + 1, rest, locs, jh, hp⟩)) := rfl
  rw [hfn, hnull]; rfl

private theorem stepStatic_checkNotNullParameter_heap
    {pc : Nat} {msg obj : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hnull : obj.isNull = false) :
    stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      (if obj.isNull then .inr none else .inl (some ⟨pc + 1, rest, locs, jh, hp⟩)) := rfl
  rw [hfn, hnull]; rfl

private theorem stepStatic_checkNotNullExpressionValue_heap
    {pc : Nat} {msg obj : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hnull : obj.isNull = false) :
    stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullExpressionValue" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, msg :: obj :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "checkNotNullExpressionValue" "(Ljava/lang/Object;Ljava/lang/String;)V" =
      (if obj.isNull then .inr none else .inl (some ⟨pc + 1, rest, locs, jh, hp⟩)) := rfl
  rw [hfn, hnull]; rfl

private theorem stepStatic_noCells_105_heap
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "Life105LeanKt" "f_Algorithm_noCells" "()[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref u64.length) :: rest, locs, jh, ⟨ar, u64 ++ [#[]], asc⟩⟩) := rfl

private theorem stepStatic_closed5_105_heap
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_deserializeLife105___closed__5" "()[Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.objArray "java/lang/Object"
          #[.allocRef "com/alexvanyo/composelife/model/Life105Warning$EmptyFile"])).2, hp⟩) := rfl

private theorem stepStatic_closed1_105_heap
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_deserializeLife105___closed__1" "()[Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.objArray "java/lang/Object" #[])).2, hp⟩) := rfl

private theorem stepSpecial_life105Result_init
    {pc : Nat} {marker cells warns status : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    (stepInvokeSpecial ⟨pc, marker :: cells :: warns :: status ::
        .allocRef "com/alexvanyo/composelife/model/Life105Result" ::
        .allocRef "com/alexvanyo/composelife/model/Life105Result" :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/Life105Result" "<init>"
 "(Lcom/alexvanyo/composelife/model/Life105Status;[Ljava/lang/Object;[JLkotlin/jvm/internal/DefaultConstructorMarker;)V"
    ) =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.instance "com/alexvanyo/composelife/model/Life105Result"
          [("status", status), ("warnings", warns), ("cells", cells)])).2, hp⟩) := rfl

private theorem stepStatic_intCompareUnsigned_105
    {pc : Nat} {b a : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, b :: a :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "java/lang/Integer" "compareUnsigned" "(II)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a.asI32 == b.asI32 then 0 else if a.asI32 < b.asI32 then 4294967295 else 1) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩) := rfl

private theorem stepStatic_scanDigitSet_heap
    {pc : Nat} {mask p limit : UInt32} {addr : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array UInt8} (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .i32 mask :: .i32 p :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_scanDigitSet-7IvYBaQ" "([BIII)Lkotlin/Pair;" =
      let r := Algorithm.scanDigitSet ⟨elems⟩ limit p mask
      .inl (some ⟨pc + 1, .pair (.boxedUInt r.1) (.boxedUInt r.2) :: rest, locs, jh, hp⟩) := by
  change (match decodeBytes
      (⟨pc, .i32 mask :: .i32 p :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩ : JvmState)
      (.heapRef addr) with
    | some bytes =>
      let r := Algorithm.scanDigitSet bytes limit p mask
      Sum.inl (some (⟨pc + 1, .pair (.boxedUInt r.1) (.boxedUInt r.2) :: rest, locs, jh, hp⟩ : JvmState))
    | none => Sum.inr none) = _
  simp only [decodeBytes, hget]

private theorem stepStatic_isRowRest_heap
    {pc : Nat} {p limit : UInt32} {addr : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elems : Array UInt8} (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .i32 p :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_isRowRest-BltQuoY" "([BII)Z" =
      .inl (some ⟨pc + 1, .i32 (if Algorithm.isRowRest ⟨elems⟩ limit p then 1 else 0) :: rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 p :: .i32 limit :: .heapRef addr :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_isRowRest-BltQuoY" "([BII)Z" =
      match jh.get? addr with
      | some (.byteArray e) =>
        .inl (some ⟨pc + 1, .i32 (if Algorithm.isRowRest ⟨e⟩ limit p then 1 else 0) :: rest, locs, jh, hp⟩)
      | _ => .inr none := rfl
  rw [hfn, hget]

private theorem compareUnsigned_sle_zero (a b : UInt32) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.sle 0#32 =
      decide (a ≤ b) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b
    · have hle : a ≤ b := UInt32.le_of_lt h2
      simp [h1, h2, hle]
    · have hnle : ¬(a ≤ b) := by
        intro hle
        have hle' := UInt32.le_iff_toNat_le.mp hle
        have hlt' : ¬(a.toNat < b.toNat) := mt UInt32.lt_iff_toNat_lt.mpr h2
        have heq : a = b := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by
          dsimp only [UInt32.toNat] at hle' hlt'; omega))
        exact h1 (beq_iff_eq.mpr heq)
      simp [h1, h2, hnle]

private theorem signExtend_beq_const (c : UInt8)
    (hc : c ∈ ([32, 35, 42, 46, 47, 68, 78, 80, 82] : List UInt8)) (b : UInt8) :
    (UInt32.ofBitVec (b.toBitVec.signExtend 32) == c.toUInt32) = (b == c) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (revert b; decide)

/-! #### 1. Closed Constants & `formatBlockHeader` -/

theorem serializeLife105___closed__0_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = []) :
    ∃ v st', runJvmRes 10 f_Algorithm_serializeLife105___closed__0_prog
        ⟨0, [], fun _ => .null, jh, hp⟩ = some (v, st') ∧
      decodeStrArray st' v = some #[] := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  refine ⟨.heapRef objs.size, ?_, ?_, ?_⟩
  · exact ⟨2, [.heapRef objs.size], fun _ => .null,
      ({ objects := objs, statics := [] } : Jvm.JvmHeap AlgExt).alloc
        (.objArray "java/lang/Object" #[]) |>.2, hp⟩
  · apply runJvmRes_of_runJvmResFast0 10 _ _ _ rfl
    split_res_fuel 10
    dsimp only [f_Algorithm_serializeLife105___closed__0_prog, List.drop]
    heap_step_nonbranch_chunks
    norm_res_fuel
    rw [runJvmResFast_anewarray_obj (hslt := by decide)]
    heap_step_nonbranch_chunks
    rfl
  · simp [decodeStrArray, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]

theorem deserializeLife105___closed__1_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = []) :
    ∃ v st', runJvmRes 10 f_Algorithm_deserializeLife105___closed__1_prog
        ⟨0, [], fun _ => .null, jh, hp⟩ = some (v, st') ∧
      st'.jvmHeap.get? jh.objects.size = some (.objArray "java/lang/Object" #[]) ∧
      v = .heapRef jh.objects.size ∧ st'.heap = hp := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  let stFin : JvmState := ⟨2, [.heapRef objs.size], fun _ => .null,
    ({ objects := objs, statics := [] } : Jvm.JvmHeap AlgExt).alloc
      (.objArray "java/lang/Object" #[]) |>.2, hp⟩
  refine ⟨.heapRef objs.size, stFin, ?_, ?_, rfl, rfl⟩
  · apply runJvmRes_of_runJvmResFast0 10 _ _ _ rfl
    split_res_fuel 10
    dsimp only [f_Algorithm_deserializeLife105___closed__1_prog, List.drop]
    heap_step_nonbranch_chunks
    norm_res_fuel
    rw [runJvmResFast_anewarray_obj (hslt := by decide)]
    heap_step_nonbranch_chunks
    rfl
  · simp [stFin, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]

theorem deserializeLife105___closed__2_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = []) :
    ∃ v st', runJvmRes 25 f_Algorithm_deserializeLife105___closed__2_prog
        ⟨0, [], fun _ => .null, jh, hp⟩ = some (v, st') ∧
      decodeLife105Result st' v = some ⟨.ok, #[], #[]⟩ := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  let h1 : Jvm.JvmHeap AlgExt := ⟨objs.push (.objArray "java/lang/Object" #[]), []⟩
  let h2 : Jvm.JvmHeap AlgExt := ⟨(objs.push (.objArray "java/lang/Object" #[])).push
    (.instance "com/alexvanyo/composelife/model/Life105Result"
      [("status", .allocRef "com/alexvanyo/composelife/model/Life105Status$Ok"),
       ("warnings", .heapRef objs.size),
       ("cells", .ext (.u64Ref u64.length))]), []⟩
  refine ⟨.heapRef (objs.size + 1), ?_, ?_, ?_⟩
  · exact ⟨12, [.heapRef (objs.size + 1)],
      setLocal (setLocal (fun _ => .null) 0 (.ext (.u64Ref u64.length))) 1 (.heapRef objs.size),
      h2, ⟨ar, u64 ++ [#[]], asc⟩⟩
  · apply runJvmRes_of_runJvmResFast0 25 _ _ _ rfl
    split_res_fuel 25
    dsimp only [f_Algorithm_deserializeLife105___closed__2_prog, List.drop]
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_noCells_105_heap)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_closed1_105_heap)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
    rw [runJvmResFast_invokespecial_step (hs := stepSpecial_life105Result_init)]; norm_res_fuel
    heap_step_nonbranch_chunks
    simp only [h2, Jvm.JvmHeap.alloc, Array.size_push]
  · dsimp only [h2, h1, decodeLife105Result, Jvm.JvmHeap.get?]
    have hsz : (objs.push (.objArray "java/lang/Object" #[])).size = objs.size + 1 := by simp
    rw [← hsz, Array.getElem?_push_size]
    simp [List.lookup, decodeLife105Status]
    have hwget : ((objs.push (.objArray "java/lang/Object" #[])).push
        (.instance "com/alexvanyo/composelife/model/Life105Result"
          [("status", .allocRef "com/alexvanyo/composelife/model/Life105Status$Ok"),
           ("warnings", .heapRef objs.size),
           ("cells", .ext (.u64Ref u64.length))]))[objs.size]? =
        some (.objArray "java/lang/Object" #[]) := by
      rw [Array.getElem?_push_lt (by simp), Array.getElem_push_eq]
    rw [hwget]
    rfl

theorem deserializeLife105___closed__3_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = []) :
    ∃ v st', runJvmRes 25 f_Algorithm_deserializeLife105___closed__3_prog
        ⟨0, [], fun _ => .null, jh, hp⟩ = some (v, st') ∧
      decodeLife105Result st' v = some ⟨.ruleNotSupported, #[], #[]⟩ := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  let h1 : Jvm.JvmHeap AlgExt := ⟨objs.push (.objArray "java/lang/Object" #[]), []⟩
  let h2 : Jvm.JvmHeap AlgExt := ⟨(objs.push (.objArray "java/lang/Object" #[])).push
    (.instance "com/alexvanyo/composelife/model/Life105Result"
      [("status", .allocRef "com/alexvanyo/composelife/model/Life105Status$RuleNotSupported"),
       ("warnings", .heapRef objs.size),
       ("cells", .ext (.u64Ref u64.length))]), []⟩
  refine ⟨.heapRef (objs.size + 1), ?_, ?_, ?_⟩
  · exact ⟨12, [.heapRef (objs.size + 1)],
      setLocal (setLocal (fun _ => .null) 0 (.ext (.u64Ref u64.length))) 1 (.heapRef objs.size),
      h2, ⟨ar, u64 ++ [#[]], asc⟩⟩
  · apply runJvmRes_of_runJvmResFast0 25 _ _ _ rfl
    split_res_fuel 25
    dsimp only [f_Algorithm_deserializeLife105___closed__3_prog, List.drop]
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_noCells_105_heap)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_closed1_105_heap)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
    rw [runJvmResFast_invokespecial_step (hs := stepSpecial_life105Result_init)]; norm_res_fuel
    heap_step_nonbranch_chunks
    simp only [h2, Jvm.JvmHeap.alloc, Array.size_push]
  · dsimp only [h2, h1, decodeLife105Result, Jvm.JvmHeap.get?]
    have hsz : (objs.push (.objArray "java/lang/Object" #[])).size = objs.size + 1 := by simp
    rw [← hsz, Array.getElem?_push_size]
    simp [List.lookup, decodeLife105Status]
    have hwget : ((objs.push (.objArray "java/lang/Object" #[])).push
        (.instance "com/alexvanyo/composelife/model/Life105Result"
          [("status", .allocRef "com/alexvanyo/composelife/model/Life105Status$RuleNotSupported"),
           ("warnings", .heapRef objs.size),
           ("cells", .ext (.u64Ref u64.length))]))[objs.size]? =
        some (.objArray "java/lang/Object" #[]) := by
      rw [Array.getElem?_push_lt (by simp), Array.getElem_push_eq]
    rw [hwget]
    rfl

theorem deserializeLife105___closed__5_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = []) :
    ∃ v st', runJvmRes 35 f_Algorithm_deserializeLife105___closed__5_prog
        ⟨0, [], fun _ => .null, jh, hp⟩ = some (v, st') ∧
      v = .heapRef (jh.objects.size + 1) ∧ st'.heap = hp ∧
      st'.jvmHeap.get? (jh.objects.size + 1) =
        some (.objArray "java/lang/Object"
          #[.allocRef "com/alexvanyo/composelife/model/Life105Warning$EmptyFile"]) := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  let emptyArr : Jvm.HeapObj AlgExt := .objArray "java/lang/Object" #[]
  let wArr : Jvm.HeapObj AlgExt := .objArray "java/lang/Object"
    #[.allocRef "com/alexvanyo/composelife/model/Life105Warning$EmptyFile"]
  let h1 : Jvm.JvmHeap AlgExt := ⟨objs.push emptyArr, []⟩
  let h2 : Jvm.JvmHeap AlgExt := ⟨(objs.push emptyArr).push (.objArray "java/lang/Object" #[.null]), []⟩
  let h3 : Jvm.JvmHeap AlgExt := h2.set (objs.size + 1) wArr
  refine ⟨.heapRef (objs.size + 1), ⟨25, [.heapRef (objs.size + 1)],
    setLocal (setLocal (setLocal (setLocal (setLocal (fun _ => .null)
      0 (.allocRef "com/alexvanyo/composelife/model/Life105Warning$EmptyFile"))
      1 (.heapRef objs.size)) 2 (.heapRef (objs.size + 1)))
      3 (.heapRef (objs.size + 1))) 4 (.i32 0),
    h3, hp⟩, ?_, rfl, rfl, ?_⟩
  · have hrep : Array.replicate (0 : UInt32).toNat (JvmVal.null : JvmVal) = #[] := rfl
    have hset : (#[.null] : Array JvmVal).set 0
        (.allocRef "com/alexvanyo/composelife/model/Life105Warning$EmptyFile") (by decide) =
        #[.allocRef "com/alexvanyo/composelife/model/Life105Warning$EmptyFile"] := rfl
    apply runJvmRes_of_runJvmResFast0 35 _ _ _ rfl
    split_res_fuel 35
    dsimp only [f_Algorithm_deserializeLife105___closed__5_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_anewarray_obj (hslt := by decide)]; norm_res_fuel
    rw [hrep]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_arraylength_obj (cls := "java/lang/Object") (elems := #[])
      (hget := by simp [Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc])]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_arraysCopyOf_obj
      (elemCls := "java/lang/Object") (elems := #[]) (hslt := by decide)
      (hget := by simp [Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]))]
    norm_res_fuel
    have hcopy : Array.ofFn (n := (UInt32.ofNat (#[] : Array JvmVal).size + 1).toNat)
        (fun i => if h : i.val < (#[] : Array JvmVal).size then (#[] : Array JvmVal)[i.val] else .null) =
        #[.null] := rfl
    rw [hcopy]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNullExpressionValue_heap rfl)]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_arraylength_obj (cls := "java/lang/Object") (elems := #[])
      (hget := by simp [Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc, Array.getElem?_push_lt])]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    have hidx0 : UInt32.ofNat (#[] : Array JvmVal).size = 0 := rfl
    have hsz1 : (({ objects := objs, statics := [] } : Jvm.JvmHeap AlgExt).alloc emptyArr).2.objects.size =
        objs.size + 1 := by simp [Jvm.JvmHeap.alloc]
    rw [hidx0, hsz1]
    have hget2 : ((({ objects := objs, statics := [] } : Jvm.JvmHeap AlgExt).alloc emptyArr).2.alloc
        (.objArray "java/lang/Object" #[.null])).2.get? (objs.size + 1) =
        some (.objArray "java/lang/Object" #[.null]) := by
      simp only [Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
      have hsz : objs.size + 1 = (objs.push emptyArr).size := by simp
      rw [hsz, Array.getElem?_push_size]
    rw [runJvmResFast_aastore (cls := "java/lang/Object") (elems := #[.null])
      (hget := hget2) (hslt := by decide) (hlt := by decide)]
    norm_res_fuel
    heap_step_nonbranch_chunks
    simp only [h2, h3, wArr, emptyArr, Jvm.JvmHeap.alloc, Jvm.JvmHeap.set, Array.size_push]
    rfl
  · simp only [h3, h2, Jvm.JvmHeap.get?, Jvm.JvmHeap.set, Array.size_push]
    rw [dite_eq_left_of_eq_true (eq_true (by omega))]
    simp [wArr]

theorem deserializeLife105___closed__6_equiv (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = []) :
    ∃ v st', runJvmRes 25 f_Algorithm_deserializeLife105___closed__6_prog
        ⟨0, [], fun _ => .null, jh, hp⟩ = some (v, st') ∧
      decodeLife105Result st' v = some ⟨.ok, #[.emptyFile], #[]⟩ := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  let wArr : Jvm.HeapObj AlgExt := .objArray "java/lang/Object"
    #[.allocRef "com/alexvanyo/composelife/model/Life105Warning$EmptyFile"]
  let h1 : Jvm.JvmHeap AlgExt := ({ objects := objs, statics := [] } : Jvm.JvmHeap AlgExt).alloc wArr |>.2
  let h2 := (h1.alloc (.instance "com/alexvanyo/composelife/model/Life105Result"
    [("status", .allocRef "com/alexvanyo/composelife/model/Life105Status$Ok"),
     ("warnings", .heapRef objs.size),
     ("cells", .ext (.u64Ref u64.length))])).2
  refine ⟨.heapRef (objs.size + 1), ?_, ?_, ?_⟩
  · exact ⟨12, [.heapRef (objs.size + 1)],
      setLocal (setLocal (fun _ => .null) 0 (.ext (.u64Ref u64.length))) 1 (.heapRef objs.size),
      h2, ⟨ar, u64 ++ [#[]], asc⟩⟩
  · apply runJvmRes_of_runJvmResFast0 25 _ _ _ rfl
    split_res_fuel 25
    dsimp only [f_Algorithm_deserializeLife105___closed__6_prog, List.drop]
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_noCells_105_heap)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_closed5_105_heap)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 5; arg 1; simp only [Nat.reduceAdd]
    rw [runJvmResFast_invokespecial_step (hs := stepSpecial_life105Result_init)]; norm_res_fuel
    heap_step_nonbranch_chunks
    simp only [h2, h1, Jvm.JvmHeap.alloc, Array.size_push]
    rfl
  · dsimp only [h2, h1, decodeLife105Result, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    have hsz : (objs.push wArr).size = objs.size + 1 := by simp
    rw [← hsz, Array.getElem?_push_size]
    simp [List.lookup, decodeLife105Status]
    have hwget : ((objs.push wArr).push
        (.instance "com/alexvanyo/composelife/model/Life105Result"
          [("status", .allocRef "com/alexvanyo/composelife/model/Life105Status$Ok"),
           ("warnings", .heapRef objs.size),
           ("cells", .ext (.u64Ref u64.length))]))[objs.size]? = some wArr := by
      rw [Array.getElem?_push_lt (by simp), Array.getElem_push_eq]
    rw [hwget]
    rfl

private theorem signExtend_eq_u32 {b c : UInt8} {u : UInt32}
    (hb : b = c) (hu : u = c.toUInt32) (hc : c ∈ [32, 35, 42, 46, 47, 68, 78, 80, 82]) :
    UInt32.ofBitVec (b.toBitVec.signExtend 32) = u := by
  rw [hb, hu]
  exact beq_iff_eq.mp (by simp [signExtend_beq_const c hc c])

private theorem signExtend_bne_u32 {b c : UInt8} {u : UInt32}
    (hb : b ≠ c) (hu : u = c.toUInt32) (hc : c ∈ [32, 35, 42, 46, 47, 68, 78, 80, 82]) :
    (UInt32.ofBitVec (b.toBitVec.signExtend 32) == u) = false := by
  rw [hu, signExtend_beq_const c hc b]
  exact beq_false_of_ne hb

private theorem runJvmResFast_ireturn_step (f : Nat) (prog : List JvmInstr) (pc : Nat)
    (rest : List JvmInstr) (v : JvmVal) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    runJvmResFast (f + 1) prog pc (.ireturn :: rest) ⟨pc, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := rfl

private theorem runJvmResFast_iconst_ireturn_step (f : Nat) (prog : List JvmInstr) (pc : Nat)
    (rest : List JvmInstr) (c : UInt32) (stk : List JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    runJvmResFast (f + 2) prog pc (.iconst c :: .ireturn :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      some (.i32 c, ⟨pc + 1, .i32 c :: stk, locs, jh, hp⟩) := by
  have hstep : Jvm.stepInstr algHooks (.iconst c) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 c :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]
  exact runJvmResFast_ireturn_step f prog (pc + 1) rest (.i32 c) stk locs jh hp

theorem formatBlockHeader_equiv (x y : Int32) :
    runJvm 25 f_Algorithm_formatBlockHeader_prog
        (initJvmState [(0, .i32 x.toUInt32), (1, .i32 y.toUInt32)]) =
      some (.str (Algorithm.formatBlockHeader x y)) := by
  apply runJvm_of_runJvmValFast0 25 _ _ _ rfl
  have hconcat1 : @Jvm.evalMakeConcatWithConstants AlgExt "\x01\x01"
      "(Ljava/lang/String;I)Ljava/lang/String;" [.i32 x.toUInt32, .str "#P "] =
      some ("#P " ++ (Jvm.i32ToDecimalString x.toUInt32 ++ ""), []) := rfl
  have hconcat2 : @Jvm.evalMakeConcatWithConstants AlgExt "\x01\x01\x01"
      "(Ljava/lang/String;Ljava/lang/String;I)Ljava/lang/String;"
      [.i32 y.toUInt32, .str " ", .str ("#P " ++ (Jvm.i32ToDecimalString x.toUInt32 ++ ""))] =
      some (("#P " ++ (Jvm.i32ToDecimalString x.toUInt32 ++ "")) ++
        (" " ++ (Jvm.i32ToDecimalString y.toUInt32 ++ "")), []) := rfl
  let l0 : Nat → JvmVal := setLocal (setLocal (fun _ => .i32 0) 0 (.i32 x.toUInt32)) 1 (.i32 y.toUInt32)
  let l1 : Nat → JvmVal := setLocal l0 2 (.str "#P ")
  let s1 := "#P " ++ (Jvm.i32ToDecimalString x.toUInt32 ++ "")
  let l2 : Nat → JvmVal := setLocal (setLocal l1 3 (.str s1)) 4 (.str " ")
  have hstep1 : runJvmValFast 25 f_Algorithm_formatBlockHeader_prog 0 f_Algorithm_formatBlockHeader_prog
      (initJvmState [(0, .i32 x.toUInt32), (1, .i32 y.toUInt32)]) =
      runJvmValFast 21 f_Algorithm_formatBlockHeader_prog 4
        (f_Algorithm_formatBlockHeader_prog.drop 4)
        ⟨4, [.i32 x.toUInt32, .str "#P "], l1, {}, {}⟩ := by
    split_val_fuel 21
    dsimp only [f_Algorithm_formatBlockHeader_prog, List.drop, initJvmState, Jvm.initJvmState, List.foldl]
    heap_step_blk f_Algorithm_formatBlockHeader_prog
    norm_res_fuel
    rfl
  rw [hstep1]
  have hstep2 : runJvmValFast 21 f_Algorithm_formatBlockHeader_prog 4
      (f_Algorithm_formatBlockHeader_prog.drop 4)
      ⟨4, [.i32 x.toUInt32, .str "#P "], l1, {}, {}⟩ =
      runJvmValFast 20 f_Algorithm_formatBlockHeader_prog 5
        (f_Algorithm_formatBlockHeader_prog.drop 5)
        ⟨5, [.str s1], l1, {}, {}⟩ := by
    dsimp only [f_Algorithm_formatBlockHeader_prog, List.drop]
    rw [runJvmValFast_step_nonbranch (hbr := rfl) (hno := by simp)]
    have hdyn : stepInstr
        (.invokedynamic "makeConcatWithConstants" "\x01\x01" "(Ljava/lang/String;I)Ljava/lang/String;")
        ⟨4, [.i32 x.toUInt32, .str "#P "], l1, {}, {}⟩ =
        .inl (some ⟨5, [.str s1], l1, {}, {}⟩) := by
      simp only [stepInstr, Jvm.stepInstr, hconcat1]; rfl
    dsimp only; rw [hdyn]; rfl
  rw [hstep2]
  have hstep3 : runJvmValFast 20 f_Algorithm_formatBlockHeader_prog 5
      (f_Algorithm_formatBlockHeader_prog.drop 5)
      ⟨5, [.str s1], l1, {}, {}⟩ =
      runJvmValFast 14 f_Algorithm_formatBlockHeader_prog 11
        (f_Algorithm_formatBlockHeader_prog.drop 11)
        ⟨11, [.i32 y.toUInt32, .str " ", .str s1], l2, {}, {}⟩ := by
    split_val_fuel 14
    dsimp only [f_Algorithm_formatBlockHeader_prog, List.drop]
    heap_step_blk f_Algorithm_formatBlockHeader_prog
    norm_res_fuel
    rfl
  rw [hstep3]
  have hstep4 : runJvmValFast 14 f_Algorithm_formatBlockHeader_prog 11
      (f_Algorithm_formatBlockHeader_prog.drop 11)
      ⟨11, [.i32 y.toUInt32, .str " ", .str s1], l2, {}, {}⟩ =
      some (.str (s1 ++ (" " ++ (Jvm.i32ToDecimalString y.toUInt32 ++ "")))) := by
    dsimp only [f_Algorithm_formatBlockHeader_prog, List.drop]
    rw [runJvmValFast_step_nonbranch (hbr := rfl) (hno := by simp)]
    have hdyn : stepInstr
        (.invokedynamic "makeConcatWithConstants" "\x01\x01\x01"
          "(Ljava/lang/String;Ljava/lang/String;I)Ljava/lang/String;")
        ⟨11, [.i32 y.toUInt32, .str " ", .str s1], l2, {}, {}⟩ =
        .inl (some ⟨12, [.str (s1 ++ (" " ++ (Jvm.i32ToDecimalString y.toUInt32 ++ "")))],
          l2, {}, {}⟩) := by
      simp only [stepInstr, Jvm.stepInstr]; rfl
    dsimp only; rw [hdyn]; rfl
  rw [hstep4]
  dsimp only [s1]
  rw [i32ToDecimalString_eq_toString x.toUInt32, i32ToDecimalString_eq_toString y.toUInt32]
  simp only [Int32.toInt32_toUInt32, Algorithm.formatBlockHeader, String.append_empty, String.append_assoc]
  rfl

/-! #### 2. `isRowRest`, `isRowLine`, `skipDescriptions`, `checkRuleLine` -/

private theorem isRowRest_continue (f : Nat) (bytesAddr : Nat) (limit p : UInt32)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = [])
    (h0 : locs 0 = .heapRef bytesAddr) (h1 : locs 1 = .i32 limit) (h2 : locs 2 = .i32 p) :
    ∃ locs', runJvmResFast (f + 16) f_Algorithm_isRowRest_prog 23
        (f_Algorithm_isRowRest_prog.drop 23) ⟨23, [], locs, jh, hp⟩ =
        runJvmResFast f f_Algorithm_isRowRest_prog 3
          (f_Algorithm_isRowRest_prog.drop 3) ⟨3, [], locs', jh, hp⟩ ∧
      locs' 0 = .heapRef bytesAddr ∧ locs' 1 = .i32 limit ∧ locs' 2 = .i32 (p + 1) := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_⟩
  · split_res_fuel 16
    step_drop 16
    heap_step_nonbranch_chunks; norm_res_fuel
    (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)
    rw [h0, h1, h2]
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_goto]; norm_res_fuel
    rfl
  · simp [setLocal]
  · simp [setLocal]
  · simp [setLocal, Jvm.JvmVal.asI32]

private theorem isRowRest_loop (m : Nat) (f : Nat) (bytes : ByteArray) (bytesAddr : Nat)
    (limit p : UInt32) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hm : limit.toNat - p.toNat ≤ m)
    (hf : 40 * (limit.toNat - p.toNat) + 12 ≤ f)
    (hstat : jh.statics = [])
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hlimit : limit.toNat ≤ bytes.data.size) (hlim31 : limit.toNat < 2 ^ 31)
    (h0 : locs 0 = .heapRef bytesAddr) (h1 : locs 1 = .i32 limit) (h2 : locs 2 = .i32 p) :
    ∃ st', runJvmResFast f f_Algorithm_isRowRest_prog 3
        (f_Algorithm_isRowRest_prog.drop 3) ⟨3, [], locs, jh, hp⟩ =
        some (.i32 (if Algorithm.isRowRest bytes limit p then 1 else 0), st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  induction m generalizing f p locs with
  | zero =>
    have hge : ¬(p < limit) := by
      intro hlt
      have := UInt32.lt_iff_toNat_lt.mp hlt
      omega
    have hres : Algorithm.isRowRest bytes limit p = true := by
      rw [Algorithm.isRowRest]; simp [hge]
    rw [hres]; simp only [↓reduceIte]
    refine ⟨⟨8, [.i32 1], locs, jh, hp⟩, ?_, rfl, rfl⟩
    rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
    rcases hp with ⟨ar, u64, asc⟩
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 12 := ⟨f - 12, by omega⟩
    split_res_fuel 12
    step_drop 6
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h2, h1]
    heap_step_nonbranch_chunks; norm_res_fuel
    dsimp only [Jvm.JvmVal.asI32]
    rw [runJvmResFast_iflt_fallthrough (by
      change (if p == limit then (0 : UInt32) else if p < limit then 4294967295 else 1).toBitVec.slt 0#32 = false
      rw [compareUnsigned_slt_zero]; exact decide_eq_false hge)]
    norm_res_fuel
    rw [show f' + 12 - 12 + 8 = (f' + 6) + 2 from by omega]
    exact runJvmResFast_iconst_ireturn_step (f' + 6) _ _ _ _ _ _ _ _
  | succ m ih =>
    by_cases hlt : p < limit
    · have hp_nat : p.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hlt
      have hp_sz : p.toNat < bytes.data.size := by omega
      have hslt_p : p.toBitVec.slt 0#32 = false :=
        u32_slt_zero_of_lt hlt (by omega)
      let b : UInt8 := bytes.data[p.toNat]
      have hget_b : bytes.get! p.toNat = b := by
        simp only [ByteArray.get!, getElem!_pos bytes.data p.toNat hp_sz]
        rfl
      have hb46_eq : (UInt32.ofBitVec (b.toBitVec.signExtend 32) == 46) = (b == 46) :=
        signExtend_beq_const 46 (by decide) b
      have hb42_eq : (UInt32.ofBitVec (b.toBitVec.signExtend 32) == 42) = (b == 42) :=
        signExtend_beq_const 42 (by decide) b
      rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
      rcases hp with ⟨ar, u64, asc⟩
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 40 := ⟨f - 40, by omega⟩
      let bv := UInt32.ofBitVec (b.toBitVec.signExtend 32)
      let locs1 := setLocal locs 3 (.i32 bv)
      have hpre : runJvmResFast (f' + 40) f_Algorithm_isRowRest_prog 3
          (f_Algorithm_isRowRest_prog.drop 3) ⟨3, [], locs, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
          runJvmResFast (f' + 28) f_Algorithm_isRowRest_prog 17
            (f_Algorithm_isRowRest_prog.drop 17)
            ⟨17, [.i32 46, .i32 bv], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
        split_res_fuel 12
        step_drop 4
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [h2, h1]
        heap_step_nonbranch_chunks; norm_res_fuel
        dsimp only [Jvm.JvmVal.asI32]
        rw [runJvmResFast_iflt_branch (by
          change (if p == limit then (0 : UInt32) else if p < limit then 4294967295 else 1).toBitVec.slt 0#32 = true
          rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt)]
        norm_res_fuel
        step_drop 8
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [h0, h2]
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_baload (hget := hbytes) (hslt := hslt_p) (hlt := hp_sz)]; norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        rfl
      by_cases h46 : b = 46
      · have hrec_eq : Algorithm.isRowRest bytes limit p = Algorithm.isRowRest bytes limit (p + 1) := by
          rw [Algorithm.isRowRest]; simp [hlt, hget_b, h46]
        have hm' : limit.toNat - (p + 1).toNat ≤ m := by
          rw [ui32_add1_toNat hlt]; omega
        have hf' : 40 * (limit.toNat - (p + 1).toNat) + 12 ≤ f' + 11 := by
          rw [ui32_add1_toNat hlt]; omega
        have heq46 : bv = 46 := beq_iff_eq.mp (by rw [hb46_eq]; simp [h46])
        have hbr46 : runJvmResFast (f' + 28) f_Algorithm_isRowRest_prog 17
            (f_Algorithm_isRowRest_prog.drop 17)
            ⟨17, [.i32 46, .i32 bv], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast (f' + 11 + 16) f_Algorithm_isRowRest_prog 23
              (f_Algorithm_isRowRest_prog.drop 23) ⟨23, [], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
          split_res_fuel 1
          step_drop 1
          rw [runJvmResFast_if_icmpeq_branch (heq := heq46)]; norm_res_fuel
          rfl
        rcases isRowRest_continue (f' + 11) bytesAddr limit p locs1 ⟨objs, []⟩ ⟨ar, u64, asc⟩ rfl
            (by simp [locs1, setLocal, h0]) (by simp [locs1, setLocal, h1])
            (by simp [locs1, setLocal, h2]) with
          ⟨locs2, hloop46, hl2_0, hl2_1, hl2_2⟩
        rcases ih (f' + 11) (p + 1) locs2 hm' hf' hl2_0 hl2_1 hl2_2 with
          ⟨st', hrun, hst_jh, hst_hp⟩
        refine ⟨st', ?_, hst_jh, hst_hp⟩
        rw [hpre, hbr46, hloop46, hrec_eq]
        exact hrun
      · have hne46 : (bv == 46) = false := by
          rw [hb46_eq]; exact beq_false_of_ne h46
        have hstep42_pre : runJvmResFast (f' + 28) f_Algorithm_isRowRest_prog 17
            (f_Algorithm_isRowRest_prog.drop 17)
            ⟨17, [.i32 46, .i32 bv], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast (f' + 25) f_Algorithm_isRowRest_prog 20
              (f_Algorithm_isRowRest_prog.drop 20)
              ⟨20, [.i32 42, .i32 bv], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
          split_res_fuel 3
          step_drop 1
          rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne46)]; norm_res_fuel
          step_drop 2
          heap_step_nonbranch_chunks
          rfl
        by_cases h42 : b = 42
        · have hrec_eq : Algorithm.isRowRest bytes limit p = Algorithm.isRowRest bytes limit (p + 1) := by
            rw [Algorithm.isRowRest]; simp [hlt, hget_b, h42]
          have hm' : limit.toNat - (p + 1).toNat ≤ m := by
            rw [ui32_add1_toNat hlt]; omega
          have hf' : 40 * (limit.toNat - (p + 1).toNat) + 12 ≤ f' + 8 := by
            rw [ui32_add1_toNat hlt]; omega
          have heq42 : bv = 42 := beq_iff_eq.mp (by rw [hb42_eq]; simp [h42])
          have hbr42 : runJvmResFast (f' + 25) f_Algorithm_isRowRest_prog 20
              (f_Algorithm_isRowRest_prog.drop 20)
              ⟨20, [.i32 42, .i32 bv], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
              runJvmResFast (f' + 8 + 16) f_Algorithm_isRowRest_prog 23
                (f_Algorithm_isRowRest_prog.drop 23) ⟨23, [], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
            split_res_fuel 1
            step_drop 1
            rw [runJvmResFast_if_icmpeq_branch (heq := heq42)]; norm_res_fuel
            rfl
          rcases isRowRest_continue (f' + 8) bytesAddr limit p locs1 ⟨objs, []⟩ ⟨ar, u64, asc⟩ rfl
              (by simp [locs1, setLocal, h0]) (by simp [locs1, setLocal, h1])
              (by simp [locs1, setLocal, h2]) with
            ⟨locs2, hloop42, hl2_0, hl2_1, hl2_2⟩
          rcases ih (f' + 8) (p + 1) locs2 hm' hf' hl2_0 hl2_1 hl2_2 with
            ⟨st', hrun, hst_jh, hst_hp⟩
          refine ⟨st', ?_, hst_jh, hst_hp⟩
          rw [hpre, hstep42_pre, hbr42, hloop42, hrec_eq]
          exact hrun
        · have hne42 : (bv == 42) = false := by
            rw [hb42_eq]; exact beq_false_of_ne h42
          have hres : Algorithm.isRowRest bytes limit p = false := by
            rw [Algorithm.isRowRest]; simp [hlt, hget_b, h46, h42]
          rw [hres]; simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨⟨22, [.i32 0], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
          rw [hpre, hstep42_pre]
          split_res_fuel 25
          step_drop 3
          rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne42)]; norm_res_fuel
          exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
    · exact ih f p locs (by
        have := mt UInt32.lt_iff_toNat_lt.mpr hlt
        omega) hf h0 h1 h2

theorem isRowRest_equiv (bytes : ByteArray) (bytesAddr : Nat) (limit p : UInt32)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = [])
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hlimit : limit.toNat ≤ bytes.data.size) (hlim31 : limit.toNat < 2 ^ 31) :
    ∃ st', runJvmRes (40 * (limit.toNat - p.toNat) + 20) f_Algorithm_isRowRest_prog
        ⟨0, [], setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef bytesAddr))
          1 (.i32 limit)) 2 (.i32 p), jh, hp⟩ =
        some (.i32 (if Algorithm.isRowRest bytes limit p then 1 else 0), st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (fun _ => .null) 0 (.heapRef bytesAddr))
    1 (.i32 limit)) 2 (.i32 p)
  rcases isRowRest_loop (limit.toNat - p.toNat) (40 * (limit.toNat - p.toNat) + 17) bytes bytesAddr
      limit p locs0 jh hp (Nat.le_refl _) (by omega) hstat hbytes hlimit hlim31
      (by simp [locs0, setLocal]) (by simp [locs0, setLocal]) (by simp [locs0, setLocal]) with
    ⟨st', hrun, hst_jh, hst_hp⟩
  refine ⟨st', ?_, hst_jh, hst_hp⟩
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  rw [show 40 * (limit.toNat - p.toNat) + 20 = 40 * (limit.toNat - p.toNat) + 17 + 3 from by omega]
  split_res_fuel 3
  conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_isRowRest_prog)]
  step_drop 3
  heap_step_nonbranch_chunks
  exact hrun

theorem isRowLine_equiv (bytes : ByteArray) (bytesAddr : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = [])
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data)) :
    ∃ st', runJvmRes 25 f_Algorithm_isRowLine_prog
        ⟨0, [], setLocal (fun _ => .null) 0 (.heapRef bytesAddr), jh, hp⟩ =
        some (.i32 (if Algorithm.isRowLine bytes then 1 else 0), st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  let locs0 : Nat → JvmVal := setLocal (fun _ => .null) 0 (.heapRef bytesAddr)
  let limit : UInt32 := UInt32.ofNat bytes.data.size
  have hlim_eq : bytes.size.toUInt32 = limit := rfl
  let locs1 : Nat → JvmVal := setLocal locs0 1 (.i32 limit)
  have hpre : runJvmResFast 25 f_Algorithm_isRowLine_prog 0 f_Algorithm_isRowLine_prog
      ⟨0, [], locs0, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast 18 f_Algorithm_isRowLine_prog 7 (f_Algorithm_isRowLine_prog.drop 7)
        ⟨7, [], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
    split_res_fuel 7
    conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_isRowLine_prog)]
    step_drop 7
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_arraylength_byte (hget := hbytes)]; norm_res_fuel
    heap_step_nonbranch_chunks
    rfl
  by_cases hz : limit = 0
  · have hres : Algorithm.isRowLine bytes = false := by
      simp [Algorithm.isRowLine, hlim_eq, hz]
    rw [hres]; simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨⟨15, [.i32 0], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
    apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    rw [hpre]
    split_res_fuel 18
    step_drop 2
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_ifeq_branch (hv := hz)]; norm_res_fuel
    step_drop 2
    exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
  · have hne : (limit == 0) = false := beq_false_of_ne hz
    have hres : Algorithm.isRowLine bytes = Algorithm.isRowRest bytes limit 0 := by
      simp [Algorithm.isRowLine, hlim_eq, hz]
    rw [hres]
    refine ⟨⟨13, [.i32 (if Algorithm.isRowRest bytes limit 0 then 1 else 0)],
        locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
    apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    rw [hpre]
    split_res_fuel 18
    step_drop 7
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_ifeq_fallthrough (h := hne)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_isRowRest_heap (hget := hbytes))]
    norm_res_fuel
    exact runJvmResFast_ireturn_step _ _ _ _ _ _ _ _ _

private theorem skipDescriptions_loop (m : Nat) (f : Nat) (lines : Array String)
    (numLines i : UInt32) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hm : numLines.toNat - i.toNat ≤ m)
    (hf : 65 * (numLines.toNat - i.toNat) + 12 ≤ f)
    (hstat : jh.statics = [])
    (hnum : numLines.toNat ≤ lines.size) (hlines31 : lines.size < 2 ^ 31)
    (hutf8 : ∀ k < lines.size, lines[k]!.toUTF8.data.size < 2 ^ 31)
    (h0 : locs 0 = .strArr lines) (h1 : locs 1 = .i32 numLines) (h2 : locs 2 = .i32 i) :
    ∃ st', runJvmResFast f f_Algorithm_skipDescriptions_prog 3
        (f_Algorithm_skipDescriptions_prog.drop 3) ⟨3, [], locs, jh, hp⟩ =
        some (.i32 (Algorithm.skipDescriptions lines numLines i), st') ∧
      st'.heap = hp := by
  induction m generalizing f i locs jh with
  | zero =>
    have hge : ¬(i < numLines) := by
      intro hlt
      have := UInt32.lt_iff_toNat_lt.mp hlt
      omega
    have hres : Algorithm.skipDescriptions lines numLines i = i := by
      rw [Algorithm.skipDescriptions]; simp [hge]
    rw [hres]
    refine ⟨⟨8, [.i32 i], locs, jh, hp⟩, ?_, rfl⟩
    rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
    rcases hp with ⟨ar, u64, asc⟩
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 12 := ⟨f - 12, by omega⟩
    split_res_fuel 12
    step_drop 6
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h2, h1]
    heap_step_nonbranch_chunks; norm_res_fuel
    dsimp only [Jvm.JvmVal.asI32]
    rw [runJvmResFast_iflt_fallthrough (by
      change (if i == numLines then (0 : UInt32) else if i < numLines then 4294967295 else 1).toBitVec.slt 0#32 = false
      rw [compareUnsigned_slt_zero]; exact decide_eq_false hge)]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [h2]
    heap_step_nonbranch_chunks
  | succ m ih =>
    by_cases hlt : i < numLines
    · have hi_nat : i.toNat < numLines.toNat := UInt32.lt_iff_toNat_lt.mp hlt
      have hi_sz : i.toNat < lines.size := by omega
      have hslt_i : i.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt hlt (by omega)
      let s := lines[i.toNat]!
      have hs_eq : lines[i.toNat] = s := by simp [s, hi_sz]
      let bs := s.toUTF8
      have hbs_eq : s.toByteArray = bs := rfl
      have hbs31 : bs.data.size < 2 ^ 31 := hutf8 i.toNat hi_sz
      let bsLen : UInt32 := UInt32.ofNat bs.data.size
      have hbsLen_toNat : bsLen.toNat = bs.data.size := by
        dsimp only [bsLen]
        rw [UInt32.toNat_ofNat']
        exact Nat.mod_eq_of_lt (by omega)
      let bytesAddr := jh.objects.size
      let jh1 := (jh.alloc (.byteArray bs.data)).2
      have hstat1 : jh1.statics = [] := by simp [jh1, Jvm.JvmHeap.alloc, hstat]
      have hbytes1 : jh1.get? bytesAddr = some (.byteArray bs.data) := by
        simp [jh1, bytesAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
      let locs1 : Nat → JvmVal := setLocal locs 3 (.heapRef bytesAddr)
      rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
      rcases hp with ⟨ar, u64, asc⟩
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 65 := ⟨f - 65, by omega⟩
      have hpre : runJvmResFast (f' + 65) f_Algorithm_skipDescriptions_prog 3
          (f_Algorithm_skipDescriptions_prog.drop 3) ⟨3, [], locs, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
          runJvmResFast (f' + 47) f_Algorithm_skipDescriptions_prog 23
            (f_Algorithm_skipDescriptions_prog.drop 23)
            ⟨23, [.i32 (if (2 : UInt32) == bsLen then 0 else if (2 : UInt32) < bsLen then 4294967295 else 1)],
              locs1, jh1, ⟨ar, u64, asc⟩⟩ := by
        split_res_fuel 18
        step_drop 4
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [h2, h1]
        heap_step_nonbranch_chunks; norm_res_fuel
        dsimp only [Jvm.JvmVal.asI32]
        rw [runJvmResFast_iflt_branch (by
          change (if i == numLines then (0 : UInt32)
            else if i < numLines then 4294967295 else 1).toBitVec.slt 0#32 = true
          rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt)]
        norm_res_fuel
        step_drop 14
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [h0, h2]
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_aaload_strArr (hslt := hslt_i) (hlt := hi_sz)]; norm_res_fuel
        rw [hs_eq]
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
        rw [runJvmResFast_invokestatic_step (hs := stepStatic_stringsEncodeToByteArray)]; norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_arraylength_byte (hget := hbytes1)]; norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        dsimp only [Jvm.JvmVal.asI32]
        rfl
      by_cases hlen : 2 ≤ bsLen
      · have h2_le : 2 ≤ bs.data.size := by
          have := UInt32.le_iff_toNat_le.mp hlen
          rw [hbsLen_toNat] at this
          exact this
        have hbsLen_ge2 : bs.size.toUInt32 ≥ 2 := hlen
        let b0 := bs.data[0]
        let b1 := bs.data[1]
        let bv0 := UInt32.ofBitVec (b0.toBitVec.signExtend 32)
        let bv1 := UInt32.ofBitVec (b1.toBitVec.signExtend 32)
        have hb0_get : bs.get! 0 = b0 := by
          simp only [ByteArray.get!, getElem!_pos bs.data 0 (by omega)]; rfl
        have hb1_get : bs.get! 1 = b1 := by
          simp only [ByteArray.get!, getElem!_pos bs.data 1 (by omega)]; rfl
        have hstep35 : runJvmResFast (f' + 47) f_Algorithm_skipDescriptions_prog 23
            (f_Algorithm_skipDescriptions_prog.drop 23)
            ⟨23, [.i32 (if (2 : UInt32) == bsLen then 0 else if (2 : UInt32) < bsLen then 4294967295 else 1)],
              locs1, jh1, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast (f' + 41) f_Algorithm_skipDescriptions_prog 31
              (f_Algorithm_skipDescriptions_prog.drop 31)
              ⟨31, [.i32 35, .i32 bv0], locs1, jh1, ⟨ar, u64, asc⟩⟩ := by
          split_res_fuel 6
          step_drop 1
          rw [runJvmResFast_ifle_branch (by rw [compareUnsigned_sle_zero]; exact decide_eq_true hlen)]
          norm_res_fuel
          step_drop 5
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_baload (hget := hbytes1) (hslt := by decide)
            (hlt := by show 0 < bs.data.size; omega)]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rfl
        by_cases hb0 : b0 = 35
        · have heq35 : bv0 = 35 := signExtend_eq_u32 hb0 rfl (by decide)
          have hstep68 : runJvmResFast (f' + 41) f_Algorithm_skipDescriptions_prog 31
              (f_Algorithm_skipDescriptions_prog.drop 31)
              ⟨31, [.i32 35, .i32 bv0], locs1, jh1, ⟨ar, u64, asc⟩⟩ =
              runJvmResFast (f' + 35) f_Algorithm_skipDescriptions_prog 39
                (f_Algorithm_skipDescriptions_prog.drop 39)
                ⟨39, [.i32 68, .i32 bv1], locs1, jh1, ⟨ar, u64, asc⟩⟩ := by
            split_res_fuel 6
            step_drop 1
            rw [runJvmResFast_if_icmpeq_branch (heq := heq35)]; norm_res_fuel
            step_drop 5
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_baload (hget := hbytes1) (hslt := by decide)
              (hlt := by show 1 < bs.data.size; omega)]; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            rfl
          by_cases hb1 : b1 = 68
          · have heq68 : bv1 = 68 := signExtend_eq_u32 hb1 rfl (by decide)
            have hstarts : Algorithm.startsWithHash bs 68 = true := by
              simp [Algorithm.startsWithHash, hbsLen_ge2, hb0_get, hb1_get, hb0, hb1]
            have hrec_eq : Algorithm.skipDescriptions lines numLines i =
                Algorithm.skipDescriptions lines numLines (i + 1) := by
              rw [Algorithm.skipDescriptions]
              simp [hlt, s, hbs_eq, hstarts]
            let locs2 : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs1
              4 (.strArr lines)) 5 (.i32 numLines)) 6 (.i32 (i + 1)))
              0 (.strArr lines)) 1 (.i32 numLines)) 2 (.i32 (i + 1))
            have hloop : runJvmResFast (f' + 35) f_Algorithm_skipDescriptions_prog 39
                (f_Algorithm_skipDescriptions_prog.drop 39)
                ⟨39, [.i32 68, .i32 bv1], locs1, jh1, ⟨ar, u64, asc⟩⟩ =
                runJvmResFast (f' + 18) f_Algorithm_skipDescriptions_prog 3
                  (f_Algorithm_skipDescriptions_prog.drop 3)
                  ⟨3, [], locs2, jh1, ⟨ar, u64, asc⟩⟩ := by
              split_res_fuel 17
              step_drop 1
              rw [runJvmResFast_if_icmpeq_branch (heq := heq68)]; norm_res_fuel
              step_drop 16
              heap_step_nonbranch_chunks; norm_res_fuel
              (conv => lhs; norm_jvm_locals; jvm_whnf_run_args)
              rw [h0, h1, h2]
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_goto]; norm_res_fuel
              rfl
            have hm' : numLines.toNat - (i + 1).toNat ≤ m := by rw [ui32_add1_toNat hlt]; omega
            have hf' : 65 * (numLines.toNat - (i + 1).toNat) + 12 ≤ f' + 18 := by
              rw [ui32_add1_toNat hlt]; omega
            rcases ih (f' + 18) (i + 1) locs2 jh1 hm' hf' hstat1
                (by simp [locs2, setLocal]) (by simp [locs2, setLocal]) (by simp [locs2, setLocal]) with
              ⟨st', hrun, hst_hp⟩
            refine ⟨st', ?_, hst_hp⟩
            rw [hpre, hstep35, hstep68, hloop, hrec_eq]
            exact hrun
          · have hne68 : (bv1 == 68) = false := signExtend_bne_u32 hb1 rfl (by decide)
            have hstarts : Algorithm.startsWithHash bs 68 = false := by
              simp [Algorithm.startsWithHash, hbsLen_ge2, hb0_get, hb1_get, hb0, hb1]
            have hres : Algorithm.skipDescriptions lines numLines i = i := by
              rw [Algorithm.skipDescriptions]
              simp [hlt, s, hbs_eq, hstarts]
            rw [hres]
            refine ⟨⟨41, [.i32 i], locs1, jh1, ⟨ar, u64, asc⟩⟩, ?_, rfl⟩
            rw [hpre, hstep35, hstep68]
            split_res_fuel 35
            step_drop 3
            rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne68)]; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [h2]
            heap_step_nonbranch_chunks
        · have hne35 : (bv0 == 35) = false := signExtend_bne_u32 hb0 rfl (by decide)
          have hstarts : Algorithm.startsWithHash bs 68 = false := by
            simp [Algorithm.startsWithHash, hbsLen_ge2, hb0_get, hb0]
          have hres : Algorithm.skipDescriptions lines numLines i = i := by
            rw [Algorithm.skipDescriptions]
            simp [hlt, s, hbs_eq, hstarts]
          rw [hres]
          refine ⟨⟨33, [.i32 i], locs1, jh1, ⟨ar, u64, asc⟩⟩, ?_, rfl⟩
          rw [hpre, hstep35]
          split_res_fuel 41
          step_drop 3
          rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne35)]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [h2]
          heap_step_nonbranch_chunks
      · have hstarts : Algorithm.startsWithHash bs 68 = false := by
          have hn : ¬(bs.size.toUInt32 ≥ 2) := hlen
          simp [Algorithm.startsWithHash, hn]
        have hres : Algorithm.skipDescriptions lines numLines i = i := by
          rw [Algorithm.skipDescriptions]
          simp [hlt, s, hbs_eq, hstarts]
        rw [hres]
        refine ⟨⟨25, [.i32 i], locs1, jh1, ⟨ar, u64, asc⟩⟩, ?_, rfl⟩
        rw [hpre]
        split_res_fuel 47
        step_drop 3
        rw [runJvmResFast_ifle_fallthrough (by rw [compareUnsigned_sle_zero]; exact decide_eq_false hlen)]
        norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [h2]
        heap_step_nonbranch_chunks
    · exact ih f i locs jh (by
        have := mt UInt32.lt_iff_toNat_lt.mpr hlt
        omega) hf hstat h0 h1 h2

theorem skipDescriptions_equiv (lines : Array String) (numLines i : UInt32)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = [])
    (hnum : numLines.toNat ≤ lines.size) (hlines31 : lines.size < 2 ^ 31)
    (hutf8 : ∀ k < lines.size, lines[k]!.toUTF8.data.size < 2 ^ 31) :
    ∃ st', runJvmRes (65 * (numLines.toNat - i.toNat) + 20) f_Algorithm_skipDescriptions_prog
        ⟨0, [], setLocal (setLocal (setLocal (fun (_ : Nat) => (.null : JvmVal)) 0 (.strArr lines))
          1 (.i32 numLines)) 2 (.i32 i), jh, hp⟩ =
        some (.i32 (Algorithm.skipDescriptions lines numLines i), st') ∧
      st'.heap = hp := by
  let locs0 : Nat → JvmVal := setLocal (setLocal (setLocal (fun _ => .null) 0 (.strArr lines))
    1 (.i32 numLines)) 2 (.i32 i)
  rcases skipDescriptions_loop (numLines.toNat - i.toNat) (65 * (numLines.toNat - i.toNat) + 17)
      lines numLines i locs0 jh hp (Nat.le_refl _) (by omega) hstat hnum hlines31 hutf8
      (by simp [locs0, setLocal]) (by simp [locs0, setLocal]) (by simp [locs0, setLocal]) with
    ⟨st', hrun, hst_hp⟩
  refine ⟨st', ?_, hst_hp⟩
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  rw [show 65 * (numLines.toNat - i.toNat) + 20 = 65 * (numLines.toNat - i.toNat) + 17 + 3 from by omega]
  split_res_fuel 3
  conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_skipDescriptions_prog)]
  step_drop 3
  heap_step_nonbranch_chunks
  exact hrun

theorem checkRuleLine_equiv (bytes : ByteArray) (bytesAddr : Nat)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = [])
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hb31 : bytes.data.size < 2 ^ 31) :
    ∃ st', runJvmRes 128 f_Algorithm_checkRuleLine_prog
        ⟨0, [], setLocal (fun (_ : Nat) => (.null : JvmVal)) 0 (.heapRef bytesAddr), jh, hp⟩ =
        some (.i32 (Algorithm.checkRuleLine bytes), st') ∧
      st'.jvmHeap = jh ∧ st'.heap = hp := by
  rcases jh with ⟨objs, stat⟩; dsimp only at hstat; subst hstat
  rcases hp with ⟨ar, u64, asc⟩
  let locs0 : Nat → JvmVal := setLocal (fun _ => .null) 0 (.heapRef bytesAddr)
  let limit : UInt32 := UInt32.ofNat bytes.data.size
  have hlim_eq : bytes.size.toUInt32 = limit := rfl
  have hlim_toNat : limit.toNat = bytes.data.size := by
    dsimp only [limit]
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  let locs1 : Nat → JvmVal := setLocal locs0 1 (.i32 limit)
  have hpre : runJvmResFast 128 f_Algorithm_checkRuleLine_prog 0 f_Algorithm_checkRuleLine_prog
      ⟨0, [], locs0, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast 118 f_Algorithm_checkRuleLine_prog 10 (f_Algorithm_checkRuleLine_prog.drop 10)
        ⟨10, [.i32 (if limit == 3 then 0 else if limit < 3 then 4294967295 else 1)],
          locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
    split_res_fuel 10
    conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_checkRuleLine_prog)]
    step_drop 10
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_arraylength_byte (hget := hbytes)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    dsimp only [Jvm.JvmVal.asI32]
    rfl
  by_cases hlt3 : limit < 3
  · have hres : Algorithm.checkRuleLine bytes = 1 := by
      simp [Algorithm.checkRuleLine, hlim_eq, hlt3]
    rw [hres]
    refine ⟨⟨114, [.i32 1], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
    apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    rw [hpre]
    split_res_fuel 118
    step_drop 1
    rw [runJvmResFast_iflt_branch (by
      change (if limit == 3 then (0 : UInt32) else if limit < 3 then 4294967295 else 1).toBitVec.slt 0#32 = true
      rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt3)]
    norm_res_fuel
    step_drop 2
    exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
  · have hge3 : 3 ≤ bytes.data.size := by
      have hnt : ¬(limit.toNat < 3) := mt (@UInt32.lt_iff_toNat_lt limit 3).mpr hlt3
      dsimp only [UInt32.toNat] at hnt hlim_toNat; omega
    let b0 := bytes.data[0]
    let b1 := bytes.data[1]
    let b2 := bytes.data[2]
    let bv0 := UInt32.ofBitVec (b0.toBitVec.signExtend 32)
    let bv1 := UInt32.ofBitVec (b1.toBitVec.signExtend 32)
    let bv2 := UInt32.ofBitVec (b2.toBitVec.signExtend 32)
    have hb0_get : bytes.get! 0 = b0 := by
      simp only [ByteArray.get!, getElem!_pos bytes.data 0 (by omega)]; rfl
    have hb1_get : bytes.get! 1 = b1 := by
      simp only [ByteArray.get!, getElem!_pos bytes.data 1 (by omega)]; rfl
    have hb2_get : bytes.get! 2 = b2 := by
      simp only [ByteArray.get!, getElem!_pos bytes.data 2 (by omega)]; rfl
    have hstep11 : runJvmResFast 118 f_Algorithm_checkRuleLine_prog 10 (f_Algorithm_checkRuleLine_prog.drop 10)
        ⟨10, [.i32 (if limit == 3 then 0 else if limit < 3 then 4294967295 else 1)],
          locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
        runJvmResFast 112 f_Algorithm_checkRuleLine_prog 16 (f_Algorithm_checkRuleLine_prog.drop 16)
          ⟨16, [.i32 35, .i32 bv0], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
      split_res_fuel 6
      step_drop 1
      rw [runJvmResFast_iflt_fallthrough (by
        change (if limit == 3 then (0 : UInt32) else if limit < 3 then 4294967295 else 1).toBitVec.slt 0#32 = false
        rw [compareUnsigned_slt_zero]; exact decide_eq_false hlt3)]
      norm_res_fuel
      step_drop 5
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [runJvmResFast_baload (hget := hbytes) (hslt := by decide)
        (hlt := by show 0 < bytes.data.size; omega)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rfl
    by_cases hb0 : b0 = 35
    · have heq35 : bv0 = 35 := signExtend_eq_u32 hb0 rfl (by decide)
      have hstep19 : runJvmResFast 112 f_Algorithm_checkRuleLine_prog 16 (f_Algorithm_checkRuleLine_prog.drop 16)
          ⟨16, [.i32 35, .i32 bv0], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
          runJvmResFast 106 f_Algorithm_checkRuleLine_prog 24 (f_Algorithm_checkRuleLine_prog.drop 24)
            ⟨24, [.i32 82, .i32 bv1], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
        split_res_fuel 6
        step_drop 1
        rw [runJvmResFast_if_icmpeq_branch (heq := heq35)]; norm_res_fuel
        step_drop 5
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_baload (hget := hbytes) (hslt := by decide)
          (hlt := by show 1 < bytes.data.size; omega)]; norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        rfl
      by_cases hb1 : b1 = 82
      · have heq82 : bv1 = 82 := signExtend_eq_u32 hb1 rfl (by decide)
        have hstep27 : runJvmResFast 106 f_Algorithm_checkRuleLine_prog 24 (f_Algorithm_checkRuleLine_prog.drop 24)
            ⟨24, [.i32 82, .i32 bv1], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast 100 f_Algorithm_checkRuleLine_prog 32 (f_Algorithm_checkRuleLine_prog.drop 32)
              ⟨32, [.i32 32, .i32 bv2], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
          split_res_fuel 6
          step_drop 1
          rw [runJvmResFast_if_icmpeq_branch (heq := heq82)]; norm_res_fuel
          step_drop 5
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_baload (hget := hbytes) (hslt := by decide)
            (hlt := by show 2 < bytes.data.size; omega)]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rfl
        by_cases hb2 : b2 = 32
        · have heq32 : bv2 = 32 := signExtend_eq_u32 hb2 rfl (by decide)
          let r1 := Algorithm.scanDigitSet bytes limit 3 0
          let e1 := r1.1
          let surv := r1.2
          let locs1' : Nat → JvmVal := setLocal (setLocal (setLocal locs1
            2 (.pair (.boxedUInt e1) (.boxedUInt surv))) 3 (.i32 e1)) 4 (.i32 surv)
          have hstep35 : runJvmResFast 100 f_Algorithm_checkRuleLine_prog 32 (f_Algorithm_checkRuleLine_prog.drop 32)
              ⟨32, [.i32 32, .i32 bv2], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
              runJvmResFast 81 f_Algorithm_checkRuleLine_prog 53 (f_Algorithm_checkRuleLine_prog.drop 53)
                ⟨53, [.i32 3, .i32 e1], locs1', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
            split_res_fuel 19
            step_drop 1
            rw [runJvmResFast_if_icmpeq_branch (heq := heq32)]; norm_res_fuel
            step_drop 18
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_invokestatic_step (hs := stepStatic_scanDigitSet_heap (hget := hbytes))]
            norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_checkcast_boxedUInt (hcls := Or.inl rfl)]; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_checkcast_boxedUInt (hcls := Or.inl rfl)]; norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            rfl
          have hcheck_pre : Algorithm.checkRuleLine bytes =
              if e1 == 3 || !(e1 < limit) || bytes.get! e1.toNat != 47 then 1
              else
                let s5 := e1 + 1
                let (e2, birth) := Algorithm.scanDigitSet bytes limit s5 0
                if e2 == s5 || e2 != limit then 1
                else if surv == 12 && birth == 8 then 0
                else 2 := by
            rw [Algorithm.checkRuleLine]
            simp [hlim_eq, hlt3, hb0_get, hb1_get, hb2_get, hb0, hb1, hb2,
              Algorithm.survival23Mask, Algorithm.birth3Mask, r1, e1, surv]
          by_cases he1_3 : e1 = 3
          · have hres : Algorithm.checkRuleLine bytes = 1 := by
              rw [hcheck_pre]; simp [he1_3]
            rw [hres]
            refine ⟨⟨112, [.i32 1], locs1', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
            apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
            rw [hpre, hstep11, hstep19, hstep27, hstep35]
            split_res_fuel 81
            step_drop 1
            rw [runJvmResFast_if_icmpeq_branch (heq := he1_3)]; norm_res_fuel
            step_drop 2
            exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
          · have hne_e1_3 : (e1 == 3) = false := beq_false_of_ne he1_3
            have hstep54 : runJvmResFast 81 f_Algorithm_checkRuleLine_prog 53
                (f_Algorithm_checkRuleLine_prog.drop 53)
                ⟨53, [.i32 3, .i32 e1], locs1', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
                runJvmResFast 77 f_Algorithm_checkRuleLine_prog 57
                  (f_Algorithm_checkRuleLine_prog.drop 57)
                  ⟨57, [.i32 (if e1 == limit then 0 else if e1 < limit then 4294967295 else 1)],
                    locs1', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
              split_res_fuel 4
              step_drop 1
              rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne_e1_3)]; norm_res_fuel
              step_drop 3
              heap_step_nonbranch_chunks; norm_res_fuel
              dsimp only [Jvm.JvmVal.asI32]
              rfl
            by_cases he1_lim : e1 < limit
            · have he1_nat : e1.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp he1_lim
              have hslt_e1 : e1.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt he1_lim (by omega)
              let be1 := bytes.data[e1.toNat]
              let bve1 := UInt32.ofBitVec (be1.toBitVec.signExtend 32)
              have hbe1_get : bytes.get! e1.toNat = be1 := by
                simp only [ByteArray.get!, getElem!_pos bytes.data e1.toNat (by omega)]; rfl
              have hstep60 : runJvmResFast 77 f_Algorithm_checkRuleLine_prog 57
                  (f_Algorithm_checkRuleLine_prog.drop 57)
                  ⟨57, [.i32 (if e1 == limit then 0 else if e1 < limit then 4294967295 else 1)],
                    locs1', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
                  runJvmResFast 71 f_Algorithm_checkRuleLine_prog 65
                    (f_Algorithm_checkRuleLine_prog.drop 65)
                    ⟨65, [.i32 47, .i32 bve1], locs1', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
                split_res_fuel 6
                step_drop 1
                rw [runJvmResFast_iflt_branch (by rw [compareUnsigned_slt_zero]; exact decide_eq_true he1_lim)]
                norm_res_fuel
                step_drop 5
                heap_step_nonbranch_chunks; norm_res_fuel
                rw [runJvmResFast_baload (hget := hbytes) (hslt := hslt_e1) (hlt := by omega)]; norm_res_fuel
                heap_step_nonbranch_chunks; norm_res_fuel
                rfl
              by_cases hbe1 : be1 = 47
              · have heq47 : bve1 = 47 := signExtend_eq_u32 hbe1 rfl (by decide)
                let s5 := e1 + 1
                let r2 := Algorithm.scanDigitSet bytes limit s5 0
                let e2 := r2.1
                let birth := r2.2
                let locs2' : Nat → JvmVal := setLocal (setLocal (setLocal (setLocal locs1' 5 (.i32 s5))
                  6 (.pair (.boxedUInt e2) (.boxedUInt birth))) 7 (.i32 e2)) 8 (.i32 birth)
                have hstep68 : runJvmResFast 71 f_Algorithm_checkRuleLine_prog 65
                    (f_Algorithm_checkRuleLine_prog.drop 65)
                    ⟨65, [.i32 47, .i32 bve1], locs1', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
                    runJvmResFast 47 f_Algorithm_checkRuleLine_prog 91
                      (f_Algorithm_checkRuleLine_prog.drop 91)
                      ⟨91, [.i32 s5, .i32 e2], locs2', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
                  split_res_fuel 24
                  step_drop 1
                  rw [runJvmResFast_if_icmpeq_branch (heq := heq47)]; norm_res_fuel
                  step_drop 23
                  heap_step_nonbranch_chunks; norm_res_fuel
                  rw [runJvmResFast_invokestatic_step (hs := stepStatic_scanDigitSet_heap (hget := hbytes))]
                  norm_res_fuel
                  heap_step_nonbranch_chunks; norm_res_fuel
                  rw [runJvmResFast_checkcast_boxedUInt (hcls := Or.inl rfl)]; norm_res_fuel
                  heap_step_nonbranch_chunks; norm_res_fuel
                  rw [runJvmResFast_checkcast_boxedUInt (hcls := Or.inl rfl)]; norm_res_fuel
                  heap_step_nonbranch_chunks; norm_res_fuel
                  rfl
                have hcheck_mid : Algorithm.checkRuleLine bytes =
                    if e2 == s5 || e2 != limit then 1
                    else if surv == 12 && birth == 8 then 0
                    else 2 := by
                  rw [hcheck_pre]
                  simp [he1_3, he1_lim, hbe1_get, hbe1, s5, r2, e2, birth]
                by_cases he2_s5 : e2 = s5
                · have hres : Algorithm.checkRuleLine bytes = 1 := by
                    rw [hcheck_mid]; simp [he2_s5]
                  rw [hres]
                  refine ⟨⟨110, [.i32 1], locs2', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
                  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                  rw [hpre, hstep11, hstep19, hstep27, hstep35, hstep54, hstep60, hstep68]
                  split_res_fuel 47
                  step_drop 1
                  rw [runJvmResFast_if_icmpeq_branch (heq := he2_s5)]; norm_res_fuel
                  step_drop 2
                  exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
                · have hne_e2_s5 : (e2 == s5) = false := beq_false_of_ne he2_s5
                  have hstep92 : runJvmResFast 47 f_Algorithm_checkRuleLine_prog 91
                      (f_Algorithm_checkRuleLine_prog.drop 91)
                      ⟨91, [.i32 s5, .i32 e2], locs2', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
                      runJvmResFast 44 f_Algorithm_checkRuleLine_prog 94
                        (f_Algorithm_checkRuleLine_prog.drop 94)
                        ⟨94, [.i32 limit, .i32 e2], locs2', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
                    split_res_fuel 3
                    step_drop 1
                    rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne_e2_s5)]; norm_res_fuel
                    step_drop 2
                    heap_step_nonbranch_chunks; norm_res_fuel
                    rfl
                  by_cases he2_lim : e2 = limit
                  · have hstep97 : runJvmResFast 44 f_Algorithm_checkRuleLine_prog 94
                        (f_Algorithm_checkRuleLine_prog.drop 94)
                        ⟨94, [.i32 limit, .i32 e2], locs2', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
                        runJvmResFast 41 f_Algorithm_checkRuleLine_prog 99
                          (f_Algorithm_checkRuleLine_prog.drop 99)
                          ⟨99, [.i32 12, .i32 surv], locs2', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
                      split_res_fuel 3
                      step_drop 1
                      rw [runJvmResFast_if_icmpeq_branch (heq := he2_lim)]; norm_res_fuel
                      step_drop 2
                      heap_step_nonbranch_chunks; norm_res_fuel
                      rfl
                    by_cases hsurv : surv = 12
                    · have hstep102 : runJvmResFast 41 f_Algorithm_checkRuleLine_prog 99
                          (f_Algorithm_checkRuleLine_prog.drop 99)
                          ⟨99, [.i32 12, .i32 surv], locs2', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ =
                          runJvmResFast 38 f_Algorithm_checkRuleLine_prog 104
                            (f_Algorithm_checkRuleLine_prog.drop 104)
                            ⟨104, [.i32 8, .i32 birth], locs2', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩ := by
                        split_res_fuel 3
                        step_drop 1
                        rw [runJvmResFast_if_icmpeq_branch (heq := hsurv)]; norm_res_fuel
                        step_drop 2
                        heap_step_nonbranch_chunks; norm_res_fuel
                        rfl
                      by_cases hbirth : birth = 8
                      · have hres : Algorithm.checkRuleLine bytes = 0 := by
                          rw [hcheck_mid, hne_e2_s5]; simp [he2_lim, hsurv, hbirth]
                        rw [hres]
                        refine ⟨⟨108, [.i32 0], locs2', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
                        apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                        rw [hpre, hstep11, hstep19, hstep27, hstep35, hstep54, hstep60, hstep68,
                          hstep92, hstep97, hstep102]
                        split_res_fuel 38
                        step_drop 1
                        rw [runJvmResFast_if_icmpeq_branch (heq := hbirth)]; norm_res_fuel
                        step_drop 2
                        exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
                      · have hne_birth : (birth == 8) = false := beq_false_of_ne hbirth
                        have hres : Algorithm.checkRuleLine bytes = 2 := by
                          rw [hcheck_mid, hne_e2_s5]; simp [he2_lim, hsurv, hbirth]
                        rw [hres]
                        refine ⟨⟨106, [.i32 2], locs2', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
                        apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                        rw [hpre, hstep11, hstep19, hstep27, hstep35, hstep54, hstep60, hstep68,
                          hstep92, hstep97, hstep102]
                        split_res_fuel 38
                        step_drop 3
                        rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne_birth)]; norm_res_fuel
                        exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
                    · have hne_surv : (surv == 12) = false := beq_false_of_ne hsurv
                      have hres : Algorithm.checkRuleLine bytes = 2 := by
                        rw [hcheck_mid, hne_e2_s5]; simp [he2_lim, hsurv]
                      rw [hres]
                      refine ⟨⟨101, [.i32 2], locs2', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
                      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                      rw [hpre, hstep11, hstep19, hstep27, hstep35, hstep54, hstep60, hstep68, hstep92, hstep97]
                      split_res_fuel 41
                      step_drop 3
                      rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne_surv)]; norm_res_fuel
                      exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
                  · have hne_e2l : (e2 == limit) = false := beq_false_of_ne he2_lim
                    have hres : Algorithm.checkRuleLine bytes = 1 := by
                      rw [hcheck_mid]; simp [he2_lim]
                    rw [hres]
                    refine ⟨⟨96, [.i32 1], locs2', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
                    apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                    rw [hpre, hstep11, hstep19, hstep27, hstep35, hstep54, hstep60, hstep68, hstep92]
                    split_res_fuel 44
                    step_drop 3
                    rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne_e2l)]; norm_res_fuel
                    exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
              · have hne47 : (bve1 == 47) = false := signExtend_bne_u32 hbe1 rfl (by decide)
                have hres : Algorithm.checkRuleLine bytes = 1 := by
                  rw [hcheck_pre]; simp [hbe1_get, hbe1]
                rw [hres]
                refine ⟨⟨67, [.i32 1], locs1', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
                apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
                rw [hpre, hstep11, hstep19, hstep27, hstep35, hstep54, hstep60]
                split_res_fuel 71
                step_drop 3
                rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne47)]; norm_res_fuel
                exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
            · have hres : Algorithm.checkRuleLine bytes = 1 := by
                rw [hcheck_pre]; simp [he1_lim]
              rw [hres]
              refine ⟨⟨59, [.i32 1], locs1', ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
              apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
              rw [hpre, hstep11, hstep19, hstep27, hstep35, hstep54]
              split_res_fuel 77
              step_drop 3
              rw [runJvmResFast_iflt_fallthrough (by
                change (if e1 == limit then (0 : UInt32)
                  else if e1 < limit then 4294967295 else 1).toBitVec.slt 0#32 = false
                rw [compareUnsigned_slt_zero]; exact decide_eq_false he1_lim)]
              norm_res_fuel
              exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
        · have hne32 : (bv2 == 32) = false := signExtend_bne_u32 hb2 rfl (by decide)
          have hres : Algorithm.checkRuleLine bytes = 1 := by
            simp [Algorithm.checkRuleLine, hlim_eq, hlt3, hb0_get, hb1_get, hb2_get, hb0, hb1, hb2]
          rw [hres]
          refine ⟨⟨34, [.i32 1], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
          apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
          rw [hpre, hstep11, hstep19, hstep27]
          split_res_fuel 100
          step_drop 3
          rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne32)]; norm_res_fuel
          exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
      · have hne82 : (bv1 == 82) = false := signExtend_bne_u32 hb1 rfl (by decide)
        have hres : Algorithm.checkRuleLine bytes = 1 := by
          simp [Algorithm.checkRuleLine, hlim_eq, hlt3, hb0_get, hb1_get, hb0, hb1]
        rw [hres]
        refine ⟨⟨26, [.i32 1], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
        apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
        rw [hpre, hstep11, hstep19]
        split_res_fuel 106
        step_drop 3
        rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne82)]; norm_res_fuel
        exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _
    · have hne35 : (bv0 == 35) = false := signExtend_bne_u32 hb0 rfl (by decide)
      have hres : Algorithm.checkRuleLine bytes = 1 := by
        simp [Algorithm.checkRuleLine, hlim_eq, hlt3, hb0_get, hb0]
      rw [hres]
      refine ⟨⟨18, [.i32 1], locs1, ⟨objs, []⟩, ⟨ar, u64, asc⟩⟩, ?_, rfl, rfl⟩
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      rw [hpre, hstep11]
      split_res_fuel 112
      step_drop 3
      rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne35)]; norm_res_fuel
      exact runJvmResFast_iconst_ireturn_step _ _ _ _ _ _ _ _ _

/-! #### 12. `f_Algorithm_parseBlockHeader_prog` -/

section ParseBlockHeader
set_option maxRecDepth 2048

private theorem jvmHeap_alloc_fst (h : Jvm.JvmHeap AlgExt) (o : Jvm.HeapObj AlgExt) :
    (h.alloc o).1 = h.objects.size := rfl

private theorem jhSet_statics {Ext : Type} (h : Jvm.JvmHeap Ext) (a : Nat) (o : Jvm.HeapObj Ext) :
    (h.set a o).statics = h.statics := by
  dsimp only [Jvm.JvmHeap.set]; split <;> rfl

private theorem setLocal_self (locs : Nat → JvmVal) (k : Nat) (v : JvmVal) :
    setLocal locs k v k = v := by simp [setLocal]

private theorem setLocal_ne {locs : Nat → JvmVal} {k j : Nat} {v : JvmVal} (hne : j ≠ k) :
    setLocal locs k v j = locs j := by simp [setLocal, hne]

private theorem runJvmResFast_areturn_step {f : Nat} {prog : List JvmInstr} {pc pc0 : Nat}
    {rest : List JvmInstr} {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.areturn :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := rfl

private theorem runJvmResFast_iconst {f pc pc0 : Nat} {prog rest : List JvmInstr} {c : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.iconst c :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 c :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.iconst c) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 c :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_istore {f pc pc0 idx : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.istore idx :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.istore idx) ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_astore {f pc pc0 idx : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.astore idx :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.astore idx) ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_aload {f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.aload idx :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.aload idx) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_ldcStr {f pc pc0 : Nat} {prog rest : List JvmInstr} {s : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.ldcStr s :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .str s :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.ldcStr s) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .str s :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_dup {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.dup :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, v :: v :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .dup ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, v :: v :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_intValue {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc
        (.invokevirtual "java/lang/Integer" "intValue" "()I" :: rest)
        ⟨pc0, .boxedInt v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 v :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.invokevirtual "java/lang/Integer" "intValue" "()I")
      ⟨pc, .boxedInt v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 v :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_uintUnbox {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc
        (.invokevirtual "kotlin/UInt" "unbox-impl" "()I" :: rest)
        ⟨pc0, .boxedUInt v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 v :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.invokevirtual "kotlin/UInt" "unbox-impl" "()I")
      ⟨pc, .boxedUInt v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 v :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_intValueOf {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc
        (.invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" :: rest)
        ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .boxedInt v :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks
      (.invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;")
      ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .boxedInt v :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_tableswitch {f pc pc0 dflt : Nat} {low : Int32} {targets : List Nat}
    {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.tableswitch low targets dflt :: rest)
        ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      let tgt := Jvm.tableswitchTarget v low targets dflt
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32]

private theorem runJvmResFast_instanceof_boxedInt_uint {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.instanceof "kotlin/UInt" :: rest)
        ⟨pc0, .boxedInt v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 0 :: stkRest, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.instanceof "kotlin/UInt")
      ⟨pc, .boxedInt v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 0 :: stkRest, locs, jh, hp⟩) := rfl
  simp only [runJvmResFast]
  rw [Jvm.runJvmResFast_step_nonbranch algHooks (hbr := rfl) (hno := by simp)]
  simp only [hstep, ↓reduceIte]

private theorem runJvmResFast_iload {f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.iload idx :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.iload idx) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_lload {f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.lload idx :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.lload idx) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_lstore {f pc pc0 idx : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.lstore idx :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.lstore idx) ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, setLocal locs idx v, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_aconstNull {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.aconstNull :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .null :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .aconstNull ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .null :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_nop {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.nop :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .nop ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_iadd {f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.iadd :: rest) ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 (a + b) :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .iadd ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (a + b) :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_isub {f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.isub :: rest) ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 (a - b) :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .isub ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 (a - b) :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_uintCtor {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc
        (.invokestatic "kotlin/UInt" "constructor-impl" "(I)I" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [runJvmResFast_invokestatic_step (hs := rfl)]

private theorem runJvmResFast_ubyteCtor {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc
        (.invokestatic "kotlin/UByte" "constructor-impl" "(B)B" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [runJvmResFast_invokestatic_step (hs := rfl)]

private theorem runJvmResFast_ulongCtor {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc
        (.invokestatic "kotlin/ULong" "constructor-impl" "(J)J" :: rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  rw [runJvmResFast_invokestatic_step (hs := rfl)]

private theorem runJvmResFast_compareUnsigned {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {a b : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc
        (.invokestatic "java/lang/Integer" "compareUnsigned" "(II)I" :: rest)
        ⟨pc0, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: stk,
          locs, jh, hp⟩ := by
  rw [runJvmResFast_invokestatic_step (hs := rfl)]
  rfl

private theorem parseBlockHeader_retNone
    {f pc st_loc : Nat} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hf : 12 ≤ f)
    (hdrop : f_Algorithm_parseBlockHeader_prog.drop pc =
      .iconst 1 :: .anewarray "java/lang/Object" :: .astore st_loc :: .aload st_loc ::
      .iconst 0 :: .iconst 0 ::
      .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" ::
      .aastore :: .aload st_loc :: .astore (st_loc - 1) :: .aload (st_loc - 1) ::
      .areturn :: f_Algorithm_parseBlockHeader_prog.drop (pc + 12)) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseBlockHeader_prog pc
          (f_Algorithm_parseBlockHeader_prog.drop pc) ⟨pc, stk, locs, jh, hp⟩ = some (v, st') ∧
      decodeOptParsedCoords st'.jvmHeap v = some none ∧
      st'.heap = hp ∧ st'.jvmHeap.statics = jh.statics := by
  let a0 : Array JvmVal := Array.replicate 1 .null
  let jh0 := (jh.alloc (.objArray "java/lang/Object" a0)).2
  let a1 := a0.set 0 (.boxedInt 0) (by simp [a0])
  let jh1 := jh0.set jh.objects.size (.objArray "java/lang/Object" a1)
  have hjh0 : jh0.get? jh.objects.size = some (.objArray "java/lang/Object" a0) :=
    jvmHeap_get?_alloc_self _ _
  have ha1 : a1 = #[.boxedInt 0] := rfl
  have hjh1_get : jh1.get? jh.objects.size = some (.objArray "java/lang/Object" #[.boxedInt 0]) := by
    have hset : jh1.get? jh.objects.size = some (.objArray "java/lang/Object" a1) :=
      jvmHeap_get?_set_self hjh0
    rwa [ha1] at hset
  have hjh1_stat : jh1.statics = jh.statics := jhSet_statics _ _ _
  let locs' := setLocal (setLocal locs st_loc (.heapRef jh.objects.size))
    (st_loc - 1) (.heapRef jh.objects.size)
  refine ⟨.heapRef jh.objects.size, ⟨pc + 11, .heapRef jh.objects.size :: stk, locs', jh1, hp⟩,
    ?_, ?_, rfl, hjh1_stat⟩
  · rw [hdrop]
    split_res_fuel 12
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_anewarray_obj (hslt := by decide),
      show (1 : UInt32).toNat = 1 from rfl]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_intValueOf]; norm_res_fuel
    rw [runJvmResFast_aastore (idx := 0) (hget := hjh0) (hslt := by decide) (hlt := by decide)]
    norm_res_fuel
    rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
    rw [show pc + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = pc + 11 by omega]
    exact runJvmResFast_areturn_step
  · dsimp only [decodeOptParsedCoords]
    rw [hjh1_get]
    rfl

private theorem parseBlockHeader_unpack_pair
    {f pc0 k defTgt s1 s2 : Nat} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {opt : Option Algorithm.ParsedInt32}
    (hf : 68 ≤ f)
    (hk2 : 2 ≤ k) (hs1_ne : s1 ≠ k + 2 ∧ s1 ≠ s2) (hs1_ne2 : s1 ≠ 0 ∧ s1 ≠ 1 ∧ s1 ≠ k + 3)
    (hs2_ne : s2 ≠ 0 ∧ s2 ≠ 1 ∧ s2 ≠ k + 3) (hs1_ne5 : 5 < k → s1 ≠ 5) (hs2_ne5 : 5 < k → s2 ≠ 5)
    (hdrop_pre : f_Algorithm_parseBlockHeader_prog.drop pc0 =
      .astore k :: .aload k :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload k :: .checkcast "[Ljava/lang/Object;" :: .iconst 0 :: .aaload :: .dup ::
      .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .checkcast "java/lang/Integer" :: .invokevirtual "java/lang/Integer" "intValue" "()I" ::
      .tableswitch 0 [pc0 + 14, pc0 + 26] defTgt ::
      f_Algorithm_parseBlockHeader_prog.drop (pc0 + 14))
    (hdrop_none : f_Algorithm_parseBlockHeader_prog.drop (pc0 + 14) =
      .iconst 1 :: .anewarray "java/lang/Object" :: .astore (k + 3) :: .aload (k + 3) ::
      .iconst 0 :: .iconst 0 ::
      .invokestatic "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" ::
      .aastore :: .aload (k + 3) :: .astore (k + 2) :: .aload (k + 2) ::
      .areturn :: f_Algorithm_parseBlockHeader_prog.drop (pc0 + 26))
    (hdrop_some1 : f_Algorithm_parseBlockHeader_prog.drop (pc0 + 26) =
      .aload k :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload :: .astore (k + 2) ::
      .aload (k + 2) :: .ldcStr "null cannot be cast to non-null type kotlin.Array<*>" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload (k + 2) :: .checkcast "[Ljava/lang/Object;" :: .iconst 1 :: .aaload ::
      .astore (k + 4) :: .iconst 0 :: .istore (k + 5) :: .aload (k + 4) ::
      .instanceof "kotlin/UInt" :: .ifeq (pc0 + 48) ::
      f_Algorithm_parseBlockHeader_prog.drop (pc0 + 44))
    (hdrop_some2 : f_Algorithm_parseBlockHeader_prog.drop (pc0 + 48) =
      .aload (k + 4) :: .ldcStr "null cannot be cast to non-null type kotlin.Int" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload (k + 4) :: .checkcast "java/lang/Integer" ::
      .invokevirtual "java/lang/Integer" "intValue" "()I" ::
      .istore (k + 3) :: .aload (k + 2) :: .checkcast "[Ljava/lang/Object;" :: .iconst 5 ::
      .aaload :: .astore s1 :: .iconst 0 :: .istore s2 ::
      .aload s1 :: .instanceof "java/lang/Integer" :: .ifeq (pc0 + 70) ::
      f_Algorithm_parseBlockHeader_prog.drop (pc0 + 65))
    (hdrop_some3 : f_Algorithm_parseBlockHeader_prog.drop (pc0 + 70) =
      .aload s1 :: .ldcStr "null cannot be cast to non-null type kotlin.UInt" ::
      .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull"
        "(Ljava/lang/Object;Ljava/lang/String;)V" ::
      .aload s1 :: .checkcast "kotlin/UInt" :: .invokevirtual "kotlin/UInt" "unbox-impl" "()I" ::
      f_Algorithm_parseBlockHeader_prog.drop (pc0 + 76)) :
    let enc := encodeOptScalarPair jh
      (opt.map fun r => (.boxedInt r.val.toUInt32, .boxedUInt r.next))
    match opt with
    | none =>
      ∃ v st',
        runJvmResFast f f_Algorithm_parseBlockHeader_prog pc0
          (f_Algorithm_parseBlockHeader_prog.drop pc0) ⟨pc0, enc.1 :: stk, locs, enc.2, hp⟩ =
          some (v, st') ∧
        decodeOptParsedCoords st'.jvmHeap v = some none ∧
        st'.heap = hp ∧ st'.jvmHeap.statics = jh.statics
    | some r =>
      ∃ locs',
        runJvmResFast f f_Algorithm_parseBlockHeader_prog pc0
          (f_Algorithm_parseBlockHeader_prog.drop pc0) ⟨pc0, enc.1 :: stk, locs, enc.2, hp⟩ =
        runJvmResFast (f - 55) f_Algorithm_parseBlockHeader_prog (pc0 + 76)
          (f_Algorithm_parseBlockHeader_prog.drop (pc0 + 76))
          ⟨pc0 + 76, .i32 r.next :: stk, locs', enc.2, hp⟩ ∧
        locs' 0 = locs 0 ∧ locs' 1 = locs 1 ∧
        locs' (k + 3) = .i32 r.val.toUInt32 ∧
        (5 < k → locs' 5 = locs 5) := by
  intro enc
  have hpre_opt : ∀ tag : UInt32, ∀ addr outerArr,
      enc.1 = .heapRef addr →
      enc.2.get? addr = some (.objArray "java/lang/Object" outerArr) →
      (hsz : 0 < outerArr.size) →
      outerArr[0] = .boxedInt tag →
      runJvmResFast f f_Algorithm_parseBlockHeader_prog pc0
        (f_Algorithm_parseBlockHeader_prog.drop pc0) ⟨pc0, enc.1 :: stk, locs, enc.2, hp⟩ =
      runJvmResFast (f - 14) f_Algorithm_parseBlockHeader_prog
        (Jvm.tableswitchTarget tag 0 [pc0 + 14, pc0 + 26] defTgt)
        (f_Algorithm_parseBlockHeader_prog.drop
          (Jvm.tableswitchTarget tag 0 [pc0 + 14, pc0 + 26] defTgt))
        ⟨Jvm.tableswitchTarget tag 0 [pc0 + 14, pc0 + 26] defTgt, stk,
          setLocal locs k enc.1, enc.2, hp⟩ := by
    intro tag addr outerArr henc1 hget hsz h0
    rw [henc1, hdrop_pre]
    split_res_fuel 14
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
    rw [runJvmResFast_checkcast_objArray (hget := hget) (hcls := Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_aaload (idx := 0) (hget := hget) (hslt := by decide) (hlt := hsz)]
    simp only [UInt32.toNat_zero, h0]; norm_res_fuel
    rw [runJvmResFast_dup]; norm_res_fuel
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]; norm_res_fuel
    rw [runJvmResFast_checkcast_boxedInt (hcls := Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_intValue]; norm_res_fuel
    rw [runJvmResFast_tableswitch]
  cases opt with
  | none =>
    dsimp only
    have henc1 : enc.1 = .heapRef jh.objects.size := rfl
    have hget : enc.2.get? jh.objects.size = some (.objArray "java/lang/Object" #[.boxedInt 0]) :=
      jvmHeap_get?_alloc_self _ _
    have hstat : enc.2.statics = jh.statics := rfl
    have hpre0 := hpre_opt 0 jh.objects.size #[.boxedInt 0] henc1 hget (by decide) rfl
    have hts0 : Jvm.tableswitchTarget 0 0 [pc0 + 14, pc0 + 26] defTgt = pc0 + 14 := by
      simp [Jvm.tableswitchTarget]
    rw [hts0] at hpre0
    rcases parseBlockHeader_retNone (f := f - 14) (pc := pc0 + 14) (st_loc := k + 3)
        (stk := stk) (locs := setLocal locs k enc.1) (jh := enc.2) (hp := hp) (by omega)
        (by rw [hdrop_none, show k + 3 - 1 = k + 2 by omega,
              show pc0 + 14 + 12 = pc0 + 26 by omega]) with ⟨v, st', hrun, hdec, hhp, hst⟩
    refine ⟨v, st', ?_, hdec, hhp, hst.trans hstat⟩
    rw [hpre0]
    exact hrun
  | some r =>
    dsimp only
    let innerArr : Array JvmVal :=
      #[.boxedInt 0, .boxedInt r.val.toUInt32, .null, .null, .null, .boxedUInt r.next]
    let outerArr : Array JvmVal := #[.boxedInt 1, .heapRef jh.objects.size]
    have hsome_arr : enc.1 = .heapRef (jh.objects.size + 1) ∧
        enc.2.get? (jh.objects.size + 1) = some (.objArray "java/lang/Object" outerArr) ∧
        enc.2.get? jh.objects.size = some (.objArray "java/lang/Object" innerArr) := by
      dsimp only [enc, Option.map, encodeOptScalarPair, innerArr, outerArr]
      have hsz : (jh.alloc (.objArray "java/lang/Object" innerArr)).2.objects.size =
          jh.objects.size + 1 := by simp [Jvm.JvmHeap.alloc]
      have hfst : (jh.alloc (.objArray "java/lang/Object" innerArr)).1 = jh.objects.size := rfl
      refine ⟨?_, ?_, ?_⟩
      · simp [Jvm.JvmHeap.alloc]
      · have hg := jvmHeap_get?_alloc_self
          (jh.alloc (.objArray "java/lang/Object" innerArr)).2
          (.objArray "java/lang/Object" outerArr)
        simpa only [innerArr, outerArr, hfst, hsz] using hg
      · rw [jvmHeap_get?_alloc_lt _ _ (by simp [Jvm.JvmHeap.alloc])]
        exact jvmHeap_get?_alloc_self _ _
    rcases hsome_arr with ⟨henc1, hget_outer, hget_inner⟩
    have hpre1 := hpre_opt 1 (jh.objects.size + 1) outerArr henc1 hget_outer (by simp [outerArr]) rfl
    have hts1 : Jvm.tableswitchTarget 1 0 [pc0 + 14, pc0 + 26] defTgt = pc0 + 26 := by
      simp [Jvm.tableswitchTarget]
    rw [hts1] at hpre1
    have ho1 : outerArr[(1 : UInt32).toNat]'(by simp [outerArr]) = .heapRef jh.objects.size := rfl
    have hi1 : innerArr[(1 : UInt32).toNat]'(by simp [innerArr]) = .boxedInt r.val.toUInt32 := rfl
    have hi5 : innerArr[(5 : UInt32).toNat]'(by simp [innerArr]) = .boxedUInt r.next := rfl
    apply Exists.intro _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hpre1, hdrop_some1]
      rw [show f - 14 = (f - 55) + 41 by omega]
      split_res_fuel 18
      rw [runJvmResFast_aload, setLocal_self, henc1]; norm_res_fuel
      rw [runJvmResFast_checkcast_objArray (hget := hget_outer) (hcls := Or.inl rfl)]; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_aaload (idx := 1) (hget := hget_outer) (hslt := by decide)
        (hlt := by simp [outerArr])]
      rw [ho1]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_ldcStr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_checkcast_objArray (hget := hget_inner) (hcls := Or.inl rfl)]; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_aaload (idx := 1) (hget := hget_inner) (hslt := by decide)
        (hlt := by simp [innerArr])]
      rw [hi1]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne (by omega), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_instanceof_boxedInt_uint]; norm_res_fuel
      rw [runJvmResFast_ifeq_branch (hv := rfl)]
      rw [show f - 55 + 41 - 18 = (f - 55) + 23 by omega, hdrop_some2]
      split_res_fuel 17
      rw [runJvmResFast_aload, setLocal_ne (by omega), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_ldcStr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne (by omega), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_checkcast_boxedInt (hcls := Or.inl rfl)]; norm_res_fuel
      rw [runJvmResFast_intValue]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne (by omega), setLocal_ne (by omega),
        setLocal_ne (by omega), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_checkcast_objArray (hget := hget_inner) (hcls := Or.inl rfl)]; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_aaload (idx := 5) (hget := hget_inner) (hslt := by decide)
        (hlt := by simp [innerArr])]
      rw [hi5]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne hs1_ne.2, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_instanceof_boxedUInt_int]; norm_res_fuel
      rw [runJvmResFast_ifeq_branch (hv := rfl)]
      rw [show f - 55 + 23 - 17 = (f - 55) + 6 by omega, hdrop_some3]
      split_res_fuel 6
      rw [runJvmResFast_aload, setLocal_ne hs1_ne.2, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_ldcStr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne hs1_ne.2, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_checkcast_boxedUInt (hcls := Or.inl rfl)]; norm_res_fuel
      rw [runJvmResFast_uintUnbox]
      rw [show pc0 + 70 + 1 + 1 + 1 + 1 + 1 + 1 = pc0 + 76 by omega,
        show f - 55 + 6 - 6 = f - 55 by omega]
    · repeat rw [setLocal_ne (by omega)]
    · repeat rw [setLocal_ne (by omega)]
    · rw [setLocal_ne hs2_ne.2.2.symm, setLocal_ne (by omega), setLocal_self]
    · intro hk5
      have hs1_5 := hs1_ne5 hk5
      have hs2_5 := hs2_ne5 hk5
      repeat rw [setLocal_ne (by omega)]

local macro "norm_fuel" : tactic =>
  `(tactic| (conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]))

set_option maxHeartbeats 400000 in
private theorem parseBlockHeader_retSome
    {f : Nat} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {x y : Int32} (hx : locs 5 = .i32 x.toUInt32) (hy : locs 10 = .i32 y.toUInt32)
    (hf : 46 ≤ f) :
    ∃ v st',
      runJvmResFast f f_Algorithm_parseBlockHeader_prog 277
        (f_Algorithm_parseBlockHeader_prog.drop 277) ⟨277, [], locs, jh, hp⟩ = some (v, st') ∧
      decodeOptParsedCoords st'.jvmHeap v = some (some ⟨x, y⟩) ∧
      st'.heap = hp ∧ st'.jvmHeap.statics = jh.statics := by
  let ao0 : Array JvmVal := #[.null, .null]
  let jho0 := (jh.alloc (.objArray "java/lang/Object" ao0)).2
  let ao1 : Array JvmVal := #[.boxedInt 1, .null]
  let jho1 := jho0.set jh.objects.size (.objArray "java/lang/Object" ao1)
  let ai0 : Array JvmVal := #[.null, .null, .null, .null, .null, .null]
  let jhi0 := (jho1.alloc (.objArray "java/lang/Object" ai0)).2
  let ai1 : Array JvmVal := #[.boxedInt 0, .null, .null, .null, .null, .null]
  let jhi1 := jhi0.set jho1.objects.size (.objArray "java/lang/Object" ai1)
  let ai2 : Array JvmVal := #[.boxedInt 0, .boxedInt x.toUInt32, .null, .null, .null, .null]
  let jhi2 := jhi1.set jho1.objects.size (.objArray "java/lang/Object" ai2)
  let ai3 : Array JvmVal := #[.boxedInt 0, .boxedInt x.toUInt32, .null, .null, .null, .null]
  let jhi3 := jhi2.set jho1.objects.size (.objArray "java/lang/Object" ai3)
  let ai4 : Array JvmVal := #[.boxedInt 0, .boxedInt x.toUInt32, .null, .null, .null, .null]
  let jhi4 := jhi3.set jho1.objects.size (.objArray "java/lang/Object" ai4)
  let ai5 : Array JvmVal := #[.boxedInt 0, .boxedInt x.toUInt32, .null, .null, .null, .null]
  let jhi5 := jhi4.set jho1.objects.size (.objArray "java/lang/Object" ai5)
  let ai6 : Array JvmVal :=
    #[.boxedInt 0, .boxedInt x.toUInt32, .null, .null, .null, .boxedInt y.toUInt32]
  let jhi6 := jhi5.set jho1.objects.size (.objArray "java/lang/Object" ai6)
  let ao2 : Array JvmVal := #[.boxedInt 1, .heapRef jho1.objects.size]
  let jhFin := jhi6.set jh.objects.size (.objArray "java/lang/Object" ao2)
  have ho_sz : jho1.objects.size = jh.objects.size + 1 := by
    dsimp only [jho1, jho0, Jvm.JvmHeap.set, Jvm.JvmHeap.alloc]; simp
  have ho_sz_lt : jh.objects.size < jho1.objects.size := by rw [ho_sz]; omega
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
    rw [jvmHeap_get?_alloc_lt _ _ ho_sz_lt]
    exact jvmHeap_get?_set_self hgo0
  have hfin_stat : jhFin.statics = jh.statics := by
    dsimp only [jhFin, jhi6, jhi5, jhi4, jhi3, jhi2, jhi1, jhi0, jho1, jho0]
    iterate 7 rw [jhSet_statics]
    rw [show ((jho1.alloc _).2).statics = jho1.statics from rfl, jhSet_statics]
    rfl
  have hf_add : f = (f - 46) + 46 := by omega
  have hrun : ∃ pc stk locs',
      runJvmResFast f f_Algorithm_parseBlockHeader_prog 277
        (f_Algorithm_parseBlockHeader_prog.drop 277) ⟨277, [], locs, jh, hp⟩ =
        some (.heapRef jh.objects.size, ⟨pc, stk, locs', jhFin, hp⟩) := by
    apply Exists.intro _
    apply Exists.intro _
    apply Exists.intro _
    · rw [hf_add]
      split_res_fuel 46
      step_drop 8
      rw [runJvmResFast_iconst]; norm_fuel
      rw [runJvmResFast_anewarray_obj (hslt := by decide),
        show (2 : UInt32).toNat = 2 from rfl,
        show Array.replicate 2 JvmVal.null = ao0 from rfl,
        show (jh.alloc (.objArray "java/lang/Object" ao0)).2 = jho0 from rfl]; norm_fuel
      rw [runJvmResFast_astore]; norm_fuel
      rw [runJvmResFast_aload, setLocal_self]; norm_fuel
      rw [runJvmResFast_iconst]; norm_fuel
      rw [runJvmResFast_iconst]; norm_fuel
      rw [runJvmResFast_intValueOf]; norm_fuel
      rw [runJvmResFast_aastore (idx := 0) (hget := hgo0) (hslt := by decide) (hlt := by decide)]
      rw [show ao0.set (0 : UInt32).toNat (.boxedInt 1) (by decide) = ao1 from rfl,
        show jho0.set jh.objects.size (.objArray "java/lang/Object" ao1) = jho1 from rfl]
      norm_fuel
      step_drop 10
      rw [runJvmResFast_aload, setLocal_self]; norm_fuel
      rw [runJvmResFast_iconst]; norm_fuel
      rw [runJvmResFast_iconst]; norm_fuel
      rw [runJvmResFast_anewarray_obj (hslt := by decide),
        show (6 : UInt32).toNat = 6 from rfl,
        show Array.replicate 6 JvmVal.null = ai0 from rfl,
        show (jho1.alloc (.objArray "java/lang/Object" ai0)).2 = jhi0 from rfl]; norm_fuel
      rw [runJvmResFast_astore]; norm_fuel
      rw [runJvmResFast_aload, setLocal_self]; norm_fuel
      rw [runJvmResFast_iconst]; norm_fuel
      rw [runJvmResFast_iconst]; norm_fuel
      rw [runJvmResFast_intValueOf]; norm_fuel
      rw [runJvmResFast_aastore (idx := 0) (hget := hgi0) (hslt := by decide) (hlt := by decide)]
      rw [show ai0.set (0 : UInt32).toNat (.boxedInt 0) (by decide) = ai1 from rfl,
        show jhi0.set jho1.objects.size (.objArray "java/lang/Object" ai1) = jhi1 from rfl]
      norm_fuel
      step_drop 5
      rw [runJvmResFast_aload, setLocal_self]; norm_fuel
      rw [runJvmResFast_iconst]; norm_fuel
      rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide), hx]; norm_fuel
      rw [runJvmResFast_intValueOf]; norm_fuel
      rw [runJvmResFast_aastore (idx := 1) (hget := hgi1) (hslt := by decide) (hlt := by decide)]
      rw [show ai1.set (1 : UInt32).toNat (.boxedInt x.toUInt32) (by decide) = ai2 from rfl,
        show jhi1.set jho1.objects.size (.objArray "java/lang/Object" ai2) = jhi2 from rfl]
      norm_fuel
      step_drop 4
      rw [runJvmResFast_aload, setLocal_self]; norm_fuel
      rw [runJvmResFast_iconst]; norm_fuel
      rw [runJvmResFast_aconstNull]; norm_fuel
      rw [runJvmResFast_aastore (idx := 2) (hget := hgi2) (hslt := by decide) (hlt := by simp [ai2])]
      rw [show ai2.set (2 : UInt32).toNat .null (by simp [ai2]) = ai3 from rfl,
        show jhi2.set jho1.objects.size (.objArray "java/lang/Object" ai3) = jhi3 from rfl]
      norm_fuel
      step_drop 4
      rw [runJvmResFast_aload, setLocal_self]; norm_fuel
      rw [runJvmResFast_iconst]; norm_fuel
      rw [runJvmResFast_aconstNull]; norm_fuel
      rw [runJvmResFast_aastore (idx := 3) (hget := hgi3) (hslt := by decide) (hlt := by simp [ai3])]
      rw [show ai3.set (3 : UInt32).toNat .null (by simp [ai3]) = ai4 from rfl,
        show jhi3.set jho1.objects.size (.objArray "java/lang/Object" ai4) = jhi4 from rfl]
      norm_fuel
      step_drop 4
      rw [runJvmResFast_aload, setLocal_self]; norm_fuel
      rw [runJvmResFast_iconst]; norm_fuel
      rw [runJvmResFast_aconstNull]; norm_fuel
      rw [runJvmResFast_aastore (idx := 4) (hget := hgi4) (hslt := by decide) (hlt := by simp [ai4])]
      rw [show ai4.set (4 : UInt32).toNat .null (by simp [ai4]) = ai5 from rfl,
        show jhi4.set jho1.objects.size (.objArray "java/lang/Object" ai5) = jhi5 from rfl]
      norm_fuel
      step_drop 5
      rw [runJvmResFast_aload, setLocal_self]; norm_fuel
      rw [runJvmResFast_iconst]; norm_fuel
      rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide), hy]; norm_fuel
      rw [runJvmResFast_intValueOf]; norm_fuel
      rw [runJvmResFast_aastore (idx := 5) (hget := hgi5) (hslt := by decide) (hlt := by simp [ai5])]
      rw [show ai5.set (5 : UInt32).toNat (.boxedInt y.toUInt32) (by simp [ai5]) = ai6 from rfl,
        show jhi5.set jho1.objects.size (.objArray "java/lang/Object" ai6) = jhi6 from rfl]
      norm_fuel
      step_drop 6
      rw [runJvmResFast_aload, setLocal_self]; norm_fuel
      rw [runJvmResFast_aastore (idx := 1) (hget := hgo1) (hslt := by decide) (hlt := by decide)]
      rw [show ao1.set (1 : UInt32).toNat (.heapRef jho1.objects.size) (by decide) = ao2 from rfl,
        show jhi6.set jh.objects.size (.objArray "java/lang/Object" ao2) = jhFin from rfl]
      norm_fuel
      rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_fuel
      rw [runJvmResFast_astore]; norm_fuel
      rw [runJvmResFast_aload, setLocal_self]; norm_fuel
      exact runJvmResFast_areturn_step
  rcases hrun with ⟨pc, stk, locs', hrun⟩
  refine ⟨.heapRef jh.objects.size, ⟨pc, stk, locs', jhFin, hp⟩, hrun, ?_, rfl, hfin_stat⟩
  · have hfin_o : jhFin.get? jh.objects.size =
        some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef jho1.objects.size]) :=
      jvmHeap_get?_set_self hgo1
    have hfin_i : jhFin.get? jho1.objects.size =
        some (.objArray "java/lang/Object"
          #[.boxedInt 0, .boxedInt x.toUInt32, .null, .null, .null, .boxedInt y.toUInt32]) := by
      rw [jvmHeap_get?_set_ne _ _ (by omega)]
      exact jvmHeap_get?_set_self hgi5
    have hmk_jh : ∀ p s l (j : Jvm.JvmHeap AlgExt) h,
        ({ pc := p, stack := s, locals := l, jvmHeap := j, heap := h } : JvmState).jvmHeap = j :=
      fun _ _ _ _ _ => rfl
    rw [hmk_jh]
    exact @decodeOptParsedCoords_some jhFin jh.objects.size jho1.objects.size x y hfin_o hfin_i

theorem parseBlockHeader_equiv (bytes : ByteArray) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (bytesAddr : Nat) (hget : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hlen31 : bytes.data.size < 2 ^ 31) :
    ∃ v st',
      runJvmRes 250 f_Algorithm_parseBlockHeader_prog
        ⟨0, [], setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr), jh, hp⟩ = some (v, st') ∧
      decodeOptParsedCoords st'.jvmHeap v = some (Algorithm.parseBlockHeader bytes) ∧
      st'.heap = hp ∧ st'.jvmHeap.statics = jh.statics := by
  let limit := UInt32.ofNat bytes.data.size
  have hlim_eq : bytes.size.toUInt32 = limit := rfl
  have hlim_toNat : limit.toNat = bytes.data.size := by
    dsimp only [limit]
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  let locs0 : Nat → JvmVal := setLocal (fun _ => .i32 0) 0 (.heapRef bytesAddr)
  let locs1 : Nat → JvmVal := setLocal locs0 1 (.i32 limit)
  suffices h : ∃ v st',
      runJvmResFast 250 f_Algorithm_parseBlockHeader_prog 0 f_Algorithm_parseBlockHeader_prog
        ⟨0, [], locs0, jh, hp⟩ = some (v, st') ∧
      decodeOptParsedCoords st'.jvmHeap v = some (Algorithm.parseBlockHeader bytes) ∧
      st'.heap = hp ∧ st'.jvmHeap.statics = jh.statics by
    rcases h with ⟨v, st', hrun, hdec, hhp, hst⟩
    exact ⟨v, st', by rw [runJvmRes_of_runJvmResFast0 250 _ _ _ rfl]; exact hrun, hdec, hhp, hst⟩
  have hpre :
      runJvmResFast 250 f_Algorithm_parseBlockHeader_prog 0 f_Algorithm_parseBlockHeader_prog
        ⟨0, [], locs0, jh, hp⟩ =
      runJvmResFast 240 f_Algorithm_parseBlockHeader_prog 10
        (f_Algorithm_parseBlockHeader_prog.drop 10)
        ⟨10, [.i32 (if limit == 3 then 0 else if limit < 3 then 4294967295 else 1)],
          locs1, jh, hp⟩ := by
    split_res_fuel 10
    conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_parseBlockHeader_prog)]
    step_drop 10
    heap_step_nonbranch_chunks; norm_res_fuel
    rw [runJvmResFast_arraylength_byte (hget := hget)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    dsimp only [Jvm.JvmVal.asI32]
    rfl
  by_cases hlt3 : limit < 3
  · have hres : Algorithm.parseBlockHeader bytes = none := by
      simp [Algorithm.parseBlockHeader, hlim_eq, hlt3]
    rw [hres]
    rcases parseBlockHeader_retNone (f := 239) (pc := 335) (st_loc := 3) (stk := [])
        (locs := locs1) (jh := jh) (hp := hp) (by omega) rfl with ⟨v, st', hrun, hdec, hhp, hst⟩
    refine ⟨v, st', ?_, hdec, hhp, hst⟩
    rw [hpre]
    split_res_fuel 1
    step_drop 1
    rw [runJvmResFast_iflt_branch (by
      change (if limit == 3 then (0 : UInt32) else if limit < 3 then 4294967295 else 1).toBitVec.slt 0#32 =
        true
      rw [compareUnsigned_slt_zero]; exact decide_eq_true hlt3)]
    exact hrun
  · have h3_sz : 3 ≤ bytes.data.size := by
      have hnt : ¬(limit.toNat < 3) := mt (@UInt32.lt_iff_toNat_lt limit 3).mpr hlt3
      dsimp only [UInt32.toNat] at hnt hlim_toNat; omega
    have h0_sz : 0 < bytes.data.size := by omega
    have h1_sz : 1 < bytes.data.size := by omega
    have h2_sz : 2 < bytes.data.size := by omega
    have h10_11 :
        runJvmResFast 240 f_Algorithm_parseBlockHeader_prog 10
          (f_Algorithm_parseBlockHeader_prog.drop 10)
          ⟨10, [.i32 (if limit == 3 then 0 else if limit < 3 then 4294967295 else 1)],
            locs1, jh, hp⟩ =
        runJvmResFast 234 f_Algorithm_parseBlockHeader_prog 16
          (f_Algorithm_parseBlockHeader_prog.drop 16)
          ⟨16, [.i32 35, .i32 (UInt32.ofBitVec ((bytes.get! 0).toBitVec.signExtend 32))],
            locs1, jh, hp⟩ := by
      split_res_fuel 6
      step_drop 6
      rw [runJvmResFast_iflt_fallthrough (by
        change (if limit == 3 then (0 : UInt32) else if limit < 3 then 4294967295 else 1).toBitVec.slt
          0#32 = false
        rw [compareUnsigned_slt_zero]; exact decide_eq_false hlt3)]
      norm_res_fuel
      rw [runJvmResFast_aload]; try dsimp only [locs1, locs0]
      rw [setLocal_ne (by decide), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_baload (hget := hget) (hslt := by decide)
        (hlt := by
          change (0 : UInt32).toNat < bytes.data.size
          rw [show (0 : UInt32).toNat = 0 from rfl]
          exact h0_sz)]
      norm_res_fuel
      rw [runJvmResFast_ubyteCtor]; norm_res_fuel
      rw [runJvmResFast_iconst]
      rw [show bytes.data[(0 : UInt32).toNat] = bytes.get! 0 from
        (getElem!_pos bytes.data 0 h0_sz).symm]
    by_cases hb0 : bytes.get! 0 = 35
    · have heq35 : UInt32.ofBitVec ((bytes.get! 0).toBitVec.signExtend 32) = 35 :=
        signExtend_eq_u32 hb0 rfl (by decide)
      have h16_34 :
          runJvmResFast 234 f_Algorithm_parseBlockHeader_prog 16
            (f_Algorithm_parseBlockHeader_prog.drop 16)
            ⟨16, [.i32 35, .i32 (UInt32.ofBitVec ((bytes.get! 0).toBitVec.signExtend 32))],
              locs1, jh, hp⟩ =
          runJvmResFast 228 f_Algorithm_parseBlockHeader_prog 34
            (f_Algorithm_parseBlockHeader_prog.drop 34)
            ⟨34, [.i32 80, .i32 (UInt32.ofBitVec ((bytes.get! 1).toBitVec.signExtend 32))],
              locs1, jh, hp⟩ := by
        split_res_fuel 6
        step_drop 1
        rw [runJvmResFast_if_icmpeq_branch (heq := heq35)]; norm_res_fuel
        step_drop 5
        rw [runJvmResFast_aload]; try dsimp only [locs1, locs0]
        rw [setLocal_ne (by decide), setLocal_self]; norm_res_fuel
        rw [runJvmResFast_iconst]; norm_res_fuel
        rw [runJvmResFast_baload (hget := hget) (hslt := by decide)
          (hlt := by
            change (1 : UInt32).toNat < bytes.data.size
            rw [show (1 : UInt32).toNat = 1 from rfl]
            exact h1_sz)]
        norm_res_fuel
        rw [runJvmResFast_ubyteCtor]; norm_res_fuel
        rw [runJvmResFast_iconst]
        rw [show bytes.data[(1 : UInt32).toNat] = bytes.get! 1 from
          (getElem!_pos bytes.data 1 h1_sz).symm]
      by_cases hb1 : bytes.get! 1 = 80
      · have heq80 : UInt32.ofBitVec ((bytes.get! 1).toBitVec.signExtend 32) = 80 :=
          signExtend_eq_u32 hb1 rfl (by decide)
        have h34_52 :
            runJvmResFast 228 f_Algorithm_parseBlockHeader_prog 34
              (f_Algorithm_parseBlockHeader_prog.drop 34)
              ⟨34, [.i32 80, .i32 (UInt32.ofBitVec ((bytes.get! 1).toBitVec.signExtend 32))],
                locs1, jh, hp⟩ =
            runJvmResFast 222 f_Algorithm_parseBlockHeader_prog 52
              (f_Algorithm_parseBlockHeader_prog.drop 52)
              ⟨52, [.i32 32, .i32 (UInt32.ofBitVec ((bytes.get! 2).toBitVec.signExtend 32))],
                locs1, jh, hp⟩ := by
          split_res_fuel 6
          step_drop 1
          rw [runJvmResFast_if_icmpeq_branch (heq := heq80)]; norm_res_fuel
          step_drop 5
          rw [runJvmResFast_aload]; try dsimp only [locs1, locs0]
          rw [setLocal_ne (by decide), setLocal_self]; norm_res_fuel
          rw [runJvmResFast_iconst]; norm_res_fuel
          rw [runJvmResFast_baload (hget := hget) (hslt := by decide)
            (hlt := by
              change (2 : UInt32).toNat < bytes.data.size
              rw [show (2 : UInt32).toNat = 2 from rfl]
              exact h2_sz)]
          norm_res_fuel
          rw [runJvmResFast_ubyteCtor]; norm_res_fuel
          rw [runJvmResFast_iconst]
          rw [show bytes.data[(2 : UInt32).toNat] = bytes.get! 2 from
            (getElem!_pos bytes.data 2 h2_sz).symm]
        by_cases hb2 : bytes.get! 2 = 32
        · have heq32 : UInt32.ofBitVec ((bytes.get! 2).toBitVec.signExtend 32) = 32 :=
            signExtend_eq_u32 hb2 rfl (by decide)
          let p1 := Algorithm.parseInt32At bytes 3 limit
          let enc1 := encodeOptScalarPair jh
            (p1.map fun r => (.boxedInt r.val.toUInt32, .boxedUInt r.next))
          have h52_69 :
              runJvmResFast 222 f_Algorithm_parseBlockHeader_prog 52
                (f_Algorithm_parseBlockHeader_prog.drop 52)
                ⟨52, [.i32 32, .i32 (UInt32.ofBitVec ((bytes.get! 2).toBitVec.signExtend 32))],
                  locs1, jh, hp⟩ =
              runJvmResFast 217 f_Algorithm_parseBlockHeader_prog 69
                (f_Algorithm_parseBlockHeader_prog.drop 69)
                ⟨69, [enc1.1], locs1, enc1.2, hp⟩ := by
            split_res_fuel 5
            step_drop 1
            rw [runJvmResFast_if_icmpeq_branch (heq := heq32)]; norm_res_fuel
            step_drop 4
            rw [runJvmResFast_aload]; try dsimp only [locs1, locs0]
            rw [setLocal_ne (by decide), setLocal_self]; norm_res_fuel
            rw [runJvmResFast_iconst]; norm_res_fuel
            rw [runJvmResFast_iload]; try dsimp only [locs1]
            rw [setLocal_self]; norm_res_fuel
            rw [runJvmResFast_invokestatic_step
              (hs := stepStatic_parseInt32At_heap (Or.inl rfl) hget)]
            dsimp only [Jvm.JvmVal.asI32]
            rw [show Algorithm.parseInt32At ⟨bytes.data⟩ 3 limit = p1 from rfl]
            rfl
          have hup1 := parseBlockHeader_unpack_pair (f := 217) (pc0 := 69) (k := 2) (defTgt := 329)
            (s1 := 7) (s2 := 8) (stk := []) (locs := locs1) (jh := jh) (hp := hp) (opt := p1)
            (by omega) (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)
            (fun _ => by decide) rfl rfl rfl rfl rfl
          cases hp1 : p1 with
          | none =>
            simp only [hp1] at hup1
            rcases hup1 with ⟨v, st', hrun, hdec, hhp, hst⟩
            have hres : Algorithm.parseBlockHeader bytes = none := by
              simp [Algorithm.parseBlockHeader, hlim_eq, hlt3, hb0, hb1, hb2,
                show Algorithm.parseInt32At bytes 3 limit = none from hp1]
            rw [hres]
            refine ⟨v, st', ?_, hdec, hhp, hst⟩
            dsimp only [enc1] at h52_69; rw [hp1] at h52_69
            rw [hpre, h10_11, h16_34, h34_52, h52_69]
            exact hrun
          | some r1 =>
            simp only [hp1] at hup1
            rcases hup1 with ⟨locs2, hrun1, hl2_0, hl2_1, hl2_5, _⟩
            have henc1 : enc1 = encodeOptScalarPair jh
                ((some r1).map fun r => (.boxedInt r.val.toUInt32, .boxedUInt r.next)) := by
              dsimp only [enc1]; rw [hp1]
            have henc1_bytes : enc1.2.get? bytesAddr = some (.byteArray bytes.data) := by
              let innerArr : Array JvmVal :=
                #[.boxedInt 0, .boxedInt r1.val.toUInt32, .null, .null, .null, .boxedUInt r1.next]
              have hex1 := heapExtends_alloc jh (.objArray "java/lang/Object" innerArr)
              have hex2 := heapExtends_alloc (jh.alloc (.objArray "java/lang/Object" innerArr)).2
                (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef jh.objects.size])
              dsimp only [enc1]
              rw [hp1]
              exact heapExtends_trans hex1 hex2 bytesAddr _ hget
            have hl2_0' : locs2 0 = .heapRef bytesAddr := by
              rw [hl2_0]; dsimp only [locs1, locs0]; rw [setLocal_ne (by decide), setLocal_self]
            have hl2_1' : locs2 1 = .i32 limit := by
              rw [hl2_1]; dsimp only [locs1]; rw [setLocal_self]
            let locs2' := setLocal locs2 6 (.i32 r1.next)
            have hl2'_0 : locs2' 0 = .heapRef bytesAddr := by
              dsimp only [locs2']; rw [setLocal_ne (by decide), hl2_0']
            have hl2'_1 : locs2' 1 = .i32 limit := by
              dsimp only [locs2']; rw [setLocal_ne (by decide), hl2_1']
            have hl2'_6 : locs2' 6 = .i32 r1.next := by
              dsimp only [locs2']; rw [setLocal_self]
            have h145_149 :
                runJvmResFast (217 - 55) f_Algorithm_parseBlockHeader_prog (69 + 76)
                  (f_Algorithm_parseBlockHeader_prog.drop (69 + 76))
                  ⟨69 + 76, [.i32 r1.next], locs2, enc1.2, hp⟩ =
                runJvmResFast 158 f_Algorithm_parseBlockHeader_prog 149
                  (f_Algorithm_parseBlockHeader_prog.drop 149)
                  ⟨149, [.i32 (if r1.next == limit then 0 else if r1.next < limit then 4294967295
                    else 1)], locs2', enc1.2, hp⟩ := by
              rw [show 69 + 76 = 145 by omega, show 217 - 55 = 162 by omega]
              split_res_fuel 4
              step_drop 4
              rw [runJvmResFast_istore]; norm_res_fuel
              rw [runJvmResFast_iload, setLocal_self]; norm_res_fuel
              rw [runJvmResFast_iload, setLocal_ne (by decide), hl2_1']; norm_res_fuel
              rw [runJvmResFast_compareUnsigned]
            by_cases hr1_lt : r1.next < limit
            · have hr1_sz : r1.next.toNat < bytes.data.size := by
                have := UInt32.lt_iff_toNat_lt.mp hr1_lt
                omega
              have hr1_slt : r1.next.toBitVec.slt 0#32 = false :=
                u32_slt_zero_of_lt hr1_lt (by omega)
              have h149_167 :
                  runJvmResFast 158 f_Algorithm_parseBlockHeader_prog 149
                    (f_Algorithm_parseBlockHeader_prog.drop 149)
                    ⟨149, [.i32 (if r1.next == limit then 0 else if r1.next < limit then 4294967295
                      else 1)], locs2', enc1.2, hp⟩ =
                  runJvmResFast 152 f_Algorithm_parseBlockHeader_prog 167
                    (f_Algorithm_parseBlockHeader_prog.drop 167)
                    ⟨167, [.i32 32,
                      .i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))],
                      locs2', enc1.2, hp⟩ := by
                split_res_fuel 6
                step_drop 1
                rw [runJvmResFast_iflt_branch (by
                  change (if r1.next == limit then (0 : UInt32)
                    else if r1.next < limit then 4294967295 else 1).toBitVec.slt 0#32 = true
                  rw [compareUnsigned_slt_zero]; exact decide_eq_true hr1_lt)]
                norm_res_fuel
                step_drop 5
                rw [runJvmResFast_aload]; try dsimp only [locs2']
                rw [setLocal_ne (by decide), hl2_0']; norm_res_fuel
                rw [runJvmResFast_iload]; try dsimp only [locs2']
                rw [setLocal_self]; norm_res_fuel
                rw [runJvmResFast_baload (hget := henc1_bytes) (hslt := hr1_slt)
                  (hlt := by exact hr1_sz)]
                norm_res_fuel
                rw [runJvmResFast_ubyteCtor]; norm_res_fuel
                rw [runJvmResFast_iconst]
                rw [show bytes.data[r1.next.toNat] = bytes.get! r1.next.toNat from
                  (getElem!_pos bytes.data r1.next.toNat hr1_sz).symm]
              by_cases hb_sp : bytes.get! r1.next.toNat = 32
              · have heq_sp : UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32) =
                    32 := signExtend_eq_u32 hb_sp rfl (by decide)
                let p2 := Algorithm.parseInt32At bytes (r1.next + 1) limit
                let enc2 := encodeOptScalarPair enc1.2
                  (p2.map fun r => (.boxedInt r.val.toUInt32, .boxedUInt r.next))
                have h167_187 :
                    runJvmResFast 152 f_Algorithm_parseBlockHeader_prog 167
                      (f_Algorithm_parseBlockHeader_prog.drop 167)
                      ⟨167, [.i32 32,
                        .i32 (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32))],
                        locs2', enc1.2, hp⟩ =
                    runJvmResFast 144 f_Algorithm_parseBlockHeader_prog 187
                      (f_Algorithm_parseBlockHeader_prog.drop 187)
                      ⟨187, [enc2.1], locs2', enc2.2, hp⟩ := by
                  split_res_fuel 8
                  step_drop 1
                  rw [runJvmResFast_if_icmpeq_branch (heq := heq_sp)]; norm_res_fuel
                  step_drop 7
                  rw [runJvmResFast_aload]; try dsimp only [locs2']
                  rw [setLocal_ne (by decide), hl2_0']; norm_res_fuel
                  rw [runJvmResFast_iload]; try dsimp only [locs2']
                  rw [setLocal_self]; norm_res_fuel
                  rw [runJvmResFast_iconst]; norm_res_fuel
                  rw [runJvmResFast_iadd]; norm_res_fuel
                  rw [runJvmResFast_uintCtor]; norm_res_fuel
                  rw [runJvmResFast_iload]; try dsimp only [locs2']
                  rw [setLocal_ne (by decide), hl2_1']; norm_res_fuel
                  rw [runJvmResFast_invokestatic_step
                    (hs := stepStatic_parseInt32At_heap (Or.inl rfl) henc1_bytes)]
                  dsimp only [Jvm.JvmVal.asI32]
                  rw [show Algorithm.parseInt32At ⟨bytes.data⟩ (r1.next + 1) limit = p2 from rfl]
                  rfl
                have hup2 := parseBlockHeader_unpack_pair (f := 144) (pc0 := 187) (k := 7)
                  (defTgt := 323) (s1 := 11) (s2 := 12) (stk := []) (locs := locs2')
                  (jh := enc1.2) (hp := hp) (opt := p2)
                  (by omega) (by decide) (by decide) (by decide) (by decide)
                  (fun _ => by decide) (fun _ => by decide) rfl rfl rfl rfl rfl
                cases hp2 : p2 with
                | none =>
                  simp only [hp2] at hup2
                  rcases hup2 with ⟨v, st', hrun2, hdec, hhp, hst⟩
                  have henc1_st : enc1.2.statics = jh.statics := by
                    dsimp only [enc1]; rw [hp1]; rfl
                  have hres : Algorithm.parseBlockHeader bytes = none := by
                    simp [Algorithm.parseBlockHeader, hlim_eq, hlt3, hb0, hb1, hb2,
                      show Algorithm.parseInt32At bytes 3 limit = some r1 from hp1,
                      hr1_lt, hb_sp,
                      show Algorithm.parseInt32At bytes (r1.next + 1) limit = none from hp2]
                  rw [hres]
                  refine ⟨v, st', ?_, hdec, hhp, hst.trans henc1_st⟩
                  dsimp only [enc2] at h167_187; rw [hp2] at h167_187
                  rw [hpre, h10_11, h16_34, h34_52, h52_69, henc1, hrun1, ← henc1, h145_149,
                    h149_167, h167_187]
                  exact hrun2
                | some r2 =>
                  simp only [hp2] at hup2
                  rcases hup2 with ⟨locs3, hrun2, _, hl3_1, hl3_10, hl3_5⟩
                  have henc2 : enc2 = encodeOptScalarPair enc1.2
                      ((some r2).map fun r => (.boxedInt r.val.toUInt32, .boxedUInt r.next)) := by
                    dsimp only [enc2]; rw [hp2]
                  have hl3_5' : locs3 5 = .i32 r1.val.toUInt32 := by
                    rw [hl3_5 (by decide)]
                    dsimp only [locs2']; rw [setLocal_ne (by decide), hl2_5]
                  have hl3_1' : locs3 1 = .i32 limit := by
                    rw [hl3_1, hl2'_1]
                  have henc2_st : enc2.2.statics = jh.statics := by
                    dsimp only [enc2, enc1]; rw [hp2, hp1]; rfl
                  by_cases hr2_eq : r2.next = limit
                  · have hres : Algorithm.parseBlockHeader bytes = some ⟨r1.val, r2.val⟩ := by
                      simp [Algorithm.parseBlockHeader, hlim_eq, hlt3, hb0, hb1, hb2,
                        show Algorithm.parseInt32At bytes 3 limit = some r1 from hp1,
                        hr1_lt, hb_sp,
                        show Algorithm.parseInt32At bytes (r1.next + 1) limit = some r2 from hp2,
                        hr2_eq]
                    rw [hres]
                    rcases parseBlockHeader_retSome (f := 87) (locs := locs3) (jh := enc2.2)
                        (hp := hp) hl3_5' hl3_10 (by omega) with ⟨v, st', hret, hdec, hhp, hst⟩
                    refine ⟨v, st', ?_, hdec, hhp, hst.trans henc2_st⟩
                    rw [hpre, h10_11, h16_34, h34_52, h52_69, henc1, hrun1, ← henc1, h145_149,
                      h149_167, h167_187, henc2, hrun2, ← henc2]
                    rw [show 187 + 76 = 263 by omega, show 144 - 55 = 89 by omega]
                    split_res_fuel 2
                    step_drop 2
                    rw [runJvmResFast_iload, hl3_1']; norm_res_fuel
                    rw [runJvmResFast_if_icmpeq_branch (heq := hr2_eq)]
                    exact hret
                  · have hres : Algorithm.parseBlockHeader bytes = none := by
                      simp [Algorithm.parseBlockHeader, hlim_eq, hlt3, hb0, hb1, hb2,
                        show Algorithm.parseInt32At bytes 3 limit = some r1 from hp1,
                        hr1_lt, hb_sp,
                        show Algorithm.parseInt32At bytes (r1.next + 1) limit = some r2 from hp2,
                        hr2_eq]
                    rw [hres]
                    rcases parseBlockHeader_retNone (f := 87) (pc := 265) (st_loc := 12) (stk := [])
                        (locs := locs3) (jh := enc2.2) (hp := hp) (by omega) rfl with
                        ⟨v, st', hret, hdec, hhp, hst⟩
                    refine ⟨v, st', ?_, hdec, hhp, hst.trans henc2_st⟩
                    rw [hpre, h10_11, h16_34, h34_52, h52_69, henc1, hrun1, ← henc1, h145_149,
                      h149_167, h167_187, henc2, hrun2, ← henc2]
                    rw [show 187 + 76 = 263 by omega, show 144 - 55 = 89 by omega]
                    split_res_fuel 2
                    step_drop 2
                    rw [runJvmResFast_iload, hl3_1']; norm_res_fuel
                    rw [runJvmResFast_if_icmpeq_fallthrough (hne := beq_false_of_ne hr2_eq)]
                    exact hret
              · have hne_sp : (UInt32.ofBitVec ((bytes.get! r1.next.toNat).toBitVec.signExtend 32) ==
                    32) = false := signExtend_bne_u32 hb_sp rfl (by decide)
                have henc1_st : enc1.2.statics = jh.statics := by
                  dsimp only [enc1]; rw [hp1]; rfl
                have hres : Algorithm.parseBlockHeader bytes = none := by
                  simp [Algorithm.parseBlockHeader, hlim_eq, hlt3, hb0, hb1, hb2,
                    show Algorithm.parseInt32At bytes 3 limit = some r1 from hp1,
                    hr1_lt, hb_sp]
                rw [hres]
                rcases parseBlockHeader_retNone (f := 151) (pc := 168) (st_loc := 8) (stk := [])
                    (locs := locs2') (jh := enc1.2) (hp := hp) (by omega) rfl with
                    ⟨v, st', hret, hdec, hhp, hst⟩
                refine ⟨v, st', ?_, hdec, hhp, hst.trans henc1_st⟩
                rw [hpre, h10_11, h16_34, h34_52, h52_69, henc1, hrun1, ← henc1, h145_149, h149_167]
                split_res_fuel 1
                step_drop 1
                rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne_sp)]
                exact hret
            · have henc1_st : enc1.2.statics = jh.statics := by
                dsimp only [enc1]; rw [hp1]; rfl
              have hres : Algorithm.parseBlockHeader bytes = none := by
                simp [Algorithm.parseBlockHeader, hlim_eq, hlt3, hb0, hb1, hb2,
                  show Algorithm.parseInt32At bytes 3 limit = some r1 from hp1, hr1_lt]
              rw [hres]
              rcases parseBlockHeader_retNone (f := 157) (pc := 150) (st_loc := 8) (stk := [])
                  (locs := locs2') (jh := enc1.2) (hp := hp) (by omega) rfl with
                  ⟨v, st', hret, hdec, hhp, hst⟩
              refine ⟨v, st', ?_, hdec, hhp, hst.trans henc1_st⟩
              rw [hpre, h10_11, h16_34, h34_52, h52_69, henc1, hrun1, ← henc1, h145_149]
              split_res_fuel 1
              step_drop 1
              rw [runJvmResFast_iflt_fallthrough (by
                change (if r1.next == limit then (0 : UInt32)
                  else if r1.next < limit then 4294967295 else 1).toBitVec.slt 0#32 = false
                rw [compareUnsigned_slt_zero]; exact decide_eq_false hr1_lt)]
              exact hret
        · have hne32 : (UInt32.ofBitVec ((bytes.get! 2).toBitVec.signExtend 32) == 32) = false :=
            signExtend_bne_u32 hb2 rfl (by decide)
          have hres : Algorithm.parseBlockHeader bytes = none := by
            simp [Algorithm.parseBlockHeader, hlim_eq, hlt3, hb0, hb1, hb2]
          rw [hres]
          rcases parseBlockHeader_retNone (f := 221) (pc := 53) (st_loc := 3) (stk := [])
              (locs := locs1) (jh := jh) (hp := hp) (by omega) rfl with
              ⟨v, st', hret, hdec, hhp, hst⟩
          refine ⟨v, st', ?_, hdec, hhp, hst⟩
          rw [hpre, h10_11, h16_34, h34_52]
          split_res_fuel 1
          step_drop 1
          rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne32)]
          exact hret
      · have hne80 : (UInt32.ofBitVec ((bytes.get! 1).toBitVec.signExtend 32) == 80) = false :=
          signExtend_bne_u32 hb1 rfl (by decide)
        have hres : Algorithm.parseBlockHeader bytes = none := by
          simp [Algorithm.parseBlockHeader, hlim_eq, hlt3, hb0, hb1]
        rw [hres]
        rcases parseBlockHeader_retNone (f := 227) (pc := 35) (st_loc := 3) (stk := [])
            (locs := locs1) (jh := jh) (hp := hp) (by omega) rfl with
            ⟨v, st', hret, hdec, hhp, hst⟩
        refine ⟨v, st', ?_, hdec, hhp, hst⟩
        rw [hpre, h10_11, h16_34]
        split_res_fuel 1
        step_drop 1
        rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne80)]
        exact hret
    · have hne35 : (UInt32.ofBitVec ((bytes.get! 0).toBitVec.signExtend 32) == 35) = false :=
        signExtend_bne_u32 hb0 rfl (by decide)
      have hres : Algorithm.parseBlockHeader bytes = none := by
        simp [Algorithm.parseBlockHeader, hlim_eq, hlt3, hb0]
      rw [hres]
      rcases parseBlockHeader_retNone (f := 233) (pc := 17) (st_loc := 3) (stk := [])
          (locs := locs1) (jh := jh) (hp := hp) (by omega) rfl with
          ⟨v, st', hret, hdec, hhp, hst⟩
      refine ⟨v, st', ?_, hdec, hhp, hst⟩
      rw [hpre, h10_11]
      split_res_fuel 1
      step_drop 1
      rw [runJvmResFast_if_icmpeq_fallthrough (hne := hne35)]
      exact hret

end ParseBlockHeader

/-! #### 13. `f_Algorithm_serializeLife105_loop_prog` -/

section SerializeLife105Loop
set_option maxRecDepth 2048

private theorem runJvmResFast_l2i {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.l2i :: rest) ⟨pc0, .i64 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i32 v.toUInt32 :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .l2i ⟨pc, .i64 v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 v.toUInt32 :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_lushr_32 {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.lushr :: rest) ⟨pc0, .i32 32 :: .i64 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i64 (v >>> 32) :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .lushr ⟨pc, .i32 32 :: .i64 v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 (v >>> 32) :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_checkcast_pair {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {a b : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.checkcast "kotlin/Pair" :: rest)
        ⟨pc0, .pair a b :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .pair a b :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.checkcast "kotlin/Pair")
      ⟨pc, .pair a b :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .pair a b :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem stepStatic_growBufPush_str
    {pc : Nat} {s : String} {b : Algorithm.GrowBuf String} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .str s :: .ext (.strGrowBuf b) :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_GrowBuf_push___redArg"
      "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.strGrowBuf (b.push s)) :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_life105Bounds
    {pc : Nat} {maxY minY minX limit i : UInt32} {cId : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cells : Array UInt64}
    (hget : hp.u64Arrays[cId]? = some cells) :
    stepInvokeStatic ⟨pc, .i32 maxY :: .i32 minY :: .i32 minX :: .i32 limit :: .i32 i ::
        .ext (.u64Ref cId) :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_life105Bounds-lLpu_l0" "([JIIIII)Lkotlin/Pair;" =
      let b := Algorithm.life105Bounds cells i limit minX.toInt32 minY.toInt32 maxY.toInt32
      .inl (some ⟨pc + 1, .pair (.boxedInt b.1.toUInt32)
        (.pair (.boxedInt b.2.1.toUInt32) (.boxedInt b.2.2.toUInt32)) :: rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 maxY :: .i32 minY :: .i32 minX :: .i32 limit :: .i32 i ::
      .ext (.u64Ref cId) :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_life105Bounds-lLpu_l0" "([JIIIII)Lkotlin/Pair;" =
      match hp.u64Arrays[cId]? with
      | some cs =>
        let b := Algorithm.life105Bounds cs i limit minX.toInt32 minY.toInt32 maxY.toInt32
        .inl (some ⟨pc + 1, .pair (.boxedInt b.1.toUInt32)
          (.pair (.boxedInt b.2.1.toUInt32) (.boxedInt b.2.2.toUInt32)) :: rest, locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn, hget]

private theorem stepStatic_serializeLife105Block
    {pc : Nat} {maxY minY minX : UInt32} {cId : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cells : Array UInt64}
    (hget : hp.u64Arrays[cId]? = some cells) :
    stepInvokeStatic ⟨pc, .i32 maxY :: .i32 minY :: .i32 minX ::
        .ext (.u64Ref cId) :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_serializeLife105Block-WhflrNI"
      "([JIII)[Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .strArr (Algorithm.serializeLife105Block cells
        minX.toInt32 minY.toInt32 maxY.toInt32) :: rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .i32 maxY :: .i32 minY :: .i32 minX ::
      .ext (.u64Ref cId) :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_serializeLife105Block-WhflrNI"
      "([JIII)[Ljava/lang/Object;" =
      match hp.u64Arrays[cId]? with
      | some cs =>
        .inl (some ⟨pc + 1, .strArr (Algorithm.serializeLife105Block cs
          minX.toInt32 minY.toInt32 maxY.toInt32) :: rest, locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn, hget]

private theorem stepStatic_life105Rest
    {pc : Nat} {accId : Nat} {limit i minX : UInt32} {cId : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {cells acc : Array UInt64}
    (hc : hp.u64Arrays[cId]? = some cells) (ha : hp.u64Arrays[accId]? = some acc) :
    stepInvokeStatic ⟨pc, .ext (.u64Ref accId) :: .i32 limit :: .i32 i :: .i32 minX ::
        .ext (.u64Ref cId) :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_life105Rest-dlT0rtU" "([JIII[J)[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref hp.u64Arrays.length) :: rest, locs, jh,
        { hp with u64Arrays := hp.u64Arrays ++
          [Algorithm.life105Rest cells minX.toInt32 i limit acc] }⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .ext (.u64Ref accId) :: .i32 limit :: .i32 i :: .i32 minX ::
      .ext (.u64Ref cId) :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_life105Rest-dlT0rtU" "([JIII[J)[J" =
      match hp.u64Arrays[cId]?, hp.u64Arrays[accId]? with
      | some cs, some ac =>
        .inl (some ⟨pc + 1, .ext (.u64Ref hp.u64Arrays.length) :: rest, locs, jh,
          { hp with u64Arrays := hp.u64Arrays ++
            [Algorithm.life105Rest cs minX.toInt32 i limit ac] }⟩)
      | _, _ => .inr none := rfl
  rw [hfn, hc, ha]

private theorem serializeLife105_loop_drain (rem : Nat) :
    ∀ (fuel : UInt32) (cId : Nat) (cells : Array UInt64)
      (block : Array String) (j : UInt32) (acc : Algorithm.GrowBuf String)
      (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap),
      block.size.toUInt32.toNat - j.toNat = rem →
      block.size < 2 ^ 31 →
      locs 0 = .i32 fuel → locs 1 = .ext (.u64Ref cId) → locs 2 = .strArr block →
      locs 3 = .i32 j → locs 4 = .ext (.strGrowBuf acc) →
      ∃ j' acc' locs',
        ¬(j' < block.size.toUInt32) ∧
        Algorithm.serializeLife105.loop fuel cells block j acc =
          Algorithm.serializeLife105.loop fuel cells block j' acc' ∧
        locs' 0 = .i32 fuel ∧ locs' 1 = .ext (.u64Ref cId) ∧
        locs' 2 = .strArr block ∧ locs' 3 = .i32 j' ∧
        locs' 4 = .ext (.strGrowBuf acc') ∧
        ∀ f : Nat, 6 + 34 * rem ≤ f →
          runJvmResFast f f_Algorithm_serializeLife105_loop_prog 6
            (f_Algorithm_serializeLife105_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
          runJvmResFast (f - (6 + 34 * rem)) f_Algorithm_serializeLife105_loop_prog 12
            (f_Algorithm_serializeLife105_loop_prog.drop 12) ⟨12, [], locs', jh, hp⟩ := by
  induction rem with
  | zero =>
    intro fuel cId cells block j acc locs jh hp hrem hblk31 hl0 hl1 hl2 hl3 hl4
    have hj_nlt : ¬(j < block.size.toUInt32) := by
      intro hlt
      have h1 := UInt32.lt_iff_toNat_lt.mp hlt
      omega
    have hblk_u32 : UInt32.ofNat block.size = block.size.toUInt32 := rfl
    refine ⟨j, acc, locs, hj_nlt, rfl, hl0, hl1, hl2, hl3, hl4, ?_⟩
    intro f hf
    rw [show f = (f - 6) + 6 by omega]
    split_res_fuel 6
    step_drop 6
    rw [runJvmResFast_iload, hl3]; norm_res_fuel
    rw [runJvmResFast_aload, hl2]; norm_res_fuel
    rw [runJvmResFast_arraylength_strArr, hblk_u32]; norm_res_fuel
    rw [runJvmResFast_uintCtor]; norm_res_fuel
    rw [runJvmResFast_compareUnsigned]; norm_res_fuel
    rw [runJvmResFast_iflt_fallthrough (by
      change (if j == block.size.toUInt32 then (0 : UInt32)
        else if j < block.size.toUInt32 then 4294967295 else 1).toBitVec.slt 0#32 = false
      rw [compareUnsigned_slt_zero]; exact decide_eq_false hj_nlt)]
  | succ rem ih =>
    intro fuel cId cells block j acc locs jh hp hrem hblk31 hl0 hl1 hl2 hl3 hl4
    have hblk_toNat : block.size.toUInt32.toNat = block.size := by
      change block.size % 2 ^ 32 = block.size; omega
    have hj_lt : j < block.size.toUInt32 :=
      UInt32.lt_iff_toNat_lt.mpr (by omega)
    have hj_nat : j.toNat < block.size := by
      have := UInt32.lt_iff_toNat_lt.mp hj_lt
      omega
    have hj_slt : j.toBitVec.slt 0#32 = false :=
      u32_slt_zero_of_lt hj_lt (by omega)
    have hjp1_toNat : (j + 1).toNat = j.toNat + 1 := by
      have : j.toNat + 1 < 2 ^ 32 := by omega
      change (j.toNat + 1 % 2 ^ 32) % 2 ^ 32 = j.toNat + 1
      omega
    let locs1 : Nat → JvmVal :=
      setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal (setLocal (setLocal (setLocal locs
          5 (.i32 (j + 1)))
          6 (.ext (.strGrowBuf (acc.push block[j.toNat]!))))
          7 (.i32 fuel))
          8 (.ext (.u64Ref cId)))
          9 (.strArr block))
          0 (.i32 fuel))
          1 (.ext (.u64Ref cId)))
          2 (.strArr block))
          3 (.i32 (j + 1)))
          4 (.ext (.strGrowBuf (acc.push block[j.toNat]!)))
    have hstep34 : ∃ locs1,
        locs1 0 = .i32 fuel ∧ locs1 1 = .ext (.u64Ref cId) ∧
        locs1 2 = .strArr block ∧ locs1 3 = .i32 (j + 1) ∧
        locs1 4 = .ext (.strGrowBuf (acc.push block[j.toNat]!)) ∧
        ∀ f : Nat, 34 ≤ f →
          runJvmResFast f f_Algorithm_serializeLife105_loop_prog 6
            (f_Algorithm_serializeLife105_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
          runJvmResFast (f - 34) f_Algorithm_serializeLife105_loop_prog 6
            (f_Algorithm_serializeLife105_loop_prog.drop 6) ⟨6, [], locs1, jh, hp⟩ := by
      refine ⟨locs1, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [locs1]; repeat rw [setLocal_ne (by decide)]
        rw [setLocal_self]
      · dsimp only [locs1]; repeat rw [setLocal_ne (by decide)]
        rw [setLocal_self]
      · dsimp only [locs1]; repeat rw [setLocal_ne (by decide)]
        rw [setLocal_self]
      · dsimp only [locs1]; rw [setLocal_ne (by decide), setLocal_self]
      · dsimp only [locs1]; rw [setLocal_self]
      · intro f hf
        rw [show f = (f - 34) + 34 by omega]
        split_res_fuel 6
        step_drop 6
        rw [runJvmResFast_iload, hl3]; norm_res_fuel
        rw [runJvmResFast_aload, hl2]; norm_res_fuel
        rw [runJvmResFast_arraylength_strArr]; norm_res_fuel
        rw [runJvmResFast_uintCtor]; norm_res_fuel
        rw [runJvmResFast_compareUnsigned]; norm_res_fuel
        rw [runJvmResFast_iflt_branch (by
          change (if j == UInt32.ofNat block.size then (0 : UInt32)
            else if j < UInt32.ofNat block.size then 4294967295 else 1).toBitVec.slt 0#32 = true
          rw [compareUnsigned_slt_zero]; exact decide_eq_true hj_lt)]
        rw [show f - 34 + 34 - 6 = (f - 34) + 28 by omega]
        split_res_fuel 28
        step_drop 28
        rw [runJvmResFast_iload, hl3]; norm_res_fuel
        rw [runJvmResFast_iconst]; norm_res_fuel
        rw [runJvmResFast_iadd]; norm_res_fuel
        rw [runJvmResFast_uintCtor]; norm_res_fuel
        rw [runJvmResFast_istore]; norm_res_fuel
        rw [runJvmResFast_aload, setLocal_ne (by decide), hl4]; norm_res_fuel
        rw [runJvmResFast_aload, setLocal_ne (by decide), hl2]; norm_res_fuel
        rw [runJvmResFast_iload, setLocal_ne (by decide), hl3]; norm_res_fuel
        rw [runJvmResFast_aaload_strArr (hlt := hj_nat) (hslt := hj_slt)]; norm_res_fuel
        rw [runJvmResFast_invokestatic_step (hs := stepStatic_growBufPush_str)]; norm_res_fuel
        rw [runJvmResFast_astore]; norm_res_fuel
        rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide), hl0]; norm_res_fuel
        rw [runJvmResFast_istore]; norm_res_fuel
        rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
          setLocal_ne (by decide), hl1]; norm_res_fuel
        rw [runJvmResFast_astore]; norm_res_fuel
        rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
          setLocal_ne (by decide), setLocal_ne (by decide), hl2]; norm_res_fuel
        rw [runJvmResFast_astore]; norm_res_fuel
        rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide),
          setLocal_self]; norm_res_fuel
        rw [runJvmResFast_istore]; norm_res_fuel
        rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
          setLocal_self]; norm_res_fuel
        rw [runJvmResFast_astore]; norm_res_fuel
        rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
          setLocal_self]; norm_res_fuel
        rw [runJvmResFast_astore]; norm_res_fuel
        rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide),
          setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
          setLocal_ne (by decide), setLocal_ne (by decide), setLocal_self]; norm_res_fuel
        rw [runJvmResFast_istore]; norm_res_fuel
        rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
          setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
          setLocal_ne (by decide), setLocal_ne (by decide), setLocal_self]; norm_res_fuel
        rw [runJvmResFast_astore]; norm_res_fuel
        rw [show (97 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
            1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 : Nat) = 124 from rfl,
          show f - 34 + 28 - 28 + 1 = (f - 34) + 1 by omega,
          show f - 34 + 34 - 34 = f - 34 by omega]
        rw [runJvmResFast_goto]
        dsimp only [locs1]
        simp only [getElem!_pos block j.toNat hj_nat]
    rcases hstep34 with ⟨locs1, h10, h11, h12, h13, h14, h34⟩
    rcases ih fuel cId cells block (j + 1) (acc.push block[j.toNat]!) locs1 jh hp
        (by omega) hblk31 h10 h11 h12 h13 h14 with
      ⟨j', acc', locs', hj', hloop', h0', h1', h2', h3', h4', hrec⟩
    refine ⟨j', acc', locs', hj', ?_, h0', h1', h2', h3', h4', ?_⟩
    · rw [Algorithm.serializeLife105.loop]
      simp only [hj_lt, ↓reduceDIte]
      exact hloop'
    · intro f hf
      rw [h34 f (by omega), hrec (f - 34) (by omega),
        show f - 34 - (6 + 34 * rem) = f - (6 + 34 * (rem + 1)) by omega]

private theorem serializeLife105_loop_from6 (fuelN : Nat) :
    ∀ (fuel : UInt32) (cId : Nat) (cells : Array UInt64)
      (block : Array String) (j : UInt32) (acc : Algorithm.GrowBuf String)
      (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap),
      fuel.toNat = fuelN →
      block.size < 2 ^ 31 →
      (∀ cs minX minY maxY, (Algorithm.serializeLife105Block cs minX minY maxY).size < 2 ^ 31) →
      locs 0 = .i32 fuel → locs 1 = .ext (.u64Ref cId) → locs 2 = .strArr block →
      locs 3 = .i32 j → locs 4 = .ext (.strGrowBuf acc) →
      hp.u64Arrays[cId]? = some cells →
      ∃ f st',
        runJvmResFast f f_Algorithm_serializeLife105_loop_prog 6
          (f_Algorithm_serializeLife105_loop_prog.drop 6) ⟨6, [], locs, jh, hp⟩ =
          some (.ext (.strGrowBuf (Algorithm.serializeLife105.loop fuel cells block j acc)), st') ∧
        st'.jvmHeap = jh ∧ st'.heap.arenas = hp.arenas ∧
        st'.heap.asciiArrays = hp.asciiArrays := by
  induction fuelN with
  | zero =>
    intro fuel cId cells block j acc locs jh hp hfuelN hblk31 hblocks31 hl0 hl1 hl2 hl3 hl4 hcells
    have hfuel0 : fuel = 0 :=
      UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by exact hfuelN))
    let rem := block.size.toUInt32.toNat - j.toNat
    rcases serializeLife105_loop_drain rem fuel cId cells block j acc
        locs jh hp rfl hblk31 hl0 hl1 hl2 hl3 hl4 with
      ⟨j', acc', locs', hj', hloop', h0', _, _, _, h4', hdrain⟩
    have hloop_eq : Algorithm.serializeLife105.loop fuel cells block j acc = acc' := by
      rw [hloop', Algorithm.serializeLife105.loop]
      simp [hj', hfuel0]
    rw [hloop_eq]
    refine ⟨6 + 34 * rem + 4, ⟨96, [.ext (.strGrowBuf acc')], locs', jh, hp⟩, ?_, rfl, rfl, rfl⟩
    rw [hdrain _ (by omega), show 6 + 34 * rem + 4 - (6 + 34 * rem) = 4 by omega]
    split_res_fuel 4
    step_drop 2
    rw [runJvmResFast_iload, h0']; norm_res_fuel
    rw [runJvmResFast_ifeq_branch (hv := by rw [hfuel0])]; norm_res_fuel
    step_drop 2
    rw [runJvmResFast_aload, h4']; norm_res_fuel
    exact runJvmResFast_areturn_step
  | succ fuelN' ih =>
    intro fuel cId cells block j acc locs jh hp hfuelN hblk31 hblocks31 hl0 hl1 hl2 hl3 hl4 hcells
    have hfuel_ne : fuel ≠ 0 := by
      intro h0
      rw [h0] at hfuelN
      simp at hfuelN
    let rem := block.size.toUInt32.toNat - j.toNat
    rcases serializeLife105_loop_drain rem fuel cId cells block j acc
        locs jh hp rfl hblk31 hl0 hl1 hl2 hl3 hl4 with
      ⟨j', acc', locs', hj', hloop', h0', h1', _, _, h4', hdrain⟩
    by_cases hcells0 : cells.size.toUInt32 == 0
    · have hloop_eq : Algorithm.serializeLife105.loop fuel cells block j acc = acc' := by
        rw [hloop', Algorithm.serializeLife105.loop]
        simp [hj', hfuel_ne, hcells0]
      rw [hloop_eq]
      let locs'' := setLocal locs' 5 (.i32 cells.size.toUInt32)
      refine ⟨6 + 34 * rem + 10, ⟨94, [.ext (.strGrowBuf acc')], locs'', jh, hp⟩,
        ?_, rfl, rfl, rfl⟩
      rw [hdrain _ (by omega), show 6 + 34 * rem + 10 - (6 + 34 * rem) = 10 by omega]
      split_res_fuel 8
      step_drop 2
      rw [runJvmResFast_iload, h0']; norm_res_fuel
      rw [runJvmResFast_ifeq_fallthrough (h := beq_false_of_ne hfuel_ne)]; norm_res_fuel
      step_drop 6
      rw [runJvmResFast_aload, h1']; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_ulongArrGetSize_heap hcells)]
      norm_res_fuel
      rw [runJvmResFast_uintCtor]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_ifeq_branch (hv := beq_iff_eq.mp hcells0)]; norm_res_fuel
      step_drop 2
      rw [runJvmResFast_aload, setLocal_ne (by decide), h4']; norm_res_fuel
      exact runJvmResFast_areturn_step
    · have hcells_pos : 0 < cells.size := by
        cases hsz : cells.size with
        | zero => simp [hsz] at hcells0
        | succ _ => omega
      let kCell := cells[0]!
      let y := (Algorithm.cellKeyY kCell).toInt32
      let b := Algorithm.life105Bounds cells 1 cells.size.toUInt32
        (Algorithm.cellKeyX kCell).toInt32 y y
      let minX := b.1
      let block' := Algorithm.serializeLife105Block cells minX b.2.1 b.2.2
      let restBuf := Algorithm.life105Rest cells minX 0 cells.size.toUInt32 Algorithm.U64Buf.empty
      let rest := Algorithm.U64Buf.toArray restBuf
      have hfm1_toNat : (fuel - 1).toNat = fuelN' := by
        have h1le : (1 : UInt32) ≤ fuel :=
          UInt32.le_iff_toNat_le.mpr (by change 1 ≤ fuel.toNat; omega)
        rw [UInt32.toNat_sub_of_le _ _ h1le]
        change fuel.toNat - 1 = fuelN'
        omega
      let hp1 : AlgHeap := { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }
      let hp2 : AlgHeap := { hp1 with u64Arrays := hp1.u64Arrays ++ [restBuf] }
      let hp3 : AlgHeap := { hp2 with u64Arrays := hp2.u64Arrays ++ [rest] }
      have hcId_lt : cId < hp.u64Arrays.length :=
        Nat.lt_of_not_ge fun hge => by
          have : hp.u64Arrays[cId]? = none := List.getElem?_eq_none hge
          rw [hcells] at this; cases this
      have hc1 : hp1.u64Arrays[cId]? = some cells := by
        dsimp only [hp1]; rw [List.getElem?_append_left hcId_lt]; exact hcells
      have hc2 : hp2.u64Arrays[cId]? = some cells := by
        have hc1_lt : cId < hp1.u64Arrays.length := by dsimp only [hp1]; simp; omega
        dsimp only [hp2]; rw [List.getElem?_append_left hc1_lt]; exact hc1
      have hbuf_empty : hp1.u64Arrays[hp.u64Arrays.length]? = some Algorithm.U64Buf.empty := by
        dsimp only [hp1]; simp
      have hbuf_rest : hp2.u64Arrays[hp1.u64Arrays.length]? = some restBuf := by
        dsimp only [hp2]; simp
      have hrest_get : hp3.u64Arrays[hp2.u64Arrays.length]? = some rest := by
        dsimp only [hp3]; simp
      let locsNext : Nat → JvmVal :=
        setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
          (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
            (setLocal (setLocal locs'
              5 (.i32 cells.size.toUInt32))
              6 (.i64 kCell))
              8 (.i32 kCell.toUInt32))
              9 (.pair (.boxedInt b.1.toUInt32)
                (.pair (.boxedInt b.2.1.toUInt32) (.boxedInt b.2.2.toUInt32))))
              10 (.pair (.boxedInt b.2.1.toUInt32) (.boxedInt b.2.2.toUInt32)))
              11 (.i32 b.1.toUInt32))
              12 (.strArr block'))
              13 (.ext (.u64Ref hp.u64Arrays.length)))
              14 (.ext (.u64Ref hp1.u64Arrays.length)))
              15 (.ext (.u64Ref hp2.u64Arrays.length)))
              16 (.i32 (fuel - 1)))
              17 (.ext (.strGrowBuf acc')))
              0 (.i32 (fuel - 1)))
              1 (.ext (.u64Ref hp2.u64Arrays.length)))
              2 (.strArr block'))
              3 (.i32 0))
              4 (.ext (.strGrowBuf acc'))
      have hln0 : locsNext 0 = .i32 (fuel - 1) := by
        dsimp only [locsNext]
        repeat rw [setLocal_ne (by decide)]
        rw [setLocal_self]
      have hln1 : locsNext 1 = .ext (.u64Ref hp2.u64Arrays.length) := by
        dsimp only [locsNext]
        repeat rw [setLocal_ne (by decide)]
        rw [setLocal_self]
      have hln2 : locsNext 2 = .strArr block' := by
        dsimp only [locsNext]
        repeat rw [setLocal_ne (by decide)]
        rw [setLocal_self]
      have hln3 : locsNext 3 = .i32 0 := by
        dsimp only [locsNext]; rw [setLocal_ne (by decide), setLocal_self]
      have hln4 : locsNext 4 = .ext (.strGrowBuf acc') := by
        dsimp only [locsNext]; rw [setLocal_self]
      rcases ih (fuel - 1) hp2.u64Arrays.length rest block' 0 acc' locsNext jh hp3
          hfm1_toNat (hblocks31 cells minX b.2.1 b.2.2) hblocks31 hln0 hln1 hln2 hln3 hln4
          hrest_get with
        ⟨fRec, st', hrec, hjh', har', hasc'⟩
      have hloop_eq : Algorithm.serializeLife105.loop fuel cells block j acc =
          Algorithm.serializeLife105.loop (fuel - 1) rest block' 0 acc' := by
        rw [hloop', Algorithm.serializeLife105.loop]
        simp only [hj', hfuel_ne, hcells0, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]
        rfl
      rw [hloop_eq]
      refine ⟨6 + 34 * rem + (81 + fRec), st', ?_, hjh', har', hasc'⟩
      rw [hdrain _ (by omega), show 6 + 34 * rem + (81 + fRec) - (6 + 34 * rem) = fRec + 81 by omega]
      split_res_fuel 8
      step_drop 2
      rw [runJvmResFast_iload, h0']; norm_res_fuel
      rw [runJvmResFast_ifeq_fallthrough (h := beq_false_of_ne hfuel_ne)]; norm_res_fuel
      step_drop 6
      rw [runJvmResFast_aload, h1']; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_ulongArrGetSize_heap hcells)]
      norm_res_fuel
      rw [runJvmResFast_uintCtor]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_ifeq_fallthrough (h := Bool.eq_false_of_ne_true hcells0)]
      rw [show fRec + 81 - 8 = fRec + 73 by omega]
      split_res_fuel 22
      step_drop 22
      rw [runJvmResFast_aload, setLocal_ne (by decide), h1']; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_ulongArrGetU64_heap hcells)]
      rw [show (Jvm.JvmVal.i32 0).asI32.toNat = 0 from rfl]
      norm_res_fuel
      rw [runJvmResFast_lstore]; norm_res_fuel
      rw [runJvmResFast_lload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_l2i]; norm_res_fuel
      rw [runJvmResFast_uintCtor]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
        setLocal_ne (by decide), h1']; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide),
        setLocal_self]; norm_res_fuel
      rw [runJvmResFast_nop]; norm_res_fuel
      rw [runJvmResFast_lload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_lushr_32]; norm_res_fuel
      rw [runJvmResFast_ulongCtor]; norm_res_fuel
      rw [runJvmResFast_l2i]; norm_res_fuel
      rw [runJvmResFast_uintCtor]; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_life105Bounds hcells)]
      rw [show (kCell >>> 32).toUInt32 = Algorithm.cellKeyX kCell from rfl,
        show kCell.toUInt32.toInt32 = y from rfl]
      norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      split_res_fuel 21
      step_drop 21
      rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_invokevirtual_step (hs := stepVirtual_pairGetSecond)]; norm_res_fuel
      rw [runJvmResFast_checkcast_pair]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_invokevirtual_step (hs := stepVirtual_pair_getFirst)]; norm_res_fuel
      rw [runJvmResFast_checkcast_boxedInt (hcls := Or.inr (Or.inl rfl))]; norm_res_fuel
      rw [runJvmResFast_invokevirtual_step (hs := stepVirtual_number_intValue)]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
        setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
        setLocal_ne (by decide), h1']; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_invokevirtual_step (hs := stepVirtual_pair_getFirst)]; norm_res_fuel
      rw [runJvmResFast_checkcast_boxedInt (hcls := Or.inr (Or.inl rfl))]; norm_res_fuel
      rw [runJvmResFast_invokevirtual_step (hs := stepVirtual_number_intValue)]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_invokevirtual_step (hs := stepVirtual_pairGetSecond)]; norm_res_fuel
      rw [runJvmResFast_checkcast_boxedInt (hcls := Or.inr (Or.inl rfl))]; norm_res_fuel
      rw [runJvmResFast_invokevirtual_step (hs := stepVirtual_number_intValue)]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_serializeLife105Block hcells)]
      rw [Int32.toInt32_toUInt32 b.1, Int32.toInt32_toUInt32 b.2.1, Int32.toInt32_toUInt32 b.2.2]
      norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      split_res_fuel 30
      step_drop 30
      rw [runJvmResFast_invokestatic_step
        (hs := stepStatic_u64BufEmpty_heap (hcls := Or.inl rfl))]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_aload]
      repeat rw [setLocal_ne (by decide)]
      rw [h1']; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide),
        setLocal_self]; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide),
        setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
        setLocal_ne (by decide), setLocal_ne (by decide), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
      have hhp1 :
          AlgHeap.mk hp.arenas (hp.u64Arrays ++ [Algorithm.U64Buf.empty]) hp.asciiArrays = hp1 :=
        rfl
      rw [hhp1]
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_life105Rest hc1 hbuf_empty)]
      rw [Int32.toInt32_toUInt32 b.1]
      have hhp2 :
          AlgHeap.mk hp1.arenas
            (hp1.u64Arrays ++
              [Algorithm.life105Rest cells minX 0 cells.size.toUInt32 Algorithm.U64Buf.empty])
            hp1.asciiArrays = hp2 := rfl
      rw [hhp2]
      norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step
        (hs := stepStatic_u64BufToArray_heap hbuf_rest (hcls := Or.inl rfl))]
      have hhp3 :
          AlgHeap.mk hp2.arenas (hp2.u64Arrays ++ [rest]) hp2.asciiArrays = hp3 := rfl
      rw [hhp3]
      norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_iload]
      repeat rw [setLocal_ne (by decide)]
      rw [h0']; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_isub]; norm_res_fuel
      rw [runJvmResFast_uintCtor]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload]
      repeat rw [setLocal_ne (by decide)]
      rw [h4']; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
        setLocal_ne (by decide), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
        setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
        setLocal_ne (by decide), setLocal_ne (by decide), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
        setLocal_ne (by decide), setLocal_ne (by decide), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [show fRec + 73 - 22 - 21 - 30 + 1 = fRec + 1 by omega]
      rw [runJvmResFast_goto]
      dsimp only [locsNext]
      exact hrec

theorem serializeLife105_loop_equiv
    (fuel : UInt32) (cells : Array UInt64) (block : Array String) (j : UInt32)
    (acc : Algorithm.GrowBuf String) (cId : Nat)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hl0 : locs 0 = .i32 fuel) (hl1 : locs 1 = .ext (.u64Ref cId))
    (hl2 : locs 2 = .strArr block) (hl3 : locs 3 = .i32 j) (hl4 : locs 4 = .ext (.strGrowBuf acc))
    (hcells : hp.u64Arrays[cId]? = some cells)
    (hblk31 : block.size < 2 ^ 31)
    (hblocks31 : ∀ cs minX minY maxY, (Algorithm.serializeLife105Block cs minX minY maxY).size < 2 ^ 31) :
    ∃ f st',
      runJvmRes f f_Algorithm_serializeLife105_loop_prog ⟨0, [], locs, jh, hp⟩ =
        some (.ext (.strGrowBuf (Algorithm.serializeLife105.loop fuel cells block j acc)), st') ∧
      st'.jvmHeap = jh ∧ st'.heap.arenas = hp.arenas ∧
      st'.heap.asciiArrays = hp.asciiArrays := by
  rcases serializeLife105_loop_from6 fuel.toNat fuel cId cells block j acc locs jh hp
      rfl hblk31 hblocks31 hl0 hl1 hl2 hl3 hl4 hcells with
    ⟨f6, st', h6, hjh', har', hasc'⟩
  refine ⟨6 + f6, st', ?_, hjh', har', hasc'⟩
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  split_res_fuel 6
  conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_serializeLife105_loop_prog)]
  step_drop 6
  rw [runJvmResFast_aload, hl1]; norm_res_fuel
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step
    (hs := stepStatic_checkNotNullParameter_heap rfl)]; norm_res_fuel
  rw [runJvmResFast_aload, hl2]; norm_res_fuel
  rw [runJvmResFast_ldcStr]; norm_res_fuel
  rw [runJvmResFast_invokestatic_step
    (hs := stepStatic_checkNotNullParameter_heap rfl)]; norm_res_fuel
  rw [show (0 + 1 + 1 + 1 + 1 + 1 + 1 : Nat) = 6 from rfl, show 6 + f6 - 6 = f6 by omega]
  exact h6

end SerializeLife105Loop

section ParseBlocks
set_option maxRecDepth 2048

private theorem runJvmResFast_ifge_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : (0#32).sle v.toBitVec = true) :
    runJvmResFast (f + 1) prog pc (.ifge tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, hv]

private theorem runJvmResFast_ifge_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : (0#32).sle v.toBitVec = false) :
    runJvmResFast (f + 1) prog pc (.ifge tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, hv]

private theorem runJvmResFast_ifgt_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : (0#32 : BitVec 32).slt v.toBitVec = true) :
    runJvmResFast (f + 1) prog pc (.ifgt tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, hv]

private theorem runJvmResFast_ifgt_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : (0#32 : BitVec 32).slt v.toBitVec = false) :
    runJvmResFast (f + 1) prog pc (.ifgt tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp [runJvmResFast, Jvm.JvmVal.asI32, hv]

private theorem runJvmResFast_newClass {f pc pc0 : Nat} {prog rest : List JvmInstr} {cls : String}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hstep : Jvm.stepInstr algHooks (.newClass cls) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩)) :
    runJvmResFast (f + 1) prog pc (.newClass cls :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩ := by
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_lconst {f pc pc0 : Nat} {prog rest : List JvmInstr} {c : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.lconst c :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i64 c :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks (.lconst c) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 c :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_land {f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.land :: rest) ⟨pc0, .i64 b :: .i64 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i64 (a &&& b) :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .land ⟨pc, .i64 b :: .i64 a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 (a &&& b) :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_lshl_32 {f pc pc0 : Nat} {prog rest : List JvmInstr} {a : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.lshl :: rest)
        ⟨pc0, .i32 32 :: .i64 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i64 (a <<< 32) :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .lshl ⟨pc, .i32 32 :: .i64 a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 (a <<< 32) :: stk, locs, jh, hp⟩) := by
    simp [Jvm.stepInstr, Jvm.JvmVal.asI64, Jvm.JvmVal.asI32]
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_ladd {f pc pc0 : Nat} {prog rest : List JvmInstr} {a b : UInt64}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.ladd :: rest) ⟨pc0, .i64 b :: .i64 a :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .i64 (a + b) :: stk, locs, jh, hp⟩ := by
  have hstep : Jvm.stepInstr algHooks .ladd ⟨pc, .i64 b :: .i64 a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i64 (a + b) :: stk, locs, jh, hp⟩) := rfl
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  simp only [stepInstr, hstep, ↓reduceIte]

private theorem runJvmResFast_i2l_mask {f pc pc0 : Nat} {prog rest : List JvmInstr} {v : UInt32}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 3) prog pc (.i2l :: .lconst 4294967295 :: .land :: rest)
        ⟨pc0, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 3) rest ⟨pc + 3, .i64 v.toUInt64 :: stk, locs, jh, hp⟩ := by
  conv => lhs; dsimp only [runJvmResFast]; rw [Jvm.runJvmResFast.eq_def]
  simp only [runJvmResFast]

private theorem stepSpecial_life105UnexpectedInput_init
    {pc : Nat} {marker col lineNum input : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, marker :: col :: lineNum :: input ::
        .allocRef "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput" ::
        .allocRef "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput" :: rest,
        locs, jh, hp⟩
      "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput" "<init>"
      "(Ljava/lang/String;IILkotlin/jvm/internal/DefaultConstructorMarker;)V" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.instance "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput"
          [("input", input), ("lineIndex", lineNum), ("columnIndex", col)])).2, hp⟩) := rfl

private theorem stepStatic_isRowLine_heap
    {pc addr : Nat} {elems : Array UInt8} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_isRowLine" "([B)Z" =
      .inl (some ⟨pc + 1, .i32 (if Algorithm.isRowLine ⟨elems⟩ then 1 else 0) :: rest,
        locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_isRowLine" "([B)Z" =
      match decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) with
      | some bytes =>
        .inl (some ⟨pc + 1, .i32 (if Algorithm.isRowLine bytes then 1 else 0) :: rest,
          locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn]
  have hd : decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) =
      some ⟨elems⟩ := by
    simp [decodeBytes, hget]
  rw [hd]

private theorem stepStatic_parseBlockHeader_none_heap
    {pc addr : Nat} {elems : Array UInt8} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.byteArray elems))
    (hbh : Algorithm.parseBlockHeader ⟨elems⟩ = none) :
    stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_parseBlockHeader" "([B)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_parseBlockHeader" "([B)Ljava/lang/Object;" =
      match decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) with
      | some bytes =>
        let optPair := (Algorithm.parseBlockHeader bytes).map fun r =>
          (.boxedInt r.x.toUInt32, .boxedInt r.y.toUInt32)
        let (res, h') := encodeOptScalarPair jh optPair
        .inl (some ⟨pc + 1, res :: rest, locs, h', hp⟩)
      | none => .inr none := rfl
  rw [hfn]
  have hd : decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) =
      some ⟨elems⟩ := by
    simp [decodeBytes, hget]
  rw [hd]; dsimp only; rw [hbh]
  simp only [Option.map, encodeOptScalarPair, Jvm.JvmHeap.alloc]

private theorem stepStatic_parseBlockHeader_some_heap
    {pc addr : Nat} {elems : Array UInt8} {c : Algorithm.ParsedCoords} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.byteArray elems))
    (hbh : Algorithm.parseBlockHeader ⟨elems⟩ = some c) :
    let h1 := (jh.alloc (.objArray "java/lang/Object"
      #[.boxedInt 0, .boxedInt c.x.toUInt32, .null, .null, .null, .boxedInt c.y.toUInt32])).2
    let h2 := (h1.alloc (.objArray "java/lang/Object"
      #[.boxedInt 1, .heapRef jh.objects.size])).2
    stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_parseBlockHeader" "([B)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .heapRef (jh.objects.size + 1) :: rest, locs, h2, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_parseBlockHeader" "([B)Ljava/lang/Object;" =
      match decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) with
      | some bytes =>
        let optPair := (Algorithm.parseBlockHeader bytes).map fun r =>
          (.boxedInt r.x.toUInt32, .boxedInt r.y.toUInt32)
        let (res, h') := encodeOptScalarPair jh optPair
        .inl (some ⟨pc + 1, res :: rest, locs, h', hp⟩)
      | none => .inr none := rfl
  rw [hfn]
  have hd : decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) =
      some ⟨elems⟩ := by
    simp [decodeBytes, hget]
  rw [hd]; dsimp only; rw [hbh]
  simp [Option.map, encodeOptScalarPair, Jvm.JvmHeap.alloc]

private theorem cellKey_jvm_eq (blockX blockY rowIndex : Int32) (p : UInt32) :
    (((blockX.toUInt32 + p).toUInt64 <<< 32) +
      (((blockY.toUInt32 + rowIndex.toUInt32).toUInt64) &&& 4294967295)) =
      Algorithm.cellBits (blockX + p.toInt32, blockY + rowIndex) := by
  simp only [Algorithm.cellBits, Algorithm.cellKey]
  have hx : blockX.toUInt32 + p = (blockX + p.toInt32).toUInt32 := by
    apply UInt32.eq_of_toBitVec_eq
    simp [Int32.toBitVec_toUInt32, UInt32.toBitVec_add]
  have hy : blockY.toUInt32 + rowIndex.toUInt32 = (blockY + rowIndex).toUInt32 := by
    apply UInt32.eq_of_toBitVec_eq
    simp [Int32.toBitVec_toUInt32, UInt32.toBitVec_add]
  rw [hx, hy]

private theorem compareUnsigned_iflt_cond (a b : UInt32) :
    ((if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32) =
      decide (a < b) := by
  by_cases heq : a = b
  · subst heq; simp
  · by_cases hlt : a < b
    · simp [heq, hlt]
    · have hne : (a == b) = false := beq_false_of_ne heq
      simp [hne, hlt]

private theorem compareUnsigned_ifgt_cond (a b : UInt32) :
    ((0#32 : BitVec 32).slt
      (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec) =
      decide (b < a) := by
  by_cases heq : a = b
  · subst heq; simp
  · by_cases hlt : a < b
    · have hnab : ¬ b < a := fun h => absurd (UInt32.lt_trans hlt h) (UInt32.lt_irrefl a)
      simp [heq, hlt, hnab]
    · have hne : (a == b) = false := beq_false_of_ne heq
      have hba : b < a := by
        have h1 : b.toNat ≤ a.toNat := Nat.le_of_not_lt (fun h => hlt (UInt32.lt_iff_toNat_lt.mpr h))
        have h2 : a.toNat ≠ b.toNat := fun h => heq (UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))
        exact UInt32.lt_iff_toNat_lt.mpr (Nat.lt_of_le_of_ne h1 (Ne.symm h2))
      simp [hne, hlt, hba]

private theorem compareUnsigned_sle_cond (a b : UInt32) :
    ((0#32 : BitVec 32).sle
      (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec) =
      decide (¬ a < b) := by
  by_cases heq : a = b
  · subst heq; simp
  · by_cases hlt : a < b
    · simp [heq, hlt]
    · have hne : (a == b) = false := beq_false_of_ne heq
      simp [hne, hlt]

private theorem stepStatic_intCompareUnsigned_i32
    {pc : Nat} {a b : UInt32} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 b :: .i32 a :: rest, locs, jh, hp⟩
      "java/lang/Integer" "compareUnsigned" "(II)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: rest,
        locs, jh, hp⟩) := rfl

private theorem parseBlocks_exit_ok
    (wAddr cId : Nat) (wCls : String) (wElems : Array JvmVal)
    (warns : Array Algorithm.Life105Warning) (cells : Algorithm.U64Buf)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = [])
    (hwget : jh.get? wAddr = some (.objArray wCls wElems))
    (hwfold : wElems.foldlM (fun acc v => (decodeLife105Warning jh v).map acc.push) #[] =
      some warns)
    (hcget : hp.u64Arrays[cId]? = some cells)
    (hl11 : locs 11 = .heapRef wAddr) (hl12 : locs 12 = .ext (.u64Ref cId)) :
    ∃ v st',
      runJvmResFast 14 f_Algorithm_parseBlocks_prog 24
          (f_Algorithm_parseBlocks_prog.drop 24) ⟨24, [], locs, jh, hp⟩ =
        some (v, st') ∧
      decodeLife105Result st' v = some ⟨.ok, warns, Algorithm.U64Buf.toArray cells⟩ ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.heap.arenas = hp.arenas ∧ st'.heap.asciiArrays = hp.asciiArrays := by
  rcases hp with ⟨ar, u64, asc⟩
  let rObj : Jvm.HeapObj AlgExt := .instance "com/alexvanyo/composelife/model/Life105Result"
    [("status", .allocRef "com/alexvanyo/composelife/model/Life105Status$Ok"),
     ("warnings", .heapRef wAddr), ("cells", .ext (.u64Ref u64.length))]
  let jh' := (jh.alloc rObj).2
  let hp' : AlgHeap := ⟨ar, u64 ++ [Algorithm.U64Buf.toArray cells], asc⟩
  let locs' := setLocal (setLocal locs 15 (.allocRef "com/alexvanyo/composelife/model/Life105Status$Ok"))
    16 (.ext (.u64Ref u64.length))
  refine ⟨.heapRef jh.objects.size, ⟨37, [.heapRef jh.objects.size], locs', jh', hp'⟩,
      ?_, ?_, heapExtends_alloc jh rObj, rfl, rfl⟩
  · step_drop 14
    rw [runJvmResFast_getstatic_step (hstat := hstat) (hres := rfl)]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), hl12]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step
      (hs := stepStatic_u64BufToArray_heap hcget (hcls := Or.inl rfl))]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_newClass (hstep := rfl)]; norm_res_fuel
    rw [runJvmResFast_dup]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide), hl11]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_invokespecial_step (hs := stepSpecial_life105Result_init)]; norm_res_fuel
    exact runJvmResFast_areturn_step
  · have hres_get : jh'.get? jh.objects.size = some rObj := by
      simp [jh', Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    have hext : HeapExtends jh jh' := heapExtends_alloc jh rObj
    have hwget' : jh'.get? wAddr = some (.objArray wCls wElems) := hext wAddr _ hwget
    have hwfold' := foldlM_decodeLife105Warning_mono hext wElems #[] warns hwfold
    dsimp only [decodeLife105Result]
    rw [hres_get]
    dsimp only [rObj]
    simp [List.lookup, decodeLife105Status, hwget', hwfold', hp']

private theorem parseBlocks_header_none
    (line : String) (i : UInt32) (wAddr : Nat) (wCls : String) (wElems : Array JvmVal)
    (warns : Array Algorithm.Life105Warning)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hwget : jh.get? wAddr = some (.objArray wCls wElems))
    (hwfold : wElems.foldlM (fun acc v => (decodeLife105Warning jh v).map acc.push) #[] =
      some warns)
    (hl2 : locs 2 = .i32 i) (hl11 : locs 11 = .heapRef wAddr) (hl15 : locs 15 = .str line) :
    ∃ v st',
      runJvmResFast 23 f_Algorithm_parseBlocks_prog 85
          (f_Algorithm_parseBlocks_prog.drop 85) ⟨85, [], locs, jh, hp⟩ =
        some (v, st') ∧
      decodeLife105Result st' v = some ⟨.unexpectedInput line (i + 1) 3, warns, #[]⟩ ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.heap.arenas = hp.arenas ∧ st'.heap.asciiArrays = hp.asciiArrays := by
  rcases hp with ⟨ar, u64, asc⟩
  let stObj : Jvm.HeapObj AlgExt :=
    .instance "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput"
      [("input", .str line), ("lineIndex", .i32 (i + 1)), ("columnIndex", .i32 3)]
  let jh1 := (jh.alloc stObj).2
  let rObj : Jvm.HeapObj AlgExt := .instance "com/alexvanyo/composelife/model/Life105Result"
    [("status", .heapRef jh.objects.size), ("warnings", .heapRef wAddr),
     ("cells", .ext (.u64Ref u64.length))]
  let jh2 := (jh1.alloc rObj).2
  let hp' : AlgHeap := ⟨ar, u64 ++ [#[]], asc⟩
  let locs' := setLocal (setLocal locs 19 (.heapRef jh.objects.size)) 20 (.ext (.u64Ref u64.length))
  have hext : HeapExtends jh jh2 :=
    heapExtends_trans (heapExtends_alloc jh stObj) (heapExtends_alloc jh1 rObj)
  have hst_get1 : jh1.get? jh.objects.size = some stObj := by
    simp [jh1, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  have hst_bind1 : (jh1.get? jh.objects.size).bind
      (fun o => match o with | .instance c _ => some c | _ => none) =
      some "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput" := by
    rw [hst_get1]; rfl
  refine ⟨.heapRef jh1.objects.size, ⟨107, [.heapRef jh1.objects.size], locs', jh2, hp'⟩,
      ?_, ?_, hext, rfl, rfl⟩
  · step_drop 23
    rw [runJvmResFast_newClass (hstep := rfl)]; norm_res_fuel
    rw [runJvmResFast_dup]; norm_res_fuel
    rw [runJvmResFast_aload, hl15]; norm_res_fuel
    rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
    rw [runJvmResFast_iload, hl2]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_iadd]; norm_res_fuel
    rw [runJvmResFast_uintCtor]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_invokespecial_step (hs := stepSpecial_life105UnexpectedInput_init)]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_noCells_105_heap)]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_newClass (hstep := rfl)]; norm_res_fuel
    rw [runJvmResFast_dup]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_checkcast_instance hst_bind1 (by decide)]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide), hl11]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_invokespecial_step (hs := stepSpecial_life105Result_init)]; norm_res_fuel
    exact runJvmResFast_areturn_step
  · have hres_get : jh2.get? jh1.objects.size = some rObj := by
      simp [jh2, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    have hst_get2 : jh2.get? jh.objects.size = some stObj :=
      heapExtends_alloc jh1 rObj _ _ hst_get1
    have hwget' : jh2.get? wAddr = some (.objArray wCls wElems) := hext wAddr _ hwget
    have hwfold' := foldlM_decodeLife105Warning_mono hext wElems #[] warns hwfold
    dsimp only [decodeLife105Result]
    rw [hres_get]
    dsimp only [rObj]
    simp [List.lookup, decodeLife105Status, hst_get2, stObj, hwget', hwfold', hp', Jvm.JvmVal.asI32]

private theorem parseBlocks_unexpected_row
    (line : String) (i : UInt32) (wAddr : Nat) (wCls : String) (wElems : Array JvmVal)
    (warns : Array Algorithm.Life105Warning)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hwget : jh.get? wAddr = some (.objArray wCls wElems))
    (hwfold : wElems.foldlM (fun acc v => (decodeLife105Warning jh v).map acc.push) #[] =
      some warns)
    (hl2 : locs 2 = .i32 i) (hl11 : locs 11 = .heapRef wAddr) (hl15 : locs 15 = .str line) :
    ∃ v st',
      runJvmResFast 23 f_Algorithm_parseBlocks_prog 260
          (f_Algorithm_parseBlocks_prog.drop 260) ⟨260, [], locs, jh, hp⟩ =
        some (v, st') ∧
      decodeLife105Result st' v = some ⟨.unexpectedInput line (i + 1) 1, warns, #[]⟩ ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.heap.arenas = hp.arenas ∧ st'.heap.asciiArrays = hp.asciiArrays := by
  rcases hp with ⟨ar, u64, asc⟩
  let stObj : Jvm.HeapObj AlgExt :=
    .instance "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput"
      [("input", .str line), ("lineIndex", .i32 (i + 1)), ("columnIndex", .i32 1)]
  let jh1 := (jh.alloc stObj).2
  let rObj : Jvm.HeapObj AlgExt := .instance "com/alexvanyo/composelife/model/Life105Result"
    [("status", .heapRef jh.objects.size), ("warnings", .heapRef wAddr),
     ("cells", .ext (.u64Ref u64.length))]
  let jh2 := (jh1.alloc rObj).2
  let hp' : AlgHeap := ⟨ar, u64 ++ [#[]], asc⟩
  let locs' := setLocal (setLocal locs 18 (.heapRef jh.objects.size)) 19 (.ext (.u64Ref u64.length))
  have hext : HeapExtends jh jh2 :=
    heapExtends_trans (heapExtends_alloc jh stObj) (heapExtends_alloc jh1 rObj)
  have hst_get1 : jh1.get? jh.objects.size = some stObj := by
    simp [jh1, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  have hst_bind1 : (jh1.get? jh.objects.size).bind
      (fun o => match o with | .instance c _ => some c | _ => none) =
      some "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput" := by
    rw [hst_get1]; rfl
  refine ⟨.heapRef jh1.objects.size, ⟨282, [.heapRef jh1.objects.size], locs', jh2, hp'⟩,
      ?_, ?_, hext, rfl, rfl⟩
  · step_drop 23
    rw [runJvmResFast_newClass (hstep := rfl)]; norm_res_fuel
    rw [runJvmResFast_dup]; norm_res_fuel
    rw [runJvmResFast_aload, hl15]; norm_res_fuel
    rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
    rw [runJvmResFast_iload, hl2]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_iadd]; norm_res_fuel
    rw [runJvmResFast_uintCtor]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_invokespecial_step (hs := stepSpecial_life105UnexpectedInput_init)]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_noCells_105_heap)]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_newClass (hstep := rfl)]; norm_res_fuel
    rw [runJvmResFast_dup]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_checkcast_instance hst_bind1 (by decide)]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide), hl11]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_invokespecial_step (hs := stepSpecial_life105Result_init)]; norm_res_fuel
    exact runJvmResFast_areturn_step
  · have hres_get : jh2.get? jh1.objects.size = some rObj := by
      simp [jh2, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    have hst_get2 : jh2.get? jh.objects.size = some stObj :=
      heapExtends_alloc jh1 rObj _ _ hst_get1
    have hwget' : jh2.get? wAddr = some (.objArray wCls wElems) := hext wAddr _ hwget
    have hwfold' := foldlM_decodeLife105Warning_mono hext wElems #[] warns hwfold
    dsimp only [decodeLife105Result]
    rw [hres_get]
    dsimp only [rObj]
    simp [List.lookup, decodeLife105Status, hst_get2, stObj, hwget', hwfold', hp', Jvm.JvmVal.asI32]

private theorem parseBlocks_header_some
    (lines : Array String) (numLines i limit : UInt32)
    (outerAddr innerAddr lineBytesAddr wAddr cId : Nat) (c : Algorithm.ParsedCoords)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (ho : jh.get? outerAddr = some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef innerAddr]))
    (hi : jh.get? innerAddr = some (.objArray "java/lang/Object"
      #[.boxedInt 0, .boxedInt c.x.toUInt32, .null, .null, .null, .boxedInt c.y.toUInt32]))
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines) (hl2 : locs 2 = .i32 i)
    (hl5 : locs 5 = .i32 limit) (hl11 : locs 11 = .heapRef wAddr)
    (hl12 : locs 12 = .ext (.u64Ref cId)) (hl16 : locs 16 = .heapRef lineBytesAddr)
    (hl17 : locs 17 = .heapRef outerAddr) :
    ∃ locs',
      (∀ fRest, runJvmResFast (fRest + 84) f_Algorithm_parseBlocks_prog 108
          (f_Algorithm_parseBlocks_prog.drop 108) ⟨108, [], locs, jh, hp⟩ =
        runJvmResFast fRest f_Algorithm_parseBlocks_prog 12
          (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs', jh, hp⟩) ∧
      locs' 0 = .strArr lines ∧ locs' 1 = .i32 numLines ∧ locs' 2 = .i32 (i + 1) ∧
      locs' 3 = .i32 0 ∧ locs' 4 = .heapRef lineBytesAddr ∧ locs' 5 = .i32 limit ∧
      locs' 6 = .i32 0 ∧ locs' 7 = .i32 1 ∧ locs' 8 = .i32 c.x.toUInt32 ∧
      locs' 9 = .i32 c.y.toUInt32 ∧ locs' 10 = .i32 0 ∧
      locs' 11 = .heapRef wAddr ∧ locs' 12 = .ext (.u64Ref cId) := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro fRest
    split_res_fuel 84
    step_drop 29
    rw [runJvmResFast_aload, hl17]; norm_res_fuel
    rw [runJvmResFast_checkcast_objArray (hget := ho) (hcls := Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_aaload (hget := ho) (hslt := by decide) (hlt := by simp)]; norm_res_fuel
    rw [show (#[JvmVal.boxedInt 1, .heapRef innerAddr][(1 : UInt32).toNat] : JvmVal) =
      .heapRef innerAddr from rfl]
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), hl0]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide), hl1]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), hl2]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_iadd]; norm_res_fuel
    rw [runJvmResFast_uintCtor]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), setLocal_ne (by decide), hl5]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_checkcast_objArray (hget := hi) (hcls := Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_aaload (hget := hi) (hslt := by decide) (hlt := by simp)]; norm_res_fuel
    rw [show (#[JvmVal.boxedInt 0, .boxedInt c.x.toUInt32, .null, .null, .null,
      .boxedInt c.y.toUInt32][(1 : UInt32).toNat] : JvmVal) = .boxedInt c.x.toUInt32 from rfl]
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_instanceof_boxedInt_uint]; norm_res_fuel
    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
    step_drop 17
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_checkcast_boxedInt (hcls := Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_invokevirtual_step (hs := stepVirtual_integer_intValue)]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_checkcast_objArray (hget := hi) (hcls := Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_aaload (hget := hi) (hslt := by decide) (hlt := by simp)]; norm_res_fuel
    rw [show (#[JvmVal.boxedInt 0, .boxedInt c.x.toUInt32, .null, .null, .null,
      .boxedInt c.y.toUInt32][(5 : UInt32).toNat] : JvmVal) = .boxedInt c.y.toUInt32 from rfl]
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_instanceof_boxedInt_uint]; norm_res_fuel
    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
    step_drop 19
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_checkcast_boxedInt (hcls := Or.inl rfl)]; norm_res_fuel
    rw [runJvmResFast_invokevirtual_step (hs := stepVirtual_integer_intValue)]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]);
    rw [hl11]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]);
    rw [hl12]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]);
    rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]);
    rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]);
    rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    step_drop 19
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]);
    rw [hl16]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]);
    rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]);
    rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]);
    rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_goto]; rw [Nat.add_sub_cancel]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · rw [setLocal_self]

private theorem parseBlocks_enter_row
    (lines : Array String) (numLines i : UInt32) (lineBytes : ByteArray)
    (lineBytesAddr wAddr cId : Nat) (blockX blockY rowIndex : Int32)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hlb : jh.get? lineBytesAddr = some (.byteArray lineBytes.data))
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines) (hl2 : locs 2 = .i32 i)
    (hl8 : locs 8 = .i32 blockX.toUInt32) (hl9 : locs 9 = .i32 blockY.toUInt32)
    (hl10 : locs 10 = .i32 rowIndex.toUInt32) (hl11 : locs 11 = .heapRef wAddr)
    (hl12 : locs 12 = .ext (.u64Ref cId)) (hl16 : locs 16 = .heapRef lineBytesAddr) :
    ∃ locs',
      (∀ fRest, runJvmResFast (fRest + 47) f_Algorithm_parseBlocks_prog 213
          (f_Algorithm_parseBlocks_prog.drop 213) ⟨213, [], locs, jh, hp⟩ =
        runJvmResFast fRest f_Algorithm_parseBlocks_prog 12
          (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs', jh, hp⟩) ∧
      locs' 0 = .strArr lines ∧ locs' 1 = .i32 numLines ∧ locs' 2 = .i32 i ∧
      locs' 3 = .i32 1 ∧ locs' 4 = .heapRef lineBytesAddr ∧
      locs' 5 = .i32 lineBytes.data.size.toUInt32 ∧
      locs' 6 = .i32 0 ∧ locs' 7 = .i32 1 ∧ locs' 8 = .i32 blockX.toUInt32 ∧
      locs' 9 = .i32 blockY.toUInt32 ∧ locs' 10 = .i32 rowIndex.toUInt32 ∧
      locs' 11 = .heapRef wAddr ∧ locs' 12 = .ext (.u64Ref cId) := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro fRest
    split_res_fuel 47
    step_drop 24
    rw [runJvmResFast_aload, hl0]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload, setLocal_ne (by decide), hl1]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide), hl2]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload, setLocal_ne (by decide), setLocal_ne (by decide),
      setLocal_ne (by decide), hl16]; norm_res_fuel
    rw [runJvmResFast_arraylength_byte (hget := hlb)]; norm_res_fuel
    rw [runJvmResFast_uintCtor]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl8]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl9]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl10]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [hl11]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [hl12]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    step_drop 23
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [hl16]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_goto]; rw [Nat.add_sub_cancel]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · rw [setLocal_self]

private theorem parseBlocks_inRow_end
    (lines : Array String) (numLines i : UInt32) (bytesAddr : Nat)
    (limit p : UInt32) (hasBlock : Bool) (blockX blockY rowIndex : Int32) (wAddr cId : Nat)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hi : i < numLines) (hge : ¬ p < limit)
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines) (hl2 : locs 2 = .i32 i)
    (hl3 : locs 3 = .i32 1) (hl4 : locs 4 = .heapRef bytesAddr) (hl5 : locs 5 = .i32 limit)
    (hl6 : locs 6 = .i32 p) (hl7 : locs 7 = .i32 (if hasBlock then 1 else 0))
    (hl8 : locs 8 = .i32 blockX.toUInt32) (hl9 : locs 9 = .i32 blockY.toUInt32)
    (hl10 : locs 10 = .i32 rowIndex.toUInt32) (hl11 : locs 11 = .heapRef wAddr)
    (hl12 : locs 12 = .ext (.u64Ref cId)) :
    ∃ locs',
      (∀ fRest, runJvmResFast (fRest + 71) f_Algorithm_parseBlocks_prog 12
          (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs, jh, hp⟩ =
        runJvmResFast fRest f_Algorithm_parseBlocks_prog 12
          (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs', jh, hp⟩) ∧
      locs' 0 = .strArr lines ∧ locs' 1 = .i32 numLines ∧ locs' 2 = .i32 (i + 1) ∧
      locs' 3 = .i32 0 ∧ locs' 4 = .heapRef bytesAddr ∧ locs' 5 = .i32 limit ∧
      locs' 6 = .i32 0 ∧ locs' 7 = .i32 (if hasBlock then 1 else 0) ∧
      locs' 8 = .i32 blockX.toUInt32 ∧ locs' 9 = .i32 blockY.toUInt32 ∧
      locs' 10 = .i32 (rowIndex + 1).toUInt32 ∧ locs' 11 = .heapRef wAddr ∧
      locs' 12 = .ext (.u64Ref cId) := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro fRest
    split_res_fuel 71
    step_drop 6
    rw [runJvmResFast_iload, hl2]; norm_res_fuel
    rw [runJvmResFast_iload, hl1]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_intCompareUnsigned_i32)]; norm_res_fuel
    rw [runJvmResFast_ifge_fallthrough (by
      rw [compareUnsigned_sle_cond]; exact decide_eq_false (fun h => h hi))]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_goto]; norm_res_fuel
    step_drop 5
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_ifne_branch (by decide)]; norm_res_fuel
    step_drop 2
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl3]; norm_res_fuel
    rw [runJvmResFast_ifne_branch (by decide)]; norm_res_fuel
    step_drop 4
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl6]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl5]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_intCompareUnsigned_i32)]; norm_res_fuel
    rw [runJvmResFast_iflt_fallthrough (by
      rw [compareUnsigned_iflt_cond]; exact decide_eq_false hge)]; norm_res_fuel
    step_drop 27
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [hl0]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl1]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl2]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_iadd]; norm_res_fuel
    rw [runJvmResFast_uintCtor]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [hl4]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl5]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl7]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl8]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl9]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl10]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_iadd]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [hl11]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [hl12]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    step_drop 27
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_goto]; rw [Nat.add_sub_cancel]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    have hadd : rowIndex.toUInt32 + 1 = (rowIndex + 1).toUInt32 := by
      have h1 : (1 : UInt32) = (1 : Int32).toUInt32 := rfl
      rw [h1, Int32.toUInt32_add]
    exact congrArg JvmVal.i32 hadd
  · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
  · rw [setLocal_self]

private theorem parseBlocks_inRow_step
    (lines : Array String) (numLines i : UInt32)
    (bytes : ByteArray) (bytesAddr : Nat) (limit p : UInt32)
    (hasBlock : Bool) (blockX blockY rowIndex : Int32) (wAddr cId : Nat)
    (cells : Algorithm.U64Buf) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hi : i < numLines) (hp_lt : p < limit) (hlim : limit.toNat ≤ bytes.data.size)
    (hlim31 : limit.toNat < 2 ^ 31)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hc : hp.u64Arrays[cId]? = some cells)
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines) (hl2 : locs 2 = .i32 i)
    (hl3 : locs 3 = .i32 1) (hl4 : locs 4 = .heapRef bytesAddr) (hl5 : locs 5 = .i32 limit)
    (hl6 : locs 6 = .i32 p) (hl7 : locs 7 = .i32 (if hasBlock then 1 else 0))
    (hl8 : locs 8 = .i32 blockX.toUInt32) (hl9 : locs 9 = .i32 blockY.toUInt32)
    (hl10 : locs 10 = .i32 rowIndex.toUInt32) (hl11 : locs 11 = .heapRef wAddr)
    (hl12 : locs 12 = .ext (.u64Ref cId)) :
    let newCells :=
      if bytes.get! p.toNat == 42
      then Algorithm.U64Buf.push cells (Algorithm.cellBits (blockX + p.toInt32, blockY + rowIndex))
      else cells
    ∃ k cId' hp' locs',
      (∀ fRest, runJvmResFast (fRest + k) f_Algorithm_parseBlocks_prog 12
          (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs, jh, hp⟩ =
        runJvmResFast fRest f_Algorithm_parseBlocks_prog 12
          (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs', jh, hp'⟩) ∧
      hp'.u64Arrays[cId']? = some newCells ∧
      hp'.arenas = hp.arenas ∧ hp'.asciiArrays = hp.asciiArrays ∧
      locs' 0 = .strArr lines ∧ locs' 1 = .i32 numLines ∧ locs' 2 = .i32 i ∧
      locs' 3 = .i32 1 ∧ locs' 4 = .heapRef bytesAddr ∧ locs' 5 = .i32 limit ∧
      locs' 6 = .i32 (p + 1) ∧ locs' 7 = .i32 (if hasBlock then 1 else 0) ∧
      locs' 8 = .i32 blockX.toUInt32 ∧ locs' 9 = .i32 blockY.toUInt32 ∧
      locs' 10 = .i32 rowIndex.toUInt32 ∧ locs' 11 = .heapRef wAddr ∧
      locs' 12 = .ext (.u64Ref cId') := by
  have hp_nat : p.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hp_lt
  have hp_sz : p.toNat < bytes.data.size := by omega
  have hslt_p : p.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt hp_lt (by omega)
  let b : UInt8 := bytes.data[p.toNat]
  have hget_b : bytes.get! p.toNat = b := by
    simp only [ByteArray.get!, getElem!_pos bytes.data p.toNat hp_sz]; rfl
  have hpre : ∀ fAny,
      runJvmResFast (fAny + 22) f_Algorithm_parseBlocks_prog 12
          (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs, jh, hp⟩ =
        runJvmResFast fAny f_Algorithm_parseBlocks_prog 346
          (f_Algorithm_parseBlocks_prog.drop 346)
          ⟨346, [.i32 42, .i32 (UInt32.ofBitVec (b.toBitVec.signExtend 32))],
            setLocal (setLocal locs 13 (.i32 1)) 14 .null, jh, hp⟩ := by
    intro fAny
    split_res_fuel 22
    step_drop 6
    rw [runJvmResFast_iload, hl2]; norm_res_fuel
    rw [runJvmResFast_iload, hl1]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_intCompareUnsigned_i32)]; norm_res_fuel
    rw [runJvmResFast_ifge_fallthrough (by
      rw [compareUnsigned_sle_cond]; exact decide_eq_false (fun h => h hi))]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_goto]; norm_res_fuel
    step_drop 5
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_ifne_branch (by decide)]; norm_res_fuel
    step_drop 2
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl3]; norm_res_fuel
    rw [runJvmResFast_ifne_branch (by decide)]; norm_res_fuel
    step_drop 4
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl6]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl5]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_intCompareUnsigned_i32)]; norm_res_fuel
    rw [runJvmResFast_iflt_branch (by
      rw [compareUnsigned_iflt_cond]; exact decide_eq_true hp_lt)]; norm_res_fuel
    step_drop 5
    rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [hl4]; norm_res_fuel
    rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl6]; norm_res_fuel
    rw [runJvmResFast_baload_byteArray (hget := hbytes) (hslt := hslt_p) (hlt := hp_sz)]
    norm_res_fuel
    rw [runJvmResFast_ubyteCtor]; norm_res_fuel
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [Nat.add_sub_cancel]
  have htail : ∀ (cIdNext : Nat) (locsPre : Nat → JvmVal) (hpAny : AlgHeap),
      locsPre 0 = .strArr lines → locsPre 1 = .i32 numLines → locsPre 2 = .i32 i →
      locsPre 4 = .heapRef bytesAddr → locsPre 5 = .i32 limit → locsPre 6 = .i32 p →
      locsPre 7 = .i32 (if hasBlock then 1 else 0) → locsPre 8 = .i32 blockX.toUInt32 →
      locsPre 9 = .i32 blockY.toUInt32 → locsPre 10 = .i32 rowIndex.toUInt32 →
      locsPre 11 = .heapRef wAddr → locsPre 13 = .i32 1 →
      locsPre 14 = .ext (.u64Ref cIdNext) →
      ∃ locs',
        (∀ fAny, runJvmResFast (fAny + 52) f_Algorithm_parseBlocks_prog 381
            (f_Algorithm_parseBlocks_prog.drop 381) ⟨381, [], locsPre, jh, hpAny⟩ =
          runJvmResFast fAny f_Algorithm_parseBlocks_prog 12
            (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs', jh, hpAny⟩) ∧
        locs' 0 = .strArr lines ∧ locs' 1 = .i32 numLines ∧ locs' 2 = .i32 i ∧
        locs' 3 = .i32 1 ∧ locs' 4 = .heapRef bytesAddr ∧ locs' 5 = .i32 limit ∧
        locs' 6 = .i32 (p + 1) ∧ locs' 7 = .i32 (if hasBlock then 1 else 0) ∧
        locs' 8 = .i32 blockX.toUInt32 ∧ locs' 9 = .i32 blockY.toUInt32 ∧
        locs' 10 = .i32 rowIndex.toUInt32 ∧ locs' 11 = .heapRef wAddr ∧
        locs' 12 = .ext (.u64Ref cIdNext) := by
    intro cIdNext locsPre hpAny p0 p1 p2 p4 p5 p6 p7 p8 p9 p10 p11 p13 p14
    apply Exists.intro
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro fAny
      split_res_fuel 52
      step_drop 26
      rw [runJvmResFast_aload, p0]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_ne (by decide), p1]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_ne (by decide), p2]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [p4]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [p5]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [p6]; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_iadd]; norm_res_fuel
      rw [runJvmResFast_uintCtor]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [p7]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [p8]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [p9]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [p10]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [p11]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
      step_drop 26
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [p13]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [p14]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_goto]; rw [Nat.add_sub_cancel]
    · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    · (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self]
    · rw [setLocal_self]
  by_cases h42 : b = 42
  · have hbr42 : UInt32.ofBitVec (b.toBitVec.signExtend 32) = 42 :=
      signExtend_eq_u32 h42 rfl (by decide)
    let key := Algorithm.cellBits (blockX + p.toInt32, blockY + rowIndex)
    let newCells := Algorithm.U64Buf.push cells key
    rcases hp with ⟨ar, u64, asc⟩
    let hp' : AlgHeap := ⟨ar, u64 ++ [newCells], asc⟩
    let locs0 := setLocal (setLocal locs 13 (.i32 1)) 14 .null
    let locs1 := setLocal (setLocal locs0 15 (.ext (.u64Ref u64.length)))
      14 (.ext (.u64Ref u64.length))
    rcases htail u64.length locs1 hp'
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl0)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl1)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl2)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl4)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl5)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl6)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl7)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl8)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl9)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl10)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl11)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self])
        rfl with
      ⟨locs', htl, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12⟩
    refine ⟨106, u64.length, hp', locs', ?_, ?_, rfl, rfl,
      o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12⟩
    · intro fRest
      rw [show fRest + 106 = (fRest + 52 + 32) + 22 by omega]
      rw [hpre]
      split_res_fuel 32
      step_drop 1
      rw [runJvmResFast_if_icmpeq_branch hbr42]; norm_res_fuel
      step_drop 6
      rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [hl12]; norm_res_fuel
      rw [runJvmResFast_nop]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl8]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl6]; norm_res_fuel
      rw [runJvmResFast_iadd]; norm_res_fuel
      rw [runJvmResFast_uintCtor]; norm_res_fuel
      step_drop 3
      rw [runJvmResFast_i2l_mask]; norm_res_fuel
      step_drop 9
      rw [runJvmResFast_ulongCtor]; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_lshl_32]; norm_res_fuel
      rw [runJvmResFast_ulongCtor]; norm_res_fuel
      rw [runJvmResFast_nop]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl9]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl10]; norm_res_fuel
      rw [runJvmResFast_iadd]; norm_res_fuel
      rw [runJvmResFast_uintCtor]; norm_res_fuel
      step_drop 3
      rw [runJvmResFast_i2l_mask]; norm_res_fuel
      step_drop 10
      rw [runJvmResFast_ulongCtor]; norm_res_fuel
      rw [runJvmResFast_lconst]; norm_res_fuel
      rw [runJvmResFast_land]; norm_res_fuel
      rw [runJvmResFast_ulongCtor]; norm_res_fuel
      rw [runJvmResFast_ladd]; norm_res_fuel
      rw [runJvmResFast_ulongCtor]; norm_res_fuel
      rw [cellKey_jvm_eq blockX blockY rowIndex p]
      rw [runJvmResFast_invokestatic_step
        (hs := stepStatic_u64BufPush_heap hc (hcls := Or.inl rfl))]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [show fRest + 52 + 32 - 32 = fRest + 52 by omega]; exact htl fRest
    · rw [hget_b]; simp only [beq_iff_eq.mpr h42, ↓reduceIte]
      simp [hp']; rfl
  · have hne42 : (UInt32.ofBitVec (b.toBitVec.signExtend 32) == 42) = false :=
      signExtend_bne_u32 h42 rfl (by decide)
    let locs0 := setLocal (setLocal locs 13 (.i32 1)) 14 .null
    let locs1 := setLocal locs0 14 (.ext (.u64Ref cId))
    rcases htail cId locs1 hp
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl0)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl1)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl2)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl4)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl5)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl6)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl7)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl8)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl9)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl10)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); exact hl11)
        (by dsimp only [locs1, locs0]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self])
        rfl with
      ⟨locs', htl, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12⟩
    refine ⟨78, cId, hp, locs', ?_, ?_, rfl, rfl,
      o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12⟩
    · intro fRest
      rw [show fRest + 78 = (fRest + 52 + 4) + 22 by omega]
      rw [hpre]
      split_res_fuel 4
      step_drop 4
      rw [runJvmResFast_if_icmpeq_fallthrough hne42]; norm_res_fuel
      rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [hl12]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_goto]
      rw [show fRest + 52 + 4 - 4 = fRest + 52 by omega]; exact htl fRest
    · rw [hget_b]; simp only [beq_false_of_ne h42, Bool.false_eq_true, ↓reduceIte]
      exact hc

private theorem parseBlocks_inRow_drain (rem : Nat) :
    ∀ (lines : Array String) (numLines i : UInt32)
      (bytes : ByteArray) (bytesAddr : Nat) (limit p : UInt32)
      (hasBlock : Bool) (blockX blockY rowIndex : Int32)
      (warns : Array Algorithm.Life105Warning) (wAddr cId : Nat)
      (cells : Algorithm.U64Buf) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap),
      rem = limit.toNat - p.toNat →
      i < numLines →
      limit.toNat ≤ bytes.data.size →
      limit.toNat < 2 ^ 31 →
      jh.get? bytesAddr = some (.byteArray bytes.data) →
      hp.u64Arrays[cId]? = some cells →
      locs 0 = .strArr lines → locs 1 = .i32 numLines → locs 2 = .i32 i →
      locs 3 = .i32 1 → locs 4 = .heapRef bytesAddr → locs 5 = .i32 limit →
      locs 6 = .i32 p → locs 7 = .i32 (if hasBlock then 1 else 0) →
      locs 8 = .i32 blockX.toUInt32 → locs 9 = .i32 blockY.toUInt32 →
      locs 10 = .i32 rowIndex.toUInt32 → locs 11 = .heapRef wAddr →
      locs 12 = .ext (.u64Ref cId) →
      ∃ k cId' cells' hp' locs',
        (∀ fRest, runJvmResFast (fRest + k) f_Algorithm_parseBlocks_prog 12
            (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs, jh, hp⟩ =
          runJvmResFast fRest f_Algorithm_parseBlocks_prog 12
            (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs', jh, hp'⟩) ∧
        hp'.u64Arrays[cId']? = some cells' ∧
        hp'.arenas = hp.arenas ∧ hp'.asciiArrays = hp.asciiArrays ∧
        locs' 0 = .strArr lines ∧ locs' 1 = .i32 numLines ∧ locs' 2 = .i32 (i + 1) ∧
        locs' 3 = .i32 0 ∧ locs' 4 = .heapRef bytesAddr ∧ locs' 5 = .i32 limit ∧
        locs' 6 = .i32 0 ∧ locs' 7 = .i32 (if hasBlock then 1 else 0) ∧
        locs' 8 = .i32 blockX.toUInt32 ∧ locs' 9 = .i32 blockY.toUInt32 ∧
        locs' 10 = .i32 (rowIndex + 1).toUInt32 ∧ locs' 11 = .heapRef wAddr ∧
        locs' 12 = .ext (.u64Ref cId') ∧
        Algorithm.parseBlocks lines numLines i true bytes limit p hasBlock
            blockX blockY rowIndex warns cells =
          Algorithm.parseBlocks lines numLines (i + 1) false bytes limit 0 hasBlock
            blockX blockY (rowIndex + 1) warns cells' := by
  induction rem with
  | zero =>
    intro lines numLines i bytes bytesAddr limit p hasBlock blockX blockY rowIndex warns
      wAddr cId cells locs jh hp hrem hi hlim hlim31 hbytes hc hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7
      hl8 hl9 hl10 hl11 hl12
    have hge : ¬ p < limit := by
      intro hlt; have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    rcases parseBlocks_inRow_end lines numLines i bytesAddr limit p hasBlock blockX blockY
        rowIndex wAddr cId locs jh hp hi hge hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11
        hl12 with
      ⟨locs', hrun, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12⟩
    refine ⟨71, cId, cells, hp, locs', hrun, hc, rfl, rfl,
      o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, ?_⟩
    rw [Algorithm.parseBlocks]; simp [hi, hge]
  | succ rem' ih =>
    intro lines numLines i bytes bytesAddr limit p hasBlock blockX blockY rowIndex warns
      wAddr cId cells locs jh hp hrem hi hlim hlim31 hbytes hc hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7
      hl8 hl9 hl10 hl11 hl12
    have hp_lt : p < limit := UInt32.lt_iff_toNat_lt.mpr (by omega)
    let newCells :=
      if bytes.get! p.toNat == 42
      then Algorithm.U64Buf.push cells (Algorithm.cellBits (blockX + p.toInt32, blockY + rowIndex))
      else cells
    have hp1_toNat : (p + 1).toNat = p.toNat + 1 := ui32_add1_toNat hp_lt
    have hrem' : rem' = limit.toNat - (p + 1).toNat := by omega
    rcases parseBlocks_inRow_step lines numLines i bytes bytesAddr limit p hasBlock blockX blockY
        rowIndex wAddr cId cells locs jh hp hi hp_lt hlim hlim31 hbytes hc hl0 hl1 hl2 hl3 hl4
        hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 with
      ⟨k1, cId1, hp1, locs1, hrun1, hc1, har1, hasc1, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9,
        m10, m11, m12⟩
    rcases ih lines numLines i bytes bytesAddr limit (p + 1) hasBlock blockX blockY rowIndex
        warns wAddr cId1 newCells locs1 jh hp1 hrem' hi hlim hlim31 hbytes hc1 m0 m1 m2 m3 m4 m5
        m6 m7 m8 m9 m10 m11 m12 with
      ⟨k2, cId', cells', hp', locs', hrun2, hc', har', hasc',
        o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, hpb2⟩
    refine ⟨k2 + k1, cId', cells', hp', locs', ?_, hc', har1 ▸ har', hasc1 ▸ hasc',
      o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, ?_⟩
    · intro fRest
      rw [show fRest + (k2 + k1) = (fRest + k2) + k1 by omega]
      rw [hrun1 (fRest + k2), hrun2 fRest]
    · rw [Algorithm.parseBlocks]; simp only [hi, ↓reduceDIte, ↓reduceIte, hp_lt]
      exact hpb2

set_option maxHeartbeats 400000 in
private theorem parseBlocks_loop (rem : Nat) :
    ∀ (lines : Array String) (numLines i : UInt32)
      (bytes : ByteArray) (bytesAddr : Nat) (limit p : UInt32)
      (hasBlock : Bool) (blockX blockY rowIndex : Int32)
      (warns : Array Algorithm.Life105Warning) (wAddr : Nat) (wCls : String) (wElems : Array JvmVal)
      (cells : Algorithm.U64Buf) (cId : Nat)
      (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap),
      rem = numLines.toNat - i.toNat →
      jh.statics = [] →
      lines.size < 2 ^ 31 →
      numLines.toNat ≤ lines.size →
      (∀ k < lines.size, lines[k]!.toUTF8.data.size < 2 ^ 31) →
      jh.get? bytesAddr = some (.byteArray bytes.data) →
      jh.get? wAddr = some (.objArray wCls wElems) →
      wElems.foldlM (fun acc v => (decodeLife105Warning jh v).map acc.push) #[] = some warns →
      hp.u64Arrays[cId]? = some cells →
      locs 0 = .strArr lines → locs 1 = .i32 numLines → locs 2 = .i32 i →
      locs 3 = .i32 0 → locs 4 = .heapRef bytesAddr → locs 5 = .i32 limit →
      locs 6 = .i32 p → locs 7 = .i32 (if hasBlock then 1 else 0) →
      locs 8 = .i32 blockX.toUInt32 → locs 9 = .i32 blockY.toUInt32 →
      locs 10 = .i32 rowIndex.toUInt32 → locs 11 = .heapRef wAddr →
      locs 12 = .ext (.u64Ref cId) →
      ∃ f v st',
        runJvmResFast f f_Algorithm_parseBlocks_prog 12
            (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs, jh, hp⟩ =
          some (v, st') ∧
        decodeLife105Result st' v =
          some (Algorithm.parseBlocks lines numLines i false bytes limit p hasBlock
            blockX blockY rowIndex warns cells) ∧
        HeapExtends jh st'.jvmHeap ∧
        st'.heap.arenas = hp.arenas ∧ st'.heap.asciiArrays = hp.asciiArrays := by
  induction rem with
  | zero =>
    intro lines numLines i bytes bytesAddr limit p hasBlock blockX blockY rowIndex warns
      wAddr wCls wElems cells cId locs jh hp hrem hstat _ _ _ _ hwget hwfold hc
      hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12
    have hge : ¬ i < numLines := by
      intro hlt; have := UInt32.lt_iff_toNat_lt.mp hlt; omega
    have hpb : Algorithm.parseBlocks lines numLines i false bytes limit p hasBlock
        blockX blockY rowIndex warns cells = ⟨.ok, warns, Algorithm.U64Buf.toArray cells⟩ := by
      rw [Algorithm.parseBlocks]; simp [hge]
    rw [hpb]
    let locs1 := setLocal (setLocal locs 13 (.i32 0)) 14 .null
    rcases parseBlocks_exit_ok wAddr cId wCls wElems warns cells locs1 jh hp hstat hwget hwfold hc
        (by dsimp only [locs1]; (repeat rw [setLocal_ne (by decide)]); exact hl11)
        (by dsimp only [locs1]; (repeat rw [setLocal_ne (by decide)]); exact hl12) with
      ⟨v, st', hexit, hdec, hext, har, hasc⟩
    refine ⟨24, v, st', ?_, hdec, hext, har, hasc⟩
    split_res_fuel 10
    step_drop 4
    rw [runJvmResFast_iload, hl2]; norm_res_fuel
    rw [runJvmResFast_iload, hl1]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_intCompareUnsigned_i32)]; norm_res_fuel
    rw [runJvmResFast_ifge_branch (by
      rw [compareUnsigned_sle_cond]; exact decide_eq_true hge)]; norm_res_fuel
    step_drop 6
    rw [runJvmResFast_iconst]; norm_res_fuel
    rw [runJvmResFast_istore]; norm_res_fuel
    rw [runJvmResFast_aconstNull]; norm_res_fuel
    rw [runJvmResFast_astore]; norm_res_fuel
    rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
    rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
    rw [show 24 - 10 = 14 by rfl]
    exact hexit
  | succ rem' ih =>
    intro lines numLines i bytes bytesAddr limit p hasBlock blockX blockY rowIndex warns
      wAddr wCls wElems cells cId locs jh hp hrem hstat hlines31 hnum hutf8 hbytes hwget hwfold hc
      hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12
    have hi : i < numLines := UInt32.lt_iff_toNat_lt.mpr (by omega)
    have hi_nat : i.toNat < numLines.toNat := UInt32.lt_iff_toNat_lt.mp hi
    have hi_sz : i.toNat < lines.size := by omega
    have hi_slt : i.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt hi (by omega)
    have hi1_toNat : (i + 1).toNat = i.toNat + 1 := ui32_add1_toNat hi
    have hrem' : rem' = numLines.toNat - (i + 1).toNat := by omega
    let line := lines[i.toNat]
    have hline_bang : lines[i.toNat]! = line := getElem!_pos lines i.toNat hi_sz
    let lineBytes : ByteArray := line.toByteArray
    have hutf8_sz : lineBytes.data.size < 2 ^ 31 := by
      change line.toUTF8.data.size < 2 ^ 31
      rw [← hline_bang]; exact hutf8 i.toNat hi_sz
    have hline_bytes_eq : line.toUTF8.data = lineBytes.data := rfl
    let lineBytesAddr := jh.objects.size
    let jh1 := (jh.alloc (.byteArray lineBytes.data)).2
    have hstat1 : jh1.statics = [] := hstat
    have hext1 : HeapExtends jh jh1 := heapExtends_alloc jh (.byteArray lineBytes.data)
    have hlb : jh1.get? lineBytesAddr = some (.byteArray lineBytes.data) := by
      simp [jh1, lineBytesAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    have hwget1 : jh1.get? wAddr = some (.objArray wCls wElems) := hext1 wAddr _ hwget
    have hwfold1 := foldlM_decodeLife105Warning_mono hext1 wElems #[] warns hwfold
    let locs2 := setLocal (setLocal (setLocal (setLocal locs 13 (.i32 1)) 14 .null)
      15 (.str line)) 16 (.heapRef lineBytesAddr)
    have hpre51 : ∀ fRest,
        runJvmResFast (fRest + 24) f_Algorithm_parseBlocks_prog 12
            (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs, jh, hp⟩ =
          runJvmResFast fRest f_Algorithm_parseBlocks_prog 51
            (f_Algorithm_parseBlocks_prog.drop 51) ⟨51, [], locs2, jh1, hp⟩ := by
      intro fRest
      split_res_fuel 24
      step_drop 6
      rw [runJvmResFast_iload, hl2]; norm_res_fuel
      rw [runJvmResFast_iload, hl1]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_intCompareUnsigned_i32)]; norm_res_fuel
      rw [runJvmResFast_ifge_fallthrough (by
        rw [compareUnsigned_sle_cond]; exact decide_eq_false (fun h => h hi))]; norm_res_fuel
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_goto]; norm_res_fuel
      step_drop 5
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aconstNull]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_ifne_branch (by decide)]; norm_res_fuel
      step_drop 2
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl3]; norm_res_fuel
      rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
      step_drop 11
      rw [runJvmResFast_aload]; (repeat rw [setLocal_ne (by decide)]); rw [hl0]; norm_res_fuel
      rw [runJvmResFast_iload]; (repeat rw [setLocal_ne (by decide)]); rw [hl2]; norm_res_fuel
      rw [runJvmResFast_aaload_strArr (hslt := hi_slt) (hlt := hi_sz)]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_ldcStr]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_checkcast_step rfl]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_stringsEncodeToByteArray)]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [hline_bytes_eq, Nat.add_sub_cancel]
    have h206 :
        Algorithm.startsWithHash lineBytes 80 = false →
        ∃ f v st',
          runJvmResFast f f_Algorithm_parseBlocks_prog 206
              (f_Algorithm_parseBlocks_prog.drop 206) ⟨206, [], locs2, jh1, hp⟩ =
            some (v, st') ∧
          decodeLife105Result st' v =
            some (Algorithm.parseBlocks lines numLines i false bytes limit p hasBlock
              blockX blockY rowIndex warns cells) ∧
          HeapExtends jh1 st'.jvmHeap ∧
          st'.heap.arenas = hp.arenas ∧ st'.heap.asciiArrays = hp.asciiArrays := by
      intro hnhash
      have hpb_eq :
          Algorithm.parseBlocks lines numLines i false bytes limit p hasBlock
              blockX blockY rowIndex warns cells =
            if Algorithm.isRowLine lineBytes && hasBlock then
              Algorithm.parseBlocks lines numLines i true lineBytes
                lineBytes.size.toUInt32 0 true blockX blockY rowIndex warns cells
            else ⟨.unexpectedInput line (i + 1) 1, warns, Algorithm.noCells⟩ := by
        rw [Algorithm.parseBlocks]; simp [hi, hline_bang, lineBytes, hnhash]
      let rline := Algorithm.isRowLine lineBytes
      let locs3 := setLocal locs2 17 (.i32 (if rline then 1 else 0))
      have h206_head : ∀ fAny,
          runJvmResFast (fAny + 3) f_Algorithm_parseBlocks_prog 206
              (f_Algorithm_parseBlocks_prog.drop 206) ⟨206, [], locs2, jh1, hp⟩ =
            runJvmResFast fAny f_Algorithm_parseBlocks_prog 209
              (f_Algorithm_parseBlocks_prog.drop 209) ⟨209, [], locs3, jh1, hp⟩ := by
        intro fAny
        split_res_fuel 3
        step_drop 3
        rw [runJvmResFast_aload]; dsimp only [locs2]; rw [setLocal_self]; norm_res_fuel
        rw [runJvmResFast_invokestatic_step (hs := stepStatic_isRowLine_heap hlb)]; norm_res_fuel
        rw [runJvmResFast_istore]; norm_res_fuel
        rw [Nat.add_sub_cancel]
      by_cases hrow : rline = true ∧ hasBlock = true
      · rcases hrow with ⟨hr1, hb1⟩
        have hpb_row :
            Algorithm.parseBlocks lines numLines i false bytes limit p hasBlock
                blockX blockY rowIndex warns cells =
              Algorithm.parseBlocks lines numLines i true lineBytes
                lineBytes.size.toUInt32 0 true blockX blockY rowIndex warns cells := by
          rw [hpb_eq]; simp [rline, hr1, hb1]
        rcases parseBlocks_enter_row lines numLines i lineBytes lineBytesAddr wAddr cId
            blockX blockY rowIndex locs3 jh1 hp hlb
            (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl0)
            (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl1)
            (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl2)
            (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl8)
            (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl9)
            (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl10)
            (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl11)
            (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl12)
            (by dsimp only [locs3, locs2]; rw [setLocal_ne (by decide)]; rw [setLocal_self]) with
          ⟨locs4, henter, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩
        have hlim_lb : lineBytes.data.size.toUInt32.toNat ≤ lineBytes.data.size := by
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _
        have hlim31_lb : lineBytes.data.size.toUInt32.toNat < 2 ^ 31 := by
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hutf8_sz
        rcases parseBlocks_inRow_drain (lineBytes.data.size.toUInt32.toNat - (0 : UInt32).toNat)
            lines numLines i lineBytes lineBytesAddr lineBytes.data.size.toUInt32 0 true
            blockX blockY rowIndex warns wAddr cId cells locs4 jh1 hp
            rfl hi hlim_lb hlim31_lb hlb hc q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 with
          ⟨kdr, cId', cells', hp', locs5, hdr, hc', har', hasc',
            r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, hpb_dr⟩
        rcases ih lines numLines (i + 1) lineBytes lineBytesAddr lineBytes.data.size.toUInt32 0
            true blockX blockY (rowIndex + 1) warns wAddr wCls wElems cells' cId' locs5 jh1 hp'
            hrem' hstat1 hlines31 hnum hutf8 hlb hwget1 hwfold1 hc'
            r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 with
          ⟨fih, v, st', hih, hdec, hext2, har2, hasc2⟩
        refine ⟨fih + kdr + 47 + 4 + 3, v, st', ?_, ?_, hext2, har' ▸ har2, hasc' ▸ hasc2⟩
        · rw [show fih + kdr + 47 + 4 + 3 = (fih + kdr + 47 + 4) + 3 by omega]
          rw [h206_head]
          split_res_fuel 4
          step_drop 4
          rw [runJvmResFast_iload]
          rw [show locs3 17 = .i32 (if rline = true then 1 else 0) from rfl]
          conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]
          rw [show (if rline = true then (1 : UInt32) else 0) = 1 from by simp [hr1]]
          rw [runJvmResFast_ifeq_fallthrough (by decide)]
          conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]
          rw [runJvmResFast_iload]
          rw [show locs3 7 = .i32 1 from by
            dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); rw [hl7, hb1]; rfl]
          conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]
          rw [runJvmResFast_ifeq_fallthrough (by decide)]
          conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]
          rw [show (209 + 1 + 1 + 1 + 1 : Nat) = 213 from rfl]
          rw [show fih + kdr + 47 + 4 - 4 = fih + kdr + 47 by omega, henter (fih + kdr),
            hdr fih, hih]
        · rw [hpb_row, show lineBytes.size.toUInt32 = lineBytes.data.size.toUInt32 from rfl,
            hpb_dr]
          exact hdec
      · have hpb_unexp :
            Algorithm.parseBlocks lines numLines i false bytes limit p hasBlock
                blockX blockY rowIndex warns cells =
              ⟨.unexpectedInput line (i + 1) 1, warns, #[]⟩ := by
          rw [hpb_eq]
          have hfalse : (rline && hasBlock) = false := by
            cases hr : rline <;> cases hb : hasBlock <;> simp_all
          simp [rline, hfalse, Algorithm.noCells]
        rcases parseBlocks_unexpected_row line i wAddr wCls wElems warns locs3 jh1 hp
            hwget1 hwfold1
            (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl2)
            (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl11)
            (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self])
            with ⟨v, st', hun, hdec, hext2, har2, hasc2⟩
        rw [hpb_unexp]
        by_cases hr : rline = true
        · have hhb : hasBlock = false := by
            cases hb : hasBlock with
            | false => rfl
            | true => exact absurd ⟨hr, hb⟩ hrow
          refine ⟨23 + 4 + 3, v, st', ?_, hdec, hext2, har2, hasc2⟩
          rw [show 23 + 4 + 3 = (23 + 4) + 3 by rfl, h206_head]
          split_res_fuel 4
          step_drop 4
          rw [runJvmResFast_iload]
          rw [show locs3 17 = .i32 (if rline = true then 1 else 0) from rfl]
          conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]
          rw [show (if rline = true then (1 : UInt32) else 0) = 1 from by simp [hr]]
          rw [runJvmResFast_ifeq_fallthrough (by decide)]
          conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]
          rw [runJvmResFast_iload]
          rw [show locs3 7 = .i32 0 from by
            dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); rw [hl7, hhb]; rfl]
          conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]
          rw [runJvmResFast_ifeq_branch rfl]
          conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]
          rw [show 23 + 4 - 4 = 23 by omega]; exact hun
        · have hrf : rline = false := Bool.eq_false_of_ne_true hr
          refine ⟨23 + 2 + 3, v, st', ?_, hdec, hext2, har2, hasc2⟩
          rw [show 23 + 2 + 3 = (23 + 2) + 3 by rfl, h206_head]
          split_res_fuel 2
          step_drop 2
          rw [runJvmResFast_iload]
          rw [show locs3 17 = .i32 (if rline = true then 1 else 0) from rfl]
          conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]
          rw [show (if rline = true then (1 : UInt32) else 0) = 0 from by simp [hrf]]
          rw [runJvmResFast_ifeq_branch rfl]
          conv => lhs; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]
          rw [show 23 + 2 - 2 = 23 by omega]; exact hun
    by_cases hlt2 : lineBytes.data.size < 2
    · have hnhash : Algorithm.startsWithHash lineBytes 80 = false := by
        have hlt2_u : lineBytes.data.size.toUInt32 < 2 := by
          rw [UInt32.lt_iff_toNat_lt]
          change lineBytes.data.size.toUInt32.toNat < 2
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          exact hlt2
        have hge_f : decide (lineBytes.size.toUInt32 >= 2) = false :=
          decide_eq_false (UInt32.not_le.mpr hlt2_u)
        simp only [Algorithm.startsWithHash, hge_f, Bool.false_and]
      rcases h206 hnhash with ⟨f206, v, st', hrun206, hdec, hext2, har2, hasc2⟩
      refine ⟨f206 + 6 + 24, v, st', ?_, hdec, heapExtends_trans hext1 hext2, har2, hasc2⟩
      rw [show f206 + 6 + 24 = (f206 + 6) + 24 by omega, hpre51]
      split_res_fuel 6
      step_drop 6
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
      rw [runJvmResFast_arraylength_byte (hget := hlb)]; norm_res_fuel
      rw [runJvmResFast_uintCtor]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_intCompareUnsigned_i32)]; norm_res_fuel
      rw [runJvmResFast_ifgt_branch (by
        rw [compareUnsigned_ifgt_cond]
        apply decide_eq_true
        rw [UInt32.lt_iff_toNat_lt]
        change lineBytes.data.size.toUInt32.toNat < 2
        rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        exact hlt2)]
      rw [Nat.add_sub_cancel]; exact hrun206
    · have hge2 : 2 ≤ lineBytes.data.size := Nat.le_of_not_lt hlt2
      have hge2_u : (2 : UInt32) ≤ lineBytes.data.size.toUInt32 := by
        rw [UInt32.le_iff_toNat_le]
        change 2 ≤ lineBytes.data.size.toUInt32.toNat
        rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        exact hge2
      let b0 := lineBytes.data[0]
      have hge2_step : ∀ fAny,
          runJvmResFast (fAny + 11) f_Algorithm_parseBlocks_prog 51
              (f_Algorithm_parseBlocks_prog.drop 51) ⟨51, [], locs2, jh1, hp⟩ =
            runJvmResFast fAny f_Algorithm_parseBlocks_prog 62
              (f_Algorithm_parseBlocks_prog.drop 62)
              ⟨62, [.i32 35, .i32 (UInt32.ofBitVec (b0.toBitVec.signExtend 32))],
                locs2, jh1, hp⟩ := by
        intro fAny
        split_res_fuel 11
        step_drop 6
        rw [runJvmResFast_iconst]; norm_res_fuel
        rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
        rw [runJvmResFast_arraylength_byte (hget := hlb)]; norm_res_fuel
        rw [runJvmResFast_uintCtor]; norm_res_fuel
        rw [runJvmResFast_invokestatic_step (hs := stepStatic_intCompareUnsigned_i32)]; norm_res_fuel
        rw [runJvmResFast_ifgt_fallthrough (by
          rw [compareUnsigned_ifgt_cond]
          apply decide_eq_false
          intro hlt
          exact absurd (UInt32.lt_iff_toNat_lt.mp hlt)
            (Nat.not_lt_of_le (UInt32.le_iff_toNat_le.mp hge2_u)))]; norm_res_fuel
        step_drop 5
        rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
        rw [runJvmResFast_iconst]; norm_res_fuel
        rw [runJvmResFast_baload_byteArray (hget := hlb) (hslt := by decide)
          (hlt := by change (0 : UInt32).toNat < lineBytes.data.size; rw [show (0 : UInt32).toNat = 0 from rfl]; omega)]
        norm_res_fuel
        rw [runJvmResFast_ubyteCtor]; norm_res_fuel
        rw [runJvmResFast_iconst]; norm_res_fuel
        rw [Nat.add_sub_cancel]; rfl
      by_cases hb0 : b0 = 35
      · have heq35 : UInt32.ofBitVec (b0.toBitVec.signExtend 32) = 35 :=
          signExtend_eq_u32 hb0 rfl (by decide)
        let b1 := lineBytes.data[1]
        have h62_step : ∀ fAny,
            runJvmResFast (fAny + 6) f_Algorithm_parseBlocks_prog 62
                (f_Algorithm_parseBlocks_prog.drop 62)
                ⟨62, [.i32 35, .i32 (UInt32.ofBitVec (b0.toBitVec.signExtend 32))],
                  locs2, jh1, hp⟩ =
              runJvmResFast fAny f_Algorithm_parseBlocks_prog 68
                (f_Algorithm_parseBlocks_prog.drop 68)
                ⟨68, [.i32 80, .i32 (UInt32.ofBitVec (b1.toBitVec.signExtend 32))],
                  locs2, jh1, hp⟩ := by
          intro fAny
          split_res_fuel 6
          step_drop 6
          rw [runJvmResFast_if_icmpne_fallthrough heq35]; norm_res_fuel
          rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
          rw [runJvmResFast_iconst]; norm_res_fuel
          rw [runJvmResFast_baload_byteArray (hget := hlb) (hslt := by decide)
            (hlt := by
              change (1 : UInt32).toNat < lineBytes.data.size
              rw [show (1 : UInt32).toNat = 1 from rfl]; omega)]
          norm_res_fuel
          rw [runJvmResFast_ubyteCtor]; norm_res_fuel
          rw [runJvmResFast_iconst]; norm_res_fuel
          rw [Nat.add_sub_cancel]; rfl
        by_cases hb1 : b1 = 80
        · have heq80 : UInt32.ofBitVec (b1.toBitVec.signExtend 32) = 80 :=
            signExtend_eq_u32 hb1 rfl (by decide)
          have hhash : Algorithm.startsWithHash lineBytes 80 = true := by
            have h0_bang : lineBytes.get! 0 = b0 := by
              simp [ByteArray.get!, getElem!_pos lineBytes.data 0 (by omega), b0]
            have h1_bang : lineBytes.get! 1 = b1 := by
              simp [ByteArray.get!, getElem!_pos lineBytes.data 1 (by omega), b1]
            simp only [Algorithm.startsWithHash, show lineBytes.size = lineBytes.data.size from rfl,
              decide_eq_true hge2_u, h0_bang, h1_bang, hb0, hb1, beq_self_eq_true, Bool.and_true]
          cases hbh : Algorithm.parseBlockHeader lineBytes with
          | none =>
            have hbh_data : Algorithm.parseBlockHeader ⟨lineBytes.data⟩ = none := hbh
            let outerAddr := jh1.objects.size
            let jh2 := (jh1.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2
            have hext12 : HeapExtends jh1 jh2 := heapExtends_alloc jh1 _
            have hout : jh2.get? outerAddr =
                some (.objArray "java/lang/Object" #[.boxedInt 0]) := by
              simp [jh2, outerAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
            have hwget2 : jh2.get? wAddr = some (.objArray wCls wElems) := hext12 _ _ hwget1
            have hwfold2 := foldlM_decodeLife105Warning_mono hext12 wElems #[] warns hwfold1
            let locs3 := setLocal locs2 17 (.heapRef outerAddr)
            rcases parseBlocks_header_none line i wAddr wCls wElems warns locs3 jh2 hp
                hwget2 hwfold2
                (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl2)
                (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl11)
                (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)])
                    rw [setLocal_self]) with
              ⟨v, st', hun, hdec, hext3, har3, hasc3⟩
            have hpb_none :
                Algorithm.parseBlocks lines numLines i false bytes limit p hasBlock
                    blockX blockY rowIndex warns cells =
                  ⟨.unexpectedInput line (i + 1) 3, warns, #[]⟩ := by
              rw [Algorithm.parseBlocks]
              simp [hi, hline_bang, lineBytes, hhash, hbh, Algorithm.noCells]
            rw [hpb_none]
            refine ⟨23 + 17 + 6 + 11 + 24, v, st', ?_, hdec,
              heapExtends_trans hext1 (heapExtends_trans hext12 hext3), har3, hasc3⟩
            rw [show 23 + 17 + 6 + 11 + 24 = (((23 + 17) + 6) + 11) + 24 by omega]
            rw [hpre51, hge2_step, h62_step]
            split_res_fuel 17
            step_drop 1
            rw [runJvmResFast_if_icmpne_fallthrough heq80]; norm_res_fuel
            step_drop 16
            rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
            rw [runJvmResFast_invokestatic_step
              (hs := stepStatic_parseBlockHeader_none_heap hlb hbh_data)]; norm_res_fuel
            rw [runJvmResFast_astore]; norm_res_fuel
            rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
            rw [runJvmResFast_ldcStr]; norm_res_fuel
            rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]
            norm_res_fuel
            rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
            rw [runJvmResFast_checkcast_objArray (hget := hout) (hcls := Or.inl rfl)]; norm_res_fuel
            rw [runJvmResFast_iconst]; norm_res_fuel
            rw [runJvmResFast_aaload (hget := hout) (hslt := by decide) (hlt := by simp)]
            norm_res_fuel
            rw [show (#[JvmVal.boxedInt 0][(0 : UInt32).toNat] : JvmVal) = .boxedInt 0 from rfl]
            rw [runJvmResFast_dup]; norm_res_fuel
            rw [runJvmResFast_ldcStr]; norm_res_fuel
            rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]
            norm_res_fuel
            rw [runJvmResFast_checkcast_boxedInt (hcls := Or.inl rfl)]; norm_res_fuel
            rw [runJvmResFast_invokevirtual_step (hs := stepVirtual_integer_intValue)]; norm_res_fuel
            rw [runJvmResFast_tableswitch]; dsimp only [Jvm.tableswitchTarget]; norm_res_fuel
            rw [show 23 + 17 - 17 = 23 by omega]; exact hun
          | some c =>
            have hbh_data : Algorithm.parseBlockHeader ⟨lineBytes.data⟩ = some c := hbh
            let innerAddr := jh1.objects.size
            let outerAddr := jh1.objects.size + 1
            let innerObj : Jvm.HeapObj AlgExt := .objArray "java/lang/Object"
              #[.boxedInt 0, .boxedInt c.x.toUInt32, .null, .null, .null, .boxedInt c.y.toUInt32]
            let outerObj : Jvm.HeapObj AlgExt := .objArray "java/lang/Object"
              #[.boxedInt 1, .heapRef innerAddr]
            let jh1a := (jh1.alloc innerObj).2
            let jh2 := (jh1a.alloc outerObj).2
            have hstat2 : jh2.statics = [] := hstat1
            have hext12 : HeapExtends jh1 jh2 :=
              heapExtends_trans (heapExtends_alloc jh1 innerObj) (heapExtends_alloc jh1a outerObj)
            have hin : jh2.get? innerAddr = some innerObj := by
              have hin1 : jh1a.get? innerAddr = some innerObj := by
                simp [jh1a, innerAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
              exact heapExtends_alloc jh1a outerObj _ _ hin1
            have hout : jh2.get? outerAddr = some outerObj := by
              have hsz : jh1a.objects.size = outerAddr := by simp [jh1a, outerAddr, Jvm.JvmHeap.alloc]
              rw [← hsz]; simp [jh2, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
            have hlb2 : jh2.get? lineBytesAddr = some (.byteArray lineBytes.data) :=
              hext12 _ _ hlb
            have hwget2 : jh2.get? wAddr = some (.objArray wCls wElems) := hext12 _ _ hwget1
            have hwfold2 := foldlM_decodeLife105Warning_mono hext12 wElems #[] warns hwfold1
            let locs3 := setLocal locs2 17 (.heapRef outerAddr)
            rcases parseBlocks_header_some lines numLines i limit outerAddr innerAddr lineBytesAddr
                wAddr cId c locs3 jh2 hp hout hin
                (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl0)
                (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl1)
                (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl2)
                (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl5)
                (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl11)
                (by dsimp only [locs3, locs2]; (repeat rw [setLocal_ne (by decide)]); exact hl12)
                (by dsimp only [locs3, locs2]; rw [setLocal_ne (by decide)]; rw [setLocal_self])
                (by dsimp only [locs3]; rw [setLocal_self]) with
              ⟨locs4, hhsome, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12⟩
            rcases ih lines numLines (i + 1) lineBytes lineBytesAddr limit 0 true c.x c.y 0
                warns wAddr wCls wElems cells cId locs4 jh2 hp
                hrem' hstat2 hlines31 hnum hutf8 hlb2 hwget2 hwfold2 hc
                q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 with
              ⟨fih, v, st', hih, hdec, hext3, har3, hasc3⟩
            have hpb_some :
                Algorithm.parseBlocks lines numLines i false bytes limit p hasBlock
                    blockX blockY rowIndex warns cells =
                  Algorithm.parseBlocks lines numLines (i + 1) false lineBytes limit 0 true
                    c.x c.y 0 warns cells := by
              rw [Algorithm.parseBlocks]
              simp [hi, hline_bang, lineBytes, hhash, hbh]
            rw [hpb_some]
            refine ⟨fih + 84 + 17 + 6 + 11 + 24, v, st', ?_, hdec,
              heapExtends_trans hext1 (heapExtends_trans hext12 hext3), har3, hasc3⟩
            rw [show fih + 84 + 17 + 6 + 11 + 24 = (((fih + 84) + 17) + 6 + 11) + 24 by omega]
            rw [hpre51, hge2_step, h62_step]
            split_res_fuel 17
            step_drop 1
            rw [runJvmResFast_if_icmpne_fallthrough heq80]; norm_res_fuel
            step_drop 16
            rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
            rw [runJvmResFast_invokestatic_step
              (hs := stepStatic_parseBlockHeader_some_heap hlb hbh_data)]; norm_res_fuel
            rw [runJvmResFast_astore]; norm_res_fuel
            rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
            rw [runJvmResFast_ldcStr]; norm_res_fuel
            rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]
            norm_res_fuel
            rw [runJvmResFast_aload, setLocal_self]; norm_res_fuel
            rw [runJvmResFast_checkcast_objArray (hget := hout) (hcls := Or.inl rfl)]; norm_res_fuel
            rw [runJvmResFast_iconst]; norm_res_fuel
            rw [runJvmResFast_aaload (hget := hout) (hslt := by decide) (hlt := by simp)]
            norm_res_fuel
            rw [show (#[JvmVal.boxedInt 1, .heapRef innerAddr][(0 : UInt32).toNat] : JvmVal) =
              .boxedInt 1 from rfl]
            rw [runJvmResFast_dup]; norm_res_fuel
            rw [runJvmResFast_ldcStr]; norm_res_fuel
            rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]
            norm_res_fuel
            rw [runJvmResFast_checkcast_boxedInt (hcls := Or.inl rfl)]; norm_res_fuel
            rw [runJvmResFast_invokevirtual_step (hs := stepVirtual_integer_intValue)]; norm_res_fuel
            rw [runJvmResFast_tableswitch]
            rw [show Jvm.tableswitchTarget 1 0 [85, 108] 200 = 108 from by decide]
            rw [show fih + 84 + 17 - 17 = fih + 84 by omega]
            change runJvmResFast (fih + 84) f_Algorithm_parseBlocks_prog 108
                (f_Algorithm_parseBlocks_prog.drop 108) ⟨108, [], locs3, jh2, hp⟩ = some (v, st')
            rw [hhsome fih, hih]
        · have hne80 : (UInt32.ofBitVec (b1.toBitVec.signExtend 32) == 80) = false :=
            signExtend_bne_u32 hb1 rfl (by decide)
          have hnhash : Algorithm.startsWithHash lineBytes 80 = false := by
            have h1_bang : lineBytes.get! 1 = b1 := by
              simp [ByteArray.get!, getElem!_pos lineBytes.data 1 (by omega), b1]
            simp only [Algorithm.startsWithHash, h1_bang, beq_false_of_ne hb1, Bool.and_false]
          rcases h206 hnhash with ⟨f206, v, st', hrun206, hdec, hext2, har2, hasc2⟩
          refine ⟨f206 + 1 + 6 + 11 + 24, v, st', ?_, hdec, heapExtends_trans hext1 hext2,
            har2, hasc2⟩
          rw [show f206 + 1 + 6 + 11 + 24 = (((f206 + 1) + 6) + 11) + 24 by omega]
          rw [hpre51, hge2_step, h62_step]
          split_res_fuel 1
          step_drop 1
          rw [runJvmResFast_if_icmpne_branch hne80]
          rw [show f206 + 1 - 1 = f206 by omega]; exact hrun206
      · have hne35 : (UInt32.ofBitVec (b0.toBitVec.signExtend 32) == 35) = false :=
          signExtend_bne_u32 hb0 rfl (by decide)
        have hnhash : Algorithm.startsWithHash lineBytes 80 = false := by
          have h0_bang : lineBytes.get! 0 = b0 := by
            simp [ByteArray.get!, getElem!_pos lineBytes.data 0 (by omega), b0]
          simp only [Algorithm.startsWithHash, h0_bang, beq_false_of_ne hb0, Bool.and_false,
            Bool.false_and]
        rcases h206 hnhash with ⟨f206, v, st', hrun206, hdec, hext2, har2, hasc2⟩
        refine ⟨f206 + 1 + 11 + 24, v, st', ?_, hdec, heapExtends_trans hext1 hext2, har2, hasc2⟩
        rw [show f206 + 1 + 11 + 24 = ((f206 + 1) + 11) + 24 by omega, hpre51, hge2_step]
        split_res_fuel 1
        step_drop 1
        rw [runJvmResFast_if_icmpne_branch hne35]
        rw [show f206 + 1 - 1 = f206 by omega]; exact hrun206

theorem parseBlocks_equiv
    (lines : Array String) (numLines i : UInt32) (inRow : Bool)
    (bytes : ByteArray) (bytesAddr : Nat) (limit p : UInt32)
    (hasBlock : Bool) (blockX blockY rowIndex : Int32)
    (warns : Array Algorithm.Life105Warning) (wAddr : Nat) (wCls : String) (wElems : Array JvmVal)
    (cells : Algorithm.U64Buf) (cId : Nat)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = [])
    (hlines31 : lines.size < 2 ^ 31)
    (hnum : numLines.toNat ≤ lines.size)
    (hutf8 : ∀ k < lines.size, lines[k]!.toUTF8.data.size < 2 ^ 31)
    (hlim : inRow = true → limit.toNat ≤ bytes.data.size ∧ limit.toNat < 2 ^ 31)
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hwget : jh.get? wAddr = some (.objArray wCls wElems))
    (hwfold : wElems.foldlM (fun acc v => (decodeLife105Warning jh v).map acc.push) #[] =
      some warns)
    (hc : hp.u64Arrays[cId]? = some cells)
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines) (hl2 : locs 2 = .i32 i)
    (hl3 : locs 3 = .i32 (if inRow then 1 else 0)) (hl4 : locs 4 = .heapRef bytesAddr)
    (hl5 : locs 5 = .i32 limit) (hl6 : locs 6 = .i32 p)
    (hl7 : locs 7 = .i32 (if hasBlock then 1 else 0)) (hl8 : locs 8 = .i32 blockX.toUInt32)
    (hl9 : locs 9 = .i32 blockY.toUInt32) (hl10 : locs 10 = .i32 rowIndex.toUInt32)
    (hl11 : locs 11 = .heapRef wAddr) (hl12 : locs 12 = .ext (.u64Ref cId)) :
    ∃ f v st',
      runJvmRes f f_Algorithm_parseBlocks_prog ⟨0, [], locs, jh, hp⟩ = some (v, st') ∧
      decodeLife105Result st' v =
        some (Algorithm.parseBlocks lines numLines i inRow bytes limit p hasBlock
          blockX blockY rowIndex warns cells) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.heap.arenas = hp.arenas ∧ st'.heap.asciiArrays = hp.asciiArrays := by
  have hpre12 : ∀ fRest,
      runJvmResFast (fRest + 12) f_Algorithm_parseBlocks_prog 0
          (f_Algorithm_parseBlocks_prog.drop 0) ⟨0, [], locs, jh, hp⟩ =
        runJvmResFast fRest f_Algorithm_parseBlocks_prog 12
          (f_Algorithm_parseBlocks_prog.drop 12) ⟨12, [], locs, jh, hp⟩ := by
    intro fRest
    split_res_fuel 12
    step_drop 12
    rw [runJvmResFast_aload, hl0]; norm_res_fuel
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNullParameter_heap rfl)]; norm_res_fuel
    rw [runJvmResFast_aload, hl4]; norm_res_fuel
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNullParameter_heap rfl)]; norm_res_fuel
    rw [runJvmResFast_aload, hl11]; norm_res_fuel
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNullParameter_heap rfl)]; norm_res_fuel
    rw [runJvmResFast_aload, hl12]; norm_res_fuel
    rw [runJvmResFast_ldcStr]; norm_res_fuel
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNullParameter_heap rfl)]; norm_res_fuel
    rw [Nat.add_sub_cancel]
  cases inRow with
  | false =>
    rcases parseBlocks_loop (numLines.toNat - i.toNat) lines numLines i bytes bytesAddr limit p
        hasBlock blockX blockY rowIndex warns wAddr wCls wElems cells cId locs jh hp
        rfl hstat hlines31 hnum hutf8 hbytes hwget hwfold hc
        hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 with
      ⟨floop, v, st', hrun, hdec, hext, har, hasc⟩
    refine ⟨floop + 12, v, st', ?_, hdec, hext, har, hasc⟩
    apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
    change runJvmResFast (floop + 12) f_Algorithm_parseBlocks_prog 0
        (f_Algorithm_parseBlocks_prog.drop 0) ⟨0, [], locs, jh, hp⟩ = _
    rw [hpre12 floop]
    exact hrun
  | true =>
    by_cases hi : i < numLines
    · rcases hlim rfl with ⟨hlim1, hlim31⟩
      rcases parseBlocks_inRow_drain (limit.toNat - p.toNat) lines numLines i bytes bytesAddr
          limit p hasBlock blockX blockY rowIndex warns wAddr cId cells locs jh hp
          rfl hi hlim1 hlim31 hbytes hc
          hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 with
        ⟨kdr, cId', cells', hp', locs', hdr, hc', har', hasc',
          r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, hpb_dr⟩
      rcases parseBlocks_loop (numLines.toNat - (i + 1).toNat) lines numLines (i + 1)
          bytes bytesAddr limit 0 hasBlock blockX blockY (rowIndex + 1) warns wAddr wCls wElems
          cells' cId' locs' jh hp' rfl hstat hlines31 hnum hutf8 hbytes hwget hwfold hc'
          r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 with
        ⟨floop, v, st', hrun, hdec, hext, har, hasc⟩
      refine ⟨floop + kdr + 12, v, st', ?_, ?_, hext, har' ▸ har, hasc' ▸ hasc⟩
      · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
        rw [show floop + kdr + 12 = (floop + kdr) + 12 by omega]
        change runJvmResFast ((floop + kdr) + 12) f_Algorithm_parseBlocks_prog 0
            (f_Algorithm_parseBlocks_prog.drop 0) ⟨0, [], locs, jh, hp⟩ = _
        rw [hpre12 (floop + kdr), hdr floop]
        exact hrun
      · rw [hpb_dr]; exact hdec
    · have hpb : Algorithm.parseBlocks lines numLines i true bytes limit p hasBlock
          blockX blockY rowIndex warns cells = ⟨.ok, warns, Algorithm.U64Buf.toArray cells⟩ := by
        rw [Algorithm.parseBlocks]; simp [hi]
      rw [hpb]
      let locs1 := setLocal (setLocal locs 13 (.i32 0)) 14 .null
      rcases parseBlocks_exit_ok wAddr cId wCls wElems warns cells locs1 jh hp hstat hwget hwfold hc
          (by dsimp only [locs1]; (repeat rw [setLocal_ne (by decide)]); exact hl11)
          (by dsimp only [locs1]; (repeat rw [setLocal_ne (by decide)]); exact hl12) with
        ⟨v, st', hexit, hdec, hext, har, hasc⟩
      refine ⟨24 + 12, v, st', ?_, hdec, hext, har, hasc⟩
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      change runJvmResFast (24 + 12) f_Algorithm_parseBlocks_prog 0
          (f_Algorithm_parseBlocks_prog.drop 0) ⟨0, [], locs, jh, hp⟩ = _
      rw [hpre12 24]
      split_res_fuel 10
      step_drop 4
      rw [runJvmResFast_iload, hl2]; norm_res_fuel
      rw [runJvmResFast_iload, hl1]; norm_res_fuel
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_intCompareUnsigned_i32)]; norm_res_fuel
      rw [runJvmResFast_ifge_branch (by
        rw [compareUnsigned_sle_cond]; exact decide_eq_true hi)]; norm_res_fuel
      step_drop 6
      rw [runJvmResFast_iconst]; norm_res_fuel
      rw [runJvmResFast_istore]; norm_res_fuel
      rw [runJvmResFast_aconstNull]; norm_res_fuel
      rw [runJvmResFast_astore]; norm_res_fuel
      rw [runJvmResFast_iload, setLocal_ne (by decide), setLocal_self]; norm_res_fuel
      rw [runJvmResFast_ifne_fallthrough]; norm_res_fuel
      rw [show 24 - 10 = 14 by rfl]
      exact hexit

end ParseBlocks

section DeserializeLife105

private theorem heapExtends_encodeLife105Result_tail
    (h1 : Jvm.JvmHeap AlgExt) (ws : Array Algorithm.Life105Warning)
    (statusVal : JvmVal) (cId : Nat) :
    let step : Array JvmVal × Jvm.JvmHeap AlgExt → Algorithm.Life105Warning →
        Array JvmVal × Jvm.JvmHeap AlgExt :=
      fun (a, ch) w => let (wv, nh) := encodeLife105Warning ch w; (a.push wv, nh)
    let p2 := ws.foldl step (#[], h1)
    let p3 := p2.2.alloc (.objArray "java/lang/Object" p2.1)
    let p4 := p3.2.alloc (.instance "com/alexvanyo/composelife/model/Life105Result"
      [("status", statusVal), ("warnings", .heapRef p3.1), ("cells", .ext (.u64Ref cId))])
    HeapExtends h1 p4.2 := by
  dsimp only
  let step : Array JvmVal × Jvm.JvmHeap AlgExt → Algorithm.Life105Warning →
      Array JvmVal × Jvm.JvmHeap AlgExt :=
    fun (a, ch) w => let (wv, nh) := encodeLife105Warning ch w; (a.push wv, nh)
  have hfold := encodeLife105Warnings_foldl_spec ws.toList #[] h1 #[] rfl
  have hext2 : HeapExtends h1 (ws.foldl step (#[], h1)).2 := by
    rw [← Array.foldl_toList step]; exact hfold.1
  exact heapExtends_trans hext2 (heapExtends_trans (heapExtends_alloc _ _) (heapExtends_alloc _ _))

private theorem heapExtends_encodeLife105Result
    (jh : Jvm.JvmHeap AlgExt) (u64s : List (Array UInt64)) (res : Algorithm.Life105Result) :
    HeapExtends jh (encodeLife105Result jh u64s res).2.1 := by
  rcases res with ⟨st, ws, cells⟩
  dsimp only [encodeLife105Result]
  cases st with
  | ok =>
    exact heapExtends_encodeLife105Result_tail jh ws
      (.allocRef "com/alexvanyo/composelife/model/Life105Status$Ok") u64s.length
  | ruleNotSupported =>
    exact heapExtends_encodeLife105Result_tail jh ws
      (.allocRef "com/alexvanyo/composelife/model/Life105Status$RuleNotSupported") u64s.length
  | invalidHeader line =>
    let p := jh.alloc
      (.instance "com/alexvanyo/composelife/model/Life105Status$InvalidHeader" [("line", .str line)])
    exact heapExtends_trans (heapExtends_alloc jh _)
      (heapExtends_encodeLife105Result_tail p.2 ws (.heapRef p.1) u64s.length)
  | unexpectedInput inp ln col =>
    let p := jh.alloc
      (.instance "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput"
        [("input", .str inp), ("lineIndex", .i32 ln), ("columnIndex", .i32 col)])
    exact heapExtends_trans (heapExtends_alloc jh _)
      (heapExtends_encodeLife105Result_tail p.2 ws (.heapRef p.1) u64s.length)

private theorem compareUnsigned_ifle_cond (a b : UInt32) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.sle 0#32 =
      decide (a ≤ b) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b
    · have hle : a ≤ b := UInt32.le_of_lt h2
      simp [h1, h2, hle]
    · have hnle : ¬(a ≤ b) := by
        intro hle
        rw [UInt32.le_iff_toNat_le] at hle
        rw [UInt32.lt_iff_toNat_lt] at h2
        have hne : a.toNat ≠ b.toNat := by
          intro heq
          apply h1; apply beq_iff_eq.mpr
          apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq; exact heq
        omega
      simp [h1, h2, hnle]

private theorem stepStatic_closed2_105_heap
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "Life105LeanKt" "f_Algorithm_deserializeLife105___closed__2"
      "()Lcom/alexvanyo/composelife/model/Life105Result;" =
      let r := encodeLife105Result jh u64 ⟨.ok, #[], #[]⟩
      .inl (some ⟨pc + 1, r.1 :: rest, locs, r.2.1, ⟨ar, r.2.2, asc⟩⟩) := rfl

private theorem stepStatic_closed3_105_heap
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "Life105LeanKt" "f_Algorithm_deserializeLife105___closed__3"
      "()Lcom/alexvanyo/composelife/model/Life105Result;" =
      let r := encodeLife105Result jh u64 ⟨.ruleNotSupported, #[], #[]⟩
      .inl (some ⟨pc + 1, r.1 :: rest, locs, r.2.1, ⟨ar, r.2.2, asc⟩⟩) := rfl

private theorem stepStatic_closed6_105_heap
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "Life105LeanKt" "f_Algorithm_deserializeLife105___closed__6"
      "()Lcom/alexvanyo/composelife/model/Life105Result;" =
      let r := encodeLife105Result jh u64 ⟨.ok, #[.emptyFile], #[]⟩
      .inl (some ⟨pc + 1, r.1 :: rest, locs, r.2.1, ⟨ar, r.2.2, asc⟩⟩) := rfl

private theorem stepStatic_u64BufEmpty_105_heap
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} :
    stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "Life105LeanKt" "f_Algorithm_U64Buf_empty" "()[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref u64.length) :: rest, locs, jh,
        ⟨ar, u64 ++ [Algorithm.U64Buf.empty], asc⟩⟩) := rfl

private theorem stepStatic_intrinsicsAreEqual_str
    {pc : Nat} {a b : String} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .str b :: .str a :: rest, locs, jh, hp⟩
      "kotlin/jvm/internal/Intrinsics" "areEqual" "(Ljava/lang/Object;Ljava/lang/Object;)Z" =
      .inl (some ⟨pc + 1, .bool (a == b) :: rest, locs, jh, hp⟩) := rfl

private theorem stepSpecial_life105InvalidHeader_init
    {pc : Nat} {line : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, line ::
        .allocRef "com/alexvanyo/composelife/model/Life105Status$InvalidHeader" ::
        .allocRef "com/alexvanyo/composelife/model/Life105Status$InvalidHeader" :: rest,
        locs, jh, hp⟩
      "com/alexvanyo/composelife/model/Life105Status$InvalidHeader" "<init>" "(Ljava/lang/String;)V" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.instance "com/alexvanyo/composelife/model/Life105Status$InvalidHeader"
          [("line", line)])).2, hp⟩) := rfl

private theorem stepSpecial_life105WarningUnexpectedInput_init
    {pc : Nat} {marker col lineNum input : JvmVal} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, marker :: col :: lineNum :: input ::
        .allocRef "com/alexvanyo/composelife/model/Life105Warning$UnexpectedInput" ::
        .allocRef "com/alexvanyo/composelife/model/Life105Warning$UnexpectedInput" :: rest,
        locs, jh, hp⟩
      "com/alexvanyo/composelife/model/Life105Warning$UnexpectedInput" "<init>"
      "(Ljava/lang/String;IILkotlin/jvm/internal/DefaultConstructorMarker;)V" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.instance "com/alexvanyo/composelife/model/Life105Warning$UnexpectedInput"
          [("input", input), ("lineIndex", lineNum), ("columnIndex", col)])).2, hp⟩) := rfl

private theorem stepStatic_skipDescriptions_heap
    {pc : Nat} {i numLines : UInt32} {lines : Array String} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i32 i :: .i32 numLines :: .strArr lines :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_skipDescriptions-BltQuoY" "([Ljava/lang/Object;II)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.skipDescriptions lines numLines i) :: rest,
        locs, jh, hp⟩) := rfl

private theorem stepStatic_checkRuleLine_heap
    {pc addr : Nat} {elems : Array UInt8} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_checkRuleLine" "([B)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.checkRuleLine ⟨elems⟩) :: rest, locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩
      "Life105LeanKt" "f_Algorithm_checkRuleLine" "([B)I" =
      match decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) with
      | some bytes =>
        .inl (some ⟨pc + 1, .i32 (Algorithm.checkRuleLine bytes) :: rest, locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn]
  have hd : decodeBytes ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) =
      some ⟨elems⟩ := by
    simp [decodeBytes, hget]
  rw [hd]

private theorem stepStatic_parseBlocks_match (pc : Nat) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (cId : Nat)
    (warnsVal rowIdx blockY blockX hasBlock p limit bytesVal inRow i numLines linesVal : JvmVal)
    (rest : List JvmVal) :
    let st : JvmState :=
      ⟨pc, .ext (.u64Ref cId) :: warnsVal :: rowIdx :: blockY :: blockX ::
        hasBlock :: p :: limit :: bytesVal :: inRow :: i :: numLines :: linesVal :: rest,
        locs, jh, hp⟩
    stepInvokeStatic st "Life105LeanKt" "f_Algorithm_parseBlocks-eSeeRns"
      ("([Ljava/lang/Object;IIZ[BIIZIII[Ljava/lang/Object;[J)" ++
        "Lcom/alexvanyo/composelife/model/Life105Result;") =
    match decodeStrArray st linesVal, decodeBytes st bytesVal, st.heap.u64Arrays[cId]? with
    | some lines', some bytes', some cells' =>
      let warnsOpt : Option (Array Algorithm.Life105Warning) := match warnsVal with
        | .strArr #[] => some #[]
        | .heapRef wAddr =>
          match st.jvmHeap.get? wAddr with
          | some (.objArray _ elems) =>
            elems.foldlM (fun acc v => (decodeLife105Warning st.jvmHeap v).map acc.push) #[]
          | _ => none
        | _ => none
      match warnsOpt with
      | some warns' =>
        let res := Algorithm.parseBlocks lines' numLines.asI32 i.asI32 (inRow.asI32 != 0) bytes'
          limit.asI32 p.asI32 (hasBlock.asI32 != 0) blockX.asI32.toInt32 blockY.asI32.toInt32
          rowIdx.asI32.toInt32 warns' cells'
        let (resVal, h', u64s') := encodeLife105Result st.jvmHeap st.heap.u64Arrays res
        .inl (some { st with
          pc := st.pc + 1, stack := resVal :: rest,
          jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } })
      | none => .inr none
    | _, _, _ => .inr none := by
  intro st; rfl

private theorem l105_match_elim
    (pc : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (hp : AlgHeap) (cId : Nat)
    (warnsVal rowIdx blockY blockX hasBlock p limit bytesVal inRow i numLines linesVal : JvmVal)
    (rest : List JvmVal)
    (pbFn : Array String → UInt32 → UInt32 → Bool → ByteArray → UInt32 → UInt32 → Bool →
      Int32 → Int32 → Int32 → Array Algorithm.Life105Warning → Algorithm.U64Buf →
      Algorithm.Life105Result)
    (encFn : Jvm.JvmHeap AlgExt → List (Array UInt64) → Algorithm.Life105Result →
      JvmVal × Jvm.JvmHeap AlgExt × List (Array UInt64))
    {a1 : Option (Array String)} {b1 : Option ByteArray} {c1 : Option (Array UInt64)}
    {w1 : Option (Array Algorithm.Life105Warning)}
    {a2 : Array String} {b2 : ByteArray} {c2 : Array UInt64}
    {w2 : Array Algorithm.Life105Warning}
    (ha : a1 = some a2) (hb : b1 = some b2) (hc : c1 = some c2) (hw : w1 = some w2) :
    let st : JvmState :=
      ⟨pc, .ext (.u64Ref cId) :: warnsVal :: rowIdx :: blockY :: blockX ::
        hasBlock :: p :: limit :: bytesVal :: inRow :: i :: numLines :: linesVal :: rest,
        locs, jh, hp⟩
    (stepStatic_parseBlocks_match.match_3 (fun _ _ _ => Option JvmState ⊕ Option JvmVal)
      a1 b1 c1
      (fun lines' bytes' cells' =>
        have warnsOpt := w1
        stepStatic_parseBlocks_match.match_2 (fun _ => Option JvmState ⊕ Option JvmVal) warnsOpt
          (fun warns' =>
            let res := pbFn lines' numLines.asI32 i.asI32 (inRow.asI32 != 0) bytes'
              limit.asI32 p.asI32 (hasBlock.asI32 != 0) blockX.asI32.toInt32 blockY.asI32.toInt32
              rowIdx.asI32.toInt32 warns' cells'
            decodeLife105Result_encode.match_1 (fun _ => Option JvmState ⊕ Option JvmVal)
              (encFn st.jvmHeap st.heap.u64Arrays res) fun resVal h' u64s' =>
              .inl (some { st with
                pc := st.pc + 1, stack := resVal :: rest,
                jvmHeap := h', heap := { st.heap with u64Arrays := u64s' } }))
          (fun _ => .inr none))
      (fun _ _ _ => .inr none)) =
    (.inl (some ⟨pc + 1,
      (encFn jh hp.u64Arrays (pbFn a2 numLines.asI32 i.asI32 (inRow.asI32 != 0) b2
        limit.asI32 p.asI32 (hasBlock.asI32 != 0) blockX.asI32.toInt32 blockY.asI32.toInt32
        rowIdx.asI32.toInt32 w2 c2)).1 :: rest,
      locs,
      (encFn jh hp.u64Arrays (pbFn a2 numLines.asI32 i.asI32 (inRow.asI32 != 0) b2
        limit.asI32 p.asI32 (hasBlock.asI32 != 0) blockX.asI32.toInt32 blockY.asI32.toInt32
        rowIdx.asI32.toInt32 w2 c2)).2.1,
      { arenas := hp.arenas,
        u64Arrays := (encFn jh hp.u64Arrays (pbFn a2 numLines.asI32 i.asI32
          (inRow.asI32 != 0) b2 limit.asI32 p.asI32 (hasBlock.asI32 != 0)
          blockX.asI32.toInt32 blockY.asI32.toInt32 rowIdx.asI32.toInt32 w2 c2)).2.2,
        asciiArrays := hp.asciiArrays }⟩) : Option JvmState ⊕ Option JvmVal) := by
  subst ha hb hc hw
  dsimp only

private theorem l105_enc_state_congr
    (pc : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64))
    (asc : List Algorithm.AsciiBytes) (rest : List JvmVal)
    (encFn : Jvm.JvmHeap AlgExt → List (Array UInt64) → Algorithm.Life105Result →
      JvmVal × Jvm.JvmHeap AlgExt × List (Array UInt64))
    (r1 r2 : Algorithm.Life105Result) (hr : r1 = r2) :
    (.inl (some ⟨pc + 1, (encFn jh u64 r1).1 :: rest, locs, (encFn jh u64 r1).2.1,
      ⟨ar, (encFn jh u64 r1).2.2, asc⟩⟩) : Option JvmState ⊕ Option JvmVal) =
    (.inl (some ⟨pc + 1, (encFn jh u64 r2).1 :: rest, locs, (encFn jh u64 r2).2.1,
      ⟨ar, (encFn jh u64 r2).2.2, asc⟩⟩) : Option JvmState ⊕ Option JvmVal) := by
  subst hr
  rfl

private theorem stepStatic_parseBlocks_heap
    {pc bytesAddr wAddr cId : Nat} {lines : Array String}
    {numLines i limit p : UInt32}
    {bytes : ByteArray} {wCls : String} {wElems : Array JvmVal}
    {warns : Array Algorithm.Life105Warning} {cells : Algorithm.U64Buf}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)}
    {asc : List Algorithm.AsciiBytes}
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hwget : jh.get? wAddr = some (.objArray wCls wElems))
    (hwfold : wElems.foldlM (fun acc v => (decodeLife105Warning jh v).map acc.push) #[] =
      some warns)
    (hc : u64[cId]? = some cells) :
    stepInvokeStatic
        ⟨pc, .ext (.u64Ref cId) :: .heapRef wAddr :: .i32 0 :: .i32 0 :: .i32 0 ::
          .i32 0 :: .i32 p :: .i32 limit :: .heapRef bytesAddr ::
          .i32 0 :: .i32 i :: .i32 numLines :: .strArr lines :: rest,
          locs, jh, ⟨ar, u64, asc⟩⟩
      "Life105LeanKt" "f_Algorithm_parseBlocks-eSeeRns"
      ("([Ljava/lang/Object;IIZ[BIIZIII[Ljava/lang/Object;[J)" ++
        "Lcom/alexvanyo/composelife/model/Life105Result;") =
      .inl (some ⟨pc + 1,
        (encodeLife105Result jh u64 (Algorithm.parseBlocks lines numLines i false bytes
          limit p false 0 0 0 warns cells)).1 :: rest,
        locs,
        (encodeLife105Result jh u64 (Algorithm.parseBlocks lines numLines i false bytes
          limit p false 0 0 0 warns cells)).2.1,
        ⟨ar,
         (encodeLife105Result jh u64 (Algorithm.parseBlocks lines numLines i false bytes
           limit p false 0 0 0 warns cells)).2.2,
         asc⟩⟩) := by
  have hl : decodeStrArray
      ⟨pc, .ext (.u64Ref cId) :: .heapRef wAddr :: .i32 0 :: .i32 0 :: .i32 0 ::
        .i32 0 :: .i32 p :: .i32 limit :: .heapRef bytesAddr ::
        .i32 0 :: .i32 i :: .i32 numLines :: .strArr lines :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩ (.strArr lines) = some lines := rfl
  have hb : decodeBytes
      ⟨pc, .ext (.u64Ref cId) :: .heapRef wAddr :: .i32 0 :: .i32 0 :: .i32 0 ::
        .i32 0 :: .i32 p :: .i32 limit :: .heapRef bytesAddr ::
        .i32 0 :: .i32 i :: .i32 numLines :: .strArr lines :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩ (.heapRef bytesAddr) = some bytes := by
    simp [decodeBytes, hbytes]
  have hw : stepStatic_parseBlocks_match.match_1
      (fun _ => Option (Array Algorithm.Life105Warning))
      (.heapRef wAddr)
      (fun _ => some #[])
      (fun wAddr =>
        decodeLife105Result.match_1 (fun _ => Option (Array Algorithm.Life105Warning))
          (jh.get? wAddr)
          (fun _ elems => elems.foldlM
            (fun acc v => (decodeLife105Warning jh v).map acc.push) #[])
          (fun _ => none))
      (fun _ => none) = some warns := by
    dsimp only
    rw [hwget]
    exact hwfold
  have h1 := stepStatic_parseBlocks_match pc locs jh ⟨ar, u64, asc⟩ cId
    (.heapRef wAddr) (.i32 0) (.i32 0) (.i32 0) (.i32 0) (.i32 p) (.i32 limit)
    (.heapRef bytesAddr) (.i32 0) (.i32 i) (.i32 numLines) (.strArr lines) rest
  have h2 := l105_match_elim pc locs jh ⟨ar, u64, asc⟩ cId
    (.heapRef wAddr) (.i32 0) (.i32 0) (.i32 0) (.i32 0) (.i32 p) (.i32 limit)
    (.heapRef bytesAddr) (.i32 0) (.i32 i) (.i32 numLines) (.strArr lines) rest
    Algorithm.parseBlocks encodeLife105Result hl hb hc hw
  have harg : Algorithm.parseBlocks lines (JvmVal.i32 numLines : JvmVal).asI32
      (JvmVal.i32 i : JvmVal).asI32 ((JvmVal.i32 0 : JvmVal).asI32 != 0) bytes
      (JvmVal.i32 limit : JvmVal).asI32 (JvmVal.i32 p : JvmVal).asI32
      ((JvmVal.i32 0 : JvmVal).asI32 != 0) (JvmVal.i32 0 : JvmVal).asI32.toInt32
      (JvmVal.i32 0 : JvmVal).asI32.toInt32 (JvmVal.i32 0 : JvmVal).asI32.toInt32
      warns cells =
      Algorithm.parseBlocks lines numLines i false bytes limit p false
        0 0 0 warns cells := by
    dsimp only [Jvm.JvmVal.asI32]
    rw [show ((0 : UInt32) != 0) = false from rfl,
      show (0 : UInt32).toInt32 = 0 from by
        rw [show (0 : UInt32) = (0 : Int32).toUInt32 from rfl, Int32.toInt32_toUInt32]]
  have h3 := l105_enc_state_congr pc locs jh ar u64 asc rest encodeLife105Result _ _ harg
  exact Eq.trans (Eq.trans h1 h2) h3

private theorem decodeLife105Result_encode_proj
    (pc1 : Nat) (st1 : List JvmVal) (locs1 : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (res : Algorithm.Life105Result) :
    decodeLife105Result
        ⟨pc1, st1, locs1, (encodeLife105Result jh u64 res).2.1,
          ⟨ar, (encodeLife105Result jh u64 res).2.2, asc⟩⟩
        (encodeLife105Result jh u64 res).1 =
      some res := by
  have h := decodeLife105Result_encode jh ⟨ar, u64, asc⟩ res
  rcases he : encodeLife105Result jh u64 res with ⟨a, b, c⟩
  dsimp only at h
  rw [he] at h
  dsimp only [decodeLife105Result] at h ⊢
  exact h

private theorem l105_equiv_finish
    {fuel : Nat} {prog : List JvmInstr} {pc0 pc1 : Nat} {st0 : List JvmVal}
    {locs0 locs1 : Nat → JvmVal}
    {jh0 jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 u64a : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (res : Algorithm.Life105Result)
    (hext : HeapExtends jh0 jh)
    (hrun : runJvmResFast fuel prog pc0 (prog.drop pc0) ⟨pc0, st0, locs0, jh0, ⟨ar, u64, asc⟩⟩ =
      some ((encodeLife105Result jh u64a res).1,
        ⟨pc1, [(encodeLife105Result jh u64a res).1], locs1,
          (encodeLife105Result jh u64a res).2.1,
          ⟨ar, (encodeLife105Result jh u64a res).2.2, asc⟩⟩)) :
    ∃ v st',
      runJvmResFast fuel prog pc0 (prog.drop pc0) ⟨pc0, st0, locs0, jh0, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeLife105Result st' v = some res ∧
      HeapExtends jh0 st'.jvmHeap ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc :=
  ⟨(encodeLife105Result jh u64a res).1,
    ⟨pc1, [(encodeLife105Result jh u64a res).1], locs1,
      (encodeLife105Result jh u64a res).2.1,
      ⟨ar, (encodeLife105Result jh u64a res).2.2, asc⟩⟩,
    hrun,
    decodeLife105Result_encode_proj pc1 [(encodeLife105Result jh u64a res).1] locs1
      jh ar u64a asc res,
    heapExtends_trans hext (heapExtends_encodeLife105Result jh u64a res), rfl, rfl⟩

private theorem runJvmResFast_areturn {f1 : Nat} {prog : List JvmInstr} {pc pc0 : Nat}
    {v : JvmVal} {s : List JvmVal} {rest : List JvmInstr}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f1 + 1) prog pc (.areturn :: rest) ⟨pc0, v :: s, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: s, locs, jh, hp⟩) := by
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  rfl

private theorem deserializeLife105_exit247
    {lines : Array String} {numLines i : UInt32} {bytes : ByteArray}
    {bytesAddr wAddr : Nat} {wCls : String} {wElems : Array JvmVal}
    {warns : Array Algorithm.Life105Warning}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)}
    {asc : List Algorithm.AsciiBytes}
    (hbytes : jh.get? bytesAddr = some (.byteArray bytes.data))
    (hwget : jh.get? wAddr = some (.objArray wCls wElems))
    (hwfold : wElems.foldlM (fun acc v => (decodeLife105Warning jh v).map acc.push) #[] = some warns)
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines)
    (hl4 : locs 4 = .i32 i) (hl6 : locs 6 = .heapRef bytesAddr)
    (hl7 : locs 7 = .heapRef wAddr) :
    ∃ v st',
      runJvmResFast 22 f_Algorithm_deserializeLife105_prog 247
          (f_Algorithm_deserializeLife105_prog.drop 247) ⟨247, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeLife105Result st' v =
        some (Algorithm.parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0 warns
          Algorithm.U64Buf.empty) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  let u64a := u64 ++ [Algorithm.U64Buf.empty]
  have hc : u64a[u64.length]? = some Algorithm.U64Buf.empty := by simp [u64a]
  apply l105_equiv_finish (u64a := u64a)
    (locs1 := setLocal (setLocal locs 8 (.i32 (i + 1))) 9 (.ext (.u64Ref u64.length)))
    (pc1 := 268) _ (heapExtends_refl jh)
  split_res_fuel 22
  conv => lhs; jvm_whnf_run_args
  heap_step_nonbranch_chunks
  conv => lhs; jvm_whnf_run_args
  rw [runJvmResFast_invokestatic_step (hs := stepStatic_u64BufEmpty_105_heap)]
  heap_step_nonbranch_chunks
  conv => lhs; jvm_whnf_run_args
  conv => lhs; arg 5; arg 2; rw [hl0, hl1, hl4, hl6, hl7]; dsimp only [Jvm.JvmVal.asI32]
  conv => lhs; arg 5; arg 3; rw [hl4]; dsimp only [Jvm.JvmVal.asI32]
  have hs := stepStatic_parseBlocks_heap (pc := 267) (lines := lines) (limit := 0) (p := 0)
    (numLines := numLines) (i := i + 1) (rest := [])
    (locs := setLocal (setLocal locs 8 (.i32 (i + 1))) 9 (.ext (.u64Ref u64.length)))
    (ar := ar) (asc := asc) hbytes hwget hwfold hc
  refine Eq.trans (runJvmResFast_invokestatic_step (hs := hs)) ?_
  exact runJvmResFast_areturn

private theorem deserializeLife105_0_8
    {lines : Array String} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)}
    {asc : List Algorithm.AsciiBytes} (hl0 : locs 0 = .strArr lines) (fRest : Nat) :
    runJvmResFast (fRest + 8) f_Algorithm_deserializeLife105_prog 0
        (f_Algorithm_deserializeLife105_prog.drop 0) ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast fRest f_Algorithm_deserializeLife105_prog 8
        (f_Algorithm_deserializeLife105_prog.drop 8)
        ⟨8, [.i32 lines.size.toUInt32], setLocal locs 1 (.i32 lines.size.toUInt32),
          jh, ⟨ar, u64, asc⟩⟩ := by
  split_res_fuel 8
  heap_step_nonbranch_chunks; rw [hl0]
  rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNullParameter_heap rfl)]
  heap_step_nonbranch_chunks; rw [hl0, runJvmResFast_arraylength_strArr]
  heap_step_nonbranch_chunks
  rw [← runJvmResFast_stepResHeapChunk, Nat.add_sub_cancel]; rfl

private theorem deserializeLife105_8_21
    {lines : Array String} {numLines : UInt32} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (h0 : numLines ≠ 0) (hpos : 0 < lines.size) (hl0 : locs 0 = .strArr lines) (fRest : Nat) :
    let header := lines[0]
    let locs2 := setLocal (setLocal locs 2 (.str header)) 3 (.str "#Life 1.05")
    runJvmResFast (fRest + 13) f_Algorithm_deserializeLife105_prog 8
        (f_Algorithm_deserializeLife105_prog.drop 8)
        ⟨8, [.i32 numLines], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast fRest f_Algorithm_deserializeLife105_prog 21
        (f_Algorithm_deserializeLife105_prog.drop 21)
        ⟨21, [.bool (header == "#Life 1.05")], locs2, jh, ⟨ar, u64, asc⟩⟩ := by
  dsimp only
  split_res_fuel 13; conv => lhs; jvm_whnf_run_args
  rw [runJvmResFast_ifeq_fallthrough (by simp [h0])]
  heap_step_nonbranch_chunks
  rw [hl0, runJvmResFast_aaload_strArr (hslt := by decide)
    (hlt := by rw [show (0 : UInt32).toNat = 0 from rfl]; exact hpos)]
  heap_step_nonbranch_chunks
  rw [runJvmResFast_invokestatic_step (hs := stepStatic_intrinsicsAreEqual_str)]
  rw [Nat.add_sub_cancel]; rfl

private theorem step_checkcast_subtype_heap
    {pc addr : Nat} {cls objCls : String} {fields : List (String × JvmVal)}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? addr = some (.instance objCls fields))
    (hcc : jh.checkCast cls addr = none)
    (hsub : algHooks.isSubtypeOf objCls cls = true) :
    Jvm.stepInstr algHooks (.checkcast cls)
      ⟨pc, .heapRef addr :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef addr :: rest, locs, jh, hp⟩) := by
  dsimp only [Jvm.stepInstr]
  rw [hcc, hget]
  dsimp only [algHooks] at hsub
  simp [hsub]

private theorem deserializeLife105_invalidHeader
    {header : String} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)}
    {asc : List Algorithm.AsciiBytes}
    (hhdr : header ≠ "#Life 1.05") (hl2 : locs 2 = .str header) :
    ∃ v st',
      runJvmResFast 19 f_Algorithm_deserializeLife105_prog 21
          (f_Algorithm_deserializeLife105_prog.drop 21)
          ⟨21, [.bool (header == "#Life 1.05")], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (v, st') ∧
      decodeLife105Result st' v = some ⟨.invalidHeader header, #[], Algorithm.noCells⟩ ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  have hhdr_beq : (header == "#Life 1.05") = false := beq_false_of_ne hhdr
  let stAddr := jh.objects.size
  let wAddr := jh.objects.size + 1
  let resAddr := jh.objects.size + 2
  let jh1 := (jh.alloc (.instance "com/alexvanyo/composelife/model/Life105Status$InvalidHeader"
    [("line", .str header)])).2
  let jh2 := (jh1.alloc (.objArray "java/lang/Object" #[])).2
  let jh3 := (jh2.alloc (.instance "com/alexvanyo/composelife/model/Life105Result"
    [("status", .heapRef stAddr), ("warnings", .heapRef wAddr),
      ("cells", .ext (.u64Ref u64.length))])).2
  let locs3 := setLocal (setLocal (setLocal locs 4 (.heapRef stAddr)) 5 (.heapRef wAddr)) 6
    (.ext (.u64Ref u64.length))
  have hget_st2 : jh2.get? stAddr = some (.instance
      "com/alexvanyo/composelife/model/Life105Status$InvalidHeader"
      [("line", .str header)]) := by
    apply heapExtends_alloc jh1 _
    simp [jh1, stAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  have hget_st : jh3.get? stAddr = some (.instance
      "com/alexvanyo/composelife/model/Life105Status$InvalidHeader"
      [("line", .str header)]) := heapExtends_alloc jh2 _ _ _ hget_st2
  refine ⟨.heapRef resAddr, ⟨39, [.heapRef resAddr], locs3, jh3, ⟨ar, u64 ++ [#[]], asc⟩⟩,
    ?_, ?_, heapExtends_trans (heapExtends_alloc jh _)
      (heapExtends_trans (heapExtends_alloc jh1 _) (heapExtends_alloc jh2 _)), rfl, rfl⟩
  · conv => lhs; jvm_whnf_run_args
    rw [hhdr_beq, runJvmResFast_ifne_bool_fallthrough]
    heap_step_nonbranch_chunks
    rw [hl2, runJvmResFast_invokespecial_step (hs := stepSpecial_life105InvalidHeader_init)]
    heap_step_nonbranch_chunks
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_closed1_105_heap)]
    heap_step_nonbranch_chunks
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_noCells_105_heap)]
    heap_step_nonbranch_chunks
    rw [runJvmResFast_checkcast_step (v' := .heapRef stAddr) (by
      have hcc : jh2.checkCast "com/alexvanyo/composelife/model/Life105Status" stAddr = none := by
        simp [Jvm.JvmHeap.checkCast, Jvm.JvmHeap.checkInstanceOf, hget_st2,
          Jvm.HeapObj.matchesType]
      exact step_checkcast_subtype_heap hget_st2 hcc rfl)]
    heap_step_nonbranch_chunks
    rw [runJvmResFast_invokespecial_step (hs := stepSpecial_life105Result_init)]
    heap_step_nonbranch_chunks
    simp only [Jvm.JvmHeap.alloc, Array.size_push]; rfl
  · have hget_res : jh3.get? resAddr = some (.instance
        "com/alexvanyo/composelife/model/Life105Result"
        [("status", .heapRef stAddr), ("warnings", .heapRef wAddr),
          ("cells", .ext (.u64Ref u64.length))]) := by
      have hsz : jh2.objects.size = resAddr := by simp [jh2, jh1, resAddr, Jvm.JvmHeap.alloc]
      rw [← hsz]; simp [jh3, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    have hget_w : jh3.get? wAddr = some (.objArray "java/lang/Object" #[]) := by
      apply heapExtends_alloc jh2 _
      have hsz : jh1.objects.size = wAddr := by simp [jh1, wAddr, Jvm.JvmHeap.alloc]
      rw [← hsz]; simp [jh2, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
    simp [decodeLife105Result, decodeLife105Status, hget_res, hget_st, hget_w,
      List.lookup, Algorithm.noCells]

private theorem deserializeLife105_21_48
    {lines : Array String} {numLines : UInt32} {header : String} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hhdr : header = "#Life 1.05") (hl0 : locs 0 = .strArr lines)
    (hl1 : locs 1 = .i32 numLines) (fRest : Nat) :
    let i := Algorithm.skipDescriptions lines numLines 1
    let locs3 := setLocal locs 4 (.i32 i)
    runJvmResFast (fRest + 9) f_Algorithm_deserializeLife105_prog 21
        (f_Algorithm_deserializeLife105_prog.drop 21)
        ⟨21, [.bool (header == "#Life 1.05")], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast fRest f_Algorithm_deserializeLife105_prog 48
        (f_Algorithm_deserializeLife105_prog.drop 48)
        ⟨48, [.i32 (if i == numLines then 0 else if i < numLines then 4294967295 else 1)],
          locs3, jh, ⟨ar, u64, asc⟩⟩ := by
  dsimp only
  have hhdr_beq : (header == "#Life 1.05") = true := beq_iff_eq.mpr hhdr
  split_res_fuel 9; conv => lhs; jvm_whnf_run_args
  rw [hhdr_beq, runJvmResFast_ifne_bool_branch]; conv => lhs; jvm_whnf_run_args
  heap_step_nonbranch_chunks
  rw [hl0, hl1, runJvmResFast_invokestatic_step (hs := stepStatic_skipDescriptions_heap)]
  heap_step_nonbranch_chunks; rw [hl1]; rfl

private theorem deserializeLife105_48_67
    {lines : Array String} {numLines i : UInt32} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hi : i < numLines) (hi_slt : i.toBitVec.slt 0#32 = false) (hi_sz : i.toNat < lines.size)
    (hl0 : locs 0 = .strArr lines) (hl4 : locs 4 = .i32 i) (fRest : Nat) :
    let ruleLine := lines[i.toNat]
    let bytes := ruleLine.toByteArray
    let bytesAddr := jh.objects.size
    let jh1 := (jh.alloc (.byteArray bytes.data)).2
    let locs4 := setLocal (setLocal (setLocal (setLocal (setLocal locs
      5 (.str ruleLine)) 6 (.heapRef bytesAddr)) 7 .null) 8 (.i32 0)) 9 (.i32 0)
    runJvmResFast (fRest + 17) f_Algorithm_deserializeLife105_prog 48
        (f_Algorithm_deserializeLife105_prog.drop 48)
        ⟨48, [.i32 (if i == numLines then 0 else if i < numLines then 4294967295 else 1)],
          locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast fRest f_Algorithm_deserializeLife105_prog 67
        (f_Algorithm_deserializeLife105_prog.drop 67)
        ⟨67, [], locs4, jh1, ⟨ar, u64, asc⟩⟩ := by
  dsimp only
  split_res_fuel 17; conv => lhs; jvm_whnf_run_args
  rw [runJvmResFast_iflt_branch (by
    rw [compareUnsigned_iflt_cond]; exact decide_eq_true hi)]; conv => lhs; jvm_whnf_run_args
  heap_step_nonbranch_chunks
  rw [hl0, hl4, runJvmResFast_aaload_strArr (hslt := hi_slt) (hlt := hi_sz)]
  heap_step_nonbranch_chunks
  rw [runJvmResFast_invokestatic_step (hs := stepStatic_stringsEncodeToByteArray)]
  heap_step_nonbranch_chunks
  rw [show lines[i.toNat].toUTF8.data = lines[i.toNat].toByteArray.data from rfl]
  rw [← runJvmResFast_stepResHeapChunk, Nat.add_sub_cancel]; rfl

private theorem deserializeLife105_228_exit
    {lines : Array String} {numLines i : UInt32} {bytes : ByteArray} {bytesAddr : Nat}
    {locs : Nat → JvmVal} {jh1 : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)}
    {asc : List Algorithm.AsciiBytes}
    (hba : jh1.get? bytesAddr = some (.byteArray bytes.data))
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines) (hl4 : locs 4 = .i32 i)
    (hl6 : locs 6 = .heapRef bytesAddr) (hl8 : locs 8 = .i32 0) :
    ∃ v st',
      runJvmResFast 20 f_Algorithm_deserializeLife105_prog 228
          (f_Algorithm_deserializeLife105_prog.drop 228)
          ⟨228, [], locs, jh1, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
      decodeLife105Result st' v = some (Algorithm.parseBlocks lines numLines i false bytes
        0 0 false 0 0 0 #[] Algorithm.U64Buf.empty) ∧
      HeapExtends jh1 st'.jvmHeap ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  let wAddr := jh1.objects.size
  let jh2 := (jh1.alloc (.objArray "java/lang/Object" #[])).2
  have hw2 : jh2.get? wAddr = some (.objArray "java/lang/Object" #[]) := by
    simp [jh2, wAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
  have hba2 : jh2.get? bytesAddr = some (.byteArray bytes.data) :=
    heapExtends_alloc jh1 _ _ _ hba
  let u64a := u64 ++ [Algorithm.U64Buf.empty]
  have hc : u64a[u64.length]? = some Algorithm.U64Buf.empty := by simp [u64a]
  apply l105_equiv_finish (u64a := u64a)
    (locs1 := setLocal (setLocal locs 10 (.heapRef wAddr)) 11 (.ext (.u64Ref u64.length)))
    (pc1 := 246) _ (heapExtends_alloc jh1 _)
  split_res_fuel 20; conv => lhs; jvm_whnf_run_args
  rw [runJvmResFast_invokestatic_step (hs := stepStatic_closed1_105_heap)]
  heap_step_nonbranch_chunks
  conv => lhs; jvm_whnf_run_args
  rw [runJvmResFast_invokestatic_step (hs := stepStatic_u64BufEmpty_105_heap)]
  heap_step_nonbranch_chunks
  conv => lhs; jvm_whnf_run_args
  conv => lhs; arg 5; arg 2; rw [hl0, hl1, hl4, hl6, hl8]; dsimp only [Jvm.JvmVal.asI32]
  have hs := stepStatic_parseBlocks_heap (pc := 245) (lines := lines) (limit := 0) (p := 0)
    (numLines := numLines) (i := i) (rest := [])
    (locs := setLocal (setLocal locs 10 (.heapRef wAddr)) 11 (.ext (.u64Ref u64.length)))
    (ar := ar) (asc := asc) hba2 hw2 rfl hc
  refine Eq.trans (runJvmResFast_invokestatic_step (hs := hs)) ?_
  exact runJvmResFast_areturn

private theorem deserializeLife105_ruleR
    {lines : Array String} {numLines i : UInt32} {ruleLine : String} {bytes : ByteArray}
    {bytesAddr : Nat} {locs : Nat → JvmVal} {jh1 : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)}
    {asc : List Algorithm.AsciiBytes}
    (hba : jh1.get? bytesAddr = some (.byteArray bytes.data))
    (hutf8_sz : bytes.data.size < 2 ^ 31)
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines) (hl4 : locs 4 = .i32 i)
    (hl5 : locs 5 = .str ruleLine) (hl6 : locs 6 = .heapRef bytesAddr)
    (hl9 : locs 9 = .i32 0) :
    let status := Algorithm.checkRuleLine bytes
    let expected : Algorithm.Life105Result :=
      if Algorithm.startsWithHash bytes 82 then
        if status == 0 then
          Algorithm.parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0 #[]
            Algorithm.U64Buf.empty
        else if status == 1 then
          ⟨.unexpectedInput ruleLine (i + 1) 3, #[], Algorithm.noCells⟩
        else
          ⟨.ruleNotSupported, #[], Algorithm.noCells⟩
      else
        Algorithm.parseBlocks lines numLines i false bytes 0 0 false 0 0 0 #[]
          Algorithm.U64Buf.empty
    ∃ f143 v st',
      runJvmResFast f143 f_Algorithm_deserializeLife105_prog 143
          (f_Algorithm_deserializeLife105_prog.drop 143)
          ⟨143, [], locs, jh1, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
      decodeLife105Result st' v = some expected ∧
      HeapExtends jh1 st'.jvmHeap ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  dsimp only
  have h228 : Algorithm.startsWithHash bytes 82 = false →
      ∃ v st',
        runJvmResFast 20 f_Algorithm_deserializeLife105_prog 228
            (f_Algorithm_deserializeLife105_prog.drop 228)
            ⟨228, [], setLocal locs 8 (.i32 0), jh1, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
        decodeLife105Result st' v = some
          (if Algorithm.startsWithHash bytes 82 then
            if Algorithm.checkRuleLine bytes == 0 then
              Algorithm.parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0 #[]
                Algorithm.U64Buf.empty
            else if Algorithm.checkRuleLine bytes == 1 then
              ⟨.unexpectedInput ruleLine (i + 1) 3, #[], Algorithm.noCells⟩
            else
              ⟨.ruleNotSupported, #[], Algorithm.noCells⟩
          else
            Algorithm.parseBlocks lines numLines i false bytes 0 0 false 0 0 0 #[]
              Algorithm.U64Buf.empty) ∧
        HeapExtends jh1 st'.jvmHeap ∧
        st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
    intro hnh82
    simp only [hnh82, Bool.false_eq_true, ↓reduceIte]
    exact deserializeLife105_228_exit hba
      (by rw [setLocal_ne (by decide)]; exact hl0)
      (by rw [setLocal_ne (by decide)]; exact hl1)
      (by rw [setLocal_ne (by decide)]; exact hl4)
      (by rw [setLocal_ne (by decide)]; exact hl6)
      (setLocal_self _ _ _)
  by_cases hlt2 : bytes.data.size < 2
  · have hlt2_u : bytes.data.size.toUInt32 < 2 := by
      rw [UInt32.lt_iff_toNat_lt]
      change bytes.data.size.toUInt32.toNat < 2
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      exact hlt2
    have hge_f : decide (bytes.size.toUInt32 >= 2) = false :=
      decide_eq_false (UInt32.not_le.mpr hlt2_u)
    have hnh82 : Algorithm.startsWithHash bytes 82 = false := by
      simp only [Algorithm.startsWithHash, hge_f, Bool.false_and]
    rcases h228 hnh82 with ⟨v, st', hrun, hdec, hext, har, hasc⟩
    refine ⟨20 + 9, v, st', ?_, hdec, hext, har, hasc⟩
    split_res_fuel 9
    heap_step_nonbranch_chunks; rw [hl6]
    rw [runJvmResFast_arraylength_byte (hget := hba)]
    heap_step_nonbranch_chunks
    rw [runJvmResFast_ifle_fallthrough (by
      rw [compareUnsigned_ifle_cond]; exact hge_f)]
    heap_step_nonbranch_chunks
    exact hrun
  · have hge2 : 2 ≤ bytes.data.size := Nat.le_of_not_lt hlt2
    have hge2_u : (2 : UInt32) ≤ bytes.data.size.toUInt32 := by
      rw [UInt32.le_iff_toNat_le]
      change 2 ≤ bytes.data.size.toUInt32.toNat
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      exact hge2
    let b0 := bytes.data[0]'(by omega)
    have h143_154 : ∀ fAny,
        runJvmResFast (fAny + 11) f_Algorithm_deserializeLife105_prog 143
            (f_Algorithm_deserializeLife105_prog.drop 143)
            ⟨143, [], locs, jh1, ⟨ar, u64, asc⟩⟩ =
          runJvmResFast fAny f_Algorithm_deserializeLife105_prog 157
            (f_Algorithm_deserializeLife105_prog.drop 157)
            ⟨157, [.i32 35, .i32 (UInt32.ofBitVec (b0.toBitVec.signExtend 32))],
              locs, jh1, ⟨ar, u64, asc⟩⟩ := by
      intro fAny
      split_res_fuel 11
      heap_step_nonbranch_chunks; rw [hl6]
      rw [runJvmResFast_arraylength_byte (hget := hba)]
      heap_step_nonbranch_chunks
      rw [runJvmResFast_ifle_branch (by
        rw [compareUnsigned_ifle_cond]; exact decide_eq_true hge2_u)]
      heap_step_nonbranch_chunks; rw [hl6]
      rw [runJvmResFast_baload_byteArray (hget := hba) (hslt := by decide)
        (hlt := by change (0 : UInt32).toNat < bytes.data.size
                   rw [show (0 : UInt32).toNat = 0 from rfl]; omega)]
      rw [Nat.add_sub_cancel]
      rw [runJvmResFast_ubyteCtor, runJvmResFast_iconst]
      rfl
    by_cases hb0 : b0 = 35
    · have heq35 : UInt32.ofBitVec (b0.toBitVec.signExtend 32) = 35 :=
        signExtend_eq_u32 hb0 rfl (by decide)
      let b1 := bytes.data[1]'(by omega)
      have h154_160 : ∀ fAny,
          runJvmResFast (fAny + 6) f_Algorithm_deserializeLife105_prog 157
              (f_Algorithm_deserializeLife105_prog.drop 157)
              ⟨157, [.i32 35, .i32 (UInt32.ofBitVec (b0.toBitVec.signExtend 32))],
                locs, jh1, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast fAny f_Algorithm_deserializeLife105_prog 166
              (f_Algorithm_deserializeLife105_prog.drop 166)
              ⟨166, [.i32 82, .i32 (UInt32.ofBitVec (b1.toBitVec.signExtend 32))],
                locs, jh1, ⟨ar, u64, asc⟩⟩ := by
        intro fAny
        split_res_fuel 6; conv => lhs; jvm_whnf_run_args
        rw [runJvmResFast_if_icmpeq_branch heq35]
        heap_step_nonbranch_chunks; rw [hl6]
        rw [runJvmResFast_baload_byteArray (hget := hba) (hslt := by decide)
          (hlt := by change (1 : UInt32).toNat < bytes.data.size
                     rw [show (1 : UInt32).toNat = 1 from rfl]; omega)]
        rw [Nat.add_sub_cancel]
        rw [runJvmResFast_ubyteCtor, runJvmResFast_iconst]
        rfl
      by_cases hb1 : b1 = 82
      · have heq82 : UInt32.ofBitVec (b1.toBitVec.signExtend 32) = 82 :=
          signExtend_eq_u32 hb1 rfl (by decide)
        have hhash82 : Algorithm.startsWithHash bytes 82 = true := by
          have h0_b : bytes.get! 0 = b0 := by
            simp [ByteArray.get!, getElem!_pos bytes.data 0 (by omega), b0]
          have h1_b : bytes.get! 1 = b1 := by
            simp [ByteArray.get!, getElem!_pos bytes.data 1 (by omega), b1]
          simp only [Algorithm.startsWithHash, show bytes.size = bytes.data.size from rfl,
            decide_eq_true hge2_u, h0_b, h1_b, hb0, hb1, beq_self_eq_true, Bool.and_true]
        let status := Algorithm.checkRuleLine bytes
        let locs5 := setLocal locs 10 (.i32 status)
        have hl4' : locs5 4 = .i32 i := by
          dsimp only [locs5]; rw [setLocal_ne (by decide), hl4]
        have h143_174 : ∀ fAny,
            runJvmResFast (fAny + 5 + 6 + 11) f_Algorithm_deserializeLife105_prog 143
                (f_Algorithm_deserializeLife105_prog.drop 143)
                ⟨143, [], locs, jh1, ⟨ar, u64, asc⟩⟩ =
              runJvmResFast fAny f_Algorithm_deserializeLife105_prog 174
                (f_Algorithm_deserializeLife105_prog.drop 174)
                ⟨174, [.i32 status], locs5, jh1, ⟨ar, u64, asc⟩⟩ := by
          intro fAny
          rw [show fAny + 5 + 6 + 11 = (fAny + 5 + 6) + 11 by omega, h143_154, h154_160]
          split_res_fuel 5; conv => lhs; jvm_whnf_run_args
          rw [runJvmResFast_if_icmpeq_branch heq82]
          heap_step_nonbranch_chunks; rw [hl6]
          rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkRuleLine_heap hba)]
          rw [Nat.add_sub_cancel]
          rw [runJvmResFast_istore, runJvmResFast_iload]
          rw [show Algorithm.checkRuleLine ⟨bytes.data⟩ = status from rfl]
          dsimp only [locs5]
          have htop : setLocal locs 10 (.i32 status) 10 = .i32 status := setLocal_self _ _ _
          rw [htop]
          rfl
        by_cases hst0 : status = 0
        · let wAddr := jh1.objects.size
          let jh2 := (jh1.alloc (.objArray "java/lang/Object" #[])).2
          have hw2 : jh2.get? wAddr = some (.objArray "java/lang/Object" #[]) := by
            simp [jh2, wAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
          have hba2 : jh2.get? bytesAddr = some (.byteArray bytes.data) :=
            heapExtends_alloc jh1 _ _ _ hba
          let u64a := u64 ++ [Algorithm.U64Buf.empty]
          have hc : u64a[u64.length]? = some Algorithm.U64Buf.empty := by simp [u64a]
          have hsub : ∃ v st',
              runJvmResFast 25 f_Algorithm_deserializeLife105_prog 174
                  (f_Algorithm_deserializeLife105_prog.drop 174)
                  ⟨174, [.i32 status], locs5, jh1, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
              decodeLife105Result st' v = some (Algorithm.parseBlocks lines numLines (i + 1)
                false bytes 0 0 false 0 0 0 #[] Algorithm.U64Buf.empty) ∧
              HeapExtends jh1 st'.jvmHeap ∧
              st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
            apply l105_equiv_finish (u64a := u64a)
              (locs1 := setLocal (setLocal (setLocal locs5 11 (.i32 (i + 1))) 12 (.heapRef wAddr))
                13 (.ext (.u64Ref u64.length)))
              (pc1 := 227) _ (heapExtends_alloc jh1 _)
            split_res_fuel 25; conv => lhs; jvm_whnf_run_args
            rw [runJvmResFast_ifeq_branch (by simp [hst0])]
            heap_step_nonbranch_chunks
            conv => lhs; jvm_whnf_run_args
            rw [runJvmResFast_invokestatic_step (hs := stepStatic_closed1_105_heap)]
            heap_step_nonbranch_chunks
            conv => lhs; jvm_whnf_run_args
            rw [runJvmResFast_invokestatic_step (hs := stepStatic_u64BufEmpty_105_heap)]
            heap_step_nonbranch_chunks
            conv => lhs; jvm_whnf_run_args
            conv => lhs; arg 5; arg 2; rw [hl0, hl1, hl4', hl9, hl6]; dsimp only [Jvm.JvmVal.asI32]
            conv => lhs; arg 5; arg 3; rw [hl4']; dsimp only [Jvm.JvmVal.asI32]
            have hs := stepStatic_parseBlocks_heap (pc := 226) (lines := lines) (limit := 0) (p := 0)
              (numLines := numLines) (i := i + 1) (rest := [])
              (locs := setLocal (setLocal (setLocal locs5 11 (.i32 (i + 1))) 12 (.heapRef wAddr)) 13
                (.ext (.u64Ref u64.length)))
              (ar := ar) (asc := asc) hba2 hw2 rfl hc
            refine Eq.trans (runJvmResFast_invokestatic_step (hs := hs)) ?_
            exact runJvmResFast_areturn
          rcases hsub with ⟨v, st', hrun25, hdec25, hext25, har25, hasc25⟩
          refine ⟨25 + 5 + 6 + 11, v, st', ?_, ?_, hext25, har25, hasc25⟩
          · rw [show 25 + 5 + 6 + 11 = (25) + 5 + 6 + 11 by rfl, h143_174]
            exact hrun25
          · simp [hhash82, status, hst0]
            exact hdec25
        · by_cases hst1 : status = 1
          · let stAddr := jh1.objects.size
            let wAddr := jh1.objects.size + 1
            let resAddr := jh1.objects.size + 2
            let jh1a := (jh1.alloc (.instance
              "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput"
              [("input", .str ruleLine), ("lineIndex", .i32 (i + 1)),
                ("columnIndex", .i32 3)])).2
            let jh1b := (jh1a.alloc (.objArray "java/lang/Object" #[])).2
            let jh2 := (jh1b.alloc (.instance
              "com/alexvanyo/composelife/model/Life105Result"
              [("status", .heapRef stAddr), ("warnings", .heapRef wAddr),
                ("cells", .ext (.u64Ref u64.length))])).2
            let locs6 := setLocal (setLocal (setLocal locs5 11 (.heapRef stAddr)) 12
              (.heapRef wAddr)) 13 (.ext (.u64Ref u64.length))
            have hget_st1b : jh1b.get? stAddr = some (.instance
                "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput"
                [("input", .str ruleLine), ("lineIndex", .i32 (i + 1)),
                  ("columnIndex", .i32 3)]) := by
              apply heapExtends_alloc jh1a _
              simp [jh1a, stAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
            have hget_st : jh2.get? stAddr = some (.instance
                "com/alexvanyo/composelife/model/Life105Status$UnexpectedInput"
                [("input", .str ruleLine), ("lineIndex", .i32 (i + 1)),
                  ("columnIndex", .i32 3)]) := heapExtends_alloc jh1b _ _ _ hget_st1b
            refine ⟨28 + 5 + 6 + 11, .heapRef resAddr,
              ⟨203, [.heapRef resAddr], locs6, jh2, ⟨ar, u64 ++ [#[]], asc⟩⟩,
              ?_, ?_, heapExtends_trans (heapExtends_alloc jh1 _)
                (heapExtends_trans (heapExtends_alloc jh1a _) (heapExtends_alloc jh1b _)),
              rfl, rfl⟩
            · rw [show 28 + 5 + 6 + 11 = 28 + 5 + 6 + 11 by rfl, h143_174]
              split_res_fuel 28; conv => lhs; jvm_whnf_run_args
              rw [runJvmResFast_ifeq_fallthrough (by simp [hst0])]
              heap_step_nonbranch_chunks
              rw [runJvmResFast_if_icmpeq_branch hst1]
              heap_step_nonbranch_chunks
              rw [hl4', hl5]; dsimp only [Jvm.JvmVal.asI32]
              rw [runJvmResFast_invokespecial_step
                (hs := stepSpecial_life105UnexpectedInput_init)]
              heap_step_nonbranch_chunks
              rw [runJvmResFast_invokestatic_step (hs := stepStatic_closed1_105_heap)]
              heap_step_nonbranch_chunks
              rw [runJvmResFast_invokestatic_step (hs := stepStatic_noCells_105_heap)]
              heap_step_nonbranch_chunks
              rw [runJvmResFast_checkcast_step (v' := .heapRef stAddr) (by
                have hcc : jh1b.checkCast "com/alexvanyo/composelife/model/Life105Status"
                    stAddr = none := by
                  simp [Jvm.JvmHeap.checkCast, Jvm.JvmHeap.checkInstanceOf, hget_st1b,
                    Jvm.HeapObj.matchesType]
                exact step_checkcast_subtype_heap hget_st1b hcc rfl)]
              heap_step_nonbranch_chunks
              rw [runJvmResFast_invokespecial_step (hs := stepSpecial_life105Result_init)]
              heap_step_nonbranch_chunks
              simp only [Jvm.JvmHeap.alloc, Array.size_push]; rfl
            · have hget_res : jh2.get? resAddr = some (.instance
                  "com/alexvanyo/composelife/model/Life105Result"
                  [("status", .heapRef stAddr), ("warnings", .heapRef wAddr),
                    ("cells", .ext (.u64Ref u64.length))]) := by
                have hsz : jh1b.objects.size = resAddr := by
                  simp [jh1b, jh1a, resAddr, Jvm.JvmHeap.alloc]
                rw [← hsz]; simp [jh2, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
              have hget_w : jh2.get? wAddr = some (.objArray "java/lang/Object" #[]) := by
                apply heapExtends_alloc jh1b _
                have hsz : jh1a.objects.size = wAddr := by simp [jh1a, wAddr, Jvm.JvmHeap.alloc]
                rw [← hsz]; simp [jh1b, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
              simp [hhash82, status, hst1, decodeLife105Result,
                decodeLife105Status, hget_res, hget_st, hget_w, List.lookup, Jvm.JvmVal.asI32,
                Algorithm.noCells]
          · let res : Algorithm.Life105Result := ⟨.ruleNotSupported, #[], Algorithm.noCells⟩
            let enc := encodeLife105Result jh1 u64 res
            refine ⟨6 + 5 + 6 + 11, enc.1, ⟨179, [enc.1], locs5, enc.2.1, ⟨ar, enc.2.2, asc⟩⟩,
              ?_, ?_, heapExtends_encodeLife105Result jh1 u64 res, rfl, rfl⟩
            · rw [h143_174]
              split_res_fuel 6; conv => lhs; jvm_whnf_run_args
              rw [runJvmResFast_ifeq_fallthrough (by simp [hst0])]
              heap_step_nonbranch_chunks
              rw [runJvmResFast_if_icmpeq_fallthrough (beq_false_of_ne hst1)]
              heap_step_nonbranch_chunks
              rw [runJvmResFast_invokestatic_step (hs := stepStatic_closed3_105_heap)]
              exact runJvmResFast_areturn
            · simp [hhash82, status, beq_false_of_ne hst0, beq_false_of_ne hst1]
              exact decodeLife105Result_encode jh1 ⟨ar, u64, asc⟩ res
      · have hne82 : (UInt32.ofBitVec (b1.toBitVec.signExtend 32) == 82) = false :=
          signExtend_bne_u32 hb1 rfl (by decide)
        have hnh82 : Algorithm.startsWithHash bytes 82 = false := by
          have h1_b : bytes.get! 1 = b1 := by
            simp [ByteArray.get!, getElem!_pos bytes.data 1 (by omega), b1]
          simp only [Algorithm.startsWithHash, h1_b, beq_false_of_ne hb1, Bool.and_false]
        rcases h228 hnh82 with ⟨v, st', hrun, hdec, hext, har, hasc⟩
        refine ⟨20 + 4 + 6 + 11, v, st', ?_, hdec, hext, har, hasc⟩
        rw [show 20 + 4 + 6 + 11 = ((20 + 4) + 6) + 11 by omega, h143_154, h154_160]
        split_res_fuel 4; conv => lhs; jvm_whnf_run_args
        rw [runJvmResFast_if_icmpeq_fallthrough hne82]
        heap_step_nonbranch_chunks
        exact hrun
    · have hne35 : (UInt32.ofBitVec (b0.toBitVec.signExtend 32) == 35) = false :=
        signExtend_bne_u32 hb0 rfl (by decide)
      have hnh82 : Algorithm.startsWithHash bytes 82 = false := by
        have h0_b : bytes.get! 0 = b0 := by
          simp [ByteArray.get!, getElem!_pos bytes.data 0 (by omega), b0]
        simp only [Algorithm.startsWithHash, h0_b, beq_false_of_ne hb0, Bool.and_false,
          Bool.false_and]
      rcases h228 hnh82 with ⟨v, st', hrun, hdec, hext, har, hasc⟩
      refine ⟨20 + 4 + 11, v, st', ?_, hdec, hext, har, hasc⟩
      rw [show 20 + 4 + 11 = (20 + 4) + 11 by omega, h143_154]
      split_res_fuel 4; conv => lhs; jvm_whnf_run_args
      rw [runJvmResFast_if_icmpeq_fallthrough hne35]
      heap_step_nonbranch_chunks
      exact hrun

private theorem deserializeLife105_ruleN
    {lines : Array String} {numLines i : UInt32} {ruleLine : String} {bytes : ByteArray}
    {bytesAddr : Nat} {locs : Nat → JvmVal} {jh1 : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)}
    {asc : List Algorithm.AsciiBytes}
    (hba : jh1.get? bytesAddr = some (.byteArray bytes.data))
    (hutf8_sz : bytes.data.size < 2 ^ 31)
    (hl0 : locs 0 = .strArr lines) (hl1 : locs 1 = .i32 numLines) (hl4 : locs 4 = .i32 i)
    (hl5 : locs 5 = .str ruleLine) (hl6 : locs 6 = .heapRef bytesAddr)
    (hl9 : locs 9 = .i32 0) :
    let status := Algorithm.checkRuleLine bytes
    let expected : Algorithm.Life105Result :=
      if Algorithm.startsWithHash bytes 78 then
        if ruleLine == "#N" then
          Algorithm.parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0 #[]
            Algorithm.U64Buf.empty
        else
          Algorithm.parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0
            #[.unexpectedInput ruleLine (i + 1) 3] Algorithm.U64Buf.empty
      else if Algorithm.startsWithHash bytes 82 then
        if status == 0 then
          Algorithm.parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0 #[]
            Algorithm.U64Buf.empty
        else if status == 1 then
          ⟨.unexpectedInput ruleLine (i + 1) 3, #[], Algorithm.noCells⟩
        else
          ⟨.ruleNotSupported, #[], Algorithm.noCells⟩
      else
        Algorithm.parseBlocks lines numLines i false bytes 0 0 false 0 0 0 #[]
          Algorithm.U64Buf.empty
    ∃ f67 v st',
      runJvmResFast f67 f_Algorithm_deserializeLife105_prog 67
          (f_Algorithm_deserializeLife105_prog.drop 67)
          ⟨67, [], locs, jh1, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
      decodeLife105Result st' v = some expected ∧
      HeapExtends jh1 st'.jvmHeap ∧
      st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
  dsimp only
  have hloc9 : setLocal locs 9 (.i32 0) = locs := by
    funext k
    by_cases hk : k = 9
    · subst hk; simp [setLocal, hl9]
    · simp [setLocal, hk]
  have hruleR : Algorithm.startsWithHash bytes 78 = false →
      ∃ f143 v st',
        runJvmResFast f143 f_Algorithm_deserializeLife105_prog 143
            (f_Algorithm_deserializeLife105_prog.drop 143)
            ⟨143, [], locs, jh1, ⟨ar, u64, asc⟩⟩ = some (v, st') ∧
        decodeLife105Result st' v = some
          (if Algorithm.startsWithHash bytes 78 then
            if ruleLine == "#N" then
              Algorithm.parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0 #[]
                Algorithm.U64Buf.empty
            else
              Algorithm.parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0
                #[.unexpectedInput ruleLine (i + 1) 3] Algorithm.U64Buf.empty
          else if Algorithm.startsWithHash bytes 82 then
            if Algorithm.checkRuleLine bytes == 0 then
              Algorithm.parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0 #[]
                Algorithm.U64Buf.empty
            else if Algorithm.checkRuleLine bytes == 1 then
              ⟨.unexpectedInput ruleLine (i + 1) 3, #[], Algorithm.noCells⟩
            else
              ⟨.ruleNotSupported, #[], Algorithm.noCells⟩
          else
            Algorithm.parseBlocks lines numLines i false bytes 0 0 false 0 0 0 #[]
              Algorithm.U64Buf.empty) ∧
        HeapExtends jh1 st'.jvmHeap ∧
        st'.heap.arenas = ar ∧ st'.heap.asciiArrays = asc := by
    intro hnh78
    simp only [hnh78, Bool.false_eq_true, ↓reduceIte]
    exact deserializeLife105_ruleR hba hutf8_sz hl0 hl1 hl4 hl5 hl6 hl9
  by_cases hlt2 : bytes.data.size < 2
  · have hlt2_u : bytes.data.size.toUInt32 < 2 := by
      rw [UInt32.lt_iff_toNat_lt]
      change bytes.data.size.toUInt32.toNat < 2
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      exact hlt2
    have hge_f : decide (bytes.size.toUInt32 >= 2) = false :=
      decide_eq_false (UInt32.not_le.mpr hlt2_u)
    have hnh78 : Algorithm.startsWithHash bytes 78 = false := by
      simp only [Algorithm.startsWithHash, hge_f, Bool.false_and]
    rcases hruleR hnh78 with ⟨f143, v, st', hrun143, hdec, hext, har, hasc⟩
    refine ⟨f143 + 9, v, st', ?_, hdec, hext, har, hasc⟩
    conv => lhs; jvm_whnf_run_args
    heap_step_nonbranch_chunks; rw [hl6]
    rw [runJvmResFast_arraylength_byte (hget := hba)]
    heap_step_nonbranch_chunks
    rw [runJvmResFast_ifle_fallthrough (by rw [compareUnsigned_ifle_cond]; exact hge_f)]
    rw [runJvmResFast_iconst, runJvmResFast_istore, runJvmResFast_goto]
    rw [hloc9]; exact hrun143
  · have hge2 : 2 ≤ bytes.data.size := Nat.le_of_not_lt hlt2
    have hge2_u : (2 : UInt32) ≤ bytes.data.size.toUInt32 := by
      rw [UInt32.le_iff_toNat_le]
      change 2 ≤ bytes.data.size.toUInt32.toNat
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      exact hge2
    let b0 := bytes.data[0]'(by omega)
    have h67_78 : ∀ fAny,
        runJvmResFast (fAny + 11) f_Algorithm_deserializeLife105_prog 67
            (f_Algorithm_deserializeLife105_prog.drop 67)
            ⟨67, [], locs, jh1, ⟨ar, u64, asc⟩⟩ =
          runJvmResFast fAny f_Algorithm_deserializeLife105_prog 81
            (f_Algorithm_deserializeLife105_prog.drop 81)
            ⟨81, [.i32 35, .i32 (UInt32.ofBitVec (b0.toBitVec.signExtend 32))],
              locs, jh1, ⟨ar, u64, asc⟩⟩ := by
      intro fAny
      split_res_fuel 11
      heap_step_nonbranch_chunks; rw [hl6]
      rw [runJvmResFast_arraylength_byte (hget := hba)]
      heap_step_nonbranch_chunks
      rw [runJvmResFast_ifle_branch (by
        rw [compareUnsigned_ifle_cond]; exact decide_eq_true hge2_u)]
      heap_step_nonbranch_chunks; rw [hl6]
      rw [runJvmResFast_baload_byteArray (hget := hba) (hslt := by decide)
        (hlt := by change (0 : UInt32).toNat < bytes.data.size
                   rw [show (0 : UInt32).toNat = 0 from rfl]; omega)]
      rw [Nat.add_sub_cancel]
      rw [runJvmResFast_ubyteCtor, runJvmResFast_iconst]
      rfl
    by_cases hb0 : b0 = 35
    · have heq35 : UInt32.ofBitVec (b0.toBitVec.signExtend 32) = 35 :=
        signExtend_eq_u32 hb0 rfl (by decide)
      let b1 := bytes.data[1]'(by omega)
      have h78_84 : ∀ fAny,
          runJvmResFast (fAny + 6) f_Algorithm_deserializeLife105_prog 81
              (f_Algorithm_deserializeLife105_prog.drop 81)
              ⟨81, [.i32 35, .i32 (UInt32.ofBitVec (b0.toBitVec.signExtend 32))],
                locs, jh1, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast fAny f_Algorithm_deserializeLife105_prog 90
              (f_Algorithm_deserializeLife105_prog.drop 90)
              ⟨90, [.i32 78, .i32 (UInt32.ofBitVec (b1.toBitVec.signExtend 32))],
                locs, jh1, ⟨ar, u64, asc⟩⟩ := by
        intro fAny
        split_res_fuel 6; conv => lhs; jvm_whnf_run_args
        rw [runJvmResFast_if_icmpeq_branch heq35]
        heap_step_nonbranch_chunks; rw [hl6]
        rw [runJvmResFast_baload_byteArray (hget := hba) (hslt := by decide)
          (hlt := by change (1 : UInt32).toNat < bytes.data.size
                     rw [show (1 : UInt32).toNat = 1 from rfl]; omega)]
        rw [Nat.add_sub_cancel]
        rw [runJvmResFast_ubyteCtor, runJvmResFast_iconst]
        rfl
      by_cases hb1 : b1 = 78
      · have heq78 : UInt32.ofBitVec (b1.toBitVec.signExtend 32) = 78 :=
          signExtend_eq_u32 hb1 rfl (by decide)
        have hhash78 : Algorithm.startsWithHash bytes 78 = true := by
          have h0_b : bytes.get! 0 = b0 := by
            simp [ByteArray.get!, getElem!_pos bytes.data 0 (by omega), b0]
          have h1_b : bytes.get! 1 = b1 := by
            simp [ByteArray.get!, getElem!_pos bytes.data 1 (by omega), b1]
          simp only [Algorithm.startsWithHash, show bytes.size = bytes.data.size from rfl,
            decide_eq_true hge2_u, h0_b, h1_b, hb0, hb1, beq_self_eq_true, Bool.and_true]
        let locs5 := setLocal locs 10 (.str "#N")
        have hl4' : locs5 4 = .i32 i := by
          dsimp only [locs5]; rw [setLocal_ne (by decide), hl4]
        have h67_99 : ∀ fAny,
            runJvmResFast (fAny + 6 + 6 + 11) f_Algorithm_deserializeLife105_prog 67
                (f_Algorithm_deserializeLife105_prog.drop 67)
                ⟨67, [], locs, jh1, ⟨ar, u64, asc⟩⟩ =
              runJvmResFast fAny f_Algorithm_deserializeLife105_prog 99
                (f_Algorithm_deserializeLife105_prog.drop 99)
                ⟨99, [.bool (ruleLine == "#N")],
                  locs5, jh1, ⟨ar, u64, asc⟩⟩ := by
          intro fAny
          rw [show fAny + 6 + 6 + 11 = ((fAny + 6) + 6) + 11 by omega, h67_78, h78_84]
          split_res_fuel 6; conv => lhs; jvm_whnf_run_args
          rw [runJvmResFast_if_icmpeq_branch heq78]
          heap_step_nonbranch_chunks; rw [hl5]
          rw [runJvmResFast_invokestatic_step (hs := stepStatic_intrinsicsAreEqual_str)]
          rfl
        by_cases hrn : ruleLine = "#N"
        · have hrn_beq : (ruleLine == "#N") = true := beq_iff_eq.mpr hrn
          let wAddr := jh1.objects.size
          let jh2 := (jh1.alloc (.objArray "java/lang/Object" #[])).2
          let locs6 := setLocal (setLocal locs5 11 (.heapRef wAddr)) 7 (.heapRef wAddr)
          have hw2 : jh2.get? wAddr = some (.objArray "java/lang/Object" #[]) := by
            simp [jh2, wAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
          have hba2 : jh2.get? bytesAddr = some (.byteArray bytes.data) :=
            heapExtends_alloc jh1 _ _ _ hba
          rcases deserializeLife105_exit247 (u64 := u64) (locs := locs6) hba2 hw2 rfl
              (by dsimp only [locs6, locs5]; (repeat rw [setLocal_ne (by decide)]); exact hl0)
              (by dsimp only [locs6, locs5]; (repeat rw [setLocal_ne (by decide)]); exact hl1)
              (by dsimp only [locs6, locs5]; (repeat rw [setLocal_ne (by decide)]); exact hl4)
              (by dsimp only [locs6, locs5]; (repeat rw [setLocal_ne (by decide)]); exact hl6)
              (by dsimp only [locs6]; rw [setLocal_self]) with
            ⟨v, st', h247, hdec, hext247, har, hasc⟩
          refine ⟨22 + 6 + 6 + 6 + 11, v, st', ?_, ?_,
            heapExtends_trans (heapExtends_alloc jh1 _) hext247, har, hasc⟩
          · rw [show 22 + 6 + 6 + 6 + 11 = (22 + 6) + 6 + 6 + 11 by omega, h67_99]
            split_res_fuel 6; conv => lhs; jvm_whnf_run_args
            rw [hrn_beq, runJvmResFast_ifne_bool_branch]; conv => lhs; jvm_whnf_run_args
            rw [runJvmResFast_invokestatic_step (hs := stepStatic_closed1_105_heap)]
            rw [runJvmResFast_stepResHeapChunk 3]; (conv => lhs; arg 1; jvm_whnf_blk)
            rw [afterResBlockChunk_cont]; (conv => lhs; norm_jvm_locals)
            rw [runJvmResFast_goto]; exact h247
          · simp only [hhash78, hrn_beq, ↓reduceIte]; exact hdec
        · have hrn_beq : (ruleLine == "#N") = false := beq_false_of_ne hrn
          let warnObj : Jvm.HeapObj AlgExt := .instance
            "com/alexvanyo/composelife/model/Life105Warning$UnexpectedInput"
            [("input", .str ruleLine), ("lineIndex", .i32 (i + 1)), ("columnIndex", .i32 3)]
          let warnAddr := jh1.objects.size
          let jh1a := (jh1.alloc warnObj).2
          let arr0Addr := jh1a.objects.size
          let jh1b := (jh1a.alloc (.objArray "java/lang/Object" #[])).2
          let wAddr := jh1b.objects.size
          let jh1c := (jh1b.alloc (.objArray "java/lang/Object" #[.null])).2
          let jh2 := jh1c.set wAddr (.objArray "java/lang/Object" #[.heapRef warnAddr])
          have hwAddr_gt : jh1.objects.size < wAddr := by
            simp [wAddr, jh1b, jh1a, Jvm.JvmHeap.alloc]; omega
          have hext12 : HeapExtends jh1 jh2 := by
            intro k obj hk
            have hklt : k < jh1.objects.size := by
              by_cases h : k < jh1.objects.size
              · exact h
              · simp only [Jvm.JvmHeap.get?] at hk
                rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at hk
                contradiction
            have hc : HeapExtends jh1 jh1c :=
              heapExtends_trans (heapExtends_alloc jh1 _)
                (heapExtends_trans (heapExtends_alloc jh1a _) (heapExtends_alloc jh1b _))
            have hkc := hc k obj hk
            have hne : k ≠ wAddr := by omega
            have hlt_w : wAddr < jh1c.objects.size := by
              simp [jh1c, wAddr, Jvm.JvmHeap.alloc]
            simp only [jh2, Jvm.JvmHeap.get?, Jvm.JvmHeap.set, hlt_w, ↓reduceDIte]
            rw [Array.getElem?_set_ne _ hne.symm]
            exact hkc
          have hw2 : jh2.get? wAddr =
              some (.objArray "java/lang/Object" #[.heapRef warnAddr]) := by
            have hlt : wAddr < jh1c.objects.size := by
              simp [jh1c, wAddr, Jvm.JvmHeap.alloc]
            simp [jh2, Jvm.JvmHeap.get?, Jvm.JvmHeap.set, hlt]
          have hba2 : jh2.get? bytesAddr = some (.byteArray bytes.data) := hext12 _ _ hba
          have hwarn2 : jh2.get? warnAddr = some warnObj := by
            have hget_a : jh1a.get? warnAddr = some warnObj := by
              simp [jh1a, warnAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
            have hget_c : jh1c.get? warnAddr = some warnObj :=
              heapExtends_alloc jh1b _ _ _ (heapExtends_alloc jh1a _ _ _ hget_a)
            have hlt_w : wAddr < jh1c.objects.size := by
              simp [jh1c, wAddr, Jvm.JvmHeap.alloc]
            have hne : warnAddr ≠ wAddr := by omega
            simp only [jh2, Jvm.JvmHeap.get?, Jvm.JvmHeap.set, hlt_w, ↓reduceDIte]
            rw [Array.getElem?_set_ne _ hne.symm]
            exact hget_c
          have hwfold2 : (#[(.heapRef warnAddr : JvmVal)]).foldlM
              (fun acc v => (decodeLife105Warning jh2 v).map acc.push) #[] =
              some #[.unexpectedInput ruleLine (i + 1) 3] := by
            simp [decodeLife105Warning, hwarn2, warnObj, List.lookup, Jvm.JvmVal.asI32]
          have harr1b : jh1b.get? arr0Addr = some (.objArray "java/lang/Object" #[]) := by
            simp [jh1b, arr0Addr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
          have harr1c : jh1c.get? arr0Addr = some (.objArray "java/lang/Object" #[]) :=
            heapExtends_alloc jh1b _ _ _ harr1b
          have hw1c : jh1c.get? wAddr = some (.objArray "java/lang/Object" #[.null]) := by
            simp [jh1c, wAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
          let locs6 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
            locs5 11 (.heapRef warnAddr)) 12 (.heapRef arr0Addr)) 14 (.heapRef wAddr))
            15 (.heapRef wAddr)) 16 (.i32 0)) 13 (.heapRef wAddr)) 7 (.heapRef wAddr)
          rcases deserializeLife105_exit247 (u64 := u64) (locs := locs6) hba2 hw2 hwfold2
              (by dsimp only [locs6, locs5]; (repeat rw [setLocal_ne (by decide)]); exact hl0)
              (by dsimp only [locs6, locs5]; (repeat rw [setLocal_ne (by decide)]); exact hl1)
              (by dsimp only [locs6, locs5]; (repeat rw [setLocal_ne (by decide)]); exact hl4)
              (by dsimp only [locs6, locs5]; (repeat rw [setLocal_ne (by decide)]); exact hl6)
              (by dsimp only [locs6]; rw [setLocal_self]) with
            ⟨v, st', h247, hdec, hext247, har, hasc⟩
          refine ⟨22 + 39 + 6 + 6 + 11, v, st', ?_, ?_, heapExtends_trans hext12 hext247,
            har, hasc⟩
          · rw [show 22 + 39 + 6 + 6 + 11 = (22 + 39) + 6 + 6 + 11 by omega, h67_99]
            split_res_fuel 39; conv => lhs; jvm_whnf_run_args
            rw [hrn_beq, runJvmResFast_ifne_bool_fallthrough]
            heap_step_nonbranch_chunks; rw [hl4', hl5]; dsimp only [Jvm.JvmVal.asI32]
            rw [runJvmResFast_invokespecial_step
              (hs := stepSpecial_life105WarningUnexpectedInput_init)]
            heap_step_nonbranch_chunks
            rw [runJvmResFast_anewarray_obj (hslt := by decide)]
            rw [show (0 : UInt32).toNat = 0 from rfl,
              show Array.replicate 0 JvmVal.null = #[] from rfl]
            heap_step_nonbranch_chunks
            rw [runJvmResFast_arraylength_obj (hget := harr1b)]
            heap_step_nonbranch_chunks
            rw [runJvmResFast_invokestatic_step
              (hs := stepStatic_arraysCopyOf_obj (hslt := by decide) (hget := harr1b))]
            rw [show (Array.ofFn (n := ((#[] : Array JvmVal).size.toUInt32 + 1).toNat)
                (fun i => if h : i.val < (#[] : Array JvmVal).size then
                  (#[] : Array JvmVal)[i.val] else JvmVal.null)) = #[JvmVal.null] from rfl]
            heap_step_nonbranch_chunks
            rw [runJvmResFast_invokestatic_step
              (hs := stepStatic_checkNotNullExpressionValue_heap rfl)]
            heap_step_nonbranch_chunks
            rw [runJvmResFast_arraylength_obj (hget := harr1c)]
            heap_step_nonbranch_chunks
            rw [runJvmResFast_aastore (hget := hw1c) (hslt := by decide) (hlt := by decide)]
            rw [show jh1c.set wAddr (.objArray "java/lang/Object"
                ((#[JvmVal.null]).set ((#[] : Array JvmVal).size.toUInt32).toNat
                  (.heapRef warnAddr) (by decide))) = jh2 from rfl]
            rw [runJvmResFast_stepResHeapChunk 4]; (conv => lhs; arg 1; jvm_whnf_blk)
            rw [afterResBlockChunk_cont]; (conv => lhs; norm_jvm_locals)
            rw [runJvmResFast_goto]
            exact h247
          · simp only [hhash78, hrn_beq, Bool.false_eq_true, ↓reduceIte]; exact hdec
      · have hne78 : (UInt32.ofBitVec (b1.toBitVec.signExtend 32) == 78) = false :=
          signExtend_bne_u32 hb1 rfl (by decide)
        have hnh78 : Algorithm.startsWithHash bytes 78 = false := by
          have h1_b : bytes.get! 1 = b1 := by
            simp [ByteArray.get!, getElem!_pos bytes.data 1 (by omega), b1]
          simp only [Algorithm.startsWithHash, h1_b, beq_false_of_ne hb1, Bool.and_false]
        rcases hruleR hnh78 with ⟨f143, v, st', hrun143, hdec, hext, har, hasc⟩
        refine ⟨f143 + 4 + 6 + 11, v, st', ?_, hdec, hext, har, hasc⟩
        rw [show f143 + 4 + 6 + 11 = ((f143 + 4) + 6) + 11 by omega, h67_78, h78_84]
        conv => lhs; jvm_whnf_run_args
        rw [runJvmResFast_if_icmpeq_fallthrough hne78]
        rw [runJvmResFast_iconst, runJvmResFast_istore, runJvmResFast_goto]
        rw [hloc9]; exact hrun143
    · have hne35 : (UInt32.ofBitVec (b0.toBitVec.signExtend 32) == 35) = false :=
        signExtend_bne_u32 hb0 rfl (by decide)
      have hnh78 : Algorithm.startsWithHash bytes 78 = false := by
        have h0_b : bytes.get! 0 = b0 := by
          simp [ByteArray.get!, getElem!_pos bytes.data 0 (by omega), b0]
        simp only [Algorithm.startsWithHash, h0_b, beq_false_of_ne hb0, Bool.and_false,
          Bool.false_and]
      rcases hruleR hnh78 with ⟨f143, v, st', hrun143, hdec, hext, har, hasc⟩
      refine ⟨f143 + 4 + 11, v, st', ?_, hdec, hext, har, hasc⟩
      rw [show f143 + 4 + 11 = (f143 + 4) + 11 by omega, h67_78]
      conv => lhs; jvm_whnf_run_args
      rw [runJvmResFast_if_icmpeq_fallthrough hne35]
      rw [runJvmResFast_iconst, runJvmResFast_istore, runJvmResFast_goto]
      rw [hloc9]; exact hrun143

theorem deserializeLife105_equiv
    (lines : Array String) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hlines31 : lines.size < 2 ^ 31)
    (hutf8 : ∀ k < lines.size, lines[k]!.toUTF8.data.size < 2 ^ 31)
    (hl0 : locs 0 = .strArr lines) :
    ∃ f v st',
      runJvmRes f f_Algorithm_deserializeLife105_prog ⟨0, [], locs, jh, hp⟩ = some (v, st') ∧
      decodeLife105Result st' v = some (Algorithm.deserializeLife105 lines) ∧
      HeapExtends jh st'.jvmHeap ∧
      st'.heap.arenas = hp.arenas ∧ st'.heap.asciiArrays = hp.asciiArrays := by
  rcases hp with ⟨ar, u64, asc⟩
  let numLines := lines.size.toUInt32
  have hnum_toNat : numLines.toNat = lines.size := by
    dsimp only [numLines]
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  let locs1 := setLocal locs 1 (.i32 numLines)
  by_cases h0 : numLines = 0
  · let res : Algorithm.Life105Result := ⟨.ok, #[.emptyFile], Algorithm.noCells⟩
    let enc := encodeLife105Result jh u64 res
    have hdes : Algorithm.deserializeLife105 lines = res := by
      rw [Algorithm.deserializeLife105]; simp [numLines, h0, res, Algorithm.noCells]
    rw [hdes]
    refine ⟨3 + 8, enc.1, ⟨270, [enc.1], locs1, enc.2.1, ⟨ar, enc.2.2, asc⟩⟩, ?_, ?_,
      heapExtends_encodeLife105Result jh u64 res, rfl, rfl⟩
    · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      change runJvmResFast (3 + 8) f_Algorithm_deserializeLife105_prog 0
          (f_Algorithm_deserializeLife105_prog.drop 0) ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ = _
      rw [deserializeLife105_0_8 hl0]
      split_res_fuel 3; conv => lhs; jvm_whnf_run_args
      rw [runJvmResFast_ifeq_branch (by simpa [numLines] using h0)]
      heap_step_nonbranch_chunks; conv => lhs; jvm_whnf_run_args
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_closed6_105_heap)]
      exact runJvmResFast_areturn
    · exact decodeLife105Result_encode jh ⟨ar, u64, asc⟩ res
  · have hpos : 0 < lines.size := by
      rcases Nat.eq_zero_or_pos lines.size with hz | hp
      · exfalso; apply h0; dsimp only [numLines]; rw [hz]; rfl
      · exact hp
    let header := lines[0]
    have hhdr_bang : lines[0]! = header := getElem!_pos lines 0 hpos
    let locs2 := setLocal (setLocal locs1 2 (.str header)) 3 (.str "#Life 1.05")
    by_cases hhdr : header = "#Life 1.05"
    · let i := Algorithm.skipDescriptions lines numLines 1
      let locs3 := setLocal locs2 4 (.i32 i)
      by_cases hi : i < numLines
      · have hi_nat : i.toNat < numLines.toNat := UInt32.lt_iff_toNat_lt.mp hi
        have hi_sz : i.toNat < lines.size := hnum_toNat ▸ hi_nat
        have hi_slt : i.toBitVec.slt 0#32 = false := u32_slt_zero_of_lt hi (by omega)
        let ruleLine := lines[i.toNat]
        have hrule_bang : lines[i.toNat]! = ruleLine := getElem!_pos lines i.toNat hi_sz
        let bytes := ruleLine.toByteArray
        have hutf8_sz : bytes.data.size < 2 ^ 31 := by
          change ruleLine.toUTF8.data.size < 2 ^ 31
          rw [← hrule_bang]; exact hutf8 i.toNat hi_sz
        let bytesAddr := jh.objects.size
        let jh1 := (jh.alloc (.byteArray bytes.data)).2
        have hba : jh1.get? bytesAddr = some (.byteArray bytes.data) := by
          simp [jh1, bytesAddr, Jvm.JvmHeap.get?, Jvm.JvmHeap.alloc]
        let locs4 := setLocal (setLocal (setLocal (setLocal (setLocal locs3
          5 (.str ruleLine)) 6 (.heapRef bytesAddr)) 7 .null) 8 (.i32 0)) 9 (.i32 0)
        rcases deserializeLife105_ruleN (locs := locs4) hba hutf8_sz
            (by dsimp only [locs4, locs3, locs2, locs1]
                (repeat rw [setLocal_ne (by decide)]); exact hl0)
            (by dsimp only [locs4, locs3, locs2, locs1]
                (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self])
            (by dsimp only [locs4, locs3]
                (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self])
            (by dsimp only [locs4]
                (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self])
            (by dsimp only [locs4]
                (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self])
            (by dsimp only [locs4]; rw [setLocal_self]) with
          ⟨f67, v, st', hrun67, hdec, hext67, har, hasc⟩
        have hdes : Algorithm.deserializeLife105 lines =
            if Algorithm.startsWithHash bytes 78 then
              if ruleLine == "#N" then
                Algorithm.parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0 #[]
                  Algorithm.U64Buf.empty
              else
                Algorithm.parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0
                  #[.unexpectedInput ruleLine (i + 1) 3] Algorithm.U64Buf.empty
            else if Algorithm.startsWithHash bytes 82 then
              if Algorithm.checkRuleLine bytes == 0 then
                Algorithm.parseBlocks lines numLines (i + 1) false bytes 0 0 false 0 0 0 #[]
                  Algorithm.U64Buf.empty
              else if Algorithm.checkRuleLine bytes == 1 then
                ⟨.unexpectedInput ruleLine (i + 1) 3, #[], Algorithm.noCells⟩
              else
                ⟨.ruleNotSupported, #[], Algorithm.noCells⟩
            else
              Algorithm.parseBlocks lines numLines i false bytes 0 0 false 0 0 0 #[]
                Algorithm.U64Buf.empty := by
          rw [Algorithm.deserializeLife105]
          simp only [show UInt32.ofNat lines.size ≠ 0 from h0, numLines, hhdr_bang, hhdr, i, hi,
            hrule_bang, bytes, beq_iff_eq, Algorithm.noCells]
          by_cases hrn : ruleLine = "#N" <;> simp [hrn]
        rw [hdes]
        refine ⟨f67 + 17 + 9 + 13 + 8, v, st', ?_, hdec,
          heapExtends_trans (heapExtends_alloc jh _) hext67, har, hasc⟩
        apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
        change runJvmResFast (f67 + 17 + 9 + 13 + 8) f_Algorithm_deserializeLife105_prog 0
            (f_Algorithm_deserializeLife105_prog.drop 0) ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ = _
        rw [show f67 + 17 + 9 + 13 + 8 = (((f67 + 17) + 9) + 13) + 8 by omega]
        rw [deserializeLife105_0_8 hl0]
        rw [deserializeLife105_8_21 h0 hpos (by rw [setLocal_ne (by decide)]; exact hl0)]
        rw [deserializeLife105_21_48 (locs := locs2) hhdr
          (by dsimp only [locs2, locs1]; (repeat rw [setLocal_ne (by decide)]); exact hl0)
          (by dsimp only [locs2, locs1]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self])]
        rw [deserializeLife105_48_67 (locs := locs3) hi hi_slt hi_sz
          (by dsimp only [locs3, locs2, locs1]; (repeat rw [setLocal_ne (by decide)]); exact hl0)
          (by dsimp only [locs3]; rw [setLocal_self])]
        exact hrun67
      · let res : Algorithm.Life105Result := ⟨.ok, #[], Algorithm.noCells⟩
        let enc := encodeLife105Result jh u64 res
        have hdes : Algorithm.deserializeLife105 lines = res := by
          rw [Algorithm.deserializeLife105]
          simp [numLines, h0, hhdr_bang, hhdr, i, hi, res, Algorithm.noCells]
        rw [hdes]
        refine ⟨3 + 9 + 13 + 8, enc.1, ⟨50, [enc.1], locs3, enc.2.1, ⟨ar, enc.2.2, asc⟩⟩,
          ?_, ?_, heapExtends_encodeLife105Result jh u64 res, rfl, rfl⟩
        · apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
          change runJvmResFast (3 + 9 + 13 + 8) f_Algorithm_deserializeLife105_prog 0
              (f_Algorithm_deserializeLife105_prog.drop 0) ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ = _
          rw [show 3 + 9 + 13 + 8 = ((3 + 9) + 13) + 8 by omega]
          rw [deserializeLife105_0_8 hl0]
          rw [deserializeLife105_8_21 h0 hpos (by rw [setLocal_ne (by decide)]; exact hl0)]
          rw [deserializeLife105_21_48 (locs := locs2) hhdr
            (by dsimp only [locs2, locs1]; (repeat rw [setLocal_ne (by decide)]); exact hl0)
            (by dsimp only [locs2, locs1]; (repeat rw [setLocal_ne (by decide)]); rw [setLocal_self])]
          split_res_fuel 3; conv => lhs; jvm_whnf_run_args
          rw [runJvmResFast_iflt_fallthrough (by
            rw [compareUnsigned_iflt_cond]; exact decide_eq_false hi)]
          heap_step_nonbranch_chunks
          rw [runJvmResFast_invokestatic_step (hs := stepStatic_closed2_105_heap)]
          exact runJvmResFast_areturn
        · exact decodeLife105Result_encode jh ⟨ar, u64, asc⟩ res
    · rcases deserializeLife105_invalidHeader (locs := locs2) hhdr
          (by dsimp only [locs2]; rw [setLocal_ne (by decide), setLocal_self]) with
        ⟨v, st', hinv, hdec, hext, har, hasc⟩
      have hdes : Algorithm.deserializeLife105 lines =
          ⟨.invalidHeader header, #[], Algorithm.noCells⟩ := by
        rw [Algorithm.deserializeLife105]; simp [numLines, h0, hhdr_bang, hhdr]
      rw [hdes]
      refine ⟨19 + 13 + 8, v, st', ?_, hdec, hext, har, hasc⟩
      apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
      change runJvmResFast (19 + 13 + 8) f_Algorithm_deserializeLife105_prog 0
          (f_Algorithm_deserializeLife105_prog.drop 0) ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ = _
      rw [show 19 + 13 + 8 = (19 + 13) + 8 by omega]
      rw [deserializeLife105_0_8 hl0]
      rw [deserializeLife105_8_21 h0 hpos (by rw [setLocal_ne (by decide)]; exact hl0)]
      exact hinv

end DeserializeLife105

end Algorithm.JvmVerification
