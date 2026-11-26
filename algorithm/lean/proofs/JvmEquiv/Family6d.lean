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

/-! ### Family 6d: `finishRLE` -/

private theorem list_drop_step6d {α : Type} {l : List α} {k : Nat} {x : α}
    (h : l[k]? = some x) : l.drop k = x :: l.drop (k + 1) := by
  induction k generalizing l with
  | zero => cases l <;> simp_all
  | succ k ih =>
    cases l with
    | nil => simp at h
    | cons a as => exact ih h

open Lean Elab Tactic in
elab "step_drop6d " n:num : tactic => do
  for _ in [:n.getNat] do
    evalTactic (← `(tactic| (conv => lhs; arg 4; rw [list_drop_step6d rfl]; try simp only [Nat.reduceAdd])))

private theorem HeapExtends_alloc6d {h : Jvm.JvmHeap AlgExt} (obj : Jvm.HeapObj AlgExt)
    {i : Nat} {o : Jvm.HeapObj AlgExt} (hget : h.get? i = some o) :
    (h.alloc obj).2.get? i = some o := by
  have hlt : i < h.objects.size := (Array.getElem?_eq_some_iff.mp hget).1
  exact (jvmHeap_get?_alloc_lt h obj hlt).trans hget

private theorem decodeRLEWarning_alloc6d {h1 : Jvm.JvmHeap AlgExt} (obj : Jvm.HeapObj AlgExt)
    {v : JvmVal} {w : Algorithm.RLEWarning}
    (hdec : decodeRLEWarning h1 v = some w) : decodeRLEWarning (h1.alloc obj).2 v = some w := by
  cases v with
  | allocRef cls =>
    by_cases hc : cls = "com/alexvanyo/composelife/model/RLEWarning$EmptyFile"
    · subst hc; simpa [decodeRLEWarning] using hdec
    · simp [decodeRLEWarning, hc] at hdec
  | heapRef a =>
    dsimp only [decodeRLEWarning] at hdec ⊢
    cases hg : h1.get? a with
    | none => simp [hg] at hdec
    | some o =>
      rw [hg] at hdec
      rw [HeapExtends_alloc6d obj hg]
      exact hdec
  | _ => simp [decodeRLEWarning] at hdec

private theorem mapM_decodeRLEWarning_alloc6d {h1 : Jvm.JvmHeap AlgExt} (obj : Jvm.HeapObj AlgExt)
    {vs : List JvmVal} {ws : List Algorithm.RLEWarning}
    (hm : vs.mapM (decodeRLEWarning h1) = some ws) :
    vs.mapM (decodeRLEWarning (h1.alloc obj).2) = some ws := by
  induction vs generalizing ws with
  | nil => simpa using hm
  | cons v vs ih =>
    simp only [List.mapM_cons] at hm ⊢
    cases hdv : decodeRLEWarning h1 v with
    | none => simp [hdv] at hm
    | some w =>
      rw [decodeRLEWarning_alloc6d obj hdv]
      rw [hdv] at hm
      cases hrest : vs.mapM (decodeRLEWarning h1) with
      | none => simp [hrest] at hm
      | some ws' =>
        rw [hrest] at hm
        rw [ih hrest]
        exact hm

private theorem setLocal_apply6d {Ext : Type} {locs : Nat → Jvm.JvmVal Ext} {idx i : Nat}
    {v : Jvm.JvmVal Ext} :
    setLocal locs idx v i = if (i == idx) = true then v else locs i := by
  simp [setLocal, Jvm.setLocal, beq_iff_eq]

open Lean Elab Tactic in
elab "step_res_plain6d " n:num : tactic => do
  for _ in [:n.getNat] do
    evalTactic (← `(tactic| rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]))
    evalTactic (← `(tactic| dsimp only [stepInstr, Jvm.stepInstr]))
    evalTactic (← `(tactic| try simp only [setLocal_apply6d, Jvm.JvmVal.asI32?, Jvm.JvmVal.asI64?,
      Nat.reduceAdd, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]))

private theorem growBuf_eq_empty_of6d {α : Type} {b : Algorithm.GrowBuf α}
    (he : b.data.isEmpty = true) (hz : b.size = 0) : b = Algorithm.GrowBuf.empty := by
  have hd : b.data = #[] := Array.isEmpty_iff.mp he
  rcases b with ⟨d, s⟩
  dsimp only at hd hz
  subst hd hz
  rfl

private theorem stepStatic_uintCtor6d
    {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, stk, locs, jh, hp⟩
      "kotlin/UInt" "constructor-impl" "(I)I" =
      .inl (some ⟨pc + 1, stk, locs, jh, hp⟩) := rfl

private theorem runJvmResFast_areturn6d {f pc : Nat} {prog rest : List JvmInstr} {v : JvmVal}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.areturn :: rest) ⟨pc, v :: stk, locs, jh, hp⟩ =
      some (v, ⟨pc, v :: stk, locs, jh, hp⟩) := by
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  have hstep : stepInstr .areturn ⟨pc, v :: stk, locs, jh, hp⟩ = .inr (some v) := rfl
  rw [hstep]

private theorem int32_toInt32_toUInt32_6d (x : Int32) : x.toUInt32.toInt32 = x := by
  cases x; rfl

private theorem list_foldl_encodePure6d {α : Type} (xs : List α) (f : α → JvmVal)
    (acc : Array JvmVal) (h : Jvm.JvmHeap AlgExt) :
    xs.foldl (fun p x => (p.1.push (f x), p.2)) (acc, h) =
      ((acc.toList ++ xs.map f).toArray, h) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [Array.toList_push, List.append_assoc]

private theorem encodeGrowBufArray_pure6d {α : Type} (b : Algorithm.GrowBuf α) (f : α → JvmVal)
    (h : Jvm.JvmHeap AlgExt) :
    encodeGrowBufArray h (fun ch x => (f x, ch)) b =
      let (addr, h') := h.alloc (.objArray "java/lang/Object" (b.toArray.map f))
      (.heapRef addr, h') := by
  dsimp only [encodeGrowBufArray]
  rw [← Array.foldl_toList]
  rw [list_foldl_encodePure6d b.toArray.toList f #[] h]
  have hmap : (b.toArray.toList.map f).toArray = b.toArray.map f := by
    apply Array.ext
    · simp
    · intro i hi1 hi2; simp
  simp [hmap]

private theorem stepStatic_growBufToArray_str6d
    {pc : Nat} {b : Algorithm.GrowBuf String}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .ext (.strGrowBuf b) :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg" "(Ljava/lang/Object;)[Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .strArr b.toArray :: rest, locs, jh, hp⟩) := rfl

private inductive RleWarnRep6d : Algorithm.GrowBuf Algorithm.RLEWarning → JvmVal → Prop
  | empty (d : Algorithm.GrowBuf String) :
      d.data.isEmpty = true → d.size = 0 →
      RleWarnRep6d Algorithm.GrowBuf.empty (.ext (.strGrowBuf d))
  | full (b : Algorithm.GrowBuf Algorithm.RLEWarning) :
      RleWarnRep6d b (.ext (.rleWarnGrowBuf b))

private def decodeRLEWarnings6d (h : Jvm.JvmHeap AlgExt) : JvmVal → Option (Array Algorithm.RLEWarning)
  | .strArr xs => if xs.isEmpty then some #[] else none
  | .heapRef addr =>
    match h.get? addr with
    | some (.objArray _ elems) => (elems.toList.mapM (decodeRLEWarning h)).map List.toArray
    | _ => none
  | _ => none

private def decodeRLEResult6d (st : JvmState) : JvmVal → Option Algorithm.RLEResult
  | .heapRef addr =>
    match st.jvmHeap.get? addr with
    | some (.instance "com/alexvanyo/composelife/model/RLEResult" flds) =>
      match flds.lookup "status", flds.lookup "warnings", flds.lookup "cells" with
      | some (.ext (.rleStatus status)), some warnsVal, some (.ext (.u64Ref cId)) =>
        match decodeRLEWarnings6d st.jvmHeap warnsVal, st.heap.u64Arrays[cId]? with
        | some warns, some cells => some ⟨status, warns, cells⟩
        | _, _ => none
      | _, _, _ => none
    | _ => none
  | _ => none

private theorem decodeRLEWarning_encode6d (h : Jvm.JvmHeap AlgExt) (w : Algorithm.RLEWarning) :
    decodeRLEWarning (encodeRLEWarning h w).2 (encodeRLEWarning h w).1 = some w := by
  cases w with
  | emptyFile => simp [encodeRLEWarning, decodeRLEWarning]
  | duplicateOffset ln x y =>
    have hget := jvmHeap_get?_alloc_self h
      (Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEWarning$DuplicateOffset"
        [("lineIndex", .i32 ln), ("x", .i32 x.toUInt32), ("y", .i32 y.toUInt32)])
    dsimp only [Jvm.JvmHeap.alloc] at hget
    dsimp only [encodeRLEWarning, decodeRLEWarning, Jvm.JvmHeap.alloc]
    rw [hget]
    change some (Algorithm.RLEWarning.duplicateOffset ln x.toUInt32.toInt32 y.toUInt32.toInt32) = _
    simp only [int32_toInt32_toUInt32_6d]
  | unexpectedChar ln col cp =>
    have hget := jvmHeap_get?_alloc_self h
      (Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEWarning$UnexpectedChar"
        [("lineIndex", .i32 ln), ("columnIndex", .i32 col), ("codePoint", .i32 cp)])
    dsimp only [Jvm.JvmHeap.alloc] at hget
    dsimp only [encodeRLEWarning, decodeRLEWarning, Jvm.JvmHeap.alloc]
    rw [hget]
    rfl
  | unexpectedInput ln col inp =>
    have hget := jvmHeap_get?_alloc_self h
      (Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEWarning$UnexpectedInput"
        [("lineIndex", .i32 ln), ("columnIndex", .i32 col), ("input", .str inp)])
    dsimp only [Jvm.JvmHeap.alloc] at hget
    dsimp only [encodeRLEWarning, decodeRLEWarning, Jvm.JvmHeap.alloc]
    rw [hget]
    rfl
  | charAfterEnd ln col cp =>
    have hget := jvmHeap_get?_alloc_self h
      (Jvm.HeapObj.instance "com/alexvanyo/composelife/model/RLEWarning$CharAfterEnd"
        [("lineIndex", .i32 ln), ("columnIndex", .i32 col), ("codePoint", .i32 cp)])
    dsimp only [Jvm.JvmHeap.alloc] at hget
    dsimp only [encodeRLEWarning, decodeRLEWarning, Jvm.JvmHeap.alloc]
    rw [hget]
    rfl

private theorem encodeGrowBufArray_warns_foldl6d (h : Jvm.JvmHeap AlgExt)
    (xs : List Algorithm.RLEWarning) (acc : Array JvmVal) (pfx : List Algorithm.RLEWarning)
    (hpfx : acc.toList.mapM (decodeRLEWarning h) = some pfx) :
    let res := xs.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) w =>
      let (v, nh) := encodeRLEWarning p.2 w; (p.1.push v, nh)) (acc, h)
    res.1.toList.mapM (decodeRLEWarning res.2) = some (pfx ++ xs) ∧
    (∀ i o, h.get? i = some o → res.2.get? i = some o) ∧
    res.2.statics = h.statics := by
  induction xs generalizing acc h pfx with
  | nil => exact ⟨by simpa using hpfx, fun _ _ hi => hi, rfl⟩
  | cons x xs ih =>
    simp only [List.foldl_cons]
    let e := encodeRLEWarning h x
    have hstep_alloc : ∀ i o, h.get? i = some o → e.2.get? i = some o := by
      intro i o hi
      cases x <;> simp only [e, encodeRLEWarning] at *
      all_goals try exact hi
      all_goals exact HeapExtends_alloc6d _ hi
    have hstat_eq : e.2.statics = h.statics := by
      cases x <;> simp [e, encodeRLEWarning]
      all_goals rfl
    have henc : decodeRLEWarning e.2 e.1 = some x := decodeRLEWarning_encode6d h x
    have hpfx' : (acc.push e.1).toList.mapM (decodeRLEWarning e.2) = some (pfx ++ [x]) := by
      have hm1 : acc.toList.mapM (decodeRLEWarning e.2) = some pfx := by
        cases x <;> simp only [e, encodeRLEWarning] at *
        all_goals try exact hpfx
        all_goals exact mapM_decodeRLEWarning_alloc6d _ hpfx
      simp [Array.toList_push, List.mapM_append, hm1, henc]
    rcases ih e.2 (acc.push e.1) (pfx ++ [x]) hpfx' with ⟨hmap, hext, hst⟩
    refine ⟨by simpa [List.append_assoc] using hmap, fun i o hi => hext i o (hstep_alloc i o hi),
      hst.trans hstat_eq⟩

private theorem stepStatic_growBufToArray_u32Pair6d
    {pc : Nat} {b : Algorithm.GrowBuf (UInt32 × UInt32)}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .ext (.u32PairGrowBuf b) :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg" "(Ljava/lang/Object;)[Ljava/lang/Object;" =
      let (addr, h') := jh.alloc (.objArray "java/lang/Object"
        (b.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2)))
      .inl (some ⟨pc + 1, .heapRef addr :: rest, locs, h', hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .ext (.u32PairGrowBuf b) :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg" "(Ljava/lang/Object;)[Ljava/lang/Object;" =
      let res := encodeGrowBufArray jh (fun ch x =>
        (.pair (.boxedUInt x.1) (.boxedUInt x.2), ch)) b
      .inl (some ⟨pc + 1, res.1 :: rest, locs, res.2, hp⟩) := rfl
  rw [hfn, encodeGrowBufArray_pure6d]

private theorem stepStatic_u64BufEmpty6d
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_U64Buf_empty" "()[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref hp.u64Arrays.length) :: rest, locs, jh,
        { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }⟩) := rfl

private theorem stepStatic_u64BufToArray6d
    {pc cId : Nat} {arr : Array UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} (hc : hp.u64Arrays[cId]? = some arr) :
    stepInvokeStatic ⟨pc, .ext (.u64Ref cId) :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_U64Buf_toArray-QwZRm1k" "([J)[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref hp.u64Arrays.length) :: rest, locs, jh,
        { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.toArray arr] }⟩) := by
  have hfn : stepInvokeStatic ⟨pc, .ext (.u64Ref cId) :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_U64Buf_toArray-QwZRm1k" "([J)[J" =
      match hp.u64Arrays[cId]? with
      | some arr' => .inl (some ⟨pc + 1, .ext (.u64Ref hp.u64Arrays.length) :: rest, locs, jh,
        { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.toArray arr'] }⟩)
      | none => .inr none := rfl
  rw [hfn, hc]

private theorem stepStatic_expandRuns6d
    {pc runsAddr cId : Nat} {runs : Array (UInt32 × UInt32)} {cells : Array UInt64}
    {numRuns j k : UInt32} {x y startX : Int32}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hget : jh.get? runsAddr = some (.objArray "java/lang/Object"
      (runs.map fun p => .pair (.boxedUInt p.1) (.boxedUInt p.2))))
    (hc : hp.u64Arrays[cId]? = some cells) :
    stepInvokeStatic ⟨pc, .ext (.u64Ref cId) :: .i32 startX.toUInt32 :: .i32 y.toUInt32 ::
        .i32 x.toUInt32 :: .i32 k :: .i32 j :: .i32 numRuns :: .heapRef runsAddr :: rest,
        locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_expandRuns-Wy9PQLY" "([Ljava/lang/Object;IIIIII[J)[J" =
      let res := Algorithm.expandRuns runs numRuns j k x y startX cells
      .inl (some ⟨pc + 1, .ext (.u64Ref hp.u64Arrays.length) :: rest, locs, jh,
        { hp with u64Arrays := hp.u64Arrays ++ [res] }⟩) := by
  have hfold : (runs.map fun p => JvmVal.pair (.boxedUInt p.1) (.boxedUInt p.2)).foldlM
      (fun acc (v : JvmVal) => match v with
        | .pair a b => do
          let ad ← unboxI32? a
          let bd ← unboxI32? b
          some (acc.push (ad, bd))
        | _ => none) #[] = some runs := by
    rw [← Array.foldlM_toList, Array.toList_map, List.foldlM_map]
    have hgen : ∀ (xs : List (UInt32 × UInt32)) (acc : Array (UInt32 × UInt32)),
        xs.foldlM (fun acc p => some (acc.push (p.1, p.2))) acc =
          some (acc.toList ++ xs).toArray := by
      intro xs
      induction xs with
      | nil => intro acc; simp
      | cons p xs ih =>
        intro acc
        simp only [List.foldlM_cons, bind, Option.bind_some]
        rw [ih (acc.push p)]
        simp [Array.toList_push, List.append_assoc]
    simpa [unboxI32?] using hgen runs.toList #[]
  have hfn : stepInvokeStatic ⟨pc, .ext (.u64Ref cId) :: .i32 startX.toUInt32 ::
      .i32 y.toUInt32 :: .i32 x.toUInt32 :: .i32 k :: .i32 j :: .i32 numRuns ::
      .heapRef runsAddr :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_expandRuns-Wy9PQLY" "([Ljava/lang/Object;IIIIII[J)[J" =
      match jh.get? runsAddr, hp.u64Arrays[cId]? with
      | some (.objArray _ elems), some cells' =>
        match elems.foldlM (fun acc v => match v with
            | .pair a b => do
              let ad ← unboxI32? a
              let bd ← unboxI32? b
              some (acc.push (ad, bd))
            | _ => none) #[] with
        | some runs' =>
          let res := Algorithm.expandRuns runs' numRuns j k
            x.toUInt32.toInt32 y.toUInt32.toInt32 startX.toUInt32.toInt32 cells'
          .inl (some ⟨pc + 1, .ext (.u64Ref hp.u64Arrays.length) :: rest, locs, jh,
            { hp with u64Arrays := hp.u64Arrays ++ [res] }⟩)
        | none => .inr none
      | _, _ => .inr none := rfl
  rw [hfn, hget, hc]
  dsimp only
  erw [hfold]
  simp only [int32_toInt32_toUInt32_6d]

private theorem stepSpecial_rleResultInit6d
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

private theorem finishRLE_empty_run6d
    (d : Algorithm.GrowBuf String) (runs : Algorithm.GrowBuf (UInt32 × UInt32))
    (startX startY : Int32) (jh jh1 jhRes : Jvm.JvmHeap AlgExt) (hp hp3 : AlgHeap)
    (rRuns rRes : Nat) (hstat1 : jh1.statics = [])
    (hrRuns : jh.alloc (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2))) = (rRuns, jh1))
    (hgetRuns1 : jh1.get? rRuns = some (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2))))
    (hc0 : { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }.u64Arrays[hp.u64Arrays.length]? =
      some Algorithm.U64Buf.empty)
    (hc1 : let hp1 : AlgHeap := { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }
      let c1 := Algorithm.expandRuns runs.toArray runs.toArray.size.toUInt32 0 0 startX startY startX
        Algorithm.U64Buf.empty
      let hp2 : AlgHeap := { hp1 with u64Arrays := hp1.u64Arrays ++ [c1] }
      hp2.u64Arrays[hp1.u64Arrays.length]? = some c1)
    (hrRes : jh1.alloc (.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus .ok)), ("warnings", .strArr d.toArray),
       ("cells", .ext (.u64Ref (hp.u64Arrays.length + 2)))]) = (rRes, jhRes))
    (hhp3 : hp3 =
      let hp1 : AlgHeap := { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }
      let c1 := Algorithm.expandRuns runs.toArray runs.toArray.size.toUInt32 0 0 startX startY startX
        Algorithm.U64Buf.empty
      let hp2 : AlgHeap := { hp1 with u64Arrays := hp1.u64Arrays ++ [c1] }
      { hp2 with u64Arrays := hp2.u64Arrays ++ [Algorithm.U64Buf.toArray c1] }) :
    ∃ locsF,
      runJvmRes 40 f_Algorithm_finishRLE_prog
        { initJvmState [(0, .ext (.strGrowBuf d)), (1, .ext (.u32PairGrowBuf runs)),
            (2, .i32 startX.toUInt32), (3, .i32 startY.toUInt32)]
          with jvmHeap := jh, heap := hp } =
        some (.heapRef rRes, ⟨35, [.heapRef rRes], locsF, jhRes, hp3⟩) := by
  subst hhp3
  apply Exists.intro _
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  change runJvmResFast 40 f_Algorithm_finishRLE_prog 0 f_Algorithm_finishRLE_prog
    ⟨0, [], setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
      0 (.ext (.strGrowBuf d))) 1 (.ext (.u32PairGrowBuf runs))) 2 (.i32 startX.toUInt32))
      3 (.i32 startY.toUInt32), jh, hp⟩ = _
  conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_finishRLE_prog)]
  step_drop6d 20
  step_res_plain6d 1
  rw [runJvmResFast_invokestatic_step stepStatic_growBufToArray_u32Pair6d]
  have hrRuns1 : (jh.alloc (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2)))).1 = rRuns :=
    congrArg Prod.fst hrRuns
  have hrRuns2 : (jh.alloc (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2)))).2 = jh1 :=
    congrArg Prod.snd hrRuns
  dsimp only [Jvm.JvmHeap.alloc] at hrRuns1 hrRuns2
  rw [hrRuns1, hrRuns2]
  step_res_plain6d 1
  rw [runJvmResFast_getstatic_step hstat1 (by rfl)]
  step_res_plain6d 2
  rw [runJvmResFast_invokestatic_step stepStatic_growBufToArray_str6d]
  step_res_plain6d 2
  rw [runJvmResFast_arraylength_obj hgetRuns1]
  rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6d]
  step_res_plain6d 1
  rw [runJvmResFast_invokestatic_step stepStatic_u64BufEmpty6d]
  step_drop6d 16
  step_res_plain6d 9
  have hszRuns : UInt32.ofNat (runs.toArray.map fun x =>
      (JvmVal.pair (.boxedUInt x.1) (.boxedUInt x.2) : JvmVal)).size =
      runs.toArray.size.toUInt32 := by rw [Array.size_map]
  rw [hszRuns]
  rw [runJvmResFast_invokestatic_step (stepStatic_expandRuns6d hgetRuns1 hc0)]
  step_res_plain6d 2
  rw [runJvmResFast_invokestatic_step (stepStatic_u64BufToArray6d hc1)]
  step_res_plain6d 1
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  dsimp only [stepInstr, Jvm.stepInstr]
  simp only [show ("com/alexvanyo/composelife/model/RLEResult" == "java/lang/StringBuilder") = false from rfl,
    Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
  step_res_plain6d 2
  rw [runJvmResFast_checkcast_step rfl]
  step_res_plain6d 3
  rw [runJvmResFast_invokespecial_step stepSpecial_rleResultInit6d]
  simp only [List.length_append, List.length_singleton]
  have hrRes1 : (jh1.alloc (.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus .ok)), ("warnings", .strArr d.toArray),
       ("cells", .ext (.u64Ref (hp.u64Arrays.length + 2)))])).1 = rRes :=
    congrArg Prod.fst hrRes
  have hrRes2 : (jh1.alloc (.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus .ok)), ("warnings", .strArr d.toArray),
       ("cells", .ext (.u64Ref (hp.u64Arrays.length + 2)))])).2 = jhRes :=
    congrArg Prod.snd hrRes
  dsimp only [Jvm.JvmHeap.alloc] at hrRes1 hrRes2
  rw [hrRes1, hrRes2]
  rw [runJvmResFast_areturn6d]

private theorem finishRLE_full_run6d
    (warns : Algorithm.GrowBuf Algorithm.RLEWarning) (runs : Algorithm.GrowBuf (UInt32 × UInt32))
    (startX startY : Int32) (jh jh1 jh2 jhRes : Jvm.JvmHeap AlgExt) (hp hp3 : AlgHeap)
    (rRuns rWarns rRes : Nat) (hstat1 : jh1.statics = [])
    (hrRuns : jh.alloc (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2))) = (rRuns, jh1))
    (foldRes : Array JvmVal × Jvm.JvmHeap AlgExt)
    (hfold : warns.toArray.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) w =>
      (p.1.push (encodeRLEWarning p.2 w).1, (encodeRLEWarning p.2 w).2)) (#[], jh1) = foldRes)
    (hrWarns : foldRes.2.alloc (.objArray "java/lang/Object" foldRes.1) = (rWarns, jh2))
    (hgetRuns2 : jh2.get? rRuns = some (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2))))
    (hc0 : { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }.u64Arrays[hp.u64Arrays.length]? =
      some Algorithm.U64Buf.empty)
    (hc1 : let hp1 : AlgHeap := { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }
      let c1 := Algorithm.expandRuns runs.toArray runs.toArray.size.toUInt32 0 0 startX startY startX
        Algorithm.U64Buf.empty
      let hp2 : AlgHeap := { hp1 with u64Arrays := hp1.u64Arrays ++ [c1] }
      hp2.u64Arrays[hp1.u64Arrays.length]? = some c1)
    (hrRes : jh2.alloc (.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus .ok)), ("warnings", .heapRef rWarns),
       ("cells", .ext (.u64Ref (hp.u64Arrays.length + 2)))]) = (rRes, jhRes))
    (hhp3 : hp3 =
      let hp1 : AlgHeap := { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }
      let c1 := Algorithm.expandRuns runs.toArray runs.toArray.size.toUInt32 0 0 startX startY startX
        Algorithm.U64Buf.empty
      let hp2 : AlgHeap := { hp1 with u64Arrays := hp1.u64Arrays ++ [c1] }
      { hp2 with u64Arrays := hp2.u64Arrays ++ [Algorithm.U64Buf.toArray c1] }) :
    ∃ locsF,
      runJvmRes 40 f_Algorithm_finishRLE_prog
        { initJvmState [(0, .ext (.rleWarnGrowBuf warns)), (1, .ext (.u32PairGrowBuf runs)),
            (2, .i32 startX.toUInt32), (3, .i32 startY.toUInt32)]
          with jvmHeap := jh, heap := hp } =
        some (.heapRef rRes, ⟨35, [.heapRef rRes], locsF, jhRes, hp3⟩) := by
  subst hhp3
  apply Exists.intro _
  apply runJvmRes_of_runJvmResFast0 _ _ _ _ rfl
  change runJvmResFast 40 f_Algorithm_finishRLE_prog 0 f_Algorithm_finishRLE_prog
    ⟨0, [], setLocal (setLocal (setLocal (setLocal (fun _ => .i32 0)
      0 (.ext (.rleWarnGrowBuf warns))) 1 (.ext (.u32PairGrowBuf runs))) 2 (.i32 startX.toUInt32))
      3 (.i32 startY.toUInt32), jh, hp⟩ = _
  conv => lhs; arg 4; rw [← List.drop_zero (l := f_Algorithm_finishRLE_prog)]
  step_drop6d 20
  step_res_plain6d 1
  rw [runJvmResFast_invokestatic_step stepStatic_growBufToArray_u32Pair6d]
  have hrRuns1 : (jh.alloc (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2)))).1 = rRuns :=
    congrArg Prod.fst hrRuns
  have hrRuns2 : (jh.alloc (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2)))).2 = jh1 :=
    congrArg Prod.snd hrRuns
  dsimp only [Jvm.JvmHeap.alloc] at hrRuns1 hrRuns2
  rw [hrRuns1, hrRuns2]
  step_res_plain6d 1
  rw [runJvmResFast_getstatic_step hstat1 (by rfl)]
  step_res_plain6d 2
  have hgw : ∀ rest6 locs6, stepInvokeStatic ⟨6, .ext (.rleWarnGrowBuf warns) :: rest6,
      locs6, jh1, hp⟩
      "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
      "(Ljava/lang/Object;)[Ljava/lang/Object;" =
      .inl (some ⟨7, .heapRef rWarns :: rest6, locs6, jh2, hp⟩) := by
    intro rest6 locs6
    have hfn : stepInvokeStatic ⟨6, .ext (.rleWarnGrowBuf warns) :: rest6, locs6, jh1, hp⟩
        "com/alexvanyo/composelife/model/RleLeanKt" "f_Algorithm_GrowBuf_toArray___redArg"
        "(Ljava/lang/Object;)[Ljava/lang/Object;" =
        let res := encodeGrowBufArray jh1 encodeRLEWarning warns
        .inl (some ⟨7, res.1 :: rest6, locs6, res.2, hp⟩) := rfl
    rw [hfn]
    dsimp only [encodeGrowBufArray]
    rw [hfold, hrWarns]
  rw [runJvmResFast_invokestatic_step (hgw _ _)]
  step_res_plain6d 2
  rw [runJvmResFast_arraylength_obj hgetRuns2]
  rw [runJvmResFast_invokestatic_step stepStatic_uintCtor6d]
  step_res_plain6d 1
  rw [runJvmResFast_invokestatic_step stepStatic_u64BufEmpty6d]
  step_drop6d 16
  step_res_plain6d 9
  have hszRuns : UInt32.ofNat (runs.toArray.map fun x =>
      (JvmVal.pair (.boxedUInt x.1) (.boxedUInt x.2) : JvmVal)).size =
      runs.toArray.size.toUInt32 := by rw [Array.size_map]
  rw [hszRuns]
  rw [runJvmResFast_invokestatic_step (stepStatic_expandRuns6d hgetRuns2 hc0)]
  step_res_plain6d 2
  rw [runJvmResFast_invokestatic_step (stepStatic_u64BufToArray6d hc1)]
  step_res_plain6d 1
  rw [runJvmResFast_step_nonbranch (hbr := rfl) (hno := by simp)]
  dsimp only [stepInstr, Jvm.stepInstr]
  simp only [show ("com/alexvanyo/composelife/model/RLEResult" == "java/lang/StringBuilder") = false from rfl,
    Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd]
  step_res_plain6d 2
  rw [runJvmResFast_checkcast_step rfl]
  step_res_plain6d 3
  rw [runJvmResFast_invokespecial_step stepSpecial_rleResultInit6d]
  simp only [List.length_append, List.length_singleton]
  have hrRes1 : (jh2.alloc (.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus .ok)), ("warnings", .heapRef rWarns),
       ("cells", .ext (.u64Ref (hp.u64Arrays.length + 2)))])).1 = rRes :=
    congrArg Prod.fst hrRes
  have hrRes2 : (jh2.alloc (.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus .ok)), ("warnings", .heapRef rWarns),
       ("cells", .ext (.u64Ref (hp.u64Arrays.length + 2)))])).2 = jhRes :=
    congrArg Prod.snd hrRes
  dsimp only [Jvm.JvmHeap.alloc] at hrRes1 hrRes2
  rw [hrRes1, hrRes2]
  rw [runJvmResFast_areturn6d]

private theorem list_push3_get6d {α : Type} (l : List α) (c0 c1 c2 : α) :
    (((l ++ [c0]) ++ [c1]) ++ [c2])[l.length + 2]? = some c2 := by
  simp [List.append_assoc]

private theorem decode_empty_ok6d
    (d : Algorithm.GrowBuf String) (runs : Algorithm.GrowBuf (UInt32 × UInt32))
    (startX startY : Int32) (jhRes : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hp3 : AlgHeap)
    (rRes : Nat) (locsF : Nat → JvmVal)
    (hd1 : d.data.isEmpty = true) (hd2 : d.size = 0)
    (hgetRes : jhRes.get? rRes = some (.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus .ok)), ("warnings", .strArr d.toArray),
       ("cells", .ext (.u64Ref (hp.u64Arrays.length + 2)))]))
    (hc2 : hp3.u64Arrays[hp.u64Arrays.length + 2]? = some (Algorithm.U64Buf.toArray
      (Algorithm.expandRuns runs.toArray runs.toArray.size.toUInt32 0 0 startX startY startX
        Algorithm.U64Buf.empty))) :
    decodeRLEResult6d ⟨35, [.heapRef rRes], locsF, jhRes, hp3⟩ (.heapRef rRes) =
      some (Algorithm.finishRLE Algorithm.GrowBuf.empty runs startX startY) := by
  have hemp : d.toArray.isEmpty = true := by rw [growBuf_eq_empty_of6d hd1 hd2]; rfl
  have hw : (Algorithm.GrowBuf.empty : Algorithm.GrowBuf Algorithm.RLEWarning).toArray = #[] := by
    simp [Algorithm.GrowBuf.empty, Algorithm.GrowBuf.toArray]
  simp only [decodeRLEResult6d, hgetRes, List.lookup,
    show ("status" == "status") = true from rfl,
    show ("warnings" == "status") = false from rfl,
    show ("warnings" == "warnings") = true from rfl,
    show ("cells" == "status") = false from rfl,
    show ("cells" == "warnings") = false from rfl,
    show ("cells" == "cells") = true from rfl,
    decodeRLEWarnings6d, hemp, ↓reduceIte, hc2, Algorithm.finishRLE, hw]

private theorem decode_full_ok6d
    (warns : Algorithm.GrowBuf Algorithm.RLEWarning) (runs : Algorithm.GrowBuf (UInt32 × UInt32))
    (startX startY : Int32) (jhRes : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (hp3 : AlgHeap)
    (rWarns rRes : Nat) (locsF : Nat → JvmVal) (warnsElems : Array JvmVal)
    (hgetRes : jhRes.get? rRes = some (.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus .ok)), ("warnings", .heapRef rWarns),
       ("cells", .ext (.u64Ref (hp.u64Arrays.length + 2)))]))
    (hgetWarn : jhRes.get? rWarns = some (.objArray "java/lang/Object" warnsElems))
    (hmap : warnsElems.toList.mapM (decodeRLEWarning jhRes) = some warns.toArray.toList)
    (hc2 : hp3.u64Arrays[hp.u64Arrays.length + 2]? = some (Algorithm.U64Buf.toArray
      (Algorithm.expandRuns runs.toArray runs.toArray.size.toUInt32 0 0 startX startY startX
        Algorithm.U64Buf.empty))) :
    decodeRLEResult6d ⟨35, [.heapRef rRes], locsF, jhRes, hp3⟩ (.heapRef rRes) =
      some (Algorithm.finishRLE warns runs startX startY) := by
  simp only [decodeRLEResult6d, hgetRes, List.lookup,
    show ("status" == "status") = true from rfl,
    show ("warnings" == "status") = false from rfl,
    show ("warnings" == "warnings") = true from rfl,
    show ("cells" == "status") = false from rfl,
    show ("cells" == "warnings") = false from rfl,
    show ("cells" == "cells") = true from rfl,
    decodeRLEWarnings6d, hgetWarn, hmap, hc2, Algorithm.finishRLE]
  simp

private theorem finishRLE_empty_equiv6d
    (d : Algorithm.GrowBuf String) (runs : Algorithm.GrowBuf (UInt32 × UInt32))
    (startX startY : Int32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hd1 : d.data.isEmpty = true) (hd2 : d.size = 0) (hstat : jh.statics = []) :
    ∃ fuel st',
      runJvmRes fuel f_Algorithm_finishRLE_prog
        { initJvmState [(0, .ext (.strGrowBuf d)), (1, .ext (.u32PairGrowBuf runs)),
            (2, .i32 startX.toUInt32), (3, .i32 startY.toUInt32)]
          with jvmHeap := jh, heap := hp } = some st' ∧
      decodeRLEResult6d st'.2 st'.1 =
        some (Algorithm.finishRLE Algorithm.GrowBuf.empty runs startX startY) ∧
      (∀ i o, jh.get? i = some o → st'.2.jvmHeap.get? i = some o) := by
  obtain ⟨rRuns, jh1, hrRuns⟩ : ∃ r j, jh.alloc (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2))) = (r, j) := ⟨_, _, rfl⟩
  have hstat1 : jh1.statics = [] := by
    have : jh1 = (jh.alloc (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2)))).2 := congrArg Prod.snd hrRuns.symm
    rw [this]; exact hstat
  have hgetRuns1 : jh1.get? rRuns = some (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2))) := by
    have h1 : rRuns = (jh.alloc _).1 := congrArg Prod.fst hrRuns.symm
    have h2 : jh1 = (jh.alloc _).2 := congrArg Prod.snd hrRuns.symm
    rw [h1, h2]; exact jvmHeap_get?_alloc_self _ _
  have hc0 : { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }.u64Arrays[hp.u64Arrays.length]? =
      some Algorithm.U64Buf.empty := by simp
  have hc1 : let hp1 : AlgHeap := { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }
      let c1 := Algorithm.expandRuns runs.toArray runs.toArray.size.toUInt32 0 0 startX startY startX
        Algorithm.U64Buf.empty
      let hp2 : AlgHeap := { hp1 with u64Arrays := hp1.u64Arrays ++ [c1] }
      hp2.u64Arrays[hp1.u64Arrays.length]? = some c1 := by simp
  obtain ⟨hp3, hhp3⟩ : ∃ hp3 : AlgHeap, hp3 =
      let hp1 : AlgHeap := { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }
      let c1 := Algorithm.expandRuns runs.toArray runs.toArray.size.toUInt32 0 0 startX startY startX
        Algorithm.U64Buf.empty
      let hp2 : AlgHeap := { hp1 with u64Arrays := hp1.u64Arrays ++ [c1] }
      { hp2 with u64Arrays := hp2.u64Arrays ++ [Algorithm.U64Buf.toArray c1] } := ⟨_, rfl⟩
  obtain ⟨rRes, jhRes, hrRes⟩ : ∃ r j, jh1.alloc (.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus .ok)), ("warnings", .strArr d.toArray),
       ("cells", .ext (.u64Ref (hp.u64Arrays.length + 2)))]) = (r, j) := ⟨_, _, rfl⟩
  have hrun := finishRLE_empty_run6d d runs startX startY jh jh1 jhRes hp hp3 rRuns rRes
    hstat1 hrRuns hgetRuns1 hc0 hc1 hrRes hhp3
  rcases hrun with ⟨locsF, hrun⟩
  have hgetRes : jhRes.get? rRes = some (.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus .ok)), ("warnings", .strArr d.toArray),
       ("cells", .ext (.u64Ref (hp.u64Arrays.length + 2)))]) := by
    have h1 : rRes = (jh1.alloc _).1 := congrArg Prod.fst hrRes.symm
    have h2 : jhRes = (jh1.alloc _).2 := congrArg Prod.snd hrRes.symm
    rw [h1, h2]; exact jvmHeap_get?_alloc_self _ _
  have hc2 : hp3.u64Arrays[hp.u64Arrays.length + 2]? = some (Algorithm.U64Buf.toArray
      (Algorithm.expandRuns runs.toArray runs.toArray.size.toUInt32 0 0 startX startY startX
        Algorithm.U64Buf.empty)) := by
    rw [hhp3]; exact list_push3_get6d hp.u64Arrays _ _ _
  refine ⟨40, (.heapRef rRes, ⟨35, [.heapRef rRes], locsF, jhRes, hp3⟩), hrun,
    decode_empty_ok6d d runs startX startY jhRes hp hp3 rRes locsF hd1 hd2 hgetRes hc2, ?_⟩
  intro i o hi
  have h1 : jh1 = (jh.alloc _).2 := congrArg Prod.snd hrRuns.symm
  have h2 : jhRes = (jh1.alloc _).2 := congrArg Prod.snd hrRes.symm
  rw [h2, h1]; exact HeapExtends_alloc6d _ (HeapExtends_alloc6d _ hi)

private theorem finishRLE_full_equiv6d
    (warns : Algorithm.GrowBuf Algorithm.RLEWarning) (runs : Algorithm.GrowBuf (UInt32 × UInt32))
    (startX startY : Int32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hstat : jh.statics = []) :
    ∃ fuel st',
      runJvmRes fuel f_Algorithm_finishRLE_prog
        { initJvmState [(0, .ext (.rleWarnGrowBuf warns)), (1, .ext (.u32PairGrowBuf runs)),
            (2, .i32 startX.toUInt32), (3, .i32 startY.toUInt32)]
          with jvmHeap := jh, heap := hp } = some st' ∧
      decodeRLEResult6d st'.2 st'.1 = some (Algorithm.finishRLE warns runs startX startY) ∧
      (∀ i o, jh.get? i = some o → st'.2.jvmHeap.get? i = some o) := by
  obtain ⟨rRuns, jh1, hrRuns⟩ : ∃ r j, jh.alloc (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2))) = (r, j) := ⟨_, _, rfl⟩
  have hstat1 : jh1.statics = [] := by
    have : jh1 = (jh.alloc (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2)))).2 := congrArg Prod.snd hrRuns.symm
    rw [this]; exact hstat
  have hgetRuns1 : jh1.get? rRuns = some (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2))) := by
    have h1 : rRuns = (jh.alloc _).1 := congrArg Prod.fst hrRuns.symm
    have h2 : jh1 = (jh.alloc _).2 := congrArg Prod.snd hrRuns.symm
    rw [h1, h2]; exact jvmHeap_get?_alloc_self _ _
  have hc0 : { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }.u64Arrays[hp.u64Arrays.length]? =
      some Algorithm.U64Buf.empty := by simp
  have hc1 : let hp1 : AlgHeap := { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }
      let c1 := Algorithm.expandRuns runs.toArray runs.toArray.size.toUInt32 0 0 startX startY startX
        Algorithm.U64Buf.empty
      let hp2 : AlgHeap := { hp1 with u64Arrays := hp1.u64Arrays ++ [c1] }
      hp2.u64Arrays[hp1.u64Arrays.length]? = some c1 := by simp
  obtain ⟨hp3, hhp3⟩ : ∃ hp3 : AlgHeap, hp3 =
      let hp1 : AlgHeap := { hp with u64Arrays := hp.u64Arrays ++ [Algorithm.U64Buf.empty] }
      let c1 := Algorithm.expandRuns runs.toArray runs.toArray.size.toUInt32 0 0 startX startY startX
        Algorithm.U64Buf.empty
      let hp2 : AlgHeap := { hp1 with u64Arrays := hp1.u64Arrays ++ [c1] }
      { hp2 with u64Arrays := hp2.u64Arrays ++ [Algorithm.U64Buf.toArray c1] } := ⟨_, rfl⟩
  have hw_enc := encodeGrowBufArray_warns_foldl6d jh1 warns.toArray.toList #[] [] (by simp)
  dsimp only at hw_enc
  obtain ⟨foldRes, hfold⟩ : ∃ fr : Array JvmVal × Jvm.JvmHeap AlgExt,
      warns.toArray.foldl (fun (p : Array JvmVal × Jvm.JvmHeap AlgExt) w =>
        (p.1.push (encodeRLEWarning p.2 w).1, (encodeRLEWarning p.2 w).2)) (#[], jh1) = fr := ⟨_, rfl⟩
  obtain ⟨rWarns, jh2, hrWarns⟩ : ∃ r j, foldRes.2.alloc (.objArray "java/lang/Object" foldRes.1) =
      (r, j) := ⟨_, _, rfl⟩
  have hgetRunsMid : foldRes.2.get? rRuns = some (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2))) := by
    rw [← hfold]; simpa using hw_enc.2.1 _ _ hgetRuns1
  have hgetRuns2 : jh2.get? rRuns = some (.objArray "java/lang/Object"
      (runs.toArray.map fun x => .pair (.boxedUInt x.1) (.boxedUInt x.2))) := by
    have h2 : jh2 = (foldRes.2.alloc _).2 := congrArg Prod.snd hrWarns.symm
    rw [h2]; exact HeapExtends_alloc6d _ hgetRunsMid
  obtain ⟨rRes, jhRes, hrRes⟩ : ∃ r j, jh2.alloc (.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus .ok)), ("warnings", .heapRef rWarns),
       ("cells", .ext (.u64Ref (hp.u64Arrays.length + 2)))]) = (r, j) := ⟨_, _, rfl⟩
  have hrun := finishRLE_full_run6d warns runs startX startY jh jh1 jh2 jhRes hp hp3
    rRuns rWarns rRes hstat1 hrRuns foldRes hfold hrWarns hgetRuns2 hc0 hc1 hrRes hhp3
  rcases hrun with ⟨locsF, hrun⟩
  have hgetRes : jhRes.get? rRes = some (.instance "com/alexvanyo/composelife/model/RLEResult"
      [("status", .ext (.rleStatus .ok)), ("warnings", .heapRef rWarns),
       ("cells", .ext (.u64Ref (hp.u64Arrays.length + 2)))]) := by
    have h1 : rRes = (jh2.alloc _).1 := congrArg Prod.fst hrRes.symm
    have h2 : jhRes = (jh2.alloc _).2 := congrArg Prod.snd hrRes.symm
    rw [h1, h2]; exact jvmHeap_get?_alloc_self _ _
  have hgetWarn : jhRes.get? rWarns = some (.objArray "java/lang/Object" foldRes.1) := by
    have h1 : rWarns = (foldRes.2.alloc _).1 := congrArg Prod.fst hrWarns.symm
    have h2 : jh2 = (foldRes.2.alloc _).2 := congrArg Prod.snd hrWarns.symm
    have h3 : jhRes = (jh2.alloc _).2 := congrArg Prod.snd hrRes.symm
    rw [h3, h2, h1]; exact HeapExtends_alloc6d _ (jvmHeap_get?_alloc_self _ _)
  have hmap0 : foldRes.1.toList.mapM (decodeRLEWarning foldRes.2) = some warns.toArray.toList := by
    rw [← hfold]; simpa using hw_enc.1
  have hmap : foldRes.1.toList.mapM (decodeRLEWarning jhRes) = some warns.toArray.toList := by
    have h2 : jh2 = (foldRes.2.alloc _).2 := congrArg Prod.snd hrWarns.symm
    have h3 : jhRes = (jh2.alloc _).2 := congrArg Prod.snd hrRes.symm
    rw [h3, h2]; exact mapM_decodeRLEWarning_alloc6d _ (mapM_decodeRLEWarning_alloc6d _ hmap0)
  have hc2 : hp3.u64Arrays[hp.u64Arrays.length + 2]? = some (Algorithm.U64Buf.toArray
      (Algorithm.expandRuns runs.toArray runs.toArray.size.toUInt32 0 0 startX startY startX
        Algorithm.U64Buf.empty)) := by
    rw [hhp3]; exact list_push3_get6d hp.u64Arrays _ _ _
  refine ⟨40, (.heapRef rRes, ⟨35, [.heapRef rRes], locsF, jhRes, hp3⟩), hrun,
    decode_full_ok6d warns runs startX startY jhRes hp hp3 rWarns rRes locsF foldRes.1
      hgetRes hgetWarn hmap hc2, ?_⟩
  intro i o hi
  have h1 : jh1 = (jh.alloc _).2 := congrArg Prod.snd hrRuns.symm
  have h2 : jh2 = (foldRes.2.alloc _).2 := congrArg Prod.snd hrWarns.symm
  have h3 : jhRes = (jh2.alloc _).2 := congrArg Prod.snd hrRes.symm
  have hmid : foldRes.2.get? i = some o := by
    rw [← hfold]; simpa using hw_enc.2.1 _ _ (by rw [h1]; exact HeapExtends_alloc6d _ hi)
  rw [h3, h2]; exact HeapExtends_alloc6d _ (HeapExtends_alloc6d _ hmid)

theorem finishRLE_equiv (warns : Algorithm.GrowBuf Algorithm.RLEWarning)
    (runs : Algorithm.GrowBuf (UInt32 × UInt32)) (startX startY : Int32)
    (warnsVal : JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hwarns : RleWarnRep6d warns warnsVal) (hstat : jh.statics = []) :
    ∃ fuel st',
      runJvmRes fuel f_Algorithm_finishRLE_prog
        { initJvmState [(0, warnsVal), (1, .ext (.u32PairGrowBuf runs)),
            (2, .i32 startX.toUInt32), (3, .i32 startY.toUInt32)]
          with jvmHeap := jh, heap := hp } = some st' ∧
      decodeRLEResult6d st'.2 st'.1 = some (Algorithm.finishRLE warns runs startX startY) ∧
      (∀ i o, jh.get? i = some o → st'.2.jvmHeap.get? i = some o) := by
  cases hwarns with
  | empty d hd1 hd2 => exact finishRLE_empty_equiv6d d runs startX startY jh hp hd1 hd2 hstat
  | full _ => exact finishRLE_full_equiv6d warns runs startX startY jh hp hstat

end Algorithm.JvmVerification
