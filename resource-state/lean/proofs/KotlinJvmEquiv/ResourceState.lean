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

import proofs.KotlinJvmEquiv.ResourceStateInfra

namespace ResourceState.KotlinJvmVerification

open ResourceState.JvmVerification
open ResourceState.KotlinJvmBytecode
open ResourceState.Model

private theorem drop_eq_take_drop {α : Type} (l : List α) (a b : Nat) (h : a ≤ b) :
    l.drop a = (l.drop a).take (b - a) ++ l.drop b := by
  have h1 := List.take_append_drop (b - a) (l.drop a)
  rw [List.drop_drop, show a + (b - a) = b by omega] at h1
  exact h1.symm

private theorem runJvmResFast_unfold_rest {hooks : Jvm.JvmHooks RsExt RsHeap}
    {f pc : Nat} {prog rest newRest : List JvmInstr} {st : JvmState}
    (h : rest = newRest) :
    Jvm.runJvmResFast hooks f prog pc rest st =
      Jvm.runJvmResFast hooks f prog pc newRest st := by
  rw [h]

private theorem filter_isLoading_not_empty (states : List (Model.ResourceState RsVal))
    (h : Model.hasLoading states = true) :
    (states.filter Model.ResourceState.isLoading).isEmpty = false := by
  induction states with
  | nil => simp [Model.hasLoading] at h
  | cons r rs ih =>
    cases r with
    | loading => simp [Model.ResourceState.isLoading]
    | success _ =>
      change Model.hasLoading rs = true at h
      simp [Model.ResourceState.isLoading, ih h]
    | failure _ =>
      change Model.hasLoading rs = true at h
      simp [Model.ResourceState.isLoading, ih h]

private theorem filter_isSuccess_map_eq (vs : List RsVal) :
    (vs.map Model.ResourceState.success).filter Model.ResourceState.isSuccess =
      vs.map Model.ResourceState.success := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [Model.ResourceState.isSuccess, List.filter_cons, ih]

private theorem filter_isFailure_ext_map (states : List (Model.ResourceState RsVal)) :
    (states.filter Model.ResourceState.isFailure).map (fun r => (.ext (.res r) : JvmVal)) =
      (Model.extractFailures states).map (fun t => (.ext (.res (.failure t)) : JvmVal)) := by
  induction states with
  | nil => rfl
  | cons r rs ih =>
    cases r <;> simp [Model.ResourceState.isFailure, Model.extractFailures, List.filter_cons, ih]

private theorem array2_set0 (v : JvmVal) (h : (0 : UInt32).toNat < (#[.null, .null] : Array JvmVal).size) :
    (#[.null, .null] : Array JvmVal).set (0 : UInt32).toNat v h = #[v, .null] := rfl

private theorem array2_set1 (v1 v2 : JvmVal) (h : (1 : UInt32).toNat < (#[v1, .null] : Array JvmVal).size) :
    (#[v1, .null] : Array JvmVal).set (1 : UInt32).toNat v2 h = #[v1, v2] := rfl

private theorem array3_set0 (v : JvmVal) (h : (0 : UInt32).toNat < (#[.null, .null, .null] : Array JvmVal).size) :
    (#[.null, .null, .null] : Array JvmVal).set (0 : UInt32).toNat v h = #[v, .null, .null] := rfl

private theorem array3_set1 (v1 v2 : JvmVal) (h : (1 : UInt32).toNat < (#[v1, .null, .null] : Array JvmVal).size) :
    (#[v1, .null, .null] : Array JvmVal).set (1 : UInt32).toNat v2 h = #[v1, v2, .null] := rfl

private theorem array3_set2 (v1 v2 v3 : JvmVal) (h : (2 : UInt32).toNat < (#[v1, v2, .null] : Array JvmVal).size) :
    (#[v1, v2, .null] : Array JvmVal).set (2 : UInt32).toNat v3 h = #[v1, v2, v3] := rfl

private def filterBlockInstrs
    (pc0 srcSlot s1 s2 s3 s4 s5 s6 s7 tmpSlot outSlot : Nat)
    (cls : String) (tail : List JvmInstr) : List JvmInstr :=
  [.aload srcSlot, .astore s1, .iconst 0, .istore s2,
   .aload s1, .astore s3,
   .newClass "java/util/ArrayList", .dup,
   .invokespecial "java/util/ArrayList" "<init>" "()V",
   .checkcast "java/util/Collection", .astore s4,
   .iconst 0, .istore s5, .iconst 0, .istore s6,
   .aload s3, .arraylength, .istore s7] ++
  filterLoopInstrs (pc0 + 18) (pc0 + 34) s3 s4 s6 s7 tmpSlot cls
    ([.aload s4, .checkcast "java/util/List", .nop, .astore outSlot] ++ tail)

private theorem runJvmResFast_filterBlock {resolveProg : String → Option (List JvmInstr)}
    {d subFuel fRest pc0 srcSlot s1 s2 s3 s4 s5 s6 s7 tmpSlot outSlot srcArrAddr : Nat}
    {prog : List JvmInstr} {cls : String} {pred : Model.ResourceState RsVal → Bool}
    {states : List (Model.ResourceState RsVal)} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    {P : JvmVal × JvmState → Prop}
    (hBlk : prog.drop pc0 =
      filterBlockInstrs pc0 srcSlot s1 s2 s3 s4 s5 s6 s7 tmpSlot outSlot cls (prog.drop (pc0 + 38)))
    (hNodup : [srcSlot, s1, s2, s3, s4, s5, s6, s7, tmpSlot, outSlot].Nodup)
    (hInst : ∀ r : Model.ResourceState RsVal,
      (mkRsHooks resolveProg (d + 1) subFuel).checkInstanceOf cls (.ext (.res r)) = pred r)
    (hlenLt : states.length < 2 ^ 31)
    (hSrcArr : jh.get? srcArrAddr = some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
      (states.map fun r => (.ext (.res r) : JvmVal)).toArray))
    (hSrcLt : srcArrAddr < jh.objects.size)
    (hLocSrc : locs srcSlot = .heapRef srcArrAddr)
    (hcont : ∀ endLocs endJh,
      (∀ s, s ∉ [s1, s2, s3, s4, s5, s6, s7, tmpSlot, outSlot] → endLocs s = locs s) →
      endLocs outSlot = .heapRef (jh.objects.size + 1) →
      ListBackedBy endJh (jh.objects.size + 1) jh.objects.size
        ((states.filter pred).map fun r => (.ext (.res r) : JvmVal)).toArray →
      (∀ a, a < jh.objects.size → endJh.get? a = jh.get? a) →
      endJh.objects.size = jh.objects.size + 2 →
      endJh.statics = jh.statics →
      ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) fRest prog (pc0 + 38) (prog.drop (pc0 + 38))
        ⟨pc0 + 38, stk, endLocs, endJh, hp⟩ = some p ∧ P p) :
    ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel)
      (16 * states.length + 25 + fRest) prog pc0 (prog.drop pc0)
      ⟨pc0, stk, locs, jh, hp⟩ = some p ∧ P p := by
  have hfEq : 16 * states.length + 25 + fRest =
      (16 * states.length + 3 + (4 + fRest)) +
      1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by omega
  rw [hfEq, hBlk]
  dsimp only [filterBlockInstrs, List.cons_append, List.nil_append]
  have hs3s1 : s3 ≠ s1 := fun h => by simp [h] at hNodup
  have hs3s2 : s3 ≠ s2 := fun h => by simp [h] at hNodup
  have hs1s2 : s1 ≠ s2 := fun h => by simp [h] at hNodup
  have h1s3 : s1 ≠ s3 := hs3s1.symm
  have hs3s6 : s3 ≠ s6 := fun h => by simp [h] at hNodup
  have hs3tmp : s3 ≠ tmpSlot := fun h => by simp [h] at hNodup
  have hs4s6 : s4 ≠ s6 := fun h => by simp [h] at hNodup
  have hs4tmp : s4 ≠ tmpSlot := fun h => by simp [h] at hNodup
  have hs7s3 : s7 ≠ s3 := fun h => by simp [h] at hNodup
  have hs6s3 : s6 ≠ s3 := fun h => by simp [h] at hNodup
  have hs5s3 : s5 ≠ s3 := fun h => by simp [h] at hNodup
  have hs4s3 : s4 ≠ s3 := fun h => by simp [h] at hNodup
  have hs7s4 : s7 ≠ s4 := fun h => by simp [h] at hNodup
  have hs6s4 : s6 ≠ s4 := fun h => by simp [h] at hNodup
  have hs5s4 : s5 ≠ s4 := fun h => by simp [h] at hNodup
  have hs7s6 : s7 ≠ s6 := fun h => by simp [h] at hNodup
  have hs7tmp : s7 ≠ tmpSlot := fun h => by simp [h] at hNodup
  have hs6tmp : s6 ≠ tmpSlot := fun h => by simp [h] at hNodup
  rw [runJvmResFast_aload hLocSrc]
  rw [runJvmResFast_astore]
  rw [runJvmResFast_iconst]
  rw [runJvmResFast_istore]
  rw [runJvmResFast_aload (v := .heapRef srcArrAddr) (by simp [Jvm.setLocal, hs1s2])]
  rw [runJvmResFast_astore]
  rw [runJvmResFast_newClass_rs (by decide)]
  rw [runJvmResFast_dup]
  rw [runJvmResFast_arraylist_init_void]
  have hInit := arraylist_init_backed (jh := jh)
  let arrAlloc := jh.alloc (.objArray "java/lang/Object" #[])
  let listAlloc := arrAlloc.2.alloc (.instance "java/util/ArrayList" [("arr", .heapRef arrAlloc.1)])
  have hInitB : ListBackedBy listAlloc.2 listAlloc.1 arrAlloc.1 #[] := hInit.1
  have hInitA : arrAlloc.1 = jh.objects.size := hInit.2.1
  have hInitL : listAlloc.1 = jh.objects.size + 1 := hInit.2.2.1
  have hInitSz : listAlloc.2.objects.size = jh.objects.size + 2 := hInit.2.2.2.1
  have hInitSt : listAlloc.2.statics = jh.statics := hInit.2.2.2.2.1
  have hInitOld : ∀ a, a < jh.objects.size → listAlloc.2.get? a = jh.get? a := hInit.2.2.2.2.2
  rw [runJvmResFast_checkcast_arrayList hInitB (Or.inl rfl)]
  rw [runJvmResFast_astore]
  rw [runJvmResFast_iconst]
  rw [runJvmResFast_istore]
  rw [runJvmResFast_iconst]
  rw [runJvmResFast_istore]
  have hLocS3 :
      (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal
        (Jvm.setLocal locs s1 (.heapRef srcArrAddr)) s2 (.i32 0)) s3 (.heapRef srcArrAddr))
        s4 (.heapRef listAlloc.1)) s5 (.i32 0)) s6 (.i32 0)) s3 = .heapRef srcArrAddr := by
    simp [Jvm.setLocal, hs6s3.symm, hs5s3.symm, hs4s3.symm]
  rw [runJvmResFast_aload hLocS3]
  have hSrcNew : listAlloc.2.get? srcArrAddr =
      some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
        (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
    rw [hInitOld srcArrAddr hSrcLt, hSrcArr]
  rw [runJvmResFast_arraylength hSrcNew]
  rw [runJvmResFast_istore]
  simp only [List.size_toArray, List.length_map]
  have hDrop34 : prog.drop (pc0 + 34) =
      [.aload s4, .checkcast "java/util/List", .nop, .astore outSlot] ++ prog.drop (pc0 + 38) := by
    have ht2 := congrArg (List.drop 34) hBlk
    simp only [List.drop_drop, filterBlockInstrs, filterLoopInstrs, List.cons_append, List.nil_append,
      List.drop_succ_cons, List.drop_zero] at ht2
    exact ht2
  have hLoopDrop : prog.drop (pc0 + 18) =
      filterLoopInstrs (pc0 + 18) (pc0 + 34) s3 s4 s6 s7 tmpSlot cls (prog.drop (pc0 + 34)) := by
    have ht := congrArg (List.drop 18) hBlk
    simp only [List.drop_drop, filterBlockInstrs, List.cons_append, List.nil_append,
      List.drop_succ_cons, List.drop_zero] at ht
    rw [ht, hDrop34]
    rfl
  have hLoop := runJvmResFast_filter_loop (fRest := 4 + fRest)
    (pcLoop := pc0 + 18) (pcDone := pc0 + 34)
    (arrSlot := s3) (listSlot := s4) (idxSlot := s6) (lenSlot := s7) (tmpSlot := tmpSlot)
    (srcArrAddr := srcArrAddr) (listAddr := listAlloc.1) (listArrAddr := arrAlloc.1)
    (pred := pred) (states := states) (stk := stk) (P := P)
    (locs := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal
        (Jvm.setLocal locs s1 (.heapRef srcArrAddr)) s2 (.i32 0)) s3 (.heapRef srcArrAddr))
        s4 (.heapRef listAlloc.1)) s5 (.i32 0)) s6 (.i32 0)) s7 (.i32 (UInt32.ofNat states.length)))
    (jh := listAlloc.2) (hp := hp)
    hLoopDrop hInst hlenLt hSrcNew (by rw [hInitA]; omega)
    ⟨hs3s6, hs3tmp, hs4s6, hs4tmp, hs7s6, hs7tmp, hs6tmp⟩
    (by simp [Jvm.setLocal, hs7s3.symm, hs6s3.symm, hs5s3.symm, hs4s3.symm])
    (by simp [Jvm.setLocal, hs7s4.symm, hs6s4.symm, hs5s4.symm])
    (by simp [Jvm.setLocal])
    0 (by omega) _ _ (fun _ _ _ => rfl) (by simp [Jvm.setLocal, hs7s6.symm])
    (by simpa [List.take_zero] using hInitB) (fun _ _ => rfl) rfl rfl
  simp only [Nat.sub_zero] at hLoop
  have hDrop34' : prog.drop (pc0 + 34) =
      .aload s4 :: .checkcast "java/util/List" :: .nop :: .astore outSlot :: prog.drop (pc0 + 38) := hDrop34
  rw [← hDrop34', ← hLoopDrop]
  apply hLoop
  intro endLocs endJh hOtherLoc hListEnd hOtherJh hSize hStat
  rw [show 4 + fRest = fRest + 1 + 1 + 1 + 1 by omega, hDrop34]
  dsimp only [List.cons_append, List.nil_append]
  rw [show fRest = fRest by rfl] at *
  have hEndS4 : endLocs s4 = .heapRef (jh.objects.size + 1) := by
    rw [hOtherLoc s4 hs4s6 hs4tmp]
    simp [Jvm.setLocal, hs7s4.symm, hs6s4.symm, hs5s4.symm, hInitL]
  simp only [hInitA, hInitL] at hListEnd hOtherJh
  rw [runJvmResFast_aload hEndS4]
  rw [runJvmResFast_checkcast_arrayList hListEnd (Or.inr (Or.inl rfl))]
  rw [runJvmResFast_nop]
  rw [runJvmResFast_astore]
  rw [show pc0 + 34 + 1 + 1 + 1 + 1 = pc0 + 38 by omega]
  refine hcont _ _ ?_ (by simp [Jvm.setLocal]) hListEnd ?_ ?_ ?_
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
    rcases hs with ⟨hs1', hs2', hs3', hs4', hs5', hs6', hs7', hsTmp', hsOut'⟩
    simp only [Jvm.setLocal, hsOut', ↓reduceIte]
    rw [hOtherLoc s hs6' hsTmp']
    simp [Jvm.setLocal, hs1', hs2', hs3', hs4', hs5', hs6', hs7']
  · intro a ha
    have hane : a ≠ jh.objects.size := by omega
    rw [hOtherJh a hane, hInitOld a ha]
  · rw [hSize, hInitSz]
  · rw [hStat, hInitSt]

private def failureBranchInstrs
    (pc0 pcEmpty pcRet failSlot m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 c1 c2 : Nat)
    (tailEmpty : List JvmInstr) : List JvmInstr :=
  [.aload failSlot,
   .checkcast "java/util/Collection",
   .invokeinterface "java/util/Collection" "isEmpty" "()Z",
   .ifne (pc0 + 6),
   .iconst 1,
   .goto (pc0 + 7),
   .iconst 0,
   .ifeq pcEmpty,
   .aload failSlot,
   .invokeinterface "java/util/List" "size" "()I",
   .iconst 1,
   .if_icmpne (pc0 + 17),
   .aload failSlot,
   .invokestatic "kotlin/collections/CollectionsKt" "first" "(Ljava/util/List;)Ljava/lang/Object;",
   .checkcast "com/alexvanyo/composelife/resourcestate/ResourceState$Failure",
   .invokevirtual "com/alexvanyo/composelife/resourcestate/ResourceState$Failure" "getThrowable"
     "()Ljava/lang/Throwable;",
   .goto (pc0 + 66),
   .aload failSlot,
   .checkcast "java/lang/Iterable",
   .astore m1,
   .iconst 0,
   .istore m2,
   .aload m1,
   .astore m3,
   .newClass "java/util/ArrayList",
   .dup,
   .aload m1,
   .iconst 10,
   .invokestatic "kotlin/collections/CollectionsKt" "collectionSizeOrDefault" "(Ljava/lang/Iterable;I)I",
   .invokespecial "java/util/ArrayList" "<init>" "(I)V",
   .checkcast "java/util/Collection",
   .astore m4,
   .iconst 0,
   .istore m5,
   .aload m3,
   .invokeinterface "java/lang/Iterable" "iterator" "()Ljava/util/Iterator;",
   .astore m6] ++
  mapFailureLoopInstrs (pc0 + 37) (pc0 + 57) m6 m4 m7 m8 m9 m10
    [.aload m4,
     .checkcast "java/util/List",
     .nop,
     .astore c1,
     .newClass "com/alexvanyo/composelife/resourcestate/CompositeException",
     .dup,
     .aload c1,
     .invokespecial "com/alexvanyo/composelife/resourcestate/CompositeException" "<init>" "(Ljava/util/List;)V",
     .checkcast "java/lang/Throwable",
     .astore c2,
     .newClass "com/alexvanyo/composelife/resourcestate/ResourceState$Failure",
     .dup,
     .aload c2,
     .invokespecial "com/alexvanyo/composelife/resourcestate/ResourceState$Failure" "<init>"
       "(Ljava/lang/Throwable;)V",
     .checkcast "com/alexvanyo/composelife/resourcestate/ResourceState",
     .goto pcRet] ++ tailEmpty

private theorem runJvmResFast_failureBranch {resolveProg : String → Option (List JvmInstr)}
    {d subFuel fFuel pc0 pcEmpty pcRet failSlot m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 c1 c2
      failListAddr failArrAddr : Nat}
    {prog : List JvmInstr} {ts : List ThrowableModel}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    {P : JvmVal × JvmState → Prop}
    (hBlk : prog.drop pc0 =
      failureBranchInstrs pc0 pcEmpty pcRet failSlot m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 c1 c2 (prog.drop pcEmpty))
    (hNodup : [failSlot, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, c1, c2].Nodup)
    (hlenLt : ts.length < 2 ^ 31)
    (hFail : ListBackedBy jh failListAddr failArrAddr
      (ts.map fun t => (.ext (.res (.failure t)) : JvmVal)).toArray)
    (hLocFail : locs failSlot = .heapRef failListAddr)
    (hf : 20 * ts.length + 52 ≤ fFuel)
    (hEmpty : ts = [] →
      ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (fFuel - 8) prog pcEmpty (prog.drop pcEmpty)
        ⟨pcEmpty, [], locs, jh, hp⟩ = some p ∧ P p)
    (hSingle : ∀ t, ts = [t] →
      ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (fFuel - 23) prog pcRet (prog.drop pcRet)
        ⟨pcRet, [.ext (.res (.failure t))], Jvm.setLocal locs c2 (.ext (.throwable t)), jh, hp⟩ = some p ∧ P p)
    (hMany : ∀ t1 t2 ts', ts = t1 :: t2 :: ts' →
      ∀ endLocs endJh,
        endJh.statics = jh.statics →
        ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (fFuel - (20 * ts.length + 52))
          prog pcRet (prog.drop pcRet)
          ⟨pcRet, [.ext (.res (.failure (.composite ts)))], endLocs, endJh, hp⟩ = some p ∧ P p) :
    ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) fFuel prog pc0 (prog.drop pc0)
      ⟨pc0, [], locs, jh, hp⟩ = some p ∧ P p := by
  cases ts with
  | nil =>
    rw [show fFuel = (fFuel - 8) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, hBlk]
    dsimp only [failureBranchInstrs, List.cons_append, List.nil_append]
    rw [runJvmResFast_aload hLocFail]
    rw [runJvmResFast_checkcast_arrayList hFail (Or.inl rfl)]
    rw [runJvmResFast_collection_isEmpty hFail]
    simp only [List.map_nil, Array.isEmpty, List.size_toArray, List.length_nil, decide_true, ↓reduceIte]
    rw [Jvm.runJvmResFast_ifne_branch (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by decide)]
    have hD6 : prog.drop (pc0 + 6) = [.iconst 0, .ifeq pcEmpty] ++
        ((failureBranchInstrs pc0 pcEmpty pcRet failSlot m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 c1 c2
          (prog.drop pcEmpty)).drop 8) := by
      have ht := congrArg (List.drop 6) hBlk
      simp only [List.drop_drop, failureBranchInstrs, List.cons_append, List.nil_append] at ht
      rw [ht]
      rfl
    rw [hD6]
    dsimp only [List.cons_append, List.nil_append]
    rw [runJvmResFast_iconst]
    rw [Jvm.runJvmResFast_ifeq_branch (hooks := mkRsHooks resolveProg (d + 1) subFuel) rfl]
    obtain ⟨p, hpRun, hP⟩ := hEmpty rfl
    exact ⟨p, runJvmResFast_mono _ (by omega) hpRun, hP⟩
  | cons t1 rest =>
    cases rest with
    | nil =>
      rw [show fFuel = (fFuel - 23) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, hBlk]
      dsimp only [failureBranchInstrs, List.cons_append, List.nil_append]
      rw [runJvmResFast_aload hLocFail]
      rw [runJvmResFast_checkcast_arrayList hFail (Or.inl rfl)]
      rw [runJvmResFast_collection_isEmpty hFail]
      have hZero1 : (if ([t1].map fun t => (.ext (.res (.failure t)) : JvmVal)).toArray.isEmpty
          then (1 : UInt32) else 0) = 0 := rfl
      rw [hZero1]
      rw [Jvm.runJvmResFast_ifne_fallthrough (hooks := mkRsHooks resolveProg (d + 1) subFuel) rfl]
      rw [runJvmResFast_iconst]
      rw [Jvm.runJvmResFast_goto]
      have hD7 : prog.drop (pc0 + 7) =
          [.ifeq pcEmpty, .aload failSlot,
           .invokeinterface "java/util/List" "size" "()I", .iconst 1,
           .if_icmpne (pc0 + 17), .aload failSlot,
           .invokestatic "kotlin/collections/CollectionsKt" "first" "(Ljava/util/List;)Ljava/lang/Object;",
           .checkcast "com/alexvanyo/composelife/resourcestate/ResourceState$Failure",
           .invokevirtual "com/alexvanyo/composelife/resourcestate/ResourceState$Failure" "getThrowable"
             "()Ljava/lang/Throwable;",
           .goto (pc0 + 66)] ++
          ((failureBranchInstrs pc0 pcEmpty pcRet failSlot m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 c1 c2
            (prog.drop pcEmpty)).drop 17) := by
        have ht := congrArg (List.drop 7) hBlk
        simp only [List.drop_drop, failureBranchInstrs, List.cons_append, List.nil_append] at ht
        rw [ht]
        rfl
      rw [hD7]
      dsimp only [List.cons_append, List.nil_append]
      rw [Jvm.runJvmResFast_ifeq_fallthrough (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by decide)]
      rw [runJvmResFast_aload hLocFail]
      rw [runJvmResFast_list_size hFail]
      rw [runJvmResFast_iconst]
      simp only [List.map_cons, List.map_nil, List.size_toArray, List.length_cons, List.length_nil]
      rw [Jvm.runJvmResFast_if_icmpne_fallthrough (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by simp)]
      rw [runJvmResFast_aload hLocFail]
      rw [runJvmResFast_collections_first hFail (by simp)]
      simp only [List.map_cons, List.map_nil, List.getElem_toArray, List.getElem_cons_zero]
      rw [runJvmResFast_checkcast_res rfl]
      rw [runJvmResFast_failure_getThrowable]
      rw [Jvm.runJvmResFast_goto]
      have hD66 : prog.drop (pc0 + 66) =
          [.astore c2,
           .newClass "com/alexvanyo/composelife/resourcestate/ResourceState$Failure",
           .dup,
           .aload c2,
           .invokespecial "com/alexvanyo/composelife/resourcestate/ResourceState$Failure" "<init>"
             "(Ljava/lang/Throwable;)V",
           .checkcast "com/alexvanyo/composelife/resourcestate/ResourceState",
           .goto pcRet] ++ prog.drop pcEmpty := by
        have ht := congrArg (List.drop 66) hBlk
        simp only [List.drop_drop, failureBranchInstrs, mapFailureLoopInstrs, List.cons_append, List.nil_append,
          List.drop_succ_cons, List.drop_zero] at ht
        exact ht
      rw [hD66]
      dsimp only [List.cons_append, List.nil_append]
      rw [runJvmResFast_astore]
      rw [runJvmResFast_newClass_rs (by decide)]
      rw [runJvmResFast_dup]
      rw [runJvmResFast_aload (v := .ext (.throwable t1)) (by simp [Jvm.setLocal])]
      rw [runJvmResFast_failure_init]
      rw [runJvmResFast_checkcast_res rfl]
      rw [Jvm.runJvmResFast_goto]
      exact hSingle t1 rfl
    | cons t2 ts' =>
      let ts := t1 :: t2 :: ts'
      have htsLen : ts.length = ts'.length + 2 := by simp [ts]
      have hFuelGe : 20 * (ts'.length + 2) + 52 ≤ fFuel := by simpa [ts, htsLen] using hf
      have hfSplit : fFuel =
          (20 * (ts'.length + 2) + 3 + (16 + (fFuel - (20 * ts.length + 52)))) +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by omega
      rw [hfSplit, hBlk]
      dsimp only [failureBranchInstrs, List.cons_append, List.nil_append]
      rw [runJvmResFast_aload hLocFail]
      rw [runJvmResFast_checkcast_arrayList hFail (Or.inl rfl)]
      rw [runJvmResFast_collection_isEmpty hFail]
      have hZero2 : (if (ts.map fun t => (.ext (.res (.failure t)) : JvmVal)).toArray.isEmpty
          then (1 : UInt32) else 0) = 0 := by
        simp [ts, Array.isEmpty]
      rw [hZero2]
      rw [Jvm.runJvmResFast_ifne_fallthrough (hooks := mkRsHooks resolveProg (d + 1) subFuel) rfl]
      rw [runJvmResFast_iconst]
      rw [Jvm.runJvmResFast_goto]
      have hD7 : prog.drop (pc0 + 7) =
          [.ifeq pcEmpty, .aload failSlot,
           .invokeinterface "java/util/List" "size" "()I", .iconst 1,
           .if_icmpne (pc0 + 17)] ++
          ((failureBranchInstrs pc0 pcEmpty pcRet failSlot m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 c1 c2
            (prog.drop pcEmpty)).drop 12) := by
        have ht := congrArg (List.drop 7) hBlk
        simp only [List.drop_drop, failureBranchInstrs, List.cons_append, List.nil_append] at ht
        rw [ht]
        rfl
      rw [hD7]
      dsimp only [List.cons_append, List.nil_append]
      rw [Jvm.runJvmResFast_ifeq_fallthrough (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by decide)]
      rw [runJvmResFast_aload hLocFail]
      rw [runJvmResFast_list_size hFail]
      rw [runJvmResFast_iconst]
      simp only [List.map_cons, List.size_toArray, List.length_cons, List.length_map]
      have hNeOne : UInt32.ofNat (ts'.length + 1 + 1) ≠ 1 := by
        intro h
        have hv := congrArg UInt32.toNat h
        rw [Jvm.ui32_ofNat_toNat_of_lt _ (by simpa [ts] using hlenLt)] at hv
        simp at hv
      rw [Jvm.runJvmResFast_if_icmpne_branch (hooks := mkRsHooks resolveProg (d + 1) subFuel) hNeOne]
      have hD17 : prog.drop (pc0 + 17) =
          [.aload failSlot, .checkcast "java/lang/Iterable",
           .astore m1, .iconst 0, .istore m2, .aload m1, .astore m3,
           .newClass "java/util/ArrayList", .dup, .aload m1, .iconst 10,
           .invokestatic "kotlin/collections/CollectionsKt" "collectionSizeOrDefault" "(Ljava/lang/Iterable;I)I",
           .invokespecial "java/util/ArrayList" "<init>" "(I)V",
           .checkcast "java/util/Collection", .astore m4, .iconst 0, .istore m5,
           .aload m3, .invokeinterface "java/lang/Iterable" "iterator" "()Ljava/util/Iterator;", .astore m6] ++
          ((failureBranchInstrs pc0 pcEmpty pcRet failSlot m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 c1 c2
            (prog.drop pcEmpty)).drop 37) := by
        have ht := congrArg (List.drop 17) hBlk
        simp only [List.drop_drop, failureBranchInstrs, List.cons_append, List.nil_append] at ht
        rw [ht]
        rfl
      rw [hD17]
      dsimp only [List.cons_append, List.nil_append]
      have hm3m1 : m3 ≠ m1 := fun h => by simp [h] at hNodup
      have hm3m2 : m3 ≠ m2 := fun h => by simp [h] at hNodup
      have hm4m3 : m4 ≠ m3 := fun h => by simp [h] at hNodup
      have hm5m3 : m5 ≠ m3 := fun h => by simp [h] at hNodup
      have hm5m4 : m5 ≠ m4 := fun h => by simp [h] at hNodup
      have hm6m4 : m6 ≠ m4 := fun h => by simp [h] at hNodup
      have hm1m2 : m1 ≠ m2 := fun h => by simp [h] at hNodup
      rw [runJvmResFast_aload hLocFail]
      rw [runJvmResFast_checkcast_arrayList hFail (Or.inr (Or.inr rfl))]
      rw [runJvmResFast_astore]
      rw [runJvmResFast_iconst]
      rw [runJvmResFast_istore]
      rw [runJvmResFast_aload (v := .heapRef failListAddr) (by simp [Jvm.setLocal, hm1m2])]
      rw [runJvmResFast_astore]
      rw [runJvmResFast_newClass_rs (by decide)]
      rw [runJvmResFast_dup]
      rw [runJvmResFast_aload (v := .heapRef failListAddr) (by simp [Jvm.setLocal, hm3m1.symm, hm1m2])]
      rw [runJvmResFast_iconst]
      rw [runJvmResFast_collections_sizeOrDefault hFail]
      simp only [List.size_toArray, List.length_map, List.length_cons]
      have hSlt0 : (UInt32.ofNat (ts'.length + 1 + 1)).toBitVec.slt 0#32 = false :=
        Jvm.ui32_slt_zero_of_lt _ (by simpa [ts] using hlenLt)
      rw [runJvmResFast_arraylist_init_cap hSlt0]
      have hInit := arraylist_init_backed (jh := jh)
      let arrAlloc := jh.alloc (.objArray "java/lang/Object" #[])
      let listAlloc := arrAlloc.2.alloc (.instance "java/util/ArrayList" [("arr", .heapRef arrAlloc.1)])
      have hListSz : listAlloc.2.objects.size = jh.objects.size + 2 := hInit.2.2.2.1
      have hInitB : ListBackedBy listAlloc.2 listAlloc.1 arrAlloc.1 #[] := hInit.1
      have hInitA : arrAlloc.1 = jh.objects.size := hInit.2.1
      have hInitL : listAlloc.1 = jh.objects.size + 1 := hInit.2.2.1
      have hInitSt : listAlloc.2.statics = jh.statics := hInit.2.2.2.2.1
      have hInitOld : ∀ a, a < jh.objects.size → listAlloc.2.get? a = jh.get? a := hInit.2.2.2.2.2
      rw [runJvmResFast_checkcast_arrayList hInit.1 (Or.inl rfl)]
      rw [runJvmResFast_astore]
      rw [runJvmResFast_iconst]
      rw [runJvmResFast_istore]
      rw [runJvmResFast_aload (v := .heapRef failListAddr)
        (by simp [Jvm.setLocal, hm5m3.symm, hm4m3.symm])]
      have hFailNew : ListBackedBy listAlloc.2 failListAddr failArrAddr
          (ts.map fun t => (.ext (.res (.failure t)) : JvmVal)).toArray := by
        refine hFail.preserve ?_ ?_ (by rw [hListSz]; omega)
        · exact hInitOld failListAddr hFail.2.2.1
        · exact hInitOld failArrAddr hFail.2.1
      rw [runJvmResFast_iterable_iterator hFailNew]
      have hIt := iterable_iterator_backed hFailNew
      let itAlloc := listAlloc.2.alloc (.instance "java/util/Iterator" [("arr", .heapRef failArrAddr), ("idx", .i32 0)])
      have hItB : IterBackedBy itAlloc.2 itAlloc.1 failArrAddr 0
          (ts.map fun t => (.ext (.res (.failure t)) : JvmVal)).toArray := hIt.1
      have hItA : itAlloc.1 = listAlloc.2.objects.size := hIt.2.1
      have hItSz1 : itAlloc.2.objects.size = listAlloc.2.objects.size + 1 := hIt.2.2.1
      have hItSt : itAlloc.2.statics = listAlloc.2.statics := hIt.2.2.2.1
      have hItOld : ∀ a, a < listAlloc.2.objects.size → itAlloc.2.get? a = listAlloc.2.get? a := hIt.2.2.2.2
      have hItSz : itAlloc.2.objects.size = jh.objects.size + 3 := by rw [hItSz1, hListSz]
      rw [runJvmResFast_astore]
      have hD57 : prog.drop (pc0 + 57) =
          [.aload m4, .checkcast "java/util/List", .nop, .astore c1,
           .newClass "com/alexvanyo/composelife/resourcestate/CompositeException", .dup, .aload c1,
           .invokespecial "com/alexvanyo/composelife/resourcestate/CompositeException" "<init>" "(Ljava/util/List;)V",
           .checkcast "java/lang/Throwable", .astore c2,
           .newClass "com/alexvanyo/composelife/resourcestate/ResourceState$Failure", .dup, .aload c2,
           .invokespecial "com/alexvanyo/composelife/resourcestate/ResourceState$Failure" "<init>"
             "(Ljava/lang/Throwable;)V",
           .checkcast "com/alexvanyo/composelife/resourcestate/ResourceState", .goto pcRet] ++
          prog.drop pcEmpty := by
        have ht2 := congrArg (List.drop 57) hBlk
        simp only [List.drop_drop, failureBranchInstrs, mapFailureLoopInstrs, List.cons_append, List.nil_append,
          List.drop_succ_cons, List.drop_zero] at ht2
        exact ht2
      have hD37 : prog.drop (pc0 + 37) =
          mapFailureLoopInstrs (pc0 + 37) (pc0 + 57) m6 m4 m7 m8 m9 m10 (prog.drop (pc0 + 57)) := by
        have ht := congrArg (List.drop 37) hBlk
        simp only [List.drop_drop, failureBranchInstrs, List.cons_append, List.nil_append,
          List.drop_succ_cons, List.drop_zero] at ht
        rw [ht, hD57]
        rfl
      have hOutNew : ListBackedBy itAlloc.2 (jh.objects.size + 1) jh.objects.size #[] := by
        have h0 := hInitB
        rw [hInitL, hInitA] at h0
        refine h0.preserve ?_ ?_ (by rw [hListSz, hItSz]; omega)
        · exact hItOld _ (by rw [hListSz]; omega)
        · exact hItOld _ (by rw [hListSz]; omega)
      have hm67 : m6 ≠ m7 := fun h => by simp [h] at hNodup
      have hm68 : m6 ≠ m8 := fun h => by simp [h] at hNodup
      have hm69 : m6 ≠ m9 := fun h => by simp [h] at hNodup
      have hm610 : m6 ≠ m10 := fun h => by simp [h] at hNodup
      have hm47 : m4 ≠ m7 := fun h => by simp [h] at hNodup
      have hm48 : m4 ≠ m8 := fun h => by simp [h] at hNodup
      have hm49 : m4 ≠ m9 := fun h => by simp [h] at hNodup
      have hm410 : m4 ≠ m10 := fun h => by simp [h] at hNodup
      have hm89 : m8 ≠ m9 := fun h => by simp [h] at hNodup
      have hm810 : m8 ≠ m10 := fun h => by simp [h] at hNodup
      have hm910 : m9 ≠ m10 := fun h => by simp [h] at hNodup
      rw [← htsLen]
      have hLoop := runJvmResFast_mapFailure_loop
        (fRest := 16 + (fFuel - (20 * ts.length + 52)))
        (pcLoop := pc0 + 37) (pcDone := pc0 + 57)
        (iterSlot := m6) (outListSlot := m4) (tmp1 := m7) (failSlot := m8) (tmpOutSlot := m9) (dummySlot := m10)
        (itAddr := jh.objects.size + 2) (srcArrAddr := failArrAddr)
        (outListAddr := jh.objects.size + 1) (outArrAddr := jh.objects.size)
        (ts := ts) (stk := []) (P := P)
        (locs := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs
          m1 (.heapRef failListAddr)) m2 (.i32 0)) m3 (.heapRef failListAddr)) m4 (.heapRef listAlloc.1))
          m5 (.i32 0)) m6 (.heapRef itAlloc.1))
        (jh := itAlloc.2) (hp := hp) (resolveProg := resolveProg) (d := d) (subFuel := subFuel)
        hD37 hlenLt
        (by have := hFail.2.1; omega)
        (by omega)
        (by omega)
        ⟨by simp [hm67, hm68, hm69, hm610],
         by simp [hm47, hm48, hm49, hm410],
         hm89, hm810, hm910⟩
        (by simp [Jvm.setLocal, hItA, hListSz])
        (by simp [Jvm.setLocal, hm6m4.symm, hm5m4.symm, hInitL])
        0 (by omega) _ _
        (fun _ _ => rfl)
        (by simpa [hItA, hListSz] using hItB)
        (by simpa [List.take_zero] using hOutNew)
        (fun _ _ _ => rfl) rfl rfl
      simp only [Nat.sub_zero] at hLoop
      have hD37' : List.drop 37 (failureBranchInstrs pc0 pcEmpty pcRet failSlot m1 m2 m3 m4 m5 m6 m7 m8 m9 m10
          c1 c2 (prog.drop pcEmpty)) = prog.drop (pc0 + 37) := by
        rw [← hBlk, List.drop_drop, Nat.add_comm]
      rw [hD37', show pc0 + 17 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 =
        pc0 + 37 by omega]
      refine (fun ⟨p, hpRun, hP⟩ => ⟨p, runJvmResFast_mono _ (by omega) hpRun, hP⟩) (hLoop ?_)
      intro endLocs endJh hOtherLoc hOutEnd _ _ hStat
      have hm4notin : m4 ∉ [m7, m8, m9, m10] := by simp [hm47, hm48, hm49, hm410]
      have hEndM4 : endLocs m4 = .heapRef (jh.objects.size + 1) := by
        rw [hOtherLoc m4 hm4notin]
        simp [Jvm.setLocal, hm6m4.symm, hm5m4.symm, hInitL]
      rw [show 16 + (fFuel - (20 * ts.length + 52)) =
          (fFuel - (20 * ts.length + 52)) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, hD57]
      dsimp only [List.cons_append, List.nil_append]
      rw [runJvmResFast_aload hEndM4]
      rw [runJvmResFast_checkcast_arrayList hOutEnd (Or.inr (Or.inl rfl))]
      rw [runJvmResFast_nop]
      rw [runJvmResFast_astore]
      rw [runJvmResFast_newClass_rs (by decide)]
      rw [runJvmResFast_dup]
      rw [runJvmResFast_aload (v := .heapRef (jh.objects.size + 1)) (by simp [Jvm.setLocal])]
      rw [runJvmResFast_compositeException_init (ts := ts) hOutEnd (by simp) (by rw [htsLen]; omega)]
      rw [runJvmResFast_checkcast_res rfl]
      rw [runJvmResFast_astore]
      rw [runJvmResFast_newClass_rs (by decide)]
      rw [runJvmResFast_dup]
      rw [runJvmResFast_aload (v := .ext (.throwable (.composite ts))) (by simp [Jvm.setLocal])]
      rw [runJvmResFast_failure_init]
      rw [runJvmResFast_checkcast_res rfl]
      rw [Jvm.runJvmResFast_goto]
      refine hMany t1 t2 ts' rfl _ endJh ?_
      rw [hStat, hItSt, hInitSt]

private def loadingAndSuccCheckInstrs
    (pcEmpty pcRet loadSlot arrSlot succSlot : Nat)
    (tail : List JvmInstr) : List JvmInstr :=
  [.aload loadSlot,
   .checkcast "java/util/Collection",
   .invokeinterface "java/util/Collection" "isEmpty" "()Z",
   .ifne (pcEmpty + 6),
   .iconst 1,
   .goto (pcEmpty + 7),
   .iconst 0,
   .ifeq (pcEmpty + 11),
   .getstatic "com/alexvanyo/composelife/resourcestate/ResourceState$Loading" "INSTANCE"
     "Lcom/alexvanyo/composelife/resourcestate/ResourceState$Loading;",
   .checkcast "com/alexvanyo/composelife/resourcestate/ResourceState",
   .goto pcRet,
   .aload arrSlot,
   .arraylength,
   .aload succSlot,
   .invokeinterface "java/util/List" "size" "()I",
   .if_icmpne (pcEmpty + 18),
   .iconst 1,
   .goto (pcEmpty + 19),
   .iconst 0,
   .ifne (pcEmpty + 25),
   .newClass "java/lang/IllegalStateException",
   .dup,
   .ldcStr "Check failed.",
   .invokespecial "java/lang/IllegalStateException" "<init>" "(Ljava/lang/String;)V",
   .athrow] ++ tail

private theorem runJvmResFast_loadingAndSuccCheck {resolveProg : String → Option (List JvmInstr)}
    {d subFuel fFuel pcEmpty pcRet loadSlot arrSlot succSlot
      loadListAddr loadArrAddr srcArrAddr succListAddr succArrAddr : Nat}
    {prog : List JvmInstr} {states : List (Model.ResourceState RsVal)}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    {P : JvmVal × JvmState → Prop}
    (hBlk : prog.drop pcEmpty =
      loadingAndSuccCheckInstrs pcEmpty pcRet loadSlot arrSlot succSlot (prog.drop (pcEmpty + 25)))
    (hSrc : jh.get? srcArrAddr = some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
      (states.map fun r => (.ext (.res r) : JvmVal)).toArray))
    (hLoad : ListBackedBy jh loadListAddr loadArrAddr
      ((states.filter Model.ResourceState.isLoading).map fun r => (.ext (.res r) : JvmVal)).toArray)
    (hSucc : ListBackedBy jh succListAddr succArrAddr
      ((states.filter Model.ResourceState.isSuccess).map fun r => (.ext (.res r) : JvmVal)).toArray)
    (hLocLoad : locs loadSlot = .heapRef loadListAddr)
    (hLocArr : locs arrSlot = .heapRef srcArrAddr)
    (hLocSucc : locs succSlot = .heapRef succListAddr)
    (hClean : HasRsStaticsClean jh)
    (hNoFail : Model.extractFailures states = [])
    (hf : 18 ≤ fFuel)
    (hLoadBranch : Model.hasLoading states = true →
      ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (fFuel - 11) prog pcRet (prog.drop pcRet)
        ⟨pcRet, [.ext (.res .loading)], locs, jh, hp⟩ = some p ∧ P p)
    (hSuccBranch : ∀ vs : List RsVal,
      Model.hasLoading states = false →
      states = vs.map Model.ResourceState.success →
      ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) (fFuel - 18)
        prog (pcEmpty + 25) (prog.drop (pcEmpty + 25))
        ⟨pcEmpty + 25, [], locs, jh, hp⟩ = some p ∧ P p) :
    ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) fFuel prog pcEmpty (prog.drop pcEmpty)
      ⟨pcEmpty, [], locs, jh, hp⟩ = some p ∧ P p := by
  by_cases hhl : Model.hasLoading states = true
  · have hEmptyFalse : (states.filter Model.ResourceState.isLoading).isEmpty = false :=
      filter_isLoading_not_empty states hhl
    rw [show fFuel = (fFuel - 11) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, hBlk]
    dsimp only [loadingAndSuccCheckInstrs, List.cons_append, List.nil_append]
    rw [runJvmResFast_aload hLocLoad]
    rw [runJvmResFast_checkcast_arrayList hLoad (Or.inl rfl)]
    rw [runJvmResFast_collection_isEmpty hLoad]
    have hZeroLoad : (if ((states.filter Model.ResourceState.isLoading).map
        fun r => (.ext (.res r) : JvmVal)).toArray.isEmpty then (1 : UInt32) else 0) = 0 := by
      cases hfl : states.filter Model.ResourceState.isLoading with
      | nil => simp [hfl] at hEmptyFalse
      | cons _ _ => simp [Array.isEmpty]
    rw [hZeroLoad]
    rw [Jvm.runJvmResFast_ifne_fallthrough (hooks := mkRsHooks resolveProg (d + 1) subFuel) rfl]
    rw [runJvmResFast_iconst]
    rw [Jvm.runJvmResFast_goto]
    have hD7 : prog.drop (pcEmpty + 7) =
        [.ifeq (pcEmpty + 11),
         .getstatic "com/alexvanyo/composelife/resourcestate/ResourceState$Loading" "INSTANCE"
           "Lcom/alexvanyo/composelife/resourcestate/ResourceState$Loading;",
         .checkcast "com/alexvanyo/composelife/resourcestate/ResourceState",
         .goto pcRet] ++
        ((loadingAndSuccCheckInstrs pcEmpty pcRet loadSlot arrSlot succSlot (prog.drop (pcEmpty + 25))).drop 11) := by
      have ht := congrArg (List.drop 7) hBlk
      simp only [List.drop_drop, loadingAndSuccCheckInstrs, List.cons_append, List.nil_append] at ht
      rw [ht]
      rfl
    rw [hD7]
    dsimp only [List.cons_append, List.nil_append]
    rw [Jvm.runJvmResFast_ifeq_fallthrough (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by decide)]
    rw [runJvmResFast_getstatic_loading hClean]
    rw [runJvmResFast_checkcast_res rfl]
    rw [Jvm.runJvmResFast_goto]
    obtain ⟨p, hpRun, hP⟩ := hLoadBranch hhl
    exact ⟨p, runJvmResFast_mono _ (by omega) hpRun, hP⟩
  · have hhlFalse : Model.hasLoading states = false := Bool.eq_false_iff.mpr hhl
    have hEmptyLoad : (states.filter Model.ResourceState.isLoading).isEmpty = true := by
      rw [filter_isLoading_isEmpty states, hhlFalse]
      rfl
    obtain ⟨vs, hvs⟩ : ∃ vs : List RsVal, states = vs.map Model.ResourceState.success := by
      clear hBlk hSrc hLoad hSucc hLocLoad hLocArr hLocSucc hClean hLoadBranch hSuccBranch hEmptyLoad hhl
      induction states with
      | nil => exact ⟨[], rfl⟩
      | cons r rs ih =>
        cases r with
        | loading => simp [Model.hasLoading] at hhlFalse
        | failure _ => simp [Model.extractFailures] at hNoFail
        | success v =>
          simp only [Model.extractFailures] at hNoFail
          simp only [Model.hasLoading] at hhlFalse
          obtain ⟨vs', hvs'⟩ := ih hNoFail hhlFalse
          exact ⟨v :: vs', by simp [hvs']⟩
    have hFilterSucc : states.filter Model.ResourceState.isSuccess = vs.map Model.ResourceState.success := by
      rw [hvs, filter_isSuccess_map_eq]
    have hLenEq : (states.filter Model.ResourceState.isSuccess).length = states.length := by
      rw [hFilterSucc, hvs]
    rw [show fFuel = (fFuel - 18) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
        1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, hBlk]
    dsimp only [loadingAndSuccCheckInstrs, List.cons_append, List.nil_append]
    rw [runJvmResFast_aload hLocLoad]
    rw [runJvmResFast_checkcast_arrayList hLoad (Or.inl rfl)]
    rw [runJvmResFast_collection_isEmpty hLoad]
    have hOneLoad : (if ((states.filter Model.ResourceState.isLoading).map
        fun r => (.ext (.res r) : JvmVal)).toArray.isEmpty then (1 : UInt32) else 0) = 1 := by
      rw [List.isEmpty_iff.mp hEmptyLoad]
      rfl
    rw [hOneLoad]
    rw [Jvm.runJvmResFast_ifne_branch (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by decide)]
    have hD6 : prog.drop (pcEmpty + 6) =
        [.iconst 0, .ifeq (pcEmpty + 11)] ++
        ((loadingAndSuccCheckInstrs pcEmpty pcRet loadSlot arrSlot succSlot (prog.drop (pcEmpty + 25))).drop 8) := by
      have ht := congrArg (List.drop 6) hBlk
      simp only [List.drop_drop, loadingAndSuccCheckInstrs, List.cons_append, List.nil_append] at ht
      rw [ht]
      rfl
    rw [hD6]
    dsimp only [List.cons_append, List.nil_append]
    rw [runJvmResFast_iconst]
    rw [Jvm.runJvmResFast_ifeq_branch (hooks := mkRsHooks resolveProg (d + 1) subFuel) rfl]
    have hD11 : prog.drop (pcEmpty + 11) =
        [.aload arrSlot, .arraylength, .aload succSlot, .invokeinterface "java/util/List" "size" "()I",
         .if_icmpne (pcEmpty + 18), .iconst 1, .goto (pcEmpty + 19), .iconst 0, .ifne (pcEmpty + 25)] ++
        ((loadingAndSuccCheckInstrs pcEmpty pcRet loadSlot arrSlot succSlot (prog.drop (pcEmpty + 25))).drop 20) := by
      have ht := congrArg (List.drop 11) hBlk
      simp only [List.drop_drop, loadingAndSuccCheckInstrs, List.cons_append, List.nil_append] at ht
      rw [ht]
      rfl
    rw [hD11]
    dsimp only [List.cons_append, List.nil_append]
    rw [runJvmResFast_aload hLocArr]
    rw [runJvmResFast_arraylength hSrc]
    rw [runJvmResFast_aload hLocSucc]
    rw [runJvmResFast_list_size hSucc]
    simp only [List.size_toArray, List.length_map, hLenEq]
    rw [Jvm.runJvmResFast_if_icmpne_fallthrough (hooks := mkRsHooks resolveProg (d + 1) subFuel) rfl]
    rw [runJvmResFast_iconst]
    rw [Jvm.runJvmResFast_goto]
    have hD19 : prog.drop (pcEmpty + 19) =
        [.ifne (pcEmpty + 25),
         .newClass "java/lang/IllegalStateException", .dup, .ldcStr "Check failed.",
         .invokespecial "java/lang/IllegalStateException" "<init>" "(Ljava/lang/String;)V",
         .athrow] ++ prog.drop (pcEmpty + 25) := by
      have ht := congrArg (List.drop 19) hBlk
      simp only [List.drop_drop, loadingAndSuccCheckInstrs, List.cons_append, List.nil_append] at ht
      rw [ht]
      rfl
    rw [hD19]
    dsimp only [List.cons_append, List.nil_append]
    rw [Jvm.runJvmResFast_ifne_branch (hooks := mkRsHooks resolveProg (d + 1) subFuel) (by decide)]
    obtain ⟨p, hpRun, hP⟩ := hSuccBranch vs hhlFalse hvs
    exact ⟨p, runJvmResFast_mono _ (by omega) hpRun, hP⟩

private def mapSuccessCoreInstrs
    (pc0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 : Nat)
    (tail : List JvmInstr) : List JvmInstr :=
  [.iconst 0,
   .istore k2,
   .aload k1,
   .astore k3,
   .newClass "java/util/ArrayList",
   .dup,
   .aload k1,
   .iconst 10,
   .invokestatic "kotlin/collections/CollectionsKt" "collectionSizeOrDefault" "(Ljava/lang/Iterable;I)I",
   .invokespecial "java/util/ArrayList" "<init>" "(I)V",
   .checkcast "java/util/Collection",
   .astore k4,
   .iconst 0,
   .istore k5,
   .aload k3,
   .invokeinterface "java/lang/Iterable" "iterator" "()Ljava/util/Iterator;",
   .astore k6] ++
  mapSuccessLoopInstrs (pc0 + 17) (pc0 + 37) k6 k4 k7 k8 k9 k10
    ([.aload k4, .checkcast "java/util/List", .nop] ++ tail)

private theorem runJvmResFast_mapSuccessCore {resolveProg : String → Option (List JvmInstr)}
    {d subFuel fRest pc0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 succListAddr succArrAddr : Nat}
    {prog : List JvmInstr} {vs : List RsVal} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap RsExt} {hp : RsHeap}
    {P : JvmVal × JvmState → Prop}
    (hBlk : prog.drop pc0 =
      mapSuccessCoreInstrs pc0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 (prog.drop (pc0 + 40)))
    (hNodup : [k1, k2, k3, k4, k5, k6, k7, k8, k9, k10].Nodup)
    (hlenLt : vs.length < 2 ^ 31)
    (hSucc : ListBackedBy jh succListAddr succArrAddr
      (vs.map fun v => (.ext (.res (.success v)) : JvmVal)).toArray)
    (hLocK1 : locs k1 = .heapRef succListAddr)
    (hcont : ∀ endLocs endJh,
      (∀ s, s ∉ [k2, k3, k4, k5, k6, k7, k8, k9, k10] → endLocs s = locs s) →
      ListBackedBy endJh (jh.objects.size + 1) jh.objects.size (vs.map RsVal.toJvmVal).toArray →
      (∀ a, a < jh.objects.size → endJh.get? a = jh.get? a) →
      endJh.objects.size = jh.objects.size + 3 →
      endJh.statics = jh.statics →
      ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) fRest prog (pc0 + 40) (prog.drop (pc0 + 40))
        ⟨pc0 + 40, .heapRef (jh.objects.size + 1) :: stk, endLocs, endJh, hp⟩ = some p ∧ P p) :
    ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel)
      (20 * vs.length + 23 + fRest) prog pc0 (prog.drop pc0)
      ⟨pc0, stk, locs, jh, hp⟩ = some p ∧ P p := by
  have hfSplit : 20 * vs.length + 23 + fRest =
      (20 * vs.length + 3 + (3 + fRest)) +
      1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by omega
  rw [hfSplit, hBlk]
  dsimp only [mapSuccessCoreInstrs, List.cons_append, List.nil_append]
  have hk2k1 : k2 ≠ k1 := fun h => by simp [h] at hNodup
  have hk3k1 : k3 ≠ k1 := fun h => by simp [h] at hNodup
  have hk4k3 : k4 ≠ k3 := fun h => by simp [h] at hNodup
  have hk5k3 : k5 ≠ k3 := fun h => by simp [h] at hNodup
  have hk5k4 : k5 ≠ k4 := fun h => by simp [h] at hNodup
  have hk6k4 : k6 ≠ k4 := fun h => by simp [h] at hNodup
  rw [runJvmResFast_iconst]
  rw [runJvmResFast_istore]
  rw [runJvmResFast_aload (v := .heapRef succListAddr) (by simp [Jvm.setLocal, hk2k1.symm, hLocK1])]
  rw [runJvmResFast_astore]
  rw [runJvmResFast_newClass_rs (by decide)]
  rw [runJvmResFast_dup]
  rw [runJvmResFast_aload (v := .heapRef succListAddr) (by simp [Jvm.setLocal, hk3k1.symm, hk2k1.symm, hLocK1])]
  rw [runJvmResFast_iconst]
  rw [runJvmResFast_collections_sizeOrDefault hSucc]
  simp only [List.size_toArray, List.length_map]
  have hSlt0 : (UInt32.ofNat vs.length).toBitVec.slt 0#32 = false := Jvm.ui32_slt_zero_of_lt _ hlenLt
  rw [runJvmResFast_arraylist_init_cap hSlt0]
  have hInit := arraylist_init_backed (jh := jh)
  let arrAlloc := jh.alloc (.objArray "java/lang/Object" #[])
  let listAlloc := arrAlloc.2.alloc (.instance "java/util/ArrayList" [("arr", .heapRef arrAlloc.1)])
  have hListSz : listAlloc.2.objects.size = jh.objects.size + 2 := hInit.2.2.2.1
  have hInitB : ListBackedBy listAlloc.2 listAlloc.1 arrAlloc.1 #[] := hInit.1
  have hInitA : arrAlloc.1 = jh.objects.size := hInit.2.1
  have hInitL : listAlloc.1 = jh.objects.size + 1 := hInit.2.2.1
  have hInitSt : listAlloc.2.statics = jh.statics := hInit.2.2.2.2.1
  have hInitOld : ∀ a, a < jh.objects.size → listAlloc.2.get? a = jh.get? a := hInit.2.2.2.2.2
  rw [runJvmResFast_checkcast_arrayList hInit.1 (Or.inl rfl)]
  rw [runJvmResFast_astore]
  rw [runJvmResFast_iconst]
  rw [runJvmResFast_istore]
  rw [runJvmResFast_aload (v := .heapRef succListAddr) (by simp [Jvm.setLocal, hk5k3.symm, hk4k3.symm])]
  have hSuccNew : ListBackedBy listAlloc.2 succListAddr succArrAddr
      (vs.map fun v => (.ext (.res (.success v)) : JvmVal)).toArray := by
    refine hSucc.preserve ?_ ?_ (by rw [hListSz]; omega)
    · exact hInitOld succListAddr hSucc.2.2.1
    · exact hInitOld succArrAddr hSucc.2.1
  rw [runJvmResFast_iterable_iterator hSuccNew]
  have hIt := iterable_iterator_backed hSuccNew
  let itAlloc := listAlloc.2.alloc (.instance "java/util/Iterator" [("arr", .heapRef succArrAddr), ("idx", .i32 0)])
  have hItB : IterBackedBy itAlloc.2 itAlloc.1 succArrAddr 0
      (vs.map fun v => (.ext (.res (.success v)) : JvmVal)).toArray := hIt.1
  have hItA : itAlloc.1 = listAlloc.2.objects.size := hIt.2.1
  have hItSz1 : itAlloc.2.objects.size = listAlloc.2.objects.size + 1 := hIt.2.2.1
  have hItSt : itAlloc.2.statics = listAlloc.2.statics := hIt.2.2.2.1
  have hItOld : ∀ a, a < listAlloc.2.objects.size → itAlloc.2.get? a = listAlloc.2.get? a := hIt.2.2.2.2
  have hItSz : itAlloc.2.objects.size = jh.objects.size + 3 := by rw [hItSz1, hListSz]
  rw [runJvmResFast_astore]
  have hD37 : prog.drop (pc0 + 37) =
      [.aload k4, .checkcast "java/util/List", .nop] ++ prog.drop (pc0 + 40) := by
    have ht2 := congrArg (List.drop 37) hBlk
    simp only [List.drop_drop, mapSuccessCoreInstrs, mapSuccessLoopInstrs, List.cons_append, List.nil_append,
      List.drop_succ_cons, List.drop_zero] at ht2
    exact ht2
  have hD17 : prog.drop (pc0 + 17) =
      mapSuccessLoopInstrs (pc0 + 17) (pc0 + 37) k6 k4 k7 k8 k9 k10 (prog.drop (pc0 + 37)) := by
    have ht := congrArg (List.drop 17) hBlk
    simp only [List.drop_drop, mapSuccessCoreInstrs, List.cons_append, List.nil_append,
      List.drop_succ_cons, List.drop_zero] at ht
    rw [ht, hD37]
    rfl
  have hOutNew : ListBackedBy itAlloc.2 (jh.objects.size + 1) jh.objects.size #[] := by
    have h0 := hInitB
    rw [hInitL, hInitA] at h0
    refine h0.preserve ?_ ?_ (by rw [hListSz, hItSz]; omega)
    · exact hItOld _ (by rw [hListSz]; omega)
    · exact hItOld _ (by rw [hListSz]; omega)
  have hk67 : k6 ≠ k7 := fun h => by simp [h] at hNodup
  have hk68 : k6 ≠ k8 := fun h => by simp [h] at hNodup
  have hk69 : k6 ≠ k9 := fun h => by simp [h] at hNodup
  have hk610 : k6 ≠ k10 := fun h => by simp [h] at hNodup
  have hk47 : k4 ≠ k7 := fun h => by simp [h] at hNodup
  have hk48 : k4 ≠ k8 := fun h => by simp [h] at hNodup
  have hk49 : k4 ≠ k9 := fun h => by simp [h] at hNodup
  have hk410 : k4 ≠ k10 := fun h => by simp [h] at hNodup
  have hk89 : k8 ≠ k9 := fun h => by simp [h] at hNodup
  have hk810 : k8 ≠ k10 := fun h => by simp [h] at hNodup
  have hk910 : k9 ≠ k10 := fun h => by simp [h] at hNodup
  have hLoop := runJvmResFast_mapSuccess_loop
    (fRest := 3 + fRest)
    (pcLoop := pc0 + 17) (pcDone := pc0 + 37)
    (iterSlot := k6) (outListSlot := k4) (tmp1 := k7) (succSlot := k8) (tmpOutSlot := k9) (dummySlot := k10)
    (itAddr := jh.objects.size + 2) (srcArrAddr := succArrAddr)
    (outListAddr := jh.objects.size + 1) (outArrAddr := jh.objects.size)
    (vs := vs) (stk := stk) (P := P)
    (locs := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs
      k2 (.i32 0)) k3 (.heapRef succListAddr)) k4 (.heapRef listAlloc.1)) k5 (.i32 0)) k6 (.heapRef itAlloc.1))
    (jh := itAlloc.2) (hp := hp) (resolveProg := resolveProg) (d := d) (subFuel := subFuel)
    hD17 hlenLt
    (by have := hSucc.2.1; omega)
    (by omega)
    (by omega)
    ⟨by simp [hk67, hk68, hk69, hk610],
     by simp [hk47, hk48, hk49, hk410],
     hk89, hk810, hk910⟩
    (by simp [Jvm.setLocal, hItA, hListSz])
    (by simp [Jvm.setLocal, hk6k4.symm, hk5k4.symm, hInitL])
    0 (by omega) _ _
    (fun _ _ => rfl)
    (by simpa [hItA, hListSz] using hItB)
    (by simpa [List.take_zero] using hOutNew)
    (fun _ _ _ => rfl) rfl rfl
  simp only [Nat.sub_zero] at hLoop
  have hD37' : prog.drop (pc0 + 37) = .aload k4 :: .checkcast "java/util/List" :: .nop :: prog.drop (pc0 + 40) :=
    hD37
  rw [← hD37', ← hD17]
  apply hLoop
  intro endLocs endJh hOtherLoc hOutEnd hOtherJh hSize hStat
  have hk4notin : k4 ∉ [k7, k8, k9, k10] := by simp [hk47, hk48, hk49, hk410]
  have hEndK4 : endLocs k4 = .heapRef (jh.objects.size + 1) := by
    rw [hOtherLoc k4 hk4notin]
    simp [Jvm.setLocal, hk6k4.symm, hk5k4.symm, hInitL]
  rw [show 3 + fRest = fRest + 1 + 1 + 1 by omega, hD37]
  dsimp only [List.cons_append, List.nil_append]
  rw [runJvmResFast_aload hEndK4]
  rw [runJvmResFast_checkcast_arrayList hOutEnd (Or.inr (Or.inl rfl))]
  rw [runJvmResFast_nop]
  rw [show pc0 + 37 + 1 + 1 + 1 = pc0 + 40 by omega]
  refine hcont _ endJh ?_ hOutEnd ?_ ?_ ?_
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
    rcases hs with ⟨hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10⟩
    rw [hOtherLoc s (by simp [hs7, hs8, hs9, hs10])]
    simp [Jvm.setLocal, hs2, hs3, hs4, hs5, hs6]
  · intro a ha
    have hane1 : a ≠ jh.objects.size + 2 := by omega
    have hane2 : a ≠ jh.objects.size := by omega
    rw [hOtherJh a hane1 hane2]
    have hane3 : a < jh.objects.size + 2 := by omega
    rw [hItOld a (by rw [hListSz]; exact hane3)]
    exact hInitOld a ha
  · rw [hSize, hItSz]
  · rw [hStat, hItSt, hInitSt]

private theorem extractFailures_length_le (states : List (Model.ResourceState RsVal)) :
    (Model.extractFailures states).length ≤ states.length :=
  List.length_filterMap_le _ _

private theorem extractSuccesses_map_success (vs : List RsVal) :
    Model.extractSuccesses (vs.map Model.ResourceState.success) = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [Model.extractSuccesses] at ih ⊢; exact ih

private theorem jvmHeap_set_statics {Ext : Type} (h : Jvm.JvmHeap Ext) (addr : Nat) (obj : Jvm.HeapObj Ext) :
    (h.set addr obj).statics = h.statics := by
  unfold Jvm.JvmHeap.set
  split <;> rfl

private theorem exists_areturn_rs {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} {P : JvmVal × JvmState → Prop}
    (hf : 1 ≤ f) (hP : P (v, ⟨pc, v :: stk, locs, jh, hp⟩)) :
    ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog pc
        (.areturn :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ = some p ∧ P p := by
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
  exact ⟨_, runJvmResFast_areturn_rs, hP⟩

private theorem exists_nop_areturn_rs {resolveProg : String → Option (List JvmInstr)}
    {d subFuel f pc pc0 : Nat} {prog : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap RsExt} {hp : RsHeap} {P : JvmVal × JvmState → Prop}
    (hf : 2 ≤ f) (hP : P (v, ⟨pc + 1, v :: stk, locs, jh, hp⟩)) :
    ∃ p, Jvm.runJvmResFast (mkRsHooks resolveProg (d + 1) subFuel) f prog pc
        [.nop, .areturn] ⟨pc0, v :: stk, locs, jh, hp⟩ = some p ∧ P p := by
  obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 + 1 := ⟨f - 2, by omega⟩
  rw [runJvmResFast_nop]
  exact ⟨_, runJvmResFast_areturn_rs, hP⟩

theorem combineMany_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d)
    (states : List (Model.ResourceState RsVal))
    (hlen : states.length < 2 ^ 31)
    (hf : 180 + 68 * states.length ≤ fuel)
    (f : List RsVal → RsVal) (cid srcArrAddr : Nat)
    (hp : RsHeap) (jh : Jvm.JvmHeap RsExt)
    (hclean : HasRsStaticsClean jh)
    (hArr : jh.get? srcArrAddr = some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
      (states.map fun r => (.ext (.res r) : JvmVal)).toArray))
    (hcl : hp.closures[cid]? = some (.listFn1 f)) :
    ∃ endSt,
      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceStateKt_combine_2_prog
          (initRsJvmState [(0, .heapRef srcArrAddr), (1, .ext (.closureRef cid))] hp jh) =
        some (.ext (.res (Model.combineMany states f)), endSt) ∧
      HasRsStaticsClean endSt.jvmHeap ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hSrcLt : srcArrAddr < jh.objects.size := get?_some_lt hArr
  have hStatClean : ∀ {jh' : Jvm.JvmHeap RsExt}, jh'.statics = jh.statics → HasRsStaticsClean jh' := by
    intro jh' hs
    simp only [HasRsStaticsClean, Jvm.JvmHeap.getStatic?, hs] at hclean ⊢
    exact hclean
  have hCore : ∃ p : JvmVal × JvmState,
      Jvm.runJvmResFast (mkRsHooks resolveProg (d' + 1) subFuel) (180 + 68 * states.length) ResourceStateKt_combine_2_prog 0
          ResourceStateKt_combine_2_prog (initRsJvmState [(0, .heapRef srcArrAddr), (1, .ext (.closureRef cid))] hp jh) =
        some p ∧
      p.1 = .ext (.res (Model.combineMany states f)) ∧
      HasRsStaticsClean p.2.jvmHeap ∧
      p.2.heap = hp := by
    have hD8 : ResourceStateKt_combine_2_prog.drop 8 =
        filterBlockInstrs 8 0 4 5 6 7 8 9 10 11 3
          "com/alexvanyo/composelife/resourcestate/ResourceState$Loading"
          (ResourceStateKt_combine_2_prog.drop 46) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_2_prog 8 46 (by decide),
        show (ResourceStateKt_combine_2_prog.drop 8).take (46 - 8) =
          filterBlockInstrs 8 0 4 5 6 7 8 9 10 11 3
            "com/alexvanyo/composelife/resourcestate/ResourceState$Loading" [] by rfl]
      simp [filterBlockInstrs, filterLoopInstrs]
    have hD46 : ResourceStateKt_combine_2_prog.drop 46 =
        filterBlockInstrs 46 0 5 6 7 8 9 10 11 12 4
          "com/alexvanyo/composelife/resourcestate/ResourceState$Failure"
          (ResourceStateKt_combine_2_prog.drop 84) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_2_prog 46 84 (by decide),
        show (ResourceStateKt_combine_2_prog.drop 46).take (84 - 46) =
          filterBlockInstrs 46 0 5 6 7 8 9 10 11 12 4
            "com/alexvanyo/composelife/resourcestate/ResourceState$Failure" [] by rfl]
      simp [filterBlockInstrs, filterLoopInstrs]
    have hD84 : ResourceStateKt_combine_2_prog.drop 84 =
        filterBlockInstrs 84 0 6 7 8 9 10 11 12 13 5
          "com/alexvanyo/composelife/resourcestate/ResourceState$Success"
          (ResourceStateKt_combine_2_prog.drop 122) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_2_prog 84 122 (by decide),
        show (ResourceStateKt_combine_2_prog.drop 84).take (122 - 84) =
          filterBlockInstrs 84 0 6 7 8 9 10 11 12 13 5
            "com/alexvanyo/composelife/resourcestate/ResourceState$Success" [] by rfl]
      simp [filterBlockInstrs, filterLoopInstrs]
    have hD123 : ResourceStateKt_combine_2_prog.drop 123 =
        failureBranchInstrs 123 196 275 4 6 7 8 9 10 11 12 13 17 14 18 19
          (ResourceStateKt_combine_2_prog.drop 196) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_2_prog 123 196 (by decide),
        show (ResourceStateKt_combine_2_prog.drop 123).take (196 - 123) =
          failureBranchInstrs 123 196 275 4 6 7 8 9 10 11 12 13 17 14 18 19 [] by rfl]
      simp [failureBranchInstrs, mapFailureLoopInstrs]
    have hD196 : ResourceStateKt_combine_2_prog.drop 196 =
        loadingAndSuccCheckInstrs 196 275 3 0 5 (ResourceStateKt_combine_2_prog.drop 221) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_2_prog 196 221 (by decide),
        show (ResourceStateKt_combine_2_prog.drop 196).take (221 - 196) =
          loadingAndSuccCheckInstrs 196 275 3 0 5 [] by rfl]
      simp [loadingAndSuccCheckInstrs]
    have hD226 : ResourceStateKt_combine_2_prog.drop 226 =
        mapSuccessCoreInstrs 226 6 7 8 9 10 11 12 13 16 14 (ResourceStateKt_combine_2_prog.drop 266) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_2_prog 226 266 (by decide),
        show (ResourceStateKt_combine_2_prog.drop 226).take (266 - 226) =
          mapSuccessCoreInstrs 226 6 7 8 9 10 11 12 13 16 14 [] by rfl]
      simp [mapSuccessCoreInstrs, mapSuccessLoopInstrs]
    have hD0 : ResourceStateKt_combine_2_prog =
        [.aload 0, .ldcStr "resourceStates",
         .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V",
         .aload 1, .ldcStr "transform",
         .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V",
         .iconst 0, .istore 2] ++ ResourceStateKt_combine_2_prog.drop 8 := by
      have ht := drop_eq_take_drop ResourceStateKt_combine_2_prog 0 8 (by decide)
      rw [List.drop_zero] at ht
      rw [show ResourceStateKt_combine_2_prog.take (8 - 0) =
          [.aload 0, .ldcStr "resourceStates",
           .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
             "(Ljava/lang/Object;Ljava/lang/String;)V",
           .aload 1, .ldcStr "transform",
           .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter"
             "(Ljava/lang/Object;Ljava/lang/String;)V",
           .iconst 0, .istore 2] by rfl] at ht
      exact ht
    rw [show 180 + 68 * states.length =
        (16 * states.length + 25 + (16 * states.length + 25 + (16 * states.length + 25 +
          (97 + 20 * states.length)))) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    rw [runJvmResFast_unfold_rest hD0]
    dsimp only [initRsJvmState, Jvm.initJvmState, List.cons_append, List.nil_append]
    rw [runJvmResFast_aload (v := .heapRef srcArrAddr) (by rfl)]
    rw [runJvmResFast_ldcStr]
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rw [runJvmResFast_aload (v := .ext (.closureRef cid)) (by rfl)]
    rw [runJvmResFast_ldcStr]
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_istore]
    refine runJvmResFast_filterBlock (pred := Model.ResourceState.isLoading)
      hD8 (by decide) (fun r => by cases r <;> rfl) hlen hArr hSrcLt (by rfl) ?_
    intro locs1 jh1 hLocs1 hLoadLoc hLoadBacked hJh1 hSz1 hStat1
    have hSrc1 : jh1.get? srcArrAddr = some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
        (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
      rw [hJh1 srcArrAddr hSrcLt, hArr]
    refine runJvmResFast_filterBlock (pred := Model.ResourceState.isFailure)
      hD46 (by decide) (fun r => by cases r <;> rfl) hlen hSrc1 (by omega)
      (by rw [hLocs1 0 (by decide)]; rfl) ?_
    intro locs2 jh2 hLocs2 hFailLoc hFailBacked hJh2 hSz2 hStat2
    have hSrc2 : jh2.get? srcArrAddr = some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
        (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
      rw [hJh2 srcArrAddr (by omega), hSrc1]
    have hLoad2 : ListBackedBy jh2 (jh.objects.size + 1) jh.objects.size
        ((states.filter Model.ResourceState.isLoading).map fun r => (.ext (.res r) : JvmVal)).toArray := by
      refine hLoadBacked.preserve ?_ ?_ (by omega)
      · exact hJh2 (jh.objects.size + 1) (by omega)
      · exact hJh2 jh.objects.size (by omega)
    refine runJvmResFast_filterBlock (pred := Model.ResourceState.isSuccess)
      hD84 (by decide) (fun r => by cases r <;> rfl) hlen hSrc2 (by omega)
      (by rw [hLocs2 0 (by decide), hLocs1 0 (by decide)]; rfl) ?_
    intro locs3 jh3 hLocs3 hSuccLoc hSuccBacked hJh3 hSz3 hStat3
    have hSrc3 : jh3.get? srcArrAddr = some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
        (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
      rw [hJh3 srcArrAddr (by omega), hSrc2]
    have hLoad3 : ListBackedBy jh3 (jh.objects.size + 1) jh.objects.size
        ((states.filter Model.ResourceState.isLoading).map fun r => (.ext (.res r) : JvmVal)).toArray := by
      refine hLoad2.preserve ?_ ?_ (by omega)
      · exact hJh3 (jh.objects.size + 1) (by omega)
      · exact hJh3 jh.objects.size (by omega)
    have hFail3 : ListBackedBy jh3 (jh1.objects.size + 1) jh1.objects.size
        ((states.filter Model.ResourceState.isFailure).map fun r => (.ext (.res r) : JvmVal)).toArray := by
      refine hFailBacked.preserve ?_ ?_ (by omega)
      · exact hJh3 (jh1.objects.size + 1) (by omega)
      · exact hJh3 jh1.objects.size (by omega)
    have hD122 : ResourceStateKt_combine_2_prog.drop 122 = [.nop] ++ ResourceStateKt_combine_2_prog.drop 123 := by
      rw [drop_eq_take_drop ResourceStateKt_combine_2_prog 122 123 (by decide),
        show (ResourceStateKt_combine_2_prog.drop 122).take (123 - 122) = [.nop] by rfl]
    rw [show 97 + 20 * states.length = (96 + 20 * states.length) + 1 by omega, hD122]
    dsimp only [List.cons_append, List.nil_append]
    rw [runJvmResFast_nop]
    rw [filter_isFailure_ext_map states] at hFail3
    have hFailLenLt : (Model.extractFailures states).length < 2 ^ 31 := by
      have : (Model.extractFailures states).length ≤ states.length := extractFailures_length_le states
      omega
    have hFuelFail : 20 * (Model.extractFailures states).length + 52 ≤ 96 + 20 * states.length := by
      have : (Model.extractFailures states).length ≤ states.length := extractFailures_length_le states
      omega
    have hClean3 : HasRsStaticsClean jh3 := hStatClean (by rw [hStat3, hStat2, hStat1])
    refine runJvmResFast_failureBranch hD123 (by decide) hFailLenLt hFail3
      (by rw [hLocs3 4 (by decide), hFailLoc]) hFuelFail ?_ ?_ ?_
    · intro hNoFail
      have hD196' := hD196
      refine runJvmResFast_loadingAndSuccCheck hD196' hSrc3 hLoad3 hSuccBacked
        (by rw [hLocs3 3 (by decide), hLocs2 3 (by decide), hLoadLoc])
        (by rw [hLocs3 0 (by decide), hLocs2 0 (by decide), hLocs1 0 (by decide)]; rfl)
        hSuccLoc hClean3 hNoFail (by omega) ?_ ?_
      · intro hHasLoad
        rw [show ResourceStateKt_combine_2_prog.drop 275 = [.areturn] by rfl]
        refine exists_areturn_rs (by omega) ⟨?_, hClean3, rfl⟩
        simp [Model.combineMany, hNoFail, hHasLoad]
      · intro vs hHasLoadFalse hStatesEq
        have hVsLen : vs.length = states.length := by
          rw [hStatesEq]; simp
        have hVsLenLt : vs.length < 2 ^ 31 := by omega
        have hSuccEq : ((states.filter Model.ResourceState.isSuccess).map fun r => (.ext (.res r) : JvmVal)).toArray =
            (vs.map fun v => (.ext (.res (.success v)) : JvmVal)).toArray := by
          rw [hStatesEq, filter_isSuccess_map_eq, List.map_map]
          rfl
        rw [hSuccEq] at hSuccBacked
        have hD221 : ResourceStateKt_combine_2_prog.drop 221 =
            [.aload 1, .aload 5, .checkcast "java/lang/Iterable", .astore 6, .astore 15] ++
            ResourceStateKt_combine_2_prog.drop 226 := by rfl
        rw [show 96 + 20 * states.length - 8 - 18 =
            (20 * vs.length + 23 + 42) + 1 + 1 + 1 + 1 + 1 by omega, hD221]
        dsimp only [List.cons_append, List.nil_append]
        rw [runJvmResFast_aload (v := .ext (.closureRef cid)) (by
          rw [hLocs3 1 (by decide), hLocs2 1 (by decide), hLocs1 1 (by decide)]; rfl)]
        rw [runJvmResFast_aload hSuccLoc]
        rw [runJvmResFast_checkcast_arrayList hSuccBacked (Or.inr (Or.inr rfl))]
        rw [runJvmResFast_astore]
        rw [runJvmResFast_astore]
        refine runJvmResFast_mapSuccessCore (fRest := 42) hD226 (by decide) hVsLenLt hSuccBacked ?hk1 ?_
        case hk1 => simp [Jvm.setLocal]
        intro endLocs endJh hEndLocs hEndOut _ _ hEndStat
        have hD266 : ResourceStateKt_combine_2_prog.drop 266 =
            [.aload 15, .swap,
             .invokeinterface "kotlin/jvm/functions/Function1" "invoke"
               "(Ljava/lang/Object;)Ljava/lang/Object;",
             .astore 20,
             .newClass "com/alexvanyo/composelife/resourcestate/ResourceState$Success",
             .dup, .aload 20,
             .invokespecial "com/alexvanyo/composelife/resourcestate/ResourceState$Success" "<init>"
               "(Ljava/lang/Object;)V",
             .checkcast "com/alexvanyo/composelife/resourcestate/ResourceState",
             .areturn] := by rfl
        rw [show (42 : Nat) = 32 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, hD266]
        have hEnd15 : endLocs 15 = .ext (.closureRef cid) := by
          rw [hEndLocs 15 (by decide)]
          simp [Jvm.setLocal]
        rw [runJvmResFast_aload hEnd15]
        rw [runJvmResFast_swap (hca := rfl) (hcb := rfl)]
        rw [runJvmResFast_listFn1_invoke (xs := vs) hcl hEndOut (by simp)]
        rw [runJvmResFast_astore]
        rw [runJvmResFast_newClass_rs (by decide)]
        rw [runJvmResFast_dup]
        rw [runJvmResFast_aload (v := (f vs).toJvmVal) (by simp [Jvm.setLocal])]
        rw [runJvmResFast_success_init]
        rw [runJvmResFast_checkcast_res rfl]
        refine exists_areturn_rs (by omega) ⟨?_, hStatClean (by rw [hEndStat, hStat3, hStat2, hStat1]), rfl⟩
        have hExSucc : Model.extractSuccesses states = vs := by
          rw [hStatesEq]
          exact extractSuccesses_map_success vs
        simp [Model.combineMany, hNoFail, hHasLoadFalse, hExSucc]
    · intro t hFailSingle
      rw [show ResourceStateKt_combine_2_prog.drop 275 = [.areturn] by rfl]
      refine exists_areturn_rs (by omega) ⟨?_, hClean3, rfl⟩
      simp [Model.combineMany, hFailSingle]
    · intro t1 t2 ts' hFailMany endLocs endJh hEndStat
      rw [show ResourceStateKt_combine_2_prog.drop 275 = [.areturn] by rfl]
      refine exists_areturn_rs (by omega) ⟨?_, hStatClean (by rw [hEndStat, hStat3, hStat2, hStat1]), rfl⟩
      simp [Model.combineMany, hFailMany]
  rcases hCore with ⟨p, hRun, hVal, hStat, hHp⟩
  have hRun' :
      Jvm.runJvmResFast (mkRsHooks resolveProg (d' + 1) subFuel) (180 + 68 * states.length) ResourceStateKt_combine_2_prog 0
          ResourceStateKt_combine_2_prog (initRsJvmState [(0, .heapRef srcArrAddr), (1, .ext (.closureRef cid))] hp jh) =
        some (.ext (.res (Model.combineMany states f)), p.2) := by
    rw [hRun, ← hVal]
  exact ⟨p.2, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl (runJvmResFast_mono _ hf hRun'),
    hStat, hHp⟩

theorem combine2_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 400 ≤ fuel)
    (r1 r2 : Model.ResourceState RsVal)
    (f : RsVal → RsVal → RsVal) (cid : Nat)
    (hp : RsHeap) (jh : Jvm.JvmHeap RsExt)
    (hclean : HasRsStaticsClean jh)
    (hcl : hp.closures[cid]? = some (.fn2 fun a b =>
      match RsVal.ofJvmVal? a, RsVal.ofJvmVal? b with
      | some va, some vb => some (f va vb).toJvmVal
      | _, _ => none)) :
    ∃ endSt,
      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceStateKt_combine_prog
          (initRsJvmState [(0, .ext (.res r1)), (1, .ext (.res r2)), (2, .ext (.closureRef cid))] hp jh) =
        some (.ext (.res (Model.combine2 r1 r2 f)), endSt) ∧
      HasRsStaticsClean endSt.jvmHeap ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hStatClean : ∀ {jh' : Jvm.JvmHeap RsExt}, jh'.statics = jh.statics → HasRsStaticsClean jh' := by
    intro jh' hs
    simp only [HasRsStaticsClean, Jvm.JvmHeap.getStatic?, hs] at hclean ⊢
    exact hclean
  have hCore : ∃ p : JvmVal × JvmState,
      Jvm.runJvmResFast (mkRsHooks resolveProg (d' + 1) subFuel) 400 ResourceStateKt_combine_prog 0
          ResourceStateKt_combine_prog (initRsJvmState [(0, .ext (.res r1)), (1, .ext (.res r2)), (2, .ext (.closureRef cid))] hp jh) =
        some p ∧
      p.1 = .ext (.res (Model.combine2 r1 r2 f)) ∧
      HasRsStaticsClean p.2.jvmHeap ∧
      p.2.heap = hp := by
    let states : List (Model.ResourceState RsVal) := [r1, r2]
    have hD27 : ResourceStateKt_combine_prog.drop 27 =
        filterBlockInstrs 27 4 6 7 8 9 10 11 12 13 14
          "com/alexvanyo/composelife/resourcestate/ResourceState$Loading"
          (ResourceStateKt_combine_prog.drop 65) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_prog 27 65 (by decide),
        show (ResourceStateKt_combine_prog.drop 27).take (65 - 27) =
          filterBlockInstrs 27 4 6 7 8 9 10 11 12 13 14
            "com/alexvanyo/composelife/resourcestate/ResourceState$Loading" [] by rfl]
      simp [filterBlockInstrs, filterLoopInstrs]
    have hD65 : ResourceStateKt_combine_prog.drop 65 =
        filterBlockInstrs 65 4 7 8 9 10 11 12 13 15 6
          "com/alexvanyo/composelife/resourcestate/ResourceState$Failure"
          (ResourceStateKt_combine_prog.drop 103) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_prog 65 103 (by decide),
        show (ResourceStateKt_combine_prog.drop 65).take (103 - 65) =
          filterBlockInstrs 65 4 7 8 9 10 11 12 13 15 6
            "com/alexvanyo/composelife/resourcestate/ResourceState$Failure" [] by rfl]
      simp [filterBlockInstrs, filterLoopInstrs]
    have hD103 : ResourceStateKt_combine_prog.drop 103 =
        filterBlockInstrs 103 4 8 9 10 11 12 13 15 16 7
          "com/alexvanyo/composelife/resourcestate/ResourceState$Success"
          (ResourceStateKt_combine_prog.drop 141) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_prog 103 141 (by decide),
        show (ResourceStateKt_combine_prog.drop 103).take (141 - 103) =
          filterBlockInstrs 103 4 8 9 10 11 12 13 15 16 7
            "com/alexvanyo/composelife/resourcestate/ResourceState$Success" [] by rfl]
      simp [filterBlockInstrs, filterLoopInstrs]
    have hD142 : ResourceStateKt_combine_prog.drop 142 =
        failureBranchInstrs 142 215 306 6 8 9 10 11 12 13 15 16 18 19 22 23
          (ResourceStateKt_combine_prog.drop 215) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_prog 142 215 (by decide),
        show (ResourceStateKt_combine_prog.drop 142).take (215 - 142) =
          failureBranchInstrs 142 215 306 6 8 9 10 11 12 13 15 16 18 19 22 23 [] by rfl]
      simp [failureBranchInstrs, mapFailureLoopInstrs]
    have hD215 : ResourceStateKt_combine_prog.drop 215 =
        loadingAndSuccCheckInstrs 215 306 14 4 7 (ResourceStateKt_combine_prog.drop 240) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_prog 215 240 (by decide),
        show (ResourceStateKt_combine_prog.drop 215).take (240 - 215) =
          loadingAndSuccCheckInstrs 215 306 14 4 7 [] by rfl]
      simp [loadingAndSuccCheckInstrs]
    have hD243 : ResourceStateKt_combine_prog.drop 243 =
        mapSuccessCoreInstrs 243 8 9 10 11 12 13 15 16 17 19 (ResourceStateKt_combine_prog.drop 283) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_prog 243 283 (by decide),
        show (ResourceStateKt_combine_prog.drop 243).take (283 - 243) =
          mapSuccessCoreInstrs 243 8 9 10 11 12 13 15 16 17 19 [] by rfl]
      simp [mapSuccessCoreInstrs, mapSuccessLoopInstrs]
    have hD0 : ResourceStateKt_combine_prog =
        [.aload 0, .ldcStr "resourceState1",
         .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V",
         .aload 1, .ldcStr "resourceState2",
         .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V",
         .aload 2, .ldcStr "transform",
         .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V",
         .iconst 0, .istore 3, .iconst 2,
         .anewarray "com/alexvanyo/composelife/resourcestate/ResourceState", .astore 4,
         .aload 4, .iconst 0, .aload 0, .aastore,
         .aload 4, .iconst 1, .aload 1, .aastore,
         .aload 4, .astore 4, .nop, .iconst 0, .istore 5] ++ ResourceStateKt_combine_prog.drop 27 := by
      have ht := drop_eq_take_drop ResourceStateKt_combine_prog 0 27 (by decide)
      rw [List.drop_zero] at ht
      rw [show ResourceStateKt_combine_prog.take (27 - 0) = _ by rfl] at ht
      exact ht
    rw [show (400 : Nat) =
        (16 * states.length + 25 + (16 * states.length + 25 + (16 * states.length + 25 + 202))) +
        1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
        1 + 1 + 1 + 1 + 1 + 1 + 1 by simp [states]]
    rw [runJvmResFast_unfold_rest hD0]
    dsimp only [initRsJvmState, Jvm.initJvmState, List.cons_append, List.nil_append]
    rw [runJvmResFast_aload (v := .ext (.res r1)) (by rfl)]
    rw [runJvmResFast_ldcStr]
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rw [runJvmResFast_aload (v := .ext (.res r2)) (by rfl)]
    rw [runJvmResFast_ldcStr]
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rw [runJvmResFast_aload (v := .ext (.closureRef cid)) (by rfl)]
    rw [runJvmResFast_ldcStr]
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_istore]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_anewarray (by decide)]
    rw [show Array.replicate (2 : UInt32).toNat (Jvm.JvmVal.null : JvmVal) = #[.null, .null] by rfl]
    rw [runJvmResFast_astore]
    let arrAlloc := jh.alloc (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState" #[.null, .null])
    rw [runJvmResFast_aload (v := .heapRef arrAlloc.1) (by rfl)]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_aload (v := .ext (.res r1)) (by rfl)]
    have hGet0 : arrAlloc.2.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState" #[.null, .null]) :=
      Jvm.jvmHeap_get?_alloc_self _ _
    rw [runJvmResFast_aastore_res (idx := 0) (by decide) hGet0 rfl (by simp)]
    rw [array2_set0]
    rw [runJvmResFast_aload (v := .heapRef arrAlloc.1) (by rfl)]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_aload (v := .ext (.res r2)) (by rfl)]
    let jh0a := arrAlloc.2.set arrAlloc.1 (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
      #[.ext (.res r1), .null])
    have hGet1 : jh0a.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState" #[.ext (.res r1), .null]) :=
      Jvm.jvmHeap_get?_set_self hGet0
    rw [runJvmResFast_aastore_res (idx := 1) (by decide) hGet1 rfl (by simp)]
    rw [array2_set1]
    rw [runJvmResFast_aload (v := .heapRef arrAlloc.1) (by rfl)]
    rw [runJvmResFast_astore]
    rw [runJvmResFast_nop]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_istore]
    generalize hjh0 : jh0a.set arrAlloc.1 (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
      #[.ext (.res r1), .ext (.res r2)]) = jh0
    have hSrc0 : jh0.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
          (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
      rw [← hjh0]; exact Jvm.jvmHeap_get?_set_self hGet1
    have hStat0 : jh0.statics = jh.statics := by
      rw [← hjh0, jvmHeap_set_statics]; simp only [jh0a, jvmHeap_set_statics]; rfl
    have hSrc0Lt : arrAlloc.1 < jh0.objects.size := get?_some_lt hSrc0
    refine runJvmResFast_filterBlock (pred := Model.ResourceState.isLoading)
      hD27 (by decide) (fun r => by cases r <;> rfl) (by simp [states]) hSrc0 hSrc0Lt
      (by simp [Jvm.setLocal]) ?_
    intro locs1 jh1 hLocs1 hLoadLoc hLoadBacked hJh1 hSz1 hStat1
    have hSrc1 : jh1.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
          (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
      rw [hJh1 arrAlloc.1 hSrc0Lt, hSrc0]
    refine runJvmResFast_filterBlock (pred := Model.ResourceState.isFailure)
      hD65 (by decide) (fun r => by cases r <;> rfl) (by simp [states]) hSrc1 (by omega)
      (by rw [hLocs1 4 (by decide)]; simp [Jvm.setLocal]) ?_
    intro locs2 jh2 hLocs2 hFailLoc hFailBacked hJh2 hSz2 hStat2
    have hSrc2 : jh2.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
          (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
      rw [hJh2 arrAlloc.1 (by omega), hSrc1]
    have hLoad2 : ListBackedBy jh2 (jh0.objects.size + 1) jh0.objects.size
        ((states.filter Model.ResourceState.isLoading).map fun r => (.ext (.res r) : JvmVal)).toArray := by
      refine hLoadBacked.preserve ?_ ?_ (by omega)
      · exact hJh2 (jh0.objects.size + 1) (by omega)
      · exact hJh2 jh0.objects.size (by omega)
    refine runJvmResFast_filterBlock (pred := Model.ResourceState.isSuccess)
      hD103 (by decide) (fun r => by cases r <;> rfl) (by simp [states]) hSrc2 (by omega)
      (by rw [hLocs2 4 (by decide), hLocs1 4 (by decide)]; simp [Jvm.setLocal]) ?_
    intro locs3 jh3 hLocs3 hSuccLoc hSuccBacked hJh3 hSz3 hStat3
    have hSrc3 : jh3.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
          (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
      rw [hJh3 arrAlloc.1 (by omega), hSrc2]
    have hLoad3 : ListBackedBy jh3 (jh0.objects.size + 1) jh0.objects.size
        ((states.filter Model.ResourceState.isLoading).map fun r => (.ext (.res r) : JvmVal)).toArray := by
      refine hLoad2.preserve ?_ ?_ (by omega)
      · exact hJh3 (jh0.objects.size + 1) (by omega)
      · exact hJh3 jh0.objects.size (by omega)
    have hFail3 : ListBackedBy jh3 (jh1.objects.size + 1) jh1.objects.size
        ((states.filter Model.ResourceState.isFailure).map fun r => (.ext (.res r) : JvmVal)).toArray := by
      refine hFailBacked.preserve ?_ ?_ (by omega)
      · exact hJh3 (jh1.objects.size + 1) (by omega)
      · exact hJh3 jh1.objects.size (by omega)
    have hD141 : ResourceStateKt_combine_prog.drop 141 = [.nop] ++ ResourceStateKt_combine_prog.drop 142 := by
      rw [drop_eq_take_drop ResourceStateKt_combine_prog 141 142 (by decide),
        show (ResourceStateKt_combine_prog.drop 141).take (142 - 141) = [.nop] by rfl]
    rw [show (202 : Nat) = 201 + 1 by omega, hD141]
    dsimp only [List.cons_append, List.nil_append]
    rw [runJvmResFast_nop]
    rw [filter_isFailure_ext_map states] at hFail3
    have hFailLen : (Model.extractFailures states).length ≤ 2 := by
      simpa [states] using extractFailures_length_le states
    have hClean3 : HasRsStaticsClean jh3 := hStatClean (by rw [hStat3, hStat2, hStat1, hStat0])
    refine runJvmResFast_failureBranch hD142 (by decide) (by omega) hFail3
      (by rw [hLocs3 6 (by decide), hFailLoc]) (by omega) ?_ ?_ ?_
    · intro hNoFail
      refine runJvmResFast_loadingAndSuccCheck hD215 hSrc3 hLoad3 hSuccBacked
        (by rw [hLocs3 14 (by decide), hLocs2 14 (by decide), hLoadLoc])
        (by rw [hLocs3 4 (by decide), hLocs2 4 (by decide), hLocs1 4 (by decide)]; simp [Jvm.setLocal])
        hSuccLoc hClean3 hNoFail (by omega) ?_ ?_
      · intro hHasLoad
        have hD306 : ResourceStateKt_combine_prog.drop 306 = [.nop, .areturn] := by rfl
        rw [hD306]
        refine exists_nop_areturn_rs (by omega) ⟨?_, hClean3, rfl⟩
        have h1 : Model.extractFailures [r1, r2] = [] := hNoFail
        have h2 : Model.hasLoading [r1, r2] = true := hHasLoad
        cases r1 <;> cases r2 <;> simp [Model.extractFailures, Model.hasLoading, Model.combine2] at h1 h2 ⊢
      · intro vs hHasLoadFalse hStatesEq
        obtain ⟨a, b, rfl, rfl⟩ := combine2_all_success r1 r2 hNoFail hHasLoadFalse
        have hVsEq : vs = [a, b] := by
          rw [← extractSuccesses_map_success vs, ← hStatesEq]; rfl
        subst hVsEq
        have hSuccEq : ((states.filter Model.ResourceState.isSuccess).map fun r => (.ext (.res r) : JvmVal)).toArray =
            ([a, b].map fun v => (.ext (.res (.success v)) : JvmVal)).toArray := by
          rw [hStatesEq, filter_isSuccess_map_eq, List.map_map]
          rfl
        rw [hSuccEq] at hSuccBacked
        have hD240 : ResourceStateKt_combine_prog.drop 240 =
            [.aload 7, .checkcast "java/lang/Iterable", .astore 8] ++ ResourceStateKt_combine_prog.drop 243 := by
              set_option maxRecDepth 16384 in rfl
        rw [show 201 - 8 - 18 = (20 * [a, b].length + 23 + 109) + 1 + 1 + 1 by rfl, hD240]
        dsimp only [List.cons_append, List.nil_append]
        rw [runJvmResFast_aload hSuccLoc]
        rw [runJvmResFast_checkcast_arrayList hSuccBacked (Or.inr (Or.inr rfl))]
        rw [runJvmResFast_astore]
        refine runJvmResFast_mapSuccessCore (fRest := 109) hD243 (by decide) (by simp) hSuccBacked ?hk1 ?_
        case hk1 => simp [Jvm.setLocal]
        intro endLocs endJh hEndLocs hEndOut _ _ hEndStat
        have hD283 : ResourceStateKt_combine_prog.drop 283 =
            [.astore 20, .iconst 0, .istore 21, .aload 2,
             .aload 20, .iconst 0, .invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;",
             .dup, .ldcStr "null cannot be cast to non-null type T1 of com.alexvanyo.composelife.resourcestate.ResourceStateKt.combine",
             .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V",
             .aload 20, .iconst 1, .invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;",
             .dup, .ldcStr "null cannot be cast to non-null type T2 of com.alexvanyo.composelife.resourcestate.ResourceStateKt.combine",
             .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V",
             .invokeinterface "kotlin/jvm/functions/Function2" "invoke"
               "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
             .astore 24,
             .newClass "com/alexvanyo/composelife/resourcestate/ResourceState$Success",
             .dup, .aload 24,
             .invokespecial "com/alexvanyo/composelife/resourcestate/ResourceState$Success" "<init>"
               "(Ljava/lang/Object;)V",
             .checkcast "com/alexvanyo/composelife/resourcestate/ResourceState",
             .nop, .areturn] := by rfl
        rw [show (109 : Nat) = 84 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
            1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, hD283]
        have hEnd2 : (Jvm.setLocal (Jvm.setLocal endLocs 20 (.heapRef (jh3.objects.size + 1))) 21 (.i32 0)) 2 =
            .ext (.closureRef cid) := by
          simp only [Jvm.setLocal, (by decide : (2 : Nat) ≠ 21), (by decide : (2 : Nat) ≠ 20), ↓reduceIte]
          rw [hEndLocs 2 (by decide)]
          simp only [Jvm.setLocal, (by decide : (2 : Nat) ≠ 8), ↓reduceIte]
          rw [hLocs3 2 (by decide), hLocs2 2 (by decide), hLocs1 2 (by decide)]
          rfl
        rw [runJvmResFast_astore]
        rw [runJvmResFast_iconst]
        rw [runJvmResFast_istore]
        rw [runJvmResFast_aload hEnd2]
        rw [runJvmResFast_aload (v := .heapRef (jh3.objects.size + 1)) (by simp [Jvm.setLocal])]
        rw [runJvmResFast_iconst]
        rw [runJvmResFast_list_get hEndOut (by decide) (by simp)]
        rw [show ∀ h, ((List.map RsVal.toJvmVal [a, b]).toArray)[(0 : UInt32).toNat]'h = a.toJvmVal from
          fun _ => rfl]
        rw [runJvmResFast_dup]
        rw [runJvmResFast_ldcStr]
        rw [runJvmResFast_checkNotNull (RsVal.toJvmVal_isNull a)]
        rw [runJvmResFast_aload (v := .heapRef (jh3.objects.size + 1)) (by simp [Jvm.setLocal])]
        rw [runJvmResFast_iconst]
        rw [runJvmResFast_list_get hEndOut (by decide) (by simp)]
        rw [show ∀ h, ((List.map RsVal.toJvmVal [a, b]).toArray)[(1 : UInt32).toNat]'h = b.toJvmVal from
          fun _ => rfl]
        rw [runJvmResFast_dup]
        rw [runJvmResFast_ldcStr]
        rw [runJvmResFast_checkNotNull (RsVal.toJvmVal_isNull b)]
        rw [runJvmResFast_fn2_invoke hcl (out := (f a b).toJvmVal)
          (by simp [RsVal.ofJvmVal?_toJvmVal])]
        rw [runJvmResFast_astore]
        rw [runJvmResFast_newClass_rs (by decide)]
        rw [runJvmResFast_dup]
        rw [runJvmResFast_aload (v := (f a b).toJvmVal) (by simp [Jvm.setLocal])]
        rw [runJvmResFast_success_init]
        rw [runJvmResFast_checkcast_res rfl]
        rw [runJvmResFast_nop]
        refine exists_areturn_rs (by omega) ⟨?_, hStatClean (by rw [hEndStat, hStat3, hStat2, hStat1, hStat0]), rfl⟩
        simp [Model.combine2]
    · intro t hFailSingle
      have hD306 : ResourceStateKt_combine_prog.drop 306 = [.nop, .areturn] := by rfl
      rw [hD306]
      refine exists_nop_areturn_rs (by omega) ⟨?_, hClean3, rfl⟩
      have h1 : Model.extractFailures [r1, r2] = [t] := hFailSingle
      cases r1 <;> cases r2 <;> simp [Model.extractFailures, Model.combine2] at h1 ⊢ <;> simp [h1]
    · intro t1 t2 ts' hFailMany endLocs endJh hEndStat
      have hD306 : ResourceStateKt_combine_prog.drop 306 = [.nop, .areturn] := by rfl
      rw [hD306]
      refine exists_nop_areturn_rs (by omega) ⟨?_, hStatClean (by rw [hEndStat, hStat3, hStat2, hStat1, hStat0]), rfl⟩
      have h1 : Model.extractFailures [r1, r2] = t1 :: t2 :: ts' := hFailMany
      rw [show Model.extractFailures states = t1 :: t2 :: ts' from hFailMany]
      cases r1 <;> cases r2 <;> simp [Model.extractFailures, Model.combine2] at h1 ⊢ <;> simp [h1]
  rcases hCore with ⟨p, hRun, hVal, hStat, hHp⟩
  have hRun' :
      Jvm.runJvmResFast (mkRsHooks resolveProg (d' + 1) subFuel) 400 ResourceStateKt_combine_prog 0
          ResourceStateKt_combine_prog (initRsJvmState [(0, .ext (.res r1)), (1, .ext (.res r2)), (2, .ext (.closureRef cid))] hp jh) =
        some (.ext (.res (Model.combine2 r1 r2 f)), p.2) := by
    rw [hRun, ← hVal]
  exact ⟨p.2, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl (runJvmResFast_mono _ hf hRun'),
    hStat, hHp⟩

theorem combine3_equiv (resolveProg : String → Option (List JvmInstr))
    (d subFuel fuel : Nat) (hd : 1 ≤ d) (hf : 500 ≤ fuel)
    (r1 r2 r3 : Model.ResourceState RsVal)
    (f : RsVal → RsVal → RsVal → RsVal) (cid : Nat)
    (hp : RsHeap) (jh : Jvm.JvmHeap RsExt)
    (hclean : HasRsStaticsClean jh)
    (hcl : hp.closures[cid]? = some (.fn3 fun a b c =>
      match RsVal.ofJvmVal? a, RsVal.ofJvmVal? b, RsVal.ofJvmVal? c with
      | some va, some vb, some vc => some (f va vb vc).toJvmVal
      | _, _, _ => none)) :
    ∃ endSt,
      Jvm.runJvmRes (mkRsHooks resolveProg d subFuel) fuel ResourceStateKt_combine_1_prog
          (initRsJvmState [(0, .ext (.res r1)), (1, .ext (.res r2)), (2, .ext (.res r3)),
            (3, .ext (.closureRef cid))] hp jh) =
        some (.ext (.res (Model.combine3 r1 r2 r3 f)), endSt) ∧
      HasRsStaticsClean endSt.jvmHeap ∧ endSt.heap = hp := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hStatClean : ∀ {jh' : Jvm.JvmHeap RsExt}, jh'.statics = jh.statics → HasRsStaticsClean jh' := by
    intro jh' hs
    simp only [HasRsStaticsClean, Jvm.JvmHeap.getStatic?, hs] at hclean ⊢
    exact hclean
  have hCore : ∃ p : JvmVal × JvmState,
      Jvm.runJvmResFast (mkRsHooks resolveProg (d' + 1) subFuel) 500 ResourceStateKt_combine_1_prog 0
          ResourceStateKt_combine_1_prog (initRsJvmState [(0, .ext (.res r1)), (1, .ext (.res r2)), (2, .ext (.res r3)),
            (3, .ext (.closureRef cid))] hp jh) =
        some p ∧
      p.1 = .ext (.res (Model.combine3 r1 r2 r3 f)) ∧
      HasRsStaticsClean p.2.jvmHeap ∧
      p.2.heap = hp := by
    let states : List (Model.ResourceState RsVal) := [r1, r2, r3]
    have hD34 : ResourceStateKt_combine_1_prog.drop 34 =
        filterBlockInstrs 34 5 7 8 9 10 11 12 13 14 15
          "com/alexvanyo/composelife/resourcestate/ResourceState$Loading"
          (ResourceStateKt_combine_1_prog.drop 72) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_1_prog 34 72 (by decide),
        show (ResourceStateKt_combine_1_prog.drop 34).take (72 - 34) =
          filterBlockInstrs 34 5 7 8 9 10 11 12 13 14 15
            "com/alexvanyo/composelife/resourcestate/ResourceState$Loading" [] by rfl]
      simp [filterBlockInstrs, filterLoopInstrs]
    have hD72 : ResourceStateKt_combine_1_prog.drop 72 =
        filterBlockInstrs 72 5 8 9 10 11 12 13 14 16 7
          "com/alexvanyo/composelife/resourcestate/ResourceState$Failure"
          (ResourceStateKt_combine_1_prog.drop 110) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_1_prog 72 110 (by decide),
        show (ResourceStateKt_combine_1_prog.drop 72).take (110 - 72) =
          filterBlockInstrs 72 5 8 9 10 11 12 13 14 16 7
            "com/alexvanyo/composelife/resourcestate/ResourceState$Failure" [] by rfl]
      simp [filterBlockInstrs, filterLoopInstrs]
    have hD110 : ResourceStateKt_combine_1_prog.drop 110 =
        filterBlockInstrs 110 5 9 10 11 12 13 14 16 17 8
          "com/alexvanyo/composelife/resourcestate/ResourceState$Success"
          (ResourceStateKt_combine_1_prog.drop 148) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_1_prog 110 148 (by decide),
        show (ResourceStateKt_combine_1_prog.drop 110).take (148 - 110) =
          filterBlockInstrs 110 5 9 10 11 12 13 14 16 17 8
            "com/alexvanyo/composelife/resourcestate/ResourceState$Success" [] by rfl]
      simp [filterBlockInstrs, filterLoopInstrs]
    have hD149 : ResourceStateKt_combine_1_prog.drop 149 =
        failureBranchInstrs 149 222 319 7 9 10 11 12 13 14 16 17 19 20 23 24
          (ResourceStateKt_combine_1_prog.drop 222) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_1_prog 149 222 (by decide),
        show (ResourceStateKt_combine_1_prog.drop 149).take (222 - 149) =
          failureBranchInstrs 149 222 319 7 9 10 11 12 13 14 16 17 19 20 23 24 [] by rfl]
      simp [failureBranchInstrs, mapFailureLoopInstrs]
    have hD222 : ResourceStateKt_combine_1_prog.drop 222 =
        loadingAndSuccCheckInstrs 222 319 15 5 8 (ResourceStateKt_combine_1_prog.drop 247) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_1_prog 222 247 (by decide),
        show (ResourceStateKt_combine_1_prog.drop 222).take (247 - 222) =
          loadingAndSuccCheckInstrs 222 319 15 5 8 [] by rfl]
      simp [loadingAndSuccCheckInstrs]
    have hD250 : ResourceStateKt_combine_1_prog.drop 250 =
        mapSuccessCoreInstrs 250 9 10 11 12 13 14 16 17 18 20 (ResourceStateKt_combine_1_prog.drop 290) := by
      rw [drop_eq_take_drop ResourceStateKt_combine_1_prog 250 290 (by decide),
        show (ResourceStateKt_combine_1_prog.drop 250).take (290 - 250) =
          mapSuccessCoreInstrs 250 9 10 11 12 13 14 16 17 18 20 [] by rfl]
      simp [mapSuccessCoreInstrs, mapSuccessLoopInstrs]
    have hD0 : ResourceStateKt_combine_1_prog =
        [.aload 0, .ldcStr "resourceState1",
         .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V",
         .aload 1, .ldcStr "resourceState2",
         .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V",
         .aload 2, .ldcStr "resourceState3",
         .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V",
         .aload 3, .ldcStr "transform",
         .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNullParameter" "(Ljava/lang/Object;Ljava/lang/String;)V",
         .iconst 0, .istore 4, .iconst 3,
         .anewarray "com/alexvanyo/composelife/resourcestate/ResourceState", .astore 5,
         .aload 5, .iconst 0, .aload 0, .aastore,
         .aload 5, .iconst 1, .aload 1, .aastore,
         .aload 5, .iconst 2, .aload 2, .aastore,
         .aload 5, .astore 5, .nop, .iconst 0, .istore 6] ++ ResourceStateKt_combine_1_prog.drop 34 := by
      have ht := drop_eq_take_drop ResourceStateKt_combine_1_prog 0 34 (by decide)
      rw [List.drop_zero] at ht
      rw [show ResourceStateKt_combine_1_prog.take (34 - 0) = _ by rfl] at ht
      exact ht
    rw [show (500 : Nat) =
        (16 * states.length + 25 + (16 * states.length + 25 + (16 * states.length + 25 + 247))) +
        1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
        1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by simp [states]]
    rw [runJvmResFast_unfold_rest hD0]
    dsimp only [initRsJvmState, Jvm.initJvmState, List.cons_append, List.nil_append]
    rw [runJvmResFast_aload (v := .ext (.res r1)) (by rfl)]
    rw [runJvmResFast_ldcStr]
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rw [runJvmResFast_aload (v := .ext (.res r2)) (by rfl)]
    rw [runJvmResFast_ldcStr]
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rw [runJvmResFast_aload (v := .ext (.res r3)) (by rfl)]
    rw [runJvmResFast_ldcStr]
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rw [runJvmResFast_aload (v := .ext (.closureRef cid)) (by rfl)]
    rw [runJvmResFast_ldcStr]
    rw [runJvmResFast_checkNotNullParam (by rfl)]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_istore]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_anewarray (by decide)]
    rw [show Array.replicate (3 : UInt32).toNat (Jvm.JvmVal.null : JvmVal) = #[.null, .null, .null] by rfl]
    rw [runJvmResFast_astore]
    let arrAlloc := jh.alloc (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState" #[.null, .null, .null])
    rw [runJvmResFast_aload (v := .heapRef arrAlloc.1) (by rfl)]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_aload (v := .ext (.res r1)) (by rfl)]
    have hGet0 : arrAlloc.2.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState" #[.null, .null, .null]) :=
      Jvm.jvmHeap_get?_alloc_self _ _
    rw [runJvmResFast_aastore_res (idx := 0) (by decide) hGet0 rfl (by simp)]
    rw [array3_set0]
    rw [runJvmResFast_aload (v := .heapRef arrAlloc.1) (by rfl)]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_aload (v := .ext (.res r2)) (by rfl)]
    let jh0a := arrAlloc.2.set arrAlloc.1 (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
      #[.ext (.res r1), .null, .null])
    have hGet1 : jh0a.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
          #[.ext (.res r1), .null, .null]) :=
      Jvm.jvmHeap_get?_set_self hGet0
    rw [runJvmResFast_aastore_res (idx := 1) (by decide) hGet1 rfl (by simp)]
    rw [array3_set1]
    rw [runJvmResFast_aload (v := .heapRef arrAlloc.1) (by rfl)]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_aload (v := .ext (.res r3)) (by rfl)]
    let jh0b := jh0a.set arrAlloc.1 (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
      #[.ext (.res r1), .ext (.res r2), .null])
    have hGet2 : jh0b.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
          #[.ext (.res r1), .ext (.res r2), .null]) :=
      Jvm.jvmHeap_get?_set_self hGet1
    rw [runJvmResFast_aastore_res (idx := 2) (by decide) hGet2 rfl (by simp)]
    rw [array3_set2]
    rw [runJvmResFast_aload (v := .heapRef arrAlloc.1) (by rfl)]
    rw [runJvmResFast_astore]
    rw [runJvmResFast_nop]
    rw [runJvmResFast_iconst]
    rw [runJvmResFast_istore]
    generalize hjh0 : jh0b.set arrAlloc.1 (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
      #[.ext (.res r1), .ext (.res r2), .ext (.res r3)]) = jh0
    have hSrc0 : jh0.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
          (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
      rw [← hjh0]; exact Jvm.jvmHeap_get?_set_self hGet2
    have hStat0 : jh0.statics = jh.statics := by
      rw [← hjh0, jvmHeap_set_statics]; simp only [jh0b, jh0a, jvmHeap_set_statics]; rfl
    have hSrc0Lt : arrAlloc.1 < jh0.objects.size := get?_some_lt hSrc0
    refine runJvmResFast_filterBlock (pred := Model.ResourceState.isLoading)
      hD34 (by decide) (fun r => by cases r <;> rfl) (by simp [states]) hSrc0 hSrc0Lt
      (by simp [Jvm.setLocal]) ?_
    intro locs1 jh1 hLocs1 hLoadLoc hLoadBacked hJh1 hSz1 hStat1
    have hSrc1 : jh1.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
          (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
      rw [hJh1 arrAlloc.1 hSrc0Lt, hSrc0]
    refine runJvmResFast_filterBlock (pred := Model.ResourceState.isFailure)
      hD72 (by decide) (fun r => by cases r <;> rfl) (by simp [states]) hSrc1 (by omega)
      (by rw [hLocs1 5 (by decide)]; simp [Jvm.setLocal]) ?_
    intro locs2 jh2 hLocs2 hFailLoc hFailBacked hJh2 hSz2 hStat2
    have hSrc2 : jh2.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
          (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
      rw [hJh2 arrAlloc.1 (by omega), hSrc1]
    have hLoad2 : ListBackedBy jh2 (jh0.objects.size + 1) jh0.objects.size
        ((states.filter Model.ResourceState.isLoading).map fun r => (.ext (.res r) : JvmVal)).toArray := by
      refine hLoadBacked.preserve ?_ ?_ (by omega)
      · exact hJh2 (jh0.objects.size + 1) (by omega)
      · exact hJh2 jh0.objects.size (by omega)
    refine runJvmResFast_filterBlock (pred := Model.ResourceState.isSuccess)
      hD110 (by decide) (fun r => by cases r <;> rfl) (by simp [states]) hSrc2 (by omega)
      (by rw [hLocs2 5 (by decide), hLocs1 5 (by decide)]; simp [Jvm.setLocal]) ?_
    intro locs3 jh3 hLocs3 hSuccLoc hSuccBacked hJh3 hSz3 hStat3
    have hSrc3 : jh3.get? arrAlloc.1 =
        some (.objArray "com/alexvanyo/composelife/resourcestate/ResourceState"
          (states.map fun r => (.ext (.res r) : JvmVal)).toArray) := by
      rw [hJh3 arrAlloc.1 (by omega), hSrc2]
    have hLoad3 : ListBackedBy jh3 (jh0.objects.size + 1) jh0.objects.size
        ((states.filter Model.ResourceState.isLoading).map fun r => (.ext (.res r) : JvmVal)).toArray := by
      refine hLoad2.preserve ?_ ?_ (by omega)
      · exact hJh3 (jh0.objects.size + 1) (by omega)
      · exact hJh3 jh0.objects.size (by omega)
    have hFail3 : ListBackedBy jh3 (jh1.objects.size + 1) jh1.objects.size
        ((states.filter Model.ResourceState.isFailure).map fun r => (.ext (.res r) : JvmVal)).toArray := by
      refine hFailBacked.preserve ?_ ?_ (by omega)
      · exact hJh3 (jh1.objects.size + 1) (by omega)
      · exact hJh3 jh1.objects.size (by omega)
    have hD148 : ResourceStateKt_combine_1_prog.drop 148 = [.nop] ++ ResourceStateKt_combine_1_prog.drop 149 := by
      rw [drop_eq_take_drop ResourceStateKt_combine_1_prog 148 149 (by decide),
        show (ResourceStateKt_combine_1_prog.drop 148).take (149 - 148) = [.nop] by rfl]
    rw [show (247 : Nat) = 246 + 1 by omega, hD148]
    dsimp only [List.cons_append, List.nil_append]
    rw [runJvmResFast_nop]
    rw [filter_isFailure_ext_map states] at hFail3
    have hFailLen : (Model.extractFailures states).length ≤ 3 := by
      simpa [states] using extractFailures_length_le states
    have hClean3 : HasRsStaticsClean jh3 := hStatClean (by rw [hStat3, hStat2, hStat1, hStat0])
    refine runJvmResFast_failureBranch hD149 (by decide) (by omega) hFail3
      (by rw [hLocs3 7 (by decide), hFailLoc]) (by omega) ?_ ?_ ?_
    · intro hNoFail
      refine runJvmResFast_loadingAndSuccCheck hD222 hSrc3 hLoad3 hSuccBacked
        (by rw [hLocs3 15 (by decide), hLocs2 15 (by decide), hLoadLoc])
        (by rw [hLocs3 5 (by decide), hLocs2 5 (by decide), hLocs1 5 (by decide)]; simp [Jvm.setLocal])
        hSuccLoc hClean3 hNoFail (by omega) ?_ ?_
      · intro hHasLoad
        have hD319 : ResourceStateKt_combine_1_prog.drop 319 = [.nop, .areturn] := by rfl
        rw [hD319]
        refine exists_nop_areturn_rs (by omega) ⟨?_, hClean3, rfl⟩
        have h1 : Model.extractFailures [r1, r2, r3] = [] := hNoFail
        have h2 : Model.hasLoading [r1, r2, r3] = true := hHasLoad
        cases r1 <;> cases r2 <;> cases r3 <;>
          simp [Model.extractFailures, Model.hasLoading, Model.combine3] at h1 h2 ⊢
      · intro vs hHasLoadFalse hStatesEq
        obtain ⟨a, b, c, rfl, rfl, rfl⟩ := combine3_all_success r1 r2 r3 hNoFail hHasLoadFalse
        have hVsEq : vs = [a, b, c] := by
          rw [← extractSuccesses_map_success vs, ← hStatesEq]; rfl
        subst hVsEq
        have hSuccEq : ((states.filter Model.ResourceState.isSuccess).map fun r => (.ext (.res r) : JvmVal)).toArray =
            ([a, b, c].map fun v => (.ext (.res (.success v)) : JvmVal)).toArray := by
          rw [hStatesEq, filter_isSuccess_map_eq, List.map_map]
          rfl
        rw [hSuccEq] at hSuccBacked
        have hD247 : ResourceStateKt_combine_1_prog.drop 247 =
            [.aload 8, .checkcast "java/lang/Iterable", .astore 9] ++ ResourceStateKt_combine_1_prog.drop 250 := by
              set_option maxRecDepth 16384 in rfl
        rw [show 246 - 8 - 18 = (20 * [a, b, c].length + 23 + 134) + 1 + 1 + 1 by rfl, hD247]
        dsimp only [List.cons_append, List.nil_append]
        rw [runJvmResFast_aload hSuccLoc]
        rw [runJvmResFast_checkcast_arrayList hSuccBacked (Or.inr (Or.inr rfl))]
        rw [runJvmResFast_astore]
        refine runJvmResFast_mapSuccessCore (fRest := 134) hD250 (by decide) (by simp) hSuccBacked ?hk1 ?_
        case hk1 => simp [Jvm.setLocal]
        intro endLocs endJh hEndLocs hEndOut _ _ hEndStat
        have hD290 : ResourceStateKt_combine_1_prog.drop 290 =
            [.astore 21, .iconst 0, .istore 22, .aload 3,
             .aload 21, .iconst 0, .invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;",
             .dup, .ldcStr "null cannot be cast to non-null type T1 of com.alexvanyo.composelife.resourcestate.ResourceStateKt.combine",
             .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V",
             .aload 21, .iconst 1, .invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;",
             .dup, .ldcStr "null cannot be cast to non-null type T2 of com.alexvanyo.composelife.resourcestate.ResourceStateKt.combine",
             .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V",
             .aload 21, .iconst 2, .invokeinterface "java/util/List" "get" "(I)Ljava/lang/Object;",
             .dup, .ldcStr "null cannot be cast to non-null type T3 of com.alexvanyo.composelife.resourcestate.ResourceStateKt.combine",
             .invokestatic "kotlin/jvm/internal/Intrinsics" "checkNotNull" "(Ljava/lang/Object;Ljava/lang/String;)V",
             .invokeinterface "kotlin/jvm/functions/Function3" "invoke"
               "(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
             .astore 25,
             .newClass "com/alexvanyo/composelife/resourcestate/ResourceState$Success",
             .dup, .aload 25,
             .invokespecial "com/alexvanyo/composelife/resourcestate/ResourceState$Success" "<init>"
               "(Ljava/lang/Object;)V",
             .checkcast "com/alexvanyo/composelife/resourcestate/ResourceState",
             .nop, .areturn] := by rfl
        rw [show (134 : Nat) = 104 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega, hD290]
        have hEnd3 : (Jvm.setLocal (Jvm.setLocal endLocs 21 (.heapRef (jh3.objects.size + 1))) 22 (.i32 0)) 3 =
            .ext (.closureRef cid) := by
          simp only [Jvm.setLocal, (by decide : (3 : Nat) ≠ 22), (by decide : (3 : Nat) ≠ 21), ↓reduceIte]
          rw [hEndLocs 3 (by decide)]
          simp only [Jvm.setLocal, (by decide : (3 : Nat) ≠ 9), ↓reduceIte]
          rw [hLocs3 3 (by decide), hLocs2 3 (by decide), hLocs1 3 (by decide)]
          rfl
        rw [runJvmResFast_astore]
        rw [runJvmResFast_iconst]
        rw [runJvmResFast_istore]
        rw [runJvmResFast_aload hEnd3]
        rw [runJvmResFast_aload (v := .heapRef (jh3.objects.size + 1)) (by simp [Jvm.setLocal])]
        rw [runJvmResFast_iconst]
        rw [runJvmResFast_list_get hEndOut (by decide) (by simp)]
        rw [show ∀ h, ((List.map RsVal.toJvmVal [a, b, c]).toArray)[(0 : UInt32).toNat]'h = a.toJvmVal from
          fun _ => rfl]
        rw [runJvmResFast_dup]
        rw [runJvmResFast_ldcStr]
        rw [runJvmResFast_checkNotNull (RsVal.toJvmVal_isNull a)]
        rw [runJvmResFast_aload (v := .heapRef (jh3.objects.size + 1)) (by simp [Jvm.setLocal])]
        rw [runJvmResFast_iconst]
        rw [runJvmResFast_list_get hEndOut (by decide) (by simp)]
        rw [show ∀ h, ((List.map RsVal.toJvmVal [a, b, c]).toArray)[(1 : UInt32).toNat]'h = b.toJvmVal from
          fun _ => rfl]
        rw [runJvmResFast_dup]
        rw [runJvmResFast_ldcStr]
        rw [runJvmResFast_checkNotNull (RsVal.toJvmVal_isNull b)]
        rw [runJvmResFast_aload (v := .heapRef (jh3.objects.size + 1)) (by simp [Jvm.setLocal])]
        rw [runJvmResFast_iconst]
        rw [runJvmResFast_list_get hEndOut (by decide) (by simp)]
        rw [show ∀ h, ((List.map RsVal.toJvmVal [a, b, c]).toArray)[(2 : UInt32).toNat]'h = c.toJvmVal from
          fun _ => rfl]
        rw [runJvmResFast_dup]
        rw [runJvmResFast_ldcStr]
        rw [runJvmResFast_checkNotNull (RsVal.toJvmVal_isNull c)]
        rw [runJvmResFast_fn3_invoke hcl (out := (f a b c).toJvmVal)
          (by simp [RsVal.ofJvmVal?_toJvmVal])]
        rw [runJvmResFast_astore]
        rw [runJvmResFast_newClass_rs (by decide)]
        rw [runJvmResFast_dup]
        rw [runJvmResFast_aload (v := (f a b c).toJvmVal) (by simp [Jvm.setLocal])]
        rw [runJvmResFast_success_init]
        rw [runJvmResFast_checkcast_res rfl]
        rw [runJvmResFast_nop]
        refine exists_areturn_rs (by omega) ⟨?_, hStatClean (by rw [hEndStat, hStat3, hStat2, hStat1, hStat0]), rfl⟩
        simp [Model.combine3]
    · intro t hFailSingle
      have hD319 : ResourceStateKt_combine_1_prog.drop 319 = [.nop, .areturn] := by rfl
      rw [hD319]
      refine exists_nop_areturn_rs (by omega) ⟨?_, hClean3, rfl⟩
      have h1 : Model.extractFailures [r1, r2, r3] = [t] := hFailSingle
      cases r1 <;> cases r2 <;> cases r3 <;>
        simp [Model.extractFailures, Model.combine3] at h1 ⊢ <;> simp [h1]
    · intro t1 t2 ts' hFailMany endLocs endJh hEndStat
      have hD319 : ResourceStateKt_combine_1_prog.drop 319 = [.nop, .areturn] := by rfl
      rw [hD319]
      refine exists_nop_areturn_rs (by omega) ⟨?_, hStatClean (by rw [hEndStat, hStat3, hStat2, hStat1, hStat0]), rfl⟩
      have h1 : Model.extractFailures [r1, r2, r3] = t1 :: t2 :: ts' := hFailMany
      rw [show Model.extractFailures states = t1 :: t2 :: ts' from hFailMany]
      cases r1 <;> cases r2 <;> cases r3 <;>
        simp [Model.extractFailures, Model.combine3] at h1 ⊢ <;> simp [h1]
  rcases hCore with ⟨p, hRun, hVal, hStat, hHp⟩
  have hRun' :
      Jvm.runJvmResFast (mkRsHooks resolveProg (d' + 1) subFuel) 500 ResourceStateKt_combine_1_prog 0
          ResourceStateKt_combine_1_prog (initRsJvmState [(0, .ext (.res r1)), (1, .ext (.res r2)), (2, .ext (.res r3)),
            (3, .ext (.closureRef cid))] hp jh) =
        some (.ext (.res (Model.combine3 r1 r2 r3 f)), p.2) := by
    rw [hRun, ← hVal]
  exact ⟨p.2, Jvm.runJvmRes_of_runJvmResFast0 _ _ _ _ _ rfl (runJvmResFast_mono _ hf hRun'),
    hStat, hHp⟩

end ResourceState.KotlinJvmVerification
