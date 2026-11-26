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

import Jvm.Proofs
import KotlinJvmBytecode
import models.CellStateModel
import theorems.CellStateModelTheorems

namespace Algorithm.KotlinJvmVerification
open Algorithm.KotlinJvmBytecode
open Algorithm.KotlinModel

set_option maxRecDepth 2000

private abbrev CsVal := Jvm.JvmVal Empty
private abbrev CsState := Jvm.JvmState Empty Unit

private def initCsState (slots : List (Nat × CsVal)) (jh : Jvm.JvmHeap Empty := {}) : CsState :=
  Jvm.initJvmState slots (.i32 0) () jh

private def csCls : String := "com/alexvanyo/composelife/model/CellState"
private def csImplCls : String := "com/alexvanyo/composelife/model/CellStateImpl"

private def csIsSubtype (sub sup : String) : Bool :=
  sub == sup ||
  (sub == csImplCls && sup == csCls) ||
  (sub == "java/util/Set" && (sup == "java/lang/Iterable" || sup == "java/util/Collection")) ||
  (sub == "java/util/ArrayList" && (sup == "java/util/List" || sup == "java/util/Collection" || sup == "java/lang/Iterable")) ||
  (sub == "java/util/List" && (sup == "java/lang/Iterable" || sup == "java/util/Collection")) ||
  sup == "java/lang/Object"

def csGetField? (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) : Option CsVal :=
  match h.get? addr with
  | some obj => obj.getField? csIsSubtype cls field
  | none => none

private def csSetHeapAt (h : Jvm.JvmHeap Empty) (addr : Nat) (obj : Jvm.HeapObj Empty) : Jvm.JvmHeap Empty :=
  { h with objects := Array.mk (h.objects.toList.set addr obj) }

private def csSetField (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) (v : CsVal) : Jvm.JvmHeap Empty :=
  match h.get? addr with
  | some obj =>
    match obj.setField csIsSubtype cls field v with
    | some obj' => csSetHeapAt h addr obj'
    | none => h
  | none => h

def allocCsCol (h : Jvm.JvmHeap Empty) (cls : String) (elems : Array CsVal) : Nat × Jvm.JvmHeap Empty :=
  let (arrAddr, h1) := h.alloc (.objArray "java/lang/Object" elems)
  h1.alloc (.instance cls [("arr", .heapRef arrAddr)])

def getCsCol? (h : Jvm.JvmHeap Empty) (colAddr : Nat) : Option (Array CsVal) :=
  match csGetField? h colAddr "java/lang/Object" "arr" with
  | some (.heapRef arrAddr) =>
    match h.get? arrAddr with
    | some (.objArray _ elems) => some elems
    | _ => none
  | _ => none

private def setCsCol (h : Jvm.JvmHeap Empty) (colAddr : Nat) (elems : Array CsVal) : Jvm.JvmHeap Empty :=
  match csGetField? h colAddr "java/lang/Object" "arr" with
  | some (.heapRef arrAddr) => csSetHeapAt h arrAddr (.objArray "java/lang/Object" elems)
  | _ => h

private def csValEq : CsVal → CsVal → Bool
  | .boxedLong a, .boxedLong b => a == b
  | .i64 a, .i64 b => a == b
  | .i32 a, .i32 b => a == b
  | .str a, .str b => a == b
  | .heapRef a, .heapRef b => a == b
  | _, _ => false

private def arrayContainsVal (arr : Array CsVal) (v : CsVal) : Bool :=
  arr.toList.any (csValEq · v)

private def arrayUnionVals (a b : Array CsVal) : Array CsVal :=
  Array.mk (b.toList.foldl (fun acc x => if acc.any (csValEq · x) then acc else acc ++ [x]) a.toList)

private def arraySubVals (a b : Array CsVal) : Array CsVal :=
  Array.mk (a.toList.filter (fun x => !b.toList.any (csValEq · x)))

private def arrayContainsAll (a b : Array CsVal) : Bool :=
  b.toList.all (fun x => a.toList.any (csValEq · x))

private def arrayDedupVals (a : Array CsVal) : Array CsVal :=
  Array.mk (a.toList.foldl (fun acc x => if acc.any (csValEq · x) then acc else acc ++ [x]) [])

/-- Hooks for `CellState`, `CellStateKt`, and `CellStateImpl`. -/
def mkCellStateHooks
    (hashCodeFn : CsVal → UInt32 := fun _ => 0)
    (windowPointsFn : CsVal → Array UInt64 := fun _ => #[]) :
    Jvm.JvmHooks Empty Unit where
  isSubtypeOf := csIsSubtype
  checkInstanceOf cls v :=
    match cls, v with
    | "androidx/compose/ui/unit/IntOffset", .boxedLong _ => true
    | "kotlin/Pair", .pair _ _ => true
    | _, _ => false
  checkCast cls v :=
    match cls, v with
    | "androidx/compose/ui/unit/IntOffset", .boxedLong _ => some v
    | "kotlin/Pair", .pair _ _ => some v
    | _, _ => Jvm.defaultCheckCast (fun _ a => nomatch a) cls v
  resolveStatic _st cls field _desc :=
    match cls, field with
    | "androidx/compose/ui/unit/IntRect", "Companion" =>
      some (.allocRef "androidx/compose/ui/unit/IntRect$Companion")
    | _, _ => none
  stepNewClass st cls :=
    match cls with
    | "java/util/ArrayList" =>
      let (addr, h') := allocCsCol st.jvmHeap "java/util/ArrayList" #[]
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := h' })
    | _ =>
      let (addr, h') := st.jvmHeap.alloc (.instance cls [])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := h' })
  stepInvokeDynamic st name _ _ :=
    match name, st.stack with
    | "makeConcatWithConstants", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str "CellStateImpl(...)" :: rest })
    | _, _ => .inr none
  stepInvokeSpecial st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/Object", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/model/CellState", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/model/CellState$Companion", "<init>",
        "(Lkotlin/jvm/internal/DefaultConstructorMarker;)V", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/model/CellStateImpl", "<init>", "(Ljava/util/Set;)V",
        setRef :: .heapRef addr :: rest =>
      let h' := csSetField st.jvmHeap addr csImplCls "aliveCells" setRef
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "java/util/ArrayList", "<init>", "(I)V", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "java/util/ArrayList", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "androidx/compose/ui/unit/IntRect", "<init>", "(IIII)V",
        b :: r :: t :: l :: .heapRef addr :: rest =>
      let h1 := csSetField st.jvmHeap addr "androidx/compose/ui/unit/IntRect" "left" l
      let h2 := csSetField h1 addr "androidx/compose/ui/unit/IntRect" "top" t
      let h3 := csSetField h2 addr "androidx/compose/ui/unit/IntRect" "right" r
      let h4 := csSetField h3 addr "androidx/compose/ui/unit/IntRect" "bottom" b
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h4 })
    | "java/util/NoSuchElementException", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | _, _, _, _ => .inr none
  stepInvokeVirtual st cls method desc :=
    match cls, method, desc, st.stack with
    | "com/alexvanyo/composelife/model/CellState", "getAliveCells", "()Ljava/util/Set;",
        .heapRef addr :: rest
    | "com/alexvanyo/composelife/model/CellStateImpl", "getAliveCells", "()Ljava/util/Set;",
        .heapRef addr :: rest =>
      match csGetField? st.jvmHeap addr csCls "aliveCells" with
      | some s => .inl (some { st with pc := st.pc + 1, stack := s :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/model/CellState", "offsetBy--gyyYBs",
        "(J)Lcom/alexvanyo/composelife/model/CellState;", delta :: .heapRef addr :: rest =>
      match delta.asI64?, csGetField? st.jvmHeap addr csCls "aliveCells" with
      | some vd, some (.heapRef setAddr) =>
        match getCsCol? st.jvmHeap setAddr with
        | some elems =>
          let shifted := elems.map fun x => match x with
            | .boxedLong v => .boxedLong (addCellOffset v vd)
            | other => other
          let (newSet, h1) := allocCsCol st.jvmHeap "java/util/Set" (arrayDedupVals shifted)
          let (newCs, h2) := h1.alloc (.instance csImplCls [("aliveCells", .heapRef newSet)])
          .inl (some { st with pc := st.pc + 1, stack := .heapRef newCs :: rest, jvmHeap := h2 })
        | none => .inr none
      | _, _ => .inr none
    | "androidx/compose/ui/unit/IntOffset", "unbox-impl", "()J", .boxedLong v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
    | "androidx/compose/ui/unit/IntRect$Companion", "getZero", "()Landroidx/compose/ui/unit/IntRect;",
        .allocRef "androidx/compose/ui/unit/IntRect$Companion" :: rest =>
      let (addr, h') := st.jvmHeap.alloc (.instance "androidx/compose/ui/unit/IntRect"
        [("left", .i32 0), ("top", .i32 0), ("right", .i32 0), ("bottom", .i32 0)])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "java/lang/Object", "hashCode", "()I", v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (hashCodeFn v) :: rest })
    | _, _, _, _ => .inr none
  stepInvokeInterface st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/util/Set", "isEmpty", "()Z", .heapRef addr :: rest =>
      match getCsCol? st.jvmHeap addr with
      | some elems =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (if elems.isEmpty then 1 else 0) :: rest })
      | none => .inr none
    | "java/util/Set", "size", "()I", .heapRef addr :: rest =>
      match getCsCol? st.jvmHeap addr with
      | some elems =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat elems.size) :: rest })
      | none => .inr none
    | "java/util/Set", "contains", "(Ljava/lang/Object;)Z", elem :: .heapRef addr :: rest =>
      match getCsCol? st.jvmHeap addr with
      | some elems =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (if arrayContainsVal elems elem then 1 else 0) :: rest })
      | none => .inr none
    | "java/util/Set", "containsAll", "(Ljava/util/Collection;)Z",
        .heapRef otherAddr :: .heapRef addr :: rest =>
      match getCsCol? st.jvmHeap addr, getCsCol? st.jvmHeap otherAddr with
      | some a, some b =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (if arrayContainsAll a b then 1 else 0) :: rest })
      | _, _ => .inr none
    | "java/util/Collection", "add", "(Ljava/lang/Object;)Z", elem :: .heapRef addr :: rest =>
      match getCsCol? st.jvmHeap addr with
      | some elems =>
        let h' := setCsCol st.jvmHeap addr (Array.mk (elems.toList ++ [elem]))
        .inl (some { st with pc := st.pc + 1, stack := .i32 1 :: rest, jvmHeap := h' })
      | none => .inr none
    | "java/lang/Iterable", "iterator", "()Ljava/util/Iterator;", .heapRef colAddr :: rest =>
      let (itAddr, h') := st.jvmHeap.alloc (.instance "Iterator" [("col", .heapRef colAddr), ("idx", .i32 0)])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef itAddr :: rest, jvmHeap := h' })
    | "java/util/Iterator", "hasNext", "()Z", .heapRef itAddr :: rest =>
      match csGetField? st.jvmHeap itAddr "Iterator" "col", csGetField? st.jvmHeap itAddr "Iterator" "idx" with
      | some (.heapRef colAddr), some (.i32 idx) =>
        match getCsCol? st.jvmHeap colAddr with
        | some elems =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 (if idx.toNat < elems.size then 1 else 0) :: rest })
        | none => .inr none
      | _, _ => .inr none
    | "java/util/Iterator", "next", "()Ljava/lang/Object;", .heapRef itAddr :: rest =>
      match csGetField? st.jvmHeap itAddr "Iterator" "col", csGetField? st.jvmHeap itAddr "Iterator" "idx" with
      | some (.heapRef colAddr), some (.i32 idx) =>
        match getCsCol? st.jvmHeap colAddr with
        | some elems =>
          match elems[idx.toNat]? with
          | some elem =>
            let h' := csSetHeapAt st.jvmHeap itAddr (.instance "Iterator" [("col", .heapRef colAddr), ("idx", .i32 (idx + 1))])
            .inl (some { st with pc := st.pc + 1, stack := elem :: rest, jvmHeap := h' })
          | none => .inr none
        | none => .inr none
      | _, _ => .inr none
    | _, _, _, _ => .inr none
  stepInvokeStatic st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/ui/unit/IntOffset", "constructor-impl", "(J)J", _ =>
      .inl (some { st with pc := st.pc + 1 })
    | "androidx/compose/ui/unit/IntOffset", "getX-impl", "(J)I", v :: rest =>
      match v.asI64? with
      | some p => .inl (some { st with pc := st.pc + 1, stack := .i32 (cellOffsetX p).toUInt32 :: rest })
      | none => .inr none
    | "androidx/compose/ui/unit/IntOffset", "getY-impl", "(J)I", v :: rest =>
      match v.asI64? with
      | some p => .inl (some { st with pc := st.pc + 1, stack := .i32 (cellOffsetY p).toUInt32 :: rest })
      | none => .inr none
    | "androidx/compose/ui/unit/IntOffset", "box-impl", "(J)Landroidx/compose/ui/unit/IntOffset;", v :: rest =>
      match v.asI64? with
      | some p => .inl (some { st with pc := st.pc + 1, stack := .boxedLong p :: rest })
      | none => .inr none
    | "androidx/compose/ui/unit/IntOffset", "plus-qkQi6aY", "(JJ)J", b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some pa, some pb => .inl (some { st with pc := st.pc + 1, stack := .i64 (addCellOffset pa pb) :: rest })
      | _, _ => .inr none
    | "androidx/compose/ui/unit/IntOffset", "minus-qkQi6aY", "(JJ)J", b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some pa, some pb => .inl (some { st with pc := st.pc + 1, stack := .i64 (subCellOffset pa pb) :: rest })
      | _, _ => .inr none
    | "com/alexvanyo/composelife/geometry/OffsetExtensionsKt", "toIntOffset", "(Lkotlin/Pair;)J",
        .pair (.boxedInt x) (.boxedInt y) :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 (packCellOffset x.toInt32 y.toInt32) :: rest })
    | "com/alexvanyo/composelife/model/CellWindow", "constructor-impl",
        "(Landroidx/compose/ui/unit/IntRect;)Landroidx/compose/ui/unit/IntRect;", _ =>
      .inl (some { st with pc := st.pc + 1 })
    | "com/alexvanyo/composelife/model/CellWindow", "containedPoints-impl",
        "(Landroidx/compose/ui/unit/IntRect;)Ljava/util/List;", win :: rest =>
      let (addr, h') := allocCsCol st.jvmHeap "java/util/List" (Array.mk ((windowPointsFn win).toList.map Jvm.JvmVal.boxedLong))
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "kotlin/collections/SetsKt", "emptySet", "()Ljava/util/Set;", rest =>
      let (addr, h') := allocCsCol st.jvmHeap "java/util/Set" #[]
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "kotlin/collections/SetsKt", "plus", "(Ljava/util/Set;Ljava/lang/Object;)Ljava/util/Set;",
        elem :: .heapRef setAddr :: rest =>
      match getCsCol? st.jvmHeap setAddr with
      | some elems =>
        let next := if arrayContainsVal elems elem then elems else Array.mk (elems.toList ++ [elem])
        let (addr, h') := allocCsCol st.jvmHeap "java/util/Set" next
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | none => .inr none
    | "kotlin/collections/SetsKt", "minus", "(Ljava/util/Set;Ljava/lang/Object;)Ljava/util/Set;",
        elem :: .heapRef setAddr :: rest =>
      match getCsCol? st.jvmHeap setAddr with
      | some elems =>
        let (addr, h') := allocCsCol st.jvmHeap "java/util/Set" (Array.mk (elems.toList.filter (fun x => !csValEq x elem)))
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | none => .inr none
    | "kotlin/collections/CollectionsKt", "union", "(Ljava/lang/Iterable;Ljava/lang/Iterable;)Ljava/util/Set;",
        .heapRef bAddr :: .heapRef aAddr :: rest =>
      match getCsCol? st.jvmHeap aAddr, getCsCol? st.jvmHeap bAddr with
      | some a, some b =>
        let (addr, h') := allocCsCol st.jvmHeap "java/util/Set" (arrayUnionVals a b)
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | _, _ => .inr none
    | "kotlin/collections/CollectionsKt", "subtract", "(Ljava/lang/Iterable;Ljava/lang/Iterable;)Ljava/util/Set;",
        .heapRef bAddr :: .heapRef aAddr :: rest =>
      match getCsCol? st.jvmHeap aAddr, getCsCol? st.jvmHeap bAddr with
      | some a, some b =>
        let (addr, h') := allocCsCol st.jvmHeap "java/util/Set" (arraySubVals a b)
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | _, _ => .inr none
    | "kotlin/collections/CollectionsKt", "collectionSizeOrDefault", "(Ljava/lang/Iterable;I)I",
        defVal :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := defVal :: rest })
    | "kotlin/collections/CollectionsKt", "toSet", "(Ljava/lang/Iterable;)Ljava/util/Set;",
        .heapRef colAddr :: rest =>
      match getCsCol? st.jvmHeap colAddr with
      | some elems =>
        let (addr, h') := allocCsCol st.jvmHeap "java/util/Set" (arrayDedupVals elems)
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | none => .inr none
    | "com/alexvanyo/composelife/model/CellStateKt", "CellState",
        "(Ljava/util/Set;)Lcom/alexvanyo/composelife/model/CellState;", setRef :: rest =>
      let (addr, h') := st.jvmHeap.alloc (.instance csImplCls [("aliveCells", setRef)])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | _, _, _, _ => .inr none

abbrev cellStateHooks : Jvm.JvmHooks Empty Unit := mkCellStateHooks

/-! ### CellState / CellStateImpl constructors, accessors, and static init -/

theorem cellState_init_equiv (self : CsVal) :
    Jvm.runJvm cellStateHooks 10 CellState_init_prog (initCsState [(0, self)]) = some .unit := rfl

theorem cellState_clinit_equiv :
    ∃ endSt,
      Jvm.runJvmRes cellStateHooks 15 CellState_clinit_prog (initCsState []) = some (.unit, endSt) ∧
      endSt.jvmHeap.getStatic? csCls "Companion" = some (.heapRef 0) :=
  ⟨_, rfl, rfl⟩

theorem cellStateImpl_init_equiv (setRef : CsVal) (hnn : setRef.isNull = false) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance csImplCls [])
    ∃ endSt,
      Jvm.runJvmRes cellStateHooks 15 CellStateImpl_init_prog
        (initCsState [(0, .heapRef selfAddr), (1, setRef)] h) = some (.unit, endSt) ∧
      csGetField? endSt.jvmHeap selfAddr csImplCls "aliveCells" = some setRef := by
  cases setRef <;> simp_all [Jvm.JvmVal.isNull] <;> exact ⟨_, rfl, rfl⟩

theorem cellStateImpl_getAliveCells_equiv (setRef : CsVal) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance csImplCls [("aliveCells", setRef)])
    Jvm.runJvm cellStateHooks 10 CellStateImpl_getAliveCells_prog
      (initCsState [(0, .heapRef selfAddr)] h) = some setRef := rfl

theorem cellStateImpl_toString_equiv :
    let (setAddr, h0) := allocCsCol {} "java/util/Set" #[]
    let (selfAddr, h1) := h0.alloc (.instance csImplCls [("aliveCells", .heapRef setAddr)])
    Jvm.runJvm cellStateHooks 20 CellStateImpl_toString_prog
      (initCsState [(0, .heapRef selfAddr)] h1) = none := rfl

theorem cellStateKt_cellState_equiv :
    let (setAddr, h) := allocCsCol {} "java/util/Set" #[]
    ∃ csAddr endSt,
      Jvm.runJvmRes cellStateHooks 20 CellStateKt_CellState_prog
        (initCsState [(0, .heapRef setAddr)] h) = some (.heapRef csAddr, endSt) ∧
      csGetField? endSt.jvmHeap csAddr csImplCls "aliveCells" = some (.heapRef setAddr) :=
  ⟨2, _, rfl, rfl⟩

theorem cellStateKt_emptyCellState_equiv :
    ∃ csAddr setAddr endSt,
      Jvm.runJvmRes cellStateHooks 20 CellStateKt_emptyCellState_prog (initCsState []) =
        some (.heapRef csAddr, endSt) ∧
      csGetField? endSt.jvmHeap csAddr csImplCls "aliveCells" = some (.heapRef setAddr) ∧
      getCsCol? endSt.jvmHeap setAddr = some #[] :=
  ⟨2, 1, _, rfl, rfl, rfl⟩

theorem cellStateKt_toCellState_singleton_equiv (x y : Int32) :
    let (setAddr, h) := allocCsCol {} "java/util/Set"
      #[.pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32)]
    ∃ csAddr resSet endSt,
      Jvm.runJvmRes cellStateHooks 120 CellStateKt_toCellState_prog
        (initCsState [(0, .heapRef setAddr)] h) = some (.heapRef csAddr, endSt) ∧
      csGetField? endSt.jvmHeap csAddr csImplCls "aliveCells" = some (.heapRef resSet) ∧
      getCsCol? endSt.jvmHeap resSet = some #[.boxedLong (packCellOffset x y)] := by
  have hx : x.toUInt32.toInt32 = x := by cases x; rfl
  have hy : y.toUInt32.toInt32 = y := by cases y; rfl
  have hrun :
      let (setAddr, h) := allocCsCol {} "java/util/Set"
        #[.pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32)]
      ∃ csAddr resSet endSt,
        Jvm.runJvmRes cellStateHooks 120 CellStateKt_toCellState_prog
          (initCsState [(0, .heapRef setAddr)] h) = some (.heapRef csAddr, endSt) ∧
        csGetField? endSt.jvmHeap csAddr csImplCls "aliveCells" = some (.heapRef resSet) ∧
        getCsCol? endSt.jvmHeap resSet = some #[.boxedLong (packCellOffset x.toUInt32.toInt32 y.toUInt32.toInt32)] :=
    ⟨7, 6, _, rfl, rfl, rfl⟩
  rw [hx, hy] at hrun
  exact hrun

/-! ### CellState operations -/

theorem cellState_union_same_equiv :
    let (s1, h0) := allocCsCol {} "java/util/Set" #[.boxedLong 1]
    let (s2, h1) := allocCsCol h0 "java/util/Set" #[.boxedLong 1]
    let (c1, h2) := h1.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
    let (c2, h3) := h2.alloc (.instance csImplCls [("aliveCells", .heapRef s2)])
    ∃ csAddr resSet endSt,
      Jvm.runJvmRes cellStateHooks 30 CellState_union_prog
        (initCsState [(0, .heapRef c1), (1, .heapRef c2)] h3) = some (.heapRef csAddr, endSt) ∧
      csGetField? endSt.jvmHeap csAddr csImplCls "aliveCells" = some (.heapRef resSet) ∧
      getCsCol? endSt.jvmHeap resSet = some #[.boxedLong 1] :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem cellState_subtract_same_equiv :
    let (s1, h0) := allocCsCol {} "java/util/Set" #[.boxedLong 1]
    let (s2, h1) := allocCsCol h0 "java/util/Set" #[.boxedLong 1]
    let (c1, h2) := h1.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
    let (c2, h3) := h2.alloc (.instance csImplCls [("aliveCells", .heapRef s2)])
    ∃ csAddr resSet endSt,
      Jvm.runJvmRes cellStateHooks 30 CellState_subtract_prog
        (initCsState [(0, .heapRef c1), (1, .heapRef c2)] h3) = some (.heapRef csAddr, endSt) ∧
      csGetField? endSt.jvmHeap csAddr csImplCls "aliveCells" = some (.heapRef resSet) ∧
      getCsCol? endSt.jvmHeap resSet = some #[] :=
  ⟨8, 7, _, rfl, rfl, rfl⟩

set_option maxHeartbeats 400000 in
theorem cellState_offsetBy_singleton_equiv (p d : UInt64) :
    let (s1, h0) := allocCsCol {} "java/util/Set" #[.boxedLong p]
    let (c1, h1) := h0.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
    ∃ csAddr resSet endSt,
      Jvm.runJvmRes cellStateHooks 120 CellState_offsetBy_prog
        (initCsState [(0, .heapRef c1), (1, .i64 d)] h1) = some (.heapRef csAddr, endSt) ∧
      csGetField? endSt.jvmHeap csAddr csImplCls "aliveCells" = some (.heapRef resSet) ∧
      getCsCol? endSt.jvmHeap resSet = some #[.boxedLong (addCellOffset p d)] := by
  have hfast :
      let (s1, h0) := allocCsCol {} "java/util/Set" #[.boxedLong p]
      let (c1, h1) := h0.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
      ∃ csAddr resSet endSt,
        Jvm.runJvmResFast cellStateHooks 120 CellState_offsetBy_prog 0 CellState_offsetBy_prog
          (initCsState [(0, .heapRef c1), (1, .i64 d)] h1) = some (.heapRef csAddr, endSt) ∧
        csGetField? endSt.jvmHeap csAddr csImplCls "aliveCells" = some (.heapRef resSet) ∧
        getCsCol? endSt.jvmHeap resSet = some #[.boxedLong (addCellOffset p d)] :=
    ⟨8, 7, _, rfl, rfl, rfl⟩
  dsimp only at hfast ⊢
  rcases hfast with ⟨csAddr, resSet, endSt, hrun, hf, hc⟩
  exact ⟨csAddr, resSet, endSt, Jvm.runJvmRes_of_runJvmResFast0 cellStateHooks 120 _ _ _ rfl hrun, hf, hc⟩

theorem cellState_withCell_add_empty_equiv (p : UInt64) :
    let (s1, h0) := allocCsCol {} "java/util/Set" #[]
    let (c1, h1) := h0.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
    ∃ csAddr resSet endSt,
      Jvm.runJvmRes cellStateHooks 30 CellState_withCell_prog
        (initCsState [(0, .heapRef c1), (1, .i64 p), (3, .i32 1)] h1) = some (.heapRef csAddr, endSt) ∧
      csGetField? endSt.jvmHeap csAddr csImplCls "aliveCells" = some (.heapRef resSet) ∧
      getCsCol? endSt.jvmHeap resSet = some #[.boxedLong p] :=
  ⟨5, 4, _, rfl, rfl, rfl⟩

theorem cellState_withCell_remove_singleton_equiv :
    let (s1, h0) := allocCsCol {} "java/util/Set" #[.boxedLong 7]
    let (c1, h1) := h0.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
    ∃ csAddr resSet endSt,
      Jvm.runJvmRes cellStateHooks 30 CellState_withCell_prog
        (initCsState [(0, .heapRef c1), (1, .i64 7), (3, .i32 0)] h1) = some (.heapRef csAddr, endSt) ∧
      csGetField? endSt.jvmHeap csAddr csImplCls "aliveCells" = some (.heapRef resSet) ∧
      getCsCol? endSt.jvmHeap resSet = some #[] :=
  ⟨5, 4, _, rfl, rfl, rfl⟩

theorem cellState_getAliveCellsInWindow_singleton_equiv :
    let (s1, h0) := allocCsCol {} "java/util/Set" #[.boxedLong 7]
    let (c1, h1) := h0.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
    ∃ listAddr endSt,
      Jvm.runJvmRes (mkCellStateHooks (windowPointsFn := fun _ => #[7])) 120 CellState_getAliveCellsInWindow_prog
        (initCsState [(0, .heapRef c1), (1, .allocRef "Win")] h1) = some (.heapRef listAddr, endSt) ∧
      getCsCol? endSt.jvmHeap listAddr = some #[.boxedLong 7] :=
  ⟨6, _, rfl, rfl⟩

theorem cellState_getBoundingBox_empty_equiv :
    let (s1, h0) := allocCsCol {} "java/util/Set" #[]
    let (c1, h1) := h0.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
    ∃ rectAddr endSt,
      Jvm.runJvmRes cellStateHooks 40 CellState_getBoundingBox_prog
        (initCsState [(0, .heapRef c1)] h1) = some (.heapRef rectAddr, endSt) ∧
      csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "left" = some (.i32 0) ∧
      csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "top" = some (.i32 0) ∧
      csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "right" = some (.i32 0) ∧
      csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "bottom" = some (.i32 0) :=
  ⟨3, _, rfl, rfl, rfl, rfl, rfl⟩

theorem cellState_getBoundingBox_singleton_equiv :
    let p := packCellOffset 3 4
    let (s1, h0) := allocCsCol {} "java/util/Set" #[.boxedLong p]
    let (c1, h1) := h0.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
    ∃ rectAddr endSt,
      Jvm.runJvmRes cellStateHooks 150 CellState_getBoundingBox_prog
        (initCsState [(0, .heapRef c1)] h1) = some (.heapRef rectAddr, endSt) ∧
      csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "left" = some (.i32 3) ∧
      csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "top" = some (.i32 4) ∧
      csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "right" = some (.i32 4) ∧
      csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "bottom" = some (.i32 5) := by
  have hfast :
      let p := packCellOffset 3 4
      let (s1, h0) := allocCsCol {} "java/util/Set" #[.boxedLong p]
      let (c1, h1) := h0.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
      ∃ rectAddr endSt,
        Jvm.runJvmResFast cellStateHooks 150 CellState_getBoundingBox_prog 0 CellState_getBoundingBox_prog
          (initCsState [(0, .heapRef c1)] h1) = some (.heapRef rectAddr, endSt) ∧
        csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "left" = some (.i32 3) ∧
        csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "top" = some (.i32 4) ∧
        csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "right" = some (.i32 4) ∧
        csGetField? endSt.jvmHeap rectAddr "androidx/compose/ui/unit/IntRect" "bottom" = some (.i32 5) :=
    ⟨7, _, rfl, rfl, rfl, rfl, rfl⟩
  dsimp only at hfast ⊢
  rcases hfast with ⟨rectAddr, endSt, hrun, h1, h2, h3, h4⟩
  exact ⟨rectAddr, endSt, Jvm.runJvmRes_of_runJvmResFast0 cellStateHooks 150 _ _ _ rfl hrun, h1, h2, h3, h4⟩

theorem cellState_equals_nonCellState_false :
    let (s1, h0) := allocCsCol {} "java/util/Set" #[]
    let (c1, h1) := h0.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
    Jvm.runJvm cellStateHooks 30 CellState_equals_prog
      (initCsState [(0, .heapRef c1), (1, .str "not a CellState")] h1) = some (.i32 0) := rfl

theorem cellState_equals_singleton_equiv :
    (let (s1, h0) := allocCsCol {} "java/util/Set" #[.boxedLong 5]
     let (s2, h1) := allocCsCol h0 "java/util/Set" #[.boxedLong 5]
     let (c1, h2) := h1.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
     let (c2, h3) := h2.alloc (.instance csImplCls [("aliveCells", .heapRef s2)])
     Jvm.runJvm cellStateHooks 40 CellState_equals_prog
       (initCsState [(0, .heapRef c1), (1, .heapRef c2)] h3) = some (.i32 1)) ∧
    (let (s1, h0) := allocCsCol {} "java/util/Set" #[.boxedLong 5]
     let (s2, h1) := allocCsCol h0 "java/util/Set" #[.boxedLong 6]
     let (c1, h2) := h1.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
     let (c2, h3) := h2.alloc (.instance csImplCls [("aliveCells", .heapRef s2)])
     Jvm.runJvm cellStateHooks 40 CellState_equals_prog
       (initCsState [(0, .heapRef c1), (1, .heapRef c2)] h3) = some (.i32 0)) :=
  ⟨rfl, rfl⟩

theorem cellState_hashCode_equiv (hashCodeFn : CsVal → UInt32) :
    let (s1, h0) := allocCsCol {} "java/util/Set" #[]
    let (c1, h1) := h0.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
    Jvm.runJvm (mkCellStateHooks hashCodeFn) 20 CellState_hashCode_prog
      (initCsState [(0, .heapRef c1)] h1) = some (.i32 (hashCodeFn (.heapRef 4))) := rfl

theorem cellStateKt_equalsModuloOffset_empty_equiv :
    let (s1, h0) := allocCsCol {} "java/util/Set" #[]
    let (s2, h1) := allocCsCol h0 "java/util/Set" #[]
    let (c1, h2) := h1.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
    let (c2, h3) := h2.alloc (.instance csImplCls [("aliveCells", .heapRef s2)])
    Jvm.runJvm cellStateHooks 40 CellStateKt_equalsModuloOffset_prog
      (initCsState [(0, .heapRef c1), (1, .heapRef c2)] h3) = some (.i32 1) := rfl

theorem cellStateKt_equalsModuloOffset_diffSize_equiv (p : UInt64) :
    let (s1, h0) := allocCsCol {} "java/util/Set" #[.boxedLong p]
    let (s2, h1) := allocCsCol h0 "java/util/Set" #[]
    let (c1, h2) := h1.alloc (.instance csImplCls [("aliveCells", .heapRef s1)])
    let (c2, h3) := h2.alloc (.instance csImplCls [("aliveCells", .heapRef s2)])
    Jvm.runJvm cellStateHooks 40 CellStateKt_equalsModuloOffset_prog
      (initCsState [(0, .heapRef c1), (1, .heapRef c2)] h3) = some (.i32 0) := rfl

end Algorithm.KotlinJvmVerification
