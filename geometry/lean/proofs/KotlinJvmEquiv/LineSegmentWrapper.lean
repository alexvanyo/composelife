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

import Jvm.FastExec
import Jvm.Proofs
import JvmSemantics
import KotlinJvmBytecode
import models.GeometryExtensionsModel

namespace Geometry.KotlinJvmVerification
open Geometry.JvmVerification
open Geometry.KotlinJvmBytecode
open Geometry.KotlinModel

set_option maxRecDepth 2000

private def pathCls : String := "com/alexvanyo/composelife/geometry/LineSegmentPath"

/-- Helper to read an instance field from a `JvmHeap`. -/
def heapGetField? (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) : Option JvmVal :=
  match h.get? addr with
  | some obj => obj.getField? (fun a b => a == b) cls field
  | none => none

/-- Helper to write an instance field in a `JvmHeap`. -/
def heapSetField (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) (v : JvmVal) : Jvm.JvmHeap Empty :=
  match h.get? addr with
  | some obj =>
    match obj.setField (fun a b => a == b) cls field v with
    | some obj' => h.set addr obj'
    | none => h
  | none => h

/-- Allocate a JVM `List` or `Set` wrapper instance backed by an `.objArray`. -/
def allocCollection (h : Jvm.JvmHeap Empty) (cls : String) (elems : Array JvmVal) : Nat × Jvm.JvmHeap Empty :=
  let (arrAddr, h1) := h.alloc (.objArray "java/lang/Object" elems)
  h1.alloc (.instance cls [("arr", .heapRef arrAddr)])

/-- Read the backing elements of a `List` or `Set` wrapper instance. -/
def getCollectionElems? (h : Jvm.JvmHeap Empty) (colAddr : Nat) (cls : String) : Option (Array JvmVal) :=
  match heapGetField? h colAddr cls "arr" with
  | some (.heapRef arrAddr) =>
    match h.get? arrAddr with
    | some (.objArray _ elems) => some elems
    | _ => none
  | _ => none

/-- Update the backing elements of a `List` or `Set` wrapper instance. -/
def setCollectionElems (h : Jvm.JvmHeap Empty) (colAddr : Nat) (cls : String) (elems : Array JvmVal) : Jvm.JvmHeap Empty :=
  match heapGetField? h colAddr cls "arr" with
  | some (.heapRef arrAddr) => h.set arrAddr (.objArray "java/lang/Object" elems)
  | _ => h

/--
Hooks for `LineSegmentKt`, `LineSegmentPath`, and `LineSegmentPathKt`.
- `List<Offset>` / `MutableSet<IntOffset>` are represented as `.instance "java/util/List"` /
  `.instance "java/util/Set"` pointing to a backing `.objArray`.
- `LineSegmentKt.cellIntersections(Offset, Offset, MutableSet)` invokes `floorModel` and
  `rayMarchFn` (defaulting to `Geometry.rayMarchSegmentCoords`).
-/
def mkLineSegHooks
    (hashCodeFn : JvmVal → UInt32 := fun _ => 0)
    (rayMarchFn : Float → Float → Float → Float → Int32 → Int32 → Int32 → Int32 →
      Array (Int32 × Int32) := Geometry.rayMarchSegmentCoords)
    (floorFn : UInt64 → UInt64 := floorModel)
    (segOracle : UInt64 → UInt64 → Array UInt64 := fun a b =>
      let sa := floorModel a
      let sb := floorModel b
      (rayMarchFn
        (offsetFloatX a).toFloat (offsetFloatY a).toFloat
        (offsetFloatX b).toFloat (offsetFloatY b).toFloat
        (offsetX sa) (offsetY sa) (offsetX sb) (offsetY sb)).map fun (x, y) => packOffset x y) :
    Jvm.JvmHooks Empty Unit where
  isSubtypeOf sub sup :=
    sub == sup ||
    (sub == "java/util/List" && sup == "java/util/Collection") ||
    (sub == "java/util/Set" && sup == "java/util/Collection") ||
    sup == "java/lang/Object"
  checkInstanceOf cls v :=
    match cls, v with
    | "androidx/compose/ui/geometry/Offset", .boxedLong _ => true
    | "androidx/compose/ui/unit/IntOffset", .boxedLong _ => true
    | "kotlin/Pair", .pair _ _ => true
    | "java/lang/Integer", .boxedInt _ => true
    | _, _ => false
  checkCast cls v :=
    match cls, v with
    | "androidx/compose/ui/geometry/Offset", .boxedLong _ => some v
    | "androidx/compose/ui/unit/IntOffset", .boxedLong _ => some v
    | "kotlin/Pair", .pair _ _ => some v
    | "java/lang/Integer", .boxedInt _ => some v
    | _, _ => Jvm.defaultCheckCast (fun _ a => nomatch a) cls v
  stepNewClass st cls :=
    let (addr, h') := st.jvmHeap.alloc (.instance cls [])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := h' })
  stepInvokeSpecial st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/Object", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "java/lang/IllegalArgumentException", "<init>", "(Ljava/lang/String;)V", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/geometry/LineSegmentPath", "<init>", "(Ljava/util/List;)V",
        .heapRef listAddr :: .heapRef addr :: rest =>
      match getCollectionElems? st.jvmHeap listAddr "java/util/List" with
      | some elems =>
        if elems.isEmpty then .inr none
        else
          let h' := heapSetField st.jvmHeap addr pathCls "points" (.heapRef listAddr)
          .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | none => .inr none
    | _, _, _, _ => .inr none
  stepInvokeVirtual st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/ui/geometry/Offset", "unbox-impl", "()J", .boxedLong v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
    | "java/lang/Object", "toString", "()Ljava/lang/String;", .str s :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str s :: rest })
    | "java/lang/Object", "hashCode", "()I", v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (hashCodeFn v) :: rest })
    | "java/lang/Integer", "intValue", "()I", .boxedInt v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 v :: rest })
    | "com/alexvanyo/composelife/geometry/LineSegmentPath", "getPoints", "()Ljava/util/List;",
        .heapRef addr :: rest =>
      match heapGetField? st.jvmHeap addr pathCls "points" with
      | some pts => .inl (some { st with pc := st.pc + 1, stack := pts :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/geometry/LineSegmentPath", "copy",
        "(Ljava/util/List;)Lcom/alexvanyo/composelife/geometry/LineSegmentPath;",
        .heapRef listAddr :: _ :: rest =>
      match getCollectionElems? st.jvmHeap listAddr "java/util/List" with
      | some elems =>
        if elems.isEmpty then .inr none
        else
          let (newAddr, h') := st.jvmHeap.alloc (.instance pathCls [("points", .heapRef listAddr)])
          .inl (some { st with pc := st.pc + 1, stack := .heapRef newAddr :: rest, jvmHeap := h' })
      | none => .inr none
    | _, _, _, _ => .inr none
  stepInvokeInterface st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/util/Collection", "isEmpty", "()Z", .heapRef addr :: rest =>
      match getCollectionElems? st.jvmHeap addr "java/util/List" with
      | some elems =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (if elems.isEmpty then 1 else 0) :: rest })
      | none => .inr none
    | "java/util/List", "size", "()I", .heapRef addr :: rest =>
      match getCollectionElems? st.jvmHeap addr "java/util/List" with
      | some elems =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (UInt32.ofNat elems.size) :: rest })
      | none => .inr none
    | "java/util/List", "get", "(I)Ljava/lang/Object;", idx :: .heapRef addr :: rest =>
      match idx.asI32?, getCollectionElems? st.jvmHeap addr "java/util/List" with
      | some vi, some elems =>
        match elems[vi.toNat]? with
        | some elem => .inl (some { st with pc := st.pc + 1, stack := elem :: rest })
        | none => .inr none
      | _, _ => .inr none
    | "java/util/Set", "add", "(Ljava/lang/Object;)Z", elem :: .heapRef setAddr :: rest =>
      match getCollectionElems? st.jvmHeap setAddr "java/util/Set" with
      | some elems =>
        let h' := setCollectionElems st.jvmHeap setAddr "java/util/Set" (elems.push elem)
        .inl (some { st with pc := st.pc + 1, stack := .i32 1 :: rest, jvmHeap := h' })
      | none => .inr none
    | _, _, _, _ => .inr none
  stepInvokeStatic st cls method desc :=
    match stepIntOffsetStatic st cls method desc with
    | .inl (some st') => .inl (some st')
    | _ =>
      match cls, method, desc, st.stack with
      | "java/lang/Float", "intBitsToFloat", "(I)F", x :: rest =>
        match x.asI32? with
        | some bits => .inl (some { st with pc := st.pc + 1, stack := .f32 (Float32.ofBits bits) :: rest })
        | none => .inr none
      | "kotlin/jvm/internal/Intrinsics", "checkNotNull", "(Ljava/lang/Object;Ljava/lang/String;)V",
          _ :: v :: rest =>
        if v.isNull then .inr none
        else .inl (some { st with pc := st.pc + 1, stack := rest })
      | "kotlin/collections/SetsKt", "createSetBuilder", "()Ljava/util/Set;", rest =>
        let (addr, h') := allocCollection st.jvmHeap "java/util/Set" #[]
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | "kotlin/collections/SetsKt", "build", "(Ljava/util/Set;)Ljava/util/Set;", s :: rest =>
        .inl (some { st with pc := st.pc + 1, stack := s :: rest })
      | "kotlin/collections/CollectionsKt", "first", "(Ljava/util/List;)Ljava/lang/Object;",
          .heapRef addr :: rest =>
        match getCollectionElems? st.jvmHeap addr "java/util/List" with
        | some elems =>
          match elems[0]? with
          | some e => .inl (some { st with pc := st.pc + 1, stack := e :: rest })
          | none => .inr none
        | none => .inr none
      | "com/alexvanyo/composelife/geometry/GeometryExtensionsKt", "floor-k-4lQ0M", "(J)J",
          v :: rest =>
        match v.asI64? with
        | some p => .inl (some { st with pc := st.pc + 1, stack := .i64 (floorFn p) :: rest })
        | none => .inr none
      | "com/alexvanyo/composelife/geometry/LineSegmentLeanKt", "f_Geometry_rayMarchSegmentCoords",
          "(DDDDIIII)[Ljava/lang/Object;",
          ey' :: ex' :: cy :: cx :: ey :: ex :: sy :: sx :: rest =>
        match sx.asF64?, sy.asF64?, ex.asF64?, ey.asF64?,
            cx.asI32?, cy.asI32?, ex'.asI32?, ey'.asI32? with
        | some vsx, some vsy, some vex, some vey, some vcx, some vcy, some vex', some vey' =>
          let coords := rayMarchFn vsx vsy vex vey
            vcx.toInt32 vcy.toInt32 vex'.toInt32 vey'.toInt32
          let pairs := Array.mk (coords.toList.map fun (x, y) => Jvm.JvmVal.pair (.boxedInt x.toUInt32) (.boxedInt y.toUInt32))
          let (addr, h') := st.jvmHeap.alloc (.objArray "[Ljava/lang/Object;" pairs)
          .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
        | _, _, _, _, _, _, _, _ => .inr none
      | "com/alexvanyo/composelife/geometry/IntOffset_jbKt", "IntOffset", "(II)J",
          y :: x :: rest =>
        match x.asI32?, y.asI32? with
        | some vx, some vy =>
          .inl (some { st with pc := st.pc + 1, stack := .i64 (packOffset vx.toInt32 vy.toInt32) :: rest })
        | _, _ => .inr none
      | "com/alexvanyo/composelife/geometry/LineSegmentKt", "cellIntersections-Wko1d7g",
          "(JJLjava/util/Set;)V", .heapRef setAddr :: b :: a :: rest =>
        match a.asI64?, b.asI64?, getCollectionElems? st.jvmHeap setAddr "java/util/Set" with
        | some pa, some pb, some elems =>
          let added := (segOracle pa pb).toList.map Jvm.JvmVal.boxedLong
          let h' := setCollectionElems st.jvmHeap setAddr "java/util/Set" (Array.mk (elems.toList ++ added))
          .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
        | _, _, _ => .inr none
      | "com/alexvanyo/composelife/geometry/LineSegmentKt", "cellIntersections",
          "(Ljava/util/List;)Ljava/util/Set;", .heapRef listAddr :: rest =>
        match getCollectionElems? st.jvmHeap listAddr "java/util/List" with
        | some elems =>
          if elems.isEmpty then .inr none
          else
            let (setAddr, h') := allocCollection st.jvmHeap "java/util/Set" elems
            .inl (some { st with pc := st.pc + 1, stack := .heapRef setAddr :: rest, jvmHeap := h' })
        | none => .inr none
      | _, _, _, _ => .inr none

abbrev lineSegHooks : Jvm.JvmHooks Empty Unit := mkLineSegHooks

/-! ### LineSegmentPath data class & init guard -/

theorem lineSegmentPath_clinit_equiv :
    ∃ endSt,
      Jvm.runJvmRes lineSegHooks 10 LineSegmentPath_clinit_prog (initJvmState []) =
        some (.unit, endSt) ∧
      endSt.jvmHeap.getStatic? pathCls "$stable" = some (.i32 8) :=
  ⟨_, rfl, rfl⟩

theorem lineSegmentPath_init_empty_throws :
    let (listAddr, h0) := allocCollection {} "java/util/List" #[]
    let (selfAddr, h1) := h0.alloc (.instance pathCls [])
    Jvm.runJvm lineSegHooks 40 LineSegmentPath_init_prog
      (initJvmState [(0, .heapRef selfAddr), (1, .heapRef listAddr)] h1) = none := rfl

theorem lineSegmentPath_init_nonempty_equiv (p : UInt64) :
    let (listAddr, h0) := allocCollection {} "java/util/List" #[.boxedLong p]
    let (selfAddr, h1) := h0.alloc (.instance pathCls [])
    ∃ endSt,
      Jvm.runJvmRes lineSegHooks 40 LineSegmentPath_init_prog
        (initJvmState [(0, .heapRef selfAddr), (1, .heapRef listAddr)] h1) = some (.unit, endSt) ∧
      heapGetField? endSt.jvmHeap selfAddr pathCls "points" = some (.heapRef listAddr) :=
  ⟨_, rfl, rfl⟩

theorem lineSegmentPath_getPoints_equiv (pts : JvmVal) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance pathCls [("points", pts)])
    Jvm.runJvm lineSegHooks 10 LineSegmentPath_getPoints_prog
      (initJvmState [(0, .heapRef selfAddr)] h) = some pts := rfl

theorem lineSegmentPath_component1_equiv (pts : JvmVal) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance pathCls [("points", pts)])
    Jvm.runJvm lineSegHooks 10 LineSegmentPath_component1_prog
      (initJvmState [(0, .heapRef selfAddr)] h) = some pts := rfl

theorem lineSegmentPath_copy_nonempty_equiv (p : UInt64) :
    let (listAddr, h0) := allocCollection {} "java/util/List" #[.boxedLong p]
    let (selfAddr, h1) := h0.alloc (.instance pathCls [("points", .heapRef listAddr)])
    ∃ newAddr endSt,
      Jvm.runJvmRes lineSegHooks 20 LineSegmentPath_copy_prog
        (initJvmState [(0, .heapRef selfAddr), (1, .heapRef listAddr)] h1) =
        some (.heapRef newAddr, endSt) ∧
      heapGetField? endSt.jvmHeap newAddr pathCls "points" = some (.heapRef listAddr) :=
  ⟨3, _, rfl, rfl⟩

theorem lineSegmentPath_copy_default_equiv (p : UInt64) :
    let (listAddr, h0) := allocCollection {} "java/util/List" #[.boxedLong p]
    let (selfAddr, h1) := h0.alloc (.instance pathCls [("points", .heapRef listAddr)])
    ∃ newAddr endSt,
      Jvm.runJvmRes lineSegHooks 20 LineSegmentPath_copy_default_prog
        (initJvmState [(0, .heapRef selfAddr), (1, .null), (2, .i32 1)] h1) =
        some (.heapRef newAddr, endSt) ∧
      heapGetField? endSt.jvmHeap newAddr pathCls "points" = some (.heapRef listAddr) :=
  ⟨3, _, rfl, rfl⟩

theorem lineSegmentPath_toString_equiv (s : String) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance pathCls [("points", .str s)])
    Jvm.runJvm lineSegHooks 10 LineSegmentPath_toString_prog
      (initJvmState [(0, .heapRef selfAddr)] h) = some (.str ("LineSegmentPath(points=" ++ s ++ ")")) := rfl

theorem lineSegmentPath_hashCode_equiv (hashCodeFn : JvmVal → UInt32) (pts : JvmVal) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance pathCls [("points", pts)])
    Jvm.runJvm (mkLineSegHooks hashCodeFn) 10 LineSegmentPath_hashCode_prog
      (initJvmState [(0, .heapRef selfAddr)] h) = some (.i32 (hashCodeFn pts)) := rfl

theorem lineSegmentPath_equals_refl (pts : JvmVal) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance pathCls [("points", pts)])
    Jvm.runJvm lineSegHooks 20 LineSegmentPath_equals_prog
      (initJvmState [(0, .heapRef selfAddr), (1, .heapRef selfAddr)] h) = some (.i32 1) := rfl

theorem lineSegmentPath_equals_distinct :
    (let (a1, h1) := ({} : Jvm.JvmHeap Empty).alloc (.instance pathCls [("points", .str "a")])
     let (a2, h2) := h1.alloc (.instance pathCls [("points", .str "a")])
     Jvm.runJvm lineSegHooks 30 LineSegmentPath_equals_prog
       (initJvmState [(0, .heapRef a1), (1, .heapRef a2)] h2) = some (.i32 1)) ∧
    (let (a1, h1) := ({} : Jvm.JvmHeap Empty).alloc (.instance pathCls [("points", .str "a")])
     let (a2, h2) := h1.alloc (.instance pathCls [("points", .str "b")])
     Jvm.runJvm lineSegHooks 30 LineSegmentPath_equals_prog
       (initJvmState [(0, .heapRef a1), (1, .heapRef a2)] h2) = some (.i32 0)) :=
  ⟨rfl, rfl⟩

/-! ### LineSegmentKt & LineSegmentPathKt -/

theorem lineSegment_cellIntersections_empty_throws :
    let (listAddr, h) := allocCollection {} "java/util/List" #[]
    Jvm.runJvm lineSegHooks 40 LineSegmentKt_cellIntersections_prog
      (initJvmState [(0, .heapRef listAddr)] h) = none := rfl

theorem lineSegment_cellIntersections_singleton_equiv :
    let (listAddr, h) := allocCollection {} "java/util/List" #[.boxedLong 0]
    ∃ setAddr endSt,
      Jvm.runJvmRes lineSegHooks 80 LineSegmentKt_cellIntersections_prog
        (initJvmState [(0, .heapRef listAddr)] h) = some (.heapRef setAddr, endSt) ∧
      getCollectionElems? endSt.jvmHeap setAddr "java/util/Set" = some #[.boxedLong (floorModel 0)] := by
  dsimp only [allocCollection]
  have hfast : ∃ endSt,
      Jvm.runJvmResFast lineSegHooks 80 LineSegmentKt_cellIntersections_prog 0
        LineSegmentKt_cellIntersections_prog
        (initJvmState [(0, .heapRef (({} : Jvm.JvmHeap Empty).alloc (.objArray "java/lang/Object" #[.boxedLong 0])).2.objects.size)]
          ((({} : Jvm.JvmHeap Empty).alloc (.objArray "java/lang/Object" #[.boxedLong 0])).2.alloc
            (.instance "java/util/List" [("arr", .heapRef (({} : Jvm.JvmHeap Empty).alloc (.objArray "java/lang/Object" #[.boxedLong 0])).1)])).2) =
        some (.heapRef 3, endSt) ∧
      getCollectionElems? endSt.jvmHeap 3 "java/util/Set" = some #[.boxedLong (floorModel 0)] :=
    ⟨_, rfl, rfl⟩
  rcases hfast with ⟨endSt, hrun, hcol⟩
  exact ⟨3, endSt, Jvm.runJvmRes_of_runJvmResFast0 lineSegHooks 80 _ _ _ rfl hrun, hcol⟩

theorem lineSegment_cellIntersections_pair_equiv :
    let (listAddr, h) := allocCollection {} "java/util/List" #[.boxedLong 0, .boxedLong 1]
    ∃ setAddr endSt,
      Jvm.runJvmRes (mkLineSegHooks (segOracle := fun _ _ => #[packOffset 2 3])) 100
        LineSegmentKt_cellIntersections_prog
        (initJvmState [(0, .heapRef listAddr)] h) = some (.heapRef setAddr, endSt) ∧
      getCollectionElems? endSt.jvmHeap setAddr "java/util/Set" =
        some #[.boxedLong (packOffset 2 3)] := by
  dsimp only [allocCollection]
  have hfast : ∃ endSt,
      Jvm.runJvmResFast (mkLineSegHooks (segOracle := fun _ _ => #[packOffset 2 3])) 100
        LineSegmentKt_cellIntersections_prog 0 LineSegmentKt_cellIntersections_prog
        (initJvmState [(0, .heapRef (({} : Jvm.JvmHeap Empty).alloc (.objArray "java/lang/Object" #[.boxedLong 0, .boxedLong 1])).2.objects.size)]
          ((({} : Jvm.JvmHeap Empty).alloc (.objArray "java/lang/Object" #[.boxedLong 0, .boxedLong 1])).2.alloc
            (.instance "java/util/List" [("arr", .heapRef (({} : Jvm.JvmHeap Empty).alloc (.objArray "java/lang/Object" #[.boxedLong 0, .boxedLong 1])).1)])).2) =
        some (.heapRef 3, endSt) ∧
      getCollectionElems? endSt.jvmHeap 3 "java/util/Set" = some #[.boxedLong (packOffset 2 3)] := by
    refine ⟨_, rfl, ?_⟩
    rfl
  rcases hfast with ⟨endSt, hrun, hcol⟩
  exact ⟨3, endSt, Jvm.runJvmRes_of_runJvmResFast0 _ 100 _ _ _ rfl hrun, hcol⟩

theorem lineSegment_cellIntersections_1_equiv
    (segOracle : UInt64 → UInt64 → Array UInt64) (a b : UInt64) :
    ∃ setAddr endSt,
      Jvm.runJvmRes (mkLineSegHooks (segOracle := segOracle)) 40 LineSegmentKt_cellIntersections_1_prog
        (initJvmState [(0, .i64 a), (2, .i64 b)]) = some (.heapRef setAddr, endSt) ∧
      getCollectionElems? endSt.jvmHeap setAddr "java/util/Set" =
        some (Array.mk ((segOracle a b).toList.map Jvm.JvmVal.boxedLong)) :=
  ⟨1, _, rfl, rfl⟩

theorem lineSegment_cellIntersections_2_singleton_equiv :
    let (setAddr, h) := allocCollection {} "java/util/Set" #[]
    ∃ endSt,
      Jvm.runJvmRes (mkLineSegHooks (rayMarchFn := fun _ _ _ _ _ _ _ _ => #[(1, 2)]) (floorFn := fun _ => 0)) 250
        LineSegmentKt_cellIntersections_2_prog
        (initJvmState [(0, .i64 0), (2, .i64 0), (4, .heapRef setAddr)] h) =
        some (.unit, endSt) ∧
      getCollectionElems? endSt.jvmHeap setAddr "java/util/Set" = some #[.boxedLong (packOffset 1 2)] := by
  have hfast :
      let (setAddr, h) := allocCollection {} "java/util/Set" #[]
      ∃ endSt,
        Jvm.runJvmResFast (mkLineSegHooks (rayMarchFn := fun _ _ _ _ _ _ _ _ => #[(1, 2)]) (floorFn := fun _ => 0)) 250
          LineSegmentKt_cellIntersections_2_prog 0 LineSegmentKt_cellIntersections_2_prog
          (initJvmState [(0, .i64 0), (2, .i64 0), (4, .heapRef setAddr)] h) =
          some (.unit, endSt) ∧
        getCollectionElems? endSt.jvmHeap setAddr "java/util/Set" = some #[.boxedLong (packOffset 1 2)] := by
    refine ⟨_, rfl, ?_⟩
    rfl
  rcases hfast with ⟨endSt, hrun, hcol⟩
  exact ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 _ 250 _ _ _ rfl hrun, hcol⟩

theorem lineSegment_cellIntersections_2_empty_equiv :
    let (setAddr, h) := allocCollection {} "java/util/Set" #[]
    ∃ endSt,
      Jvm.runJvmRes (mkLineSegHooks (rayMarchFn := fun _ _ _ _ _ _ _ _ => #[]) (floorFn := fun _ => 0)) 200
        LineSegmentKt_cellIntersections_2_prog
        (initJvmState [(0, .i64 0), (2, .i64 0), (4, .heapRef setAddr)] h) =
        some (.unit, endSt) ∧
      getCollectionElems? endSt.jvmHeap setAddr "java/util/Set" = some #[] := by
  have hfast :
      let (setAddr, h) := allocCollection {} "java/util/Set" #[]
      ∃ endSt,
        Jvm.runJvmResFast (mkLineSegHooks (rayMarchFn := fun _ _ _ _ _ _ _ _ => #[]) (floorFn := fun _ => 0)) 200
          LineSegmentKt_cellIntersections_2_prog 0 LineSegmentKt_cellIntersections_2_prog
          (initJvmState [(0, .i64 0), (2, .i64 0), (4, .heapRef setAddr)] h) =
          some (.unit, endSt) ∧
        getCollectionElems? endSt.jvmHeap setAddr "java/util/Set" = some #[] := by
    refine ⟨_, rfl, ?_⟩
    rfl
  rcases hfast with ⟨endSt, hrun, hcol⟩
  exact ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 _ 200 _ _ _ rfl hrun, hcol⟩

theorem lineSegmentPathKt_cellIntersections_equiv (p : UInt64) :
    let (listAddr, h0) := allocCollection {} "java/util/List" #[.boxedLong p]
    let (selfAddr, h1) := h0.alloc (.instance pathCls [("points", .heapRef listAddr)])
    ∃ setAddr endSt,
      Jvm.runJvmRes lineSegHooks 30 LineSegmentPathKt_cellIntersections_prog
        (initJvmState [(0, .heapRef selfAddr)] h1) = some (.heapRef setAddr, endSt) ∧
      getCollectionElems? endSt.jvmHeap setAddr "java/util/Set" = some #[.boxedLong p] :=
  ⟨4, _, rfl, rfl⟩

end Geometry.KotlinJvmVerification
