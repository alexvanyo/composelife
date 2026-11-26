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
import JvmSemantics
import KotlinJvmBytecode
import models.ViewportMathModel
import theorems.ViewportMathModelTheorems

namespace UiCells.KotlinJvmVerification
open UiCells.JvmVerification
open UiCells.KotlinJvmBytecode
open UiCells.Model

set_option maxRecDepth 2000

private def anchorsCls : String := "com/alexvanyo/composelife/ui/cells/GridDraggableAnchors2d"
private def vpImplCls : String := "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl"
private def vpCls : String := "com/alexvanyo/composelife/ui/cells/CellWindowViewport"
private def surrCls : String := "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl$Surrogate"
private def trackCls : String := "com/alexvanyo/composelife/ui/cells/TrackingCellWindowViewportState"

private def ucIsSubtype (sub sup : String) : Bool :=
  sub == sup ||
  (sub == vpImplCls && sup == "com/alexvanyo/composelife/ui/cells/CellWindowViewportState") ||
  (sub == "MutableState" && sup == "androidx/compose/runtime/State") ||
  (sub == "MutableFloatState" && sup == "androidx/compose/runtime/FloatState") ||
  (sub == "FloatRange" && sup == "kotlin/ranges/ClosedRange") ||
  sup == "java/lang/Object"

def ucGetField? (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) : Option JvmVal :=
  match h.get? addr with
  | some obj => obj.getField? ucIsSubtype cls field
  | none => none

private def ucSetField (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) (v : JvmVal) : Jvm.JvmHeap Empty :=
  match h.get? addr with
  | some obj =>
    match obj.setField ucIsSubtype cls field v with
    | some obj' => h.set addr obj'
    | none => h
  | none => h

def packI32Pair (x y : Int32) : UInt64 :=
  (x.toUInt32.toUInt64 <<< 32) ||| y.toUInt32.toUInt64

def unpackI32X (p : UInt64) : Int32 := (p >>> 32).toUInt32.toInt32
def unpackI32Y (p : UInt64) : Int32 := p.toUInt32.toInt32

def allocFloatRange (h : Jvm.JvmHeap Empty) (lo hi : Float32) : Nat × Jvm.JvmHeap Empty :=
  h.alloc (.instance "FloatRange" [("lo", .f32 lo), ("hi", .f32 hi)])

def allocMutableState (h : Jvm.JvmHeap Empty) (v : JvmVal) : Nat × Jvm.JvmHeap Empty :=
  h.alloc (.instance "MutableState" [("value", v)])

def allocMutableFloatState (h : Jvm.JvmHeap Empty) (v : Float32) : Nat × Jvm.JvmHeap Empty :=
  h.alloc (.instance "MutableFloatState" [("value", .f32 v)])

/--
Hooks for `GridDraggableAnchors2d`, `MutableCellWindowViewportStateImpl`, and `TrackingCellWindowViewportState`.
-/
def mkViewportHooks
    (winTopLeft : UInt64 := 0)
    (offsetMinus : UInt64 → UInt64 → UInt64 := fun a _ => a)
    (offsetTimes : UInt64 → Float32 → UInt64 := fun a _ => a)
    (offsetDiv : UInt64 → Float32 → UInt64 := fun a _ => a)
    (offsetRound : UInt64 → UInt64 := fun a => a)
    (winHash : UInt32 := 7)
    (winEq : Bool := true) :
    Jvm.JvmHooks Empty Unit where
  isSubtypeOf := ucIsSubtype
  checkInstanceOf cls v :=
    match cls, v with
    | "androidx/compose/ui/unit/IntOffset", .boxedLong _ => true
    | "androidx/compose/ui/geometry/Offset", .boxedLong _ => true
    | "java/lang/Comparable", .f32 _ => true
    | "java/lang/Number", .f32 _ => true
    | _, _ => false
  checkCast cls v :=
    match cls, v with
    | "androidx/compose/ui/unit/IntOffset", .boxedLong _ => some v
    | "androidx/compose/ui/geometry/Offset", .boxedLong _ => some v
    | "java/lang/Comparable", .f32 _ => some v
    | "java/lang/Number", .f32 _ => some v
    | _, _ => Jvm.defaultCheckCast (fun _ a => nomatch a) cls v
  resolveStatic _st cls field _desc :=
    match cls, field with
    | "androidx/compose/ui/geometry/Offset", "Companion" =>
      some (.allocRef "androidx/compose/ui/geometry/Offset$Companion")
    | "com/alexvanyo/composelife/ui/cells/TrackingCellWindowViewportState$Companion", "$$INSTANCE" =>
      some (.allocRef "com/alexvanyo/composelife/ui/cells/TrackingCellWindowViewportState$Companion")
    | _, _ => none
  stepNewClass st cls :=
    let (addr, h') := st.jvmHeap.alloc (.instance cls [])
    .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := h' })
  stepInvokeDynamic st name _ _ :=
    match name, st.stack with
    | "makeConcatWithConstants", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str "GridDraggableAnchors2d(...)" :: rest })
    | _, _ => .inr none
  stepInvokeSpecial st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/Object", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "java/lang/IllegalArgumentException", "<init>", "(Ljava/lang/String;)V", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/ui/cells/GridDraggableAnchors2d", "<init>",
        "(FLandroidx/compose/ui/unit/IntRect;)V", win :: px :: .heapRef addr :: rest =>
      let h1 := ucSetField st.jvmHeap addr anchorsCls "scaledCellPixelSize" px
      let h2 := ucSetField h1 addr anchorsCls "cellWindow" win
      let h3 := ucSetField h2 addr anchorsCls "size" (.i32 2147483647)
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h3 })
    | "com/alexvanyo/composelife/ui/cells/GridDraggableAnchors2d", "<init>",
        "(FLandroidx/compose/ui/unit/IntRect;Lkotlin/jvm/internal/DefaultConstructorMarker;)V",
        _ :: win :: px :: .heapRef addr :: rest =>
      let h1 := ucSetField st.jvmHeap addr anchorsCls "scaledCellPixelSize" px
      let h2 := ucSetField h1 addr anchorsCls "cellWindow" win
      let h3 := ucSetField h2 addr anchorsCls "size" (.i32 2147483647)
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h3 })
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl$Companion", "<init>",
        "(Lkotlin/jvm/internal/DefaultConstructorMarker;)V", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/ui/cells/CellWindowViewport", "<init>",
        "(JFLkotlin/jvm/internal/DefaultConstructorMarker;)V",
        _ :: sc :: off :: .heapRef addr :: rest =>
      let h1 := ucSetField st.jvmHeap addr vpCls "offset" off
      let h2 := ucSetField h1 addr vpCls "scale" sc
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h2 })
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl$Surrogate", "<init>",
        "(JFLkotlin/ranges/ClosedRange;Lkotlin/jvm/internal/DefaultConstructorMarker;)V",
        _ :: rng :: sc :: off :: .heapRef addr :: rest =>
      let h1 := ucSetField st.jvmHeap addr surrCls "offset" off
      let h2 := ucSetField h1 addr surrCls "scale" sc
      let h3 := ucSetField h2 addr surrCls "scaleRange" rng
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h3 })
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "<init>",
        "(JFLkotlin/ranges/ClosedRange;Lkotlin/jvm/internal/DefaultConstructorMarker;)V",
        _ :: rng :: sc :: off :: .heapRef addr :: rest =>
      let h1 := ucSetField st.jvmHeap addr vpImplCls "initOffset" off
      let h2 := ucSetField h1 addr vpImplCls "initScale" sc
      let h3 := ucSetField h2 addr vpImplCls "initRange" rng
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h3 })
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "<init>",
        "(JFLkotlin/ranges/ClosedRange;ILkotlin/jvm/internal/DefaultConstructorMarker;)V",
        _ :: _ :: _ :: _ :: _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "<init>",
        "(JFLkotlin/ranges/ClosedRange;)V",
        _ :: _ :: _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "<init>",
        "(Lcom/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl$Surrogate;)V",
        _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "get_offset-F1C5BW0",
        "()J", .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr vpImplCls "_offset$delegate" with
      | some (.heapRef sAddr) =>
        match ucGetField? st.jvmHeap sAddr "MutableState" "value" with
        | some (.boxedLong v) => .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
        | _ => .inr none
      | _ => .inr none
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "set_offset-k-4lQ0M",
        "(J)V", v :: .heapRef addr :: rest =>
      match v.asI64?, ucGetField? st.jvmHeap addr vpImplCls "_offset$delegate" with
      | some pv, some (.heapRef sAddr) =>
        let h' := ucSetField st.jvmHeap sAddr "MutableState" "value" (.boxedLong pv)
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | _, _ => .inr none
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "get_scaleRange",
        "()Lkotlin/ranges/ClosedRange;", .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr vpImplCls "_scaleRange$delegate" with
      | some (.heapRef sAddr) =>
        match ucGetField? st.jvmHeap sAddr "MutableState" "value" with
        | some r => .inl (some { st with pc := st.pc + 1, stack := r :: rest })
        | none => .inr none
      | _ => .inr none
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "set_scaleRange",
        "(Lkotlin/ranges/ClosedRange;)V", r :: .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr vpImplCls "_scaleRange$delegate" with
      | some (.heapRef sAddr) =>
        let h' := ucSetField st.jvmHeap sAddr "MutableState" "value" r
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | _ => .inr none
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "get_scale",
        "()F", .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr vpImplCls "_scale$delegate" with
      | some (.heapRef sAddr) =>
        match ucGetField? st.jvmHeap sAddr "MutableFloatState" "value" with
        | some (.f32 f) => .inl (some { st with pc := st.pc + 1, stack := .f32 f :: rest })
        | _ => .inr none
      | _ => .inr none
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "set_scale",
        "(F)V", f :: .heapRef addr :: rest =>
      match f.asF32?, ucGetField? st.jvmHeap addr vpImplCls "_scale$delegate" with
      | some vf, some (.heapRef sAddr) =>
        let h' := ucSetField st.jvmHeap sAddr "MutableFloatState" "value" (.f32 vf)
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | _, _ => .inr none
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "getSurrogate",
        "()Lcom/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl$Surrogate;",
        .heapRef _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .allocRef surrCls :: rest })
    | _, _, _, _ => .inr none
  stepInvokeVirtual st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/Object", "toString", "()Ljava/lang/String;", .str s :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str s :: rest })
    | "java/lang/Number", "floatValue", "()F", .f32 f :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .f32 f :: rest })
    | "androidx/compose/ui/unit/IntOffset", "unbox-impl", "()J", .boxedLong v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
    | "androidx/compose/ui/geometry/Offset", "unbox-impl", "()J", .boxedLong v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
    | "androidx/compose/ui/geometry/Offset$Companion", "getZero-F1C5BW0", "()J", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 0 :: rest })
    | "com/alexvanyo/composelife/ui/cells/GridDraggableAnchors2d", "copy-oxMBog8",
        "(FLandroidx/compose/ui/unit/IntRect;)Lcom/alexvanyo/composelife/ui/cells/GridDraggableAnchors2d;",
        win :: px :: _ :: rest =>
      let (addr, h') := st.jvmHeap.alloc (.instance anchorsCls
        [("scaledCellPixelSize", px), ("cellWindow", win), ("size", .i32 2147483647)])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "com/alexvanyo/composelife/ui/cells/GridDraggableAnchors2d", "positionOf-LwL6lJo", "(J)J",
        a :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := a :: rest })
    | "com/alexvanyo/composelife/ui/cells/GridDraggableAnchors2d", "hasPositionFor--gyyYBs", "(J)Z",
        _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 1 :: rest })
    | "com/alexvanyo/composelife/ui/cells/GridDraggableAnchors2d", "closestAnchor-wUy82Zw", "(J)J",
        p :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := p :: rest })
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "getScaleRange",
        "()Lkotlin/ranges/ClosedRange;", .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr vpImplCls "_scaleRange$delegate" with
      | some (.heapRef sAddr) =>
        match ucGetField? st.jvmHeap sAddr "MutableState" "value" with
        | some r => .inl (some { st with pc := st.pc + 1, stack := r :: rest })
        | none => .inr none
      | _ => .inr none
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "setScaleRange",
        "(Lkotlin/ranges/ClosedRange;)V", r :: .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr vpImplCls "_scaleRange$delegate" with
      | some (.heapRef sAddr) =>
        let h' := ucSetField st.jvmHeap sAddr "MutableState" "value" r
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | _ => .inr none
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "setScale",
        "(F)V", f :: .heapRef addr :: rest =>
      match f.asF32?, ucGetField? st.jvmHeap addr vpImplCls "_scale$delegate",
            ucGetField? st.jvmHeap addr vpImplCls "_scaleRange$delegate" with
      | some vf, some (.heapRef sAddr), some (.heapRef rDel) =>
        let clamped :=
          match ucGetField? st.jvmHeap rDel "MutableState" "value" with
          | some (.heapRef rAddr) =>
            match ucGetField? st.jvmHeap rAddr "FloatRange" "lo", ucGetField? st.jvmHeap rAddr "FloatRange" "hi" with
            | some (.f32 lo), some (.f32 hi) => coerceInFloatRange vf { lo := lo, hi := hi }
            | _, _ => vf
          | _ => vf
        let h' := ucSetField st.jvmHeap sAddr "MutableFloatState" "value" (.f32 clamped)
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | _, _, _ => .inr none
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl", "setOffset-k-4lQ0M",
        "(J)V", v :: .heapRef addr :: rest =>
      match v.asI64?, ucGetField? st.jvmHeap addr vpImplCls "_offset$delegate" with
      | some pv, some (.heapRef sAddr) =>
        let h' := ucSetField st.jvmHeap sAddr "MutableState" "value" (.boxedLong pv)
        .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
      | _, _ => .inr none
    | "com/alexvanyo/composelife/ui/cells/CellWindowViewport", "getOffset-F1C5BW0", "()J",
        .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr vpCls "offset" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/ui/cells/CellWindowViewport", "getScale", "()F",
        .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr vpCls "scale" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl$Surrogate", "getOffset-F1C5BW0", "()J",
        .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr surrCls "offset" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl$Surrogate", "getScale", "()F",
        .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr surrCls "scale" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "com/alexvanyo/composelife/ui/cells/MutableCellWindowViewportStateImpl$Surrogate", "getScaleRange",
        "()Lkotlin/ranges/ClosedRange;", .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr surrCls "scaleRange" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | _, _, _, _ => .inr none
  stepInvokeInterface st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/runtime/State", "getValue", "()Ljava/lang/Object;", .heapRef sAddr :: rest =>
      match ucGetField? st.jvmHeap sAddr "MutableState" "value" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "androidx/compose/runtime/MutableState", "setValue", "(Ljava/lang/Object;)V",
        v :: .heapRef sAddr :: rest =>
      let h' := ucSetField st.jvmHeap sAddr "MutableState" "value" v
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "androidx/compose/runtime/FloatState", "getFloatValue", "()F", .heapRef sAddr :: rest =>
      match ucGetField? st.jvmHeap sAddr "MutableFloatState" "value" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none => .inr none
    | "androidx/compose/runtime/MutableFloatState", "setFloatValue", "(F)V",
        v :: .heapRef sAddr :: rest =>
      let h' := ucSetField st.jvmHeap sAddr "MutableFloatState" "value" v
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "kotlin/ranges/ClosedRange", "isEmpty", "()Z", .heapRef rAddr :: rest =>
      match ucGetField? st.jvmHeap rAddr "FloatRange" "lo", ucGetField? st.jvmHeap rAddr "FloatRange" "hi" with
      | some (.f32 lo), some (.f32 hi) =>
        let emp : UInt32 := if ({ lo := lo, hi := hi } : FloatRangeModel).isEmpty then 1 else 0
        .inl (some { st with pc := st.pc + 1, stack := .i32 emp :: rest })
      | _, _ => .inr none
    | _, _, _, _ => .inr none
  stepInvokeStatic st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/ui/unit/IntOffset", "getX-impl", "(J)I", v :: rest =>
      match v.asI64? with
      | some p => .inl (some { st with pc := st.pc + 1, stack := .i32 (unpackI32X p).toUInt32 :: rest })
      | none => .inr none
    | "androidx/compose/ui/unit/IntOffset", "getY-impl", "(J)I", v :: rest =>
      match v.asI64? with
      | some p => .inl (some { st with pc := st.pc + 1, stack := .i32 (unpackI32Y p).toUInt32 :: rest })
      | none => .inr none
    | "androidx/compose/ui/unit/IntOffset", "box-impl", "(J)Landroidx/compose/ui/unit/IntOffset;", v :: rest =>
      match v.asI64? with
      | some p => .inl (some { st with pc := st.pc + 1, stack := .boxedLong p :: rest })
      | none => .inr none
    | "androidx/compose/ui/unit/IntOffset", "plus-qkQi6aY", "(JJ)J", b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some pa, some pb =>
        let sum := packI32Pair (unpackI32X pa + unpackI32X pb) (unpackI32Y pa + unpackI32Y pb)
        .inl (some { st with pc := st.pc + 1, stack := .i64 sum :: rest })
      | _, _ => .inr none
    | "androidx/compose/ui/unit/IntOffsetKt", "round-k-4lQ0M", "(J)J", v :: rest =>
      match v.asI64? with
      | some p => .inl (some { st with pc := st.pc + 1, stack := .i64 (offsetRound p) :: rest })
      | none => .inr none
    | "androidx/compose/ui/geometry/Offset", "constructor-impl", "(J)J", _ =>
      .inl (some { st with pc := st.pc + 1 })
    | "androidx/compose/ui/geometry/Offset", "box-impl", "(J)Landroidx/compose/ui/geometry/Offset;", v :: rest =>
      match v.asI64? with
      | some p => .inl (some { st with pc := st.pc + 1, stack := .boxedLong p :: rest })
      | none => .inr none
    | "androidx/compose/ui/geometry/Offset", "minus-MK-Hz9U", "(JJ)J", b :: a :: rest =>
      match a.asI64?, b.asI64? with
      | some pa, some pb => .inl (some { st with pc := st.pc + 1, stack := .i64 (offsetMinus pa pb) :: rest })
      | _, _ => .inr none
    | "androidx/compose/ui/geometry/Offset", "times-tuRUvjQ", "(JF)J", s :: a :: rest =>
      match a.asI64?, s.asF32? with
      | some pa, some fs => .inl (some { st with pc := st.pc + 1, stack := .i64 (offsetTimes pa fs) :: rest })
      | _, _ => .inr none
    | "androidx/compose/ui/geometry/Offset", "div-tuRUvjQ", "(JF)J", s :: a :: rest =>
      match a.asI64?, s.asF32? with
      | some pa, some fs => .inl (some { st with pc := st.pc + 1, stack := .i64 (offsetDiv pa fs) :: rest })
      | _, _ => .inr none
    | "java/lang/Float", "floatToRawIntBits", "(F)I", x :: rest =>
      match x.asF32? with
      | some f => .inl (some { st with pc := st.pc + 1, stack := .i32 f.toBits :: rest })
      | none => .inr none
    | "java/lang/Float", "valueOf", "(F)Ljava/lang/Float;", x :: rest =>
      match x.asF32? with
      | some f => .inl (some { st with pc := st.pc + 1, stack := .f32 f :: rest })
      | none => .inr none
    | "java/lang/Float", "hashCode", "(F)I", x :: rest =>
      match x.asF32? with
      | some f => .inl (some { st with pc := st.pc + 1, stack := .i32 f.toBits :: rest })
      | none => .inr none
    | "java/lang/Float", "compare", "(FF)I", b :: a :: rest =>
      match a.asF32?, b.asF32? with
      | some va, some vb =>
        let c : UInt32 := if va.toBits == vb.toBits then 0 else 1
        .inl (some { st with pc := st.pc + 1, stack := .i32 c :: rest })
      | _, _ => .inr none
    | "com/alexvanyo/composelife/model/CellWindow", "getTopLeft-nOcc-ac", "(Landroidx/compose/ui/unit/IntRect;)J",
        _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 winTopLeft :: rest })
    | "com/alexvanyo/composelife/model/CellWindow", "toString-impl", "(Landroidx/compose/ui/unit/IntRect;)Ljava/lang/String;",
        _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str "CW" :: rest })
    | "com/alexvanyo/composelife/model/CellWindow", "hashCode-impl", "(Landroidx/compose/ui/unit/IntRect;)I",
        _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 winHash :: rest })
    | "com/alexvanyo/composelife/model/CellWindow", "equals-impl0",
        "(Landroidx/compose/ui/unit/IntRect;Landroidx/compose/ui/unit/IntRect;)Z",
        _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if winEq then 1 else 0) :: rest })
    | "androidx/compose/runtime/SnapshotStateKt", "mutableStateOf$default",
        "(Ljava/lang/Object;Landroidx/compose/runtime/SnapshotMutationPolicy;ILjava/lang/Object;)Landroidx/compose/runtime/MutableState;",
        _ :: _ :: _ :: v :: rest =>
      let (addr, h') := allocMutableState st.jvmHeap v
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
    | "androidx/compose/runtime/PrimitiveSnapshotStateKt", "mutableFloatStateOf",
        "(F)Landroidx/compose/runtime/MutableFloatState;", v :: rest =>
      match v.asF32? with
      | some vf =>
        let (addr, h') := allocMutableFloatState st.jvmHeap vf
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | none => .inr none
    | "kotlin/ranges/RangesKt", "rangeTo", "(FF)Lkotlin/ranges/ClosedFloatingPointRange;",
        hi :: lo :: rest =>
      match lo.asF32?, hi.asF32? with
      | some vlo, some vhi =>
        let (addr, h') := allocFloatRange st.jvmHeap vlo vhi
        .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: rest, jvmHeap := h' })
      | _, _ => .inr none
    | "kotlin/ranges/RangesKt", "coerceIn",
        "(Ljava/lang/Comparable;Lkotlin/ranges/ClosedRange;)Ljava/lang/Comparable;",
        .heapRef rAddr :: .f32 x :: rest =>
      match ucGetField? st.jvmHeap rAddr "FloatRange" "lo", ucGetField? st.jvmHeap rAddr "FloatRange" "hi" with
      | some (.f32 lo), some (.f32 hi) =>
        .inl (some { st with pc := st.pc + 1, stack := .f32 (coerceInFloatRange x { lo := lo, hi := hi }) :: rest })
      | _, _ => .inr none
    | "com/alexvanyo/composelife/ui/cells/CellWindowViewportStateKt", "getScale",
        "(Lcom/alexvanyo/composelife/ui/cells/CellWindowViewportState;)F", .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr vpImplCls "_scale$delegate" with
      | some (.heapRef sAddr) =>
        match ucGetField? st.jvmHeap sAddr "MutableFloatState" "value" with
        | some (.f32 f) => .inl (some { st with pc := st.pc + 1, stack := .f32 f :: rest })
        | _ => .inr none
      | _ => .inr none
    | "com/alexvanyo/composelife/ui/cells/CellWindowViewportStateKt", "getOffset",
        "(Lcom/alexvanyo/composelife/ui/cells/CellWindowViewportState;)J", .heapRef addr :: rest =>
      match ucGetField? st.jvmHeap addr vpImplCls "_offset$delegate" with
      | some (.heapRef sAddr) =>
        match ucGetField? st.jvmHeap sAddr "MutableState" "value" with
        | some (.boxedLong v) => .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
        | _ => .inr none
      | _ => .inr none
    | _, _, _, _ => .inr none

abbrev viewportHooks : Jvm.JvmHooks Empty Unit := mkViewportHooks

/-! ### GridDraggableAnchors2d (17 programs) -/

theorem gridDraggableAnchors2d_core_equiv (px : Float32) (anchor pos : UInt64) :
    (let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance anchorsCls [])
     ∃ endSt, Jvm.runJvmRes viewportHooks 25 GridDraggableAnchors2d_init_prog
       (initJvmState [(0, .heapRef addr), (1, .f32 px), (2, .allocRef "W")] h) = some (.unit, endSt) ∧
       ucGetField? endSt.jvmHeap addr anchorsCls "size" = some (.i32 2147483647)) ∧
    Jvm.runJvm viewportHooks 10 GridDraggableAnchors2d_hasPositionFor_prog
      (initJvmState [(0, .allocRef "A"), (1, .i64 anchor)]) = some (.i32 1) ∧
    (let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance anchorsCls
       [("scaledCellPixelSize", .f32 px), ("cellWindow", .allocRef "W"), ("size", .i32 2147483647)])
     Jvm.runJvm viewportHooks 10 GridDraggableAnchors2d_getSize_prog
       (initJvmState [(0, .heapRef addr)] h) = some (.i32 2147483647)) ∧
    (let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance anchorsCls
       [("scaledCellPixelSize", .f32 px), ("cellWindow", .allocRef "W"), ("size", .i32 2147483647)])
     Jvm.runJvm viewportHooks 10 GridDraggableAnchors2d_component1_prog
       (initJvmState [(0, .heapRef addr)] h) = some (.f32 px)) ∧
    (let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance anchorsCls
       [("scaledCellPixelSize", .f32 px), ("cellWindow", .allocRef "W"), ("size", .i32 2147483647)])
     Jvm.runJvm viewportHooks 10 GridDraggableAnchors2d_component2_prog
       (initJvmState [(0, .heapRef addr)] h) = some (.allocRef "W")) ∧
    (let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance anchorsCls
       [("scaledCellPixelSize", .f32 px), ("cellWindow", .allocRef "W")])
     Jvm.runJvm (mkViewportHooks (winTopLeft := 0) (offsetDiv := fun p _ => p) (offsetRound := fun p => p)) 25
       GridDraggableAnchors2d_closestAnchor_prog
       (initJvmState [(0, .heapRef addr), (1, .i64 pos)] h) =
       some (.i64 (packI32Pair (unpackI32X pos + 0) (unpackI32Y pos + 0)))) :=
  ⟨⟨_, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem gridDraggableAnchors2d_positionOf_and_bridges_equiv (px : Float32) (anchor pos : UInt64) :
    (let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance anchorsCls
       [("scaledCellPixelSize", .f32 px), ("cellWindow", .allocRef "W")])
     ∃ out, Jvm.runJvm viewportHooks 100 GridDraggableAnchors2d_positionOf_prog
       (initJvmState [(0, .heapRef addr), (1, .i64 anchor)] h) = some (.i64 out)) ∧
    Jvm.runJvm viewportHooks 15 GridDraggableAnchors2d_positionOf_1_prog
      (initJvmState [(0, .allocRef "A"), (1, .boxedLong anchor)]) = some (.i64 anchor) ∧
    Jvm.runJvm viewportHooks 15 GridDraggableAnchors2d_hasPositionFor_1_prog
      (initJvmState [(0, .allocRef "A"), (1, .boxedLong anchor)]) = some (.i32 1) ∧
    Jvm.runJvm viewportHooks 15 GridDraggableAnchors2d_closestAnchor_1_prog
      (initJvmState [(0, .allocRef "A"), (1, .i64 pos)]) = some (.boxedLong pos) ∧
    (let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance anchorsCls
       [("scaledCellPixelSize", .f32 px), ("cellWindow", .allocRef "W")])
     Jvm.runJvm viewportHooks 20 GridDraggableAnchors2d_copy_prog
       (initJvmState [(0, .heapRef addr), (1, .f32 px), (2, .allocRef "W")] h) = some (.heapRef 1)) ∧
    (let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance anchorsCls
       [("scaledCellPixelSize", .f32 px), ("cellWindow", .allocRef "W")])
     Jvm.runJvm viewportHooks 25 GridDraggableAnchors2d_copy_oxMBog8_default_prog
       (initJvmState [(0, .heapRef addr), (1, .f32 0.0), (2, .null), (3, .i32 3)] h) = some (.heapRef 1)) ∧
    (let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance anchorsCls
       [("scaledCellPixelSize", .f32 px), ("cellWindow", .allocRef "W")])
     Jvm.runJvm viewportHooks 15 GridDraggableAnchors2d_toString_prog
       (initJvmState [(0, .heapRef addr)] h) = none) ∧
    (let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance anchorsCls
       [("scaledCellPixelSize", .f32 px), ("cellWindow", .allocRef "W")])
     Jvm.runJvm viewportHooks 20 GridDraggableAnchors2d_hashCode_prog
       (initJvmState [(0, .heapRef addr)] h) = some (.i32 (px.toBits * 31 + 7))) ∧
    (let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance anchorsCls
       [("scaledCellPixelSize", .f32 px), ("cellWindow", .allocRef "W")])
     Jvm.runJvm viewportHooks 20 GridDraggableAnchors2d_equals_prog
       (initJvmState [(0, .heapRef addr), (1, .heapRef addr)] h) = some (.i32 1)) ∧
    (let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance anchorsCls [])
     Jvm.runJvm viewportHooks 15 GridDraggableAnchors2d_init_1_prog
       (initJvmState [(0, .heapRef addr), (1, .f32 px), (2, .allocRef "W")] h) = some .unit) ∧
    Jvm.runJvm viewportHooks 10 GridDraggableAnchors2d_clinit_prog (initJvmState []) = some .unit :=
  ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### MutableCellWindowViewportStateImpl (21 programs) & TrackingCellWindowViewportState -/

theorem mutableViewport_setScaleRange_bugfix_equiv :
    -- Valid existing range [0.5, 2.0], attempting to set empty new range [2.0, 0.5] MUST throw (return none)!
    (let (oldR, h0) := allocFloatRange {} (0.5 : Float32) (2.0 : Float32)
     let (newR, h1) := allocFloatRange h0 (2.0 : Float32) (0.5 : Float32)
     let (rDel, h2) := allocMutableState h1 (.heapRef oldR)
     let (sDel, h3) := allocMutableFloatState h2 (1.0 : Float32)
     let (selfAddr, h4) := h3.alloc (.instance vpImplCls
       [("_scaleRange$delegate", .heapRef rDel), ("_scale$delegate", .heapRef sDel)])
     Jvm.runJvm viewportHooks 40 MutableCellWindowViewportStateImpl_setScaleRange_prog
       (initJvmState [(0, .heapRef selfAddr), (1, .heapRef newR)] h4) = none) ∧
    -- Valid new range [2.0, 4.0] succeeds and re-clamps scale 1.0 -> 2.0!
    (let (oldR, h0) := allocFloatRange {} (0.5 : Float32) (2.0 : Float32)
     let (newR, h1) := allocFloatRange h0 (2.0 : Float32) (4.0 : Float32)
     let (rDel, h2) := allocMutableState h1 (.heapRef oldR)
     let (sDel, h3) := allocMutableFloatState h2 (1.0 : Float32)
     let (selfAddr, h4) := h3.alloc (.instance vpImplCls
       [("_scaleRange$delegate", .heapRef rDel), ("_scale$delegate", .heapRef sDel)])
     ∃ endSt,
       Jvm.runJvmRes viewportHooks 40 MutableCellWindowViewportStateImpl_setScaleRange_prog
         (initJvmState [(0, .heapRef selfAddr), (1, .heapRef newR)] h4) = some (.unit, endSt) ∧
       ucGetField? endSt.jvmHeap rDel "MutableState" "value" = some (.heapRef newR) ∧
       ucGetField? endSt.jvmHeap sDel "MutableFloatState" "value" = some (.f32 (2.0 : Float32))) :=
  ⟨rfl, ⟨_, rfl, rfl, rfl⟩⟩

theorem mutableViewport_setScale_clamps_equiv (x : Float32) :
    let (rAddr, h0) := allocFloatRange {} (0.5 : Float32) (2.0 : Float32)
    let (rDel, h1) := allocMutableState h0 (.heapRef rAddr)
    let (sDel, h2) := allocMutableFloatState h1 (1.0 : Float32)
    let (selfAddr, h3) := h2.alloc (.instance vpImplCls
      [("_scaleRange$delegate", .heapRef rDel), ("_scale$delegate", .heapRef sDel)])
    ∃ endSt,
      Jvm.runJvmRes viewportHooks 30 MutableCellWindowViewportStateImpl_setScale_prog
        (initJvmState [(0, .heapRef selfAddr), (1, .f32 x)] h3) = some (.unit, endSt) ∧
      ucGetField? endSt.jvmHeap sDel "MutableFloatState" "value" =
        some (.f32 (coerceInFloatRange x { lo := (0.5 : Float32), hi := (2.0 : Float32) })) :=
  ⟨_, rfl, rfl⟩

private theorem vp_hiteZ (v : Jvm.JvmVal Empty) (t e : Option (Jvm.JvmVal Empty)) :
    viewportHooks.iteZero? v t e =
      match viewportHooks.isZero? v with | some true => t | some false => e | none => none := by
  dsimp only [viewportHooks, mkViewportHooks]
  cases v.asI32? with
  | none => rfl
  | some x => cases h : (x == 0) <;> simp [h, Jvm.defaultIteVal] <;> split <;> rfl

private theorem vp_hiteNZ (v : Jvm.JvmVal Empty) (t e : Option (Jvm.JvmVal Empty)) :
    viewportHooks.iteNonZero? v t e =
      match viewportHooks.isZero? v with | some true => e | some false => t | none => none := by
  dsimp only [viewportHooks, mkViewportHooks]
  cases v.asI32? with
  | none => rfl
  | some x => cases h : (x == 0) <;> simp [h, Jvm.defaultIteVal] <;> split <;> rfl

theorem mutableViewport_init_default_equiv :
    let (_rAddr, h0) := allocFloatRange {} (0.5 : Float32) (2.0 : Float32)
    let (selfAddr, h1) := h0.alloc (.instance vpImplCls [])
    Jvm.runJvm viewportHooks 40 MutableCellWindowViewportStateImpl_init_1_prog
      (initJvmState [(0, .heapRef selfAddr), (1, .i64 0), (3, .f32 0.0), (4, .null), (5, .i32 7), (6, .null)] h1) =
      some .unit :=
  Jvm.runJvm_of_runJvmValFast0 viewportHooks vp_hiteZ vp_hiteNZ 40 _ _ _ rfl rfl

set_option maxHeartbeats 400000 in
theorem mutableViewport_init_primary_equiv (off : UInt64) (sc : Float32) :
    let (rAddr, h0) := allocFloatRange {} (0.5 : Float32) (2.0 : Float32)
    let (selfAddr, h1) := h0.alloc (.instance vpImplCls [])
    Jvm.runJvm viewportHooks 40 MutableCellWindowViewportStateImpl_init_prog
      (initJvmState [(0, .heapRef selfAddr), (1, .i64 off), (3, .f32 sc), (4, .heapRef rAddr)] h1) =
      some .unit :=
  Jvm.runJvm_of_runJvmValFast0 viewportHooks vp_hiteZ vp_hiteNZ 40 _ _ _ rfl rfl

theorem mutableViewport_inits_and_delegates_equiv (off : UInt64) (sc : Float32) :
    let (rAddr, h0) := allocFloatRange {} (0.5 : Float32) (2.0 : Float32)
    let (oDel, h1) := allocMutableState h0 (.boxedLong off)
    let (rDel, h2) := allocMutableState h1 (.heapRef rAddr)
    let (sDel, h3) := allocMutableFloatState h2 sc
    let (selfAddr, h4) := h3.alloc (.instance vpImplCls
      [("_offset$delegate", .heapRef oDel), ("_scaleRange$delegate", .heapRef rDel),
       ("_scale$delegate", .heapRef sDel)])
    let (surrAddr, h5) := h4.alloc (.instance surrCls [("offset", .i64 off), ("scale", .f32 sc), ("scaleRange", .heapRef rAddr)])
    Jvm.runJvm viewportHooks 20 MutableCellWindowViewportStateImpl_init_2_prog
      (initJvmState [(0, .heapRef selfAddr), (1, .heapRef surrAddr)] h5) = some .unit ∧
    Jvm.runJvm viewportHooks 25 MutableCellWindowViewportStateImpl_get_offset_prog
      (initJvmState [(0, .heapRef selfAddr)] h5) = some (.i64 off) ∧
    Jvm.runJvm viewportHooks 25 MutableCellWindowViewportStateImpl_set_offset_prog
      (initJvmState [(0, .heapRef selfAddr), (1, .i64 off)] h5) = some .unit ∧
    Jvm.runJvm viewportHooks 25 MutableCellWindowViewportStateImpl_get_scaleRange_prog
      (initJvmState [(0, .heapRef selfAddr)] h5) = some (.heapRef rAddr) ∧
    Jvm.runJvm viewportHooks 25 MutableCellWindowViewportStateImpl_set_scaleRange_prog
      (initJvmState [(0, .heapRef selfAddr), (1, .heapRef rAddr)] h5) = some .unit ∧
    Jvm.runJvm viewportHooks 15 MutableCellWindowViewportStateImpl_getScaleRange_prog
      (initJvmState [(0, .heapRef selfAddr)] h5) = some (.heapRef rAddr) ∧
    Jvm.runJvm viewportHooks 25 MutableCellWindowViewportStateImpl_get_scale_prog
      (initJvmState [(0, .heapRef selfAddr)] h5) = some (.f32 sc) ∧
    Jvm.runJvm viewportHooks 25 MutableCellWindowViewportStateImpl_set_scale_prog
      (initJvmState [(0, .heapRef selfAddr), (1, .f32 sc)] h5) = some .unit :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mutableViewport_viewport_and_surrogate_equiv (off : UInt64) (sc : Float32) :
    let (rAddr, h0) := allocFloatRange {} (0.5 : Float32) (2.0 : Float32)
    let (oDel, h1) := allocMutableState h0 (.boxedLong off)
    let (rDel, h2) := allocMutableState h1 (.heapRef rAddr)
    let (sDel, h3) := allocMutableFloatState h2 sc
    let (selfAddr, h4) := h3.alloc (.instance vpImplCls
      [("_offset$delegate", .heapRef oDel), ("_scaleRange$delegate", .heapRef rDel),
       ("_scale$delegate", .heapRef sDel)])
    let (vpAddr, h5) := h4.alloc (.instance vpCls [("offset", .i64 off), ("scale", .f32 sc)])
    let (surrAddr, h6) := h5.alloc (.instance surrCls [("offset", .i64 off), ("scale", .f32 sc), ("scaleRange", .heapRef rAddr)])
    (∃ a, Jvm.runJvm viewportHooks 25 MutableCellWindowViewportStateImpl_getCellWindowViewport_prog
      (initJvmState [(0, .heapRef selfAddr)] h6) = some (.heapRef a)) ∧
    Jvm.runJvm viewportHooks 25 MutableCellWindowViewportStateImpl_setCellWindowViewport_prog
      (initJvmState [(0, .heapRef selfAddr), (1, .heapRef vpAddr)] h6) = some .unit ∧
    Jvm.runJvm viewportHooks 15 MutableCellWindowViewportStateImpl_setOffset_prog
      (initJvmState [(0, .heapRef selfAddr), (1, .i64 off)] h6) = some .unit ∧
    (∃ a, Jvm.runJvm viewportHooks 25 MutableCellWindowViewportStateImpl_getSurrogate_prog
      (initJvmState [(0, .heapRef selfAddr)] h6) = some (.heapRef a)) ∧
    Jvm.runJvm viewportHooks 15 MutableCellWindowViewportStateImpl_init_3_prog
      (initJvmState [(0, .heapRef selfAddr)] h6) = some .unit ∧
    Jvm.runJvm viewportHooks 15 MutableCellWindowViewportStateImpl_init_4_prog
      (initJvmState [(0, .heapRef selfAddr), (1, .i64 off), (3, .f32 sc), (4, .heapRef rAddr)] h6) = some .unit ∧
    Jvm.runJvm viewportHooks 15 MutableCellWindowViewportStateImpl_access_getSurrogate_prog
      (initJvmState [(0, .heapRef selfAddr)] h6) = some (.allocRef surrCls) ∧
    Jvm.runJvm viewportHooks 15 MutableCellWindowViewportStateImpl_init_5_prog
      (initJvmState [(0, .heapRef selfAddr), (1, .heapRef surrAddr)] h6) = some .unit ∧
    Jvm.runJvm viewportHooks 15 MutableCellWindowViewportStateImpl_clinit_prog (initJvmState []) = some .unit ∧
    (∃ endSt, Jvm.runJvmRes viewportHooks 15 TrackingCellWindowViewportState_clinit_prog (initJvmState []) =
      some (.unit, endSt) ∧
      endSt.jvmHeap.getStatic? trackCls "Companion" =
        some (.allocRef "com/alexvanyo/composelife/ui/cells/TrackingCellWindowViewportState$Companion")) :=
  ⟨⟨_, rfl⟩, rfl, rfl, ⟨_, rfl⟩, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl, rfl⟩⟩

end UiCells.KotlinJvmVerification
