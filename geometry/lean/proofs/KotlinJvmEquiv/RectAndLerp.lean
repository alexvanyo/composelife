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

import Std.Tactic.BVDecide
import Jvm.Proofs
import JvmSemantics
import KotlinJvmBytecode
import models.RectAndLerpModel
import theorems.RectAndLerpModelTheorems

namespace Geometry.KotlinJvmVerification
open Geometry.JvmVerification
open Geometry.KotlinJvmBytecode
open Geometry.KotlinModel

/-- Encodes `LayoutDirectionModel` as a symbolic JVM object reference. -/
def layoutDirVal : LayoutDirectionModel → JvmVal
  | .ltr => .allocRef "androidx/compose/ui/unit/LayoutDirection.Ltr"
  | .rtl => .allocRef "androidx/compose/ui/unit/LayoutDirection.Rtl"

/-- Heap containing `RectExtensionsKt$WhenMappings.$EnumSwitchMapping$0 = int[]{1, 2}`. -/
def rectWhenMappingsHeap : Jvm.JvmHeap Empty :=
  let (addr, h) := ({} : Jvm.JvmHeap Empty).alloc (.intArray #[1, 2])
  h.setStatic "com/alexvanyo/composelife/geometry/RectExtensionsKt$WhenMappings"
    "$EnumSwitchMapping$0" (.heapRef addr)

/--
Hooks for `RectExtensionsKt` and `IntSizeLerpKt`.
- `rect` / `intRect` supply the six anchor points of the receiver `Rect` / `IntRect`.
- `offsetTimes` / `offsetDiv` model `Offset.times-tuRUvjQ` / `Offset.div-tuRUvjQ`.
- `lerpInt` models `MathHelpersKt.lerp(IIF)I`.
- `RectKt.Rect-0a9Yr6o(topLeft, bottomRight)` returns `.pair (.i64 topLeft) (.i64 bottomRight)`.
-/
def mkRectLerpHooks
    (rect : RectCorners)
    (intRect : RectCorners)
    (offsetTimes : UInt64 → Float32 → UInt64 := fun o _ => o)
    (offsetDiv : UInt64 → Float32 → UInt64 := fun o _ => o)
    (lerpInt : Int32 → Int32 → Float32 → Int32 := fun a _ _ => a) :
    Jvm.JvmHooks Empty Unit where
  stepInvokeVirtual st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/ui/geometry/Rect", "getTopLeft-F1C5BW0", "()J",
        .allocRef "androidx/compose/ui/geometry/Rect" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 rect.topLeft :: rest })
    | "androidx/compose/ui/geometry/Rect", "getTopRight-F1C5BW0", "()J",
        .allocRef "androidx/compose/ui/geometry/Rect" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 rect.topRight :: rest })
    | "androidx/compose/ui/geometry/Rect", "getCenterLeft-F1C5BW0", "()J",
        .allocRef "androidx/compose/ui/geometry/Rect" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 rect.centerLeft :: rest })
    | "androidx/compose/ui/geometry/Rect", "getCenterRight-F1C5BW0", "()J",
        .allocRef "androidx/compose/ui/geometry/Rect" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 rect.centerRight :: rest })
    | "androidx/compose/ui/geometry/Rect", "getBottomLeft-F1C5BW0", "()J",
        .allocRef "androidx/compose/ui/geometry/Rect" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 rect.bottomLeft :: rest })
    | "androidx/compose/ui/geometry/Rect", "getBottomRight-F1C5BW0", "()J",
        .allocRef "androidx/compose/ui/geometry/Rect" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 rect.bottomRight :: rest })
    | "androidx/compose/ui/unit/IntRect", "getTopLeft-nOcc-ac", "()J",
        .allocRef "androidx/compose/ui/unit/IntRect" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 intRect.topLeft :: rest })
    | "androidx/compose/ui/unit/IntRect", "getTopRight-nOcc-ac", "()J",
        .allocRef "androidx/compose/ui/unit/IntRect" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 intRect.topRight :: rest })
    | "androidx/compose/ui/unit/IntRect", "getCenterLeft-nOcc-ac", "()J",
        .allocRef "androidx/compose/ui/unit/IntRect" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 intRect.centerLeft :: rest })
    | "androidx/compose/ui/unit/IntRect", "getCenterRight-nOcc-ac", "()J",
        .allocRef "androidx/compose/ui/unit/IntRect" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 intRect.centerRight :: rest })
    | "androidx/compose/ui/unit/IntRect", "getBottomLeft-nOcc-ac", "()J",
        .allocRef "androidx/compose/ui/unit/IntRect" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 intRect.bottomLeft :: rest })
    | "androidx/compose/ui/unit/IntRect", "getBottomRight-nOcc-ac", "()J",
        .allocRef "androidx/compose/ui/unit/IntRect" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 intRect.bottomRight :: rest })
    | "androidx/compose/ui/unit/LayoutDirection", "ordinal", "()I",
        .allocRef "androidx/compose/ui/unit/LayoutDirection.Ltr" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 0 :: rest })
    | "androidx/compose/ui/unit/LayoutDirection", "ordinal", "()I",
        .allocRef "androidx/compose/ui/unit/LayoutDirection.Rtl" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 1 :: rest })
    | _, _, _, _ => .inr none
  stepInvokeStatic st cls method desc :=
    match cls, method, desc, st.stack with
    | "androidx/compose/ui/geometry/Offset", "times-tuRUvjQ", "(JF)J", s :: o :: rest =>
      match o.asI64?, s.asF32? with
      | some po, some fs => .inl (some { st with pc := st.pc + 1, stack := .i64 (offsetTimes po fs) :: rest })
      | _, _ => .inr none
    | "androidx/compose/ui/geometry/Offset", "div-tuRUvjQ", "(JF)J", s :: o :: rest =>
      match o.asI64?, s.asF32? with
      | some po, some fs => .inl (some { st with pc := st.pc + 1, stack := .i64 (offsetDiv po fs) :: rest })
      | _, _ => .inr none
    | "androidx/compose/ui/geometry/RectKt", "Rect-0a9Yr6o", "(JJ)Landroidx/compose/ui/geometry/Rect;",
        br :: tl :: rest =>
      match tl.asI64?, br.asI64? with
      | some ptl, some pbr =>
        .inl (some { st with pc := st.pc + 1, stack := .pair (.i64 ptl) (.i64 pbr) :: rest })
      | _, _ => .inr none
    | "androidx/compose/ui/util/MathHelpersKt", "lerp", "(IIF)I", f :: b :: a :: rest =>
      match a.asI32?, b.asI32?, f.asF32? with
      | some va, some vb, some vf =>
        .inl (some { st with pc := st.pc + 1, stack := .i32 (lerpInt va.toInt32 vb.toInt32 vf).toUInt32 :: rest })
      | _, _, _ => .inr none
    | "androidx/compose/ui/unit/IntSize", "constructor-impl", "(J)J", _ =>
      .inl (some { st with pc := st.pc + 1 })
    | _, _, _, _ => .inr none

/-! ### RectExtensionsKt: times & div -/

theorem rect_times_equiv
    (rect intRect : RectCorners)
    (offsetTimes offsetDiv : UInt64 → Float32 → UInt64)
    (lerpInt : Int32 → Int32 → Float32 → Int32)
    (scale : Float32) :
    Jvm.runJvm (mkRectLerpHooks rect intRect offsetTimes offsetDiv lerpInt) 20
      RectExtensionsKt_times_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/geometry/Rect"), (1, .f32 scale)]) =
      some (.pair (.i64 (offsetTimes rect.topLeft scale)) (.i64 (offsetTimes rect.bottomRight scale))) := rfl

theorem rect_div_equiv
    (rect intRect : RectCorners)
    (offsetTimes offsetDiv : UInt64 → Float32 → UInt64)
    (lerpInt : Int32 → Int32 → Float32 → Int32)
    (scale : Float32) :
    Jvm.runJvm (mkRectLerpHooks rect intRect offsetTimes offsetDiv lerpInt) 20
      RectExtensionsKt_div_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/geometry/Rect"), (1, .f32 scale)]) =
      some (.pair (.i64 (offsetDiv rect.topLeft scale)) (.i64 (offsetDiv rect.bottomRight scale))) := rfl

/-! ### RectExtensionsKt: Rect RTL/LTR corners -/

theorem rect_topStart_equiv (rect intRect : RectCorners) (d : LayoutDirectionModel) :
    Jvm.runJvm (mkRectLerpHooks rect intRect) 25 RectExtensionsKt_topStart_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/geometry/Rect"), (1, layoutDirVal d)]
        rectWhenMappingsHeap) =
      some (.i64 (rect.topStart d)) := by
  cases d <;> rfl

theorem rect_topEnd_equiv (rect intRect : RectCorners) (d : LayoutDirectionModel) :
    Jvm.runJvm (mkRectLerpHooks rect intRect) 25 RectExtensionsKt_topEnd_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/geometry/Rect"), (1, layoutDirVal d)]
        rectWhenMappingsHeap) =
      some (.i64 (rect.topEnd d)) := by
  cases d <;> rfl

theorem rect_centerStart_equiv (rect intRect : RectCorners) (d : LayoutDirectionModel) :
    Jvm.runJvm (mkRectLerpHooks rect intRect) 25 RectExtensionsKt_centerStart_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/geometry/Rect"), (1, layoutDirVal d)]
        rectWhenMappingsHeap) =
      some (.i64 (rect.centerStart d)) := by
  cases d <;> rfl

theorem rect_centerEnd_equiv (rect intRect : RectCorners) (d : LayoutDirectionModel) :
    Jvm.runJvm (mkRectLerpHooks rect intRect) 25 RectExtensionsKt_centerEnd_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/geometry/Rect"), (1, layoutDirVal d)]
        rectWhenMappingsHeap) =
      some (.i64 (rect.centerEnd d)) := by
  cases d <;> rfl

theorem rect_bottomStart_equiv (rect intRect : RectCorners) (d : LayoutDirectionModel) :
    Jvm.runJvm (mkRectLerpHooks rect intRect) 25 RectExtensionsKt_bottomStart_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/geometry/Rect"), (1, layoutDirVal d)]
        rectWhenMappingsHeap) =
      some (.i64 (rect.bottomStart d)) := by
  cases d <;> rfl

theorem rect_bottomEnd_equiv (rect intRect : RectCorners) (d : LayoutDirectionModel) :
    Jvm.runJvm (mkRectLerpHooks rect intRect) 25 RectExtensionsKt_bottomEnd_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/geometry/Rect"), (1, layoutDirVal d)]
        rectWhenMappingsHeap) =
      some (.i64 (rect.bottomEnd d)) := by
  cases d <;> rfl

/-! ### RectExtensionsKt: IntRect RTL/LTR corners -/

theorem intRect_topStart_equiv (rect intRect : RectCorners) (d : LayoutDirectionModel) :
    Jvm.runJvm (mkRectLerpHooks rect intRect) 25 RectExtensionsKt_topStart_1_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/unit/IntRect"), (1, layoutDirVal d)]
        rectWhenMappingsHeap) =
      some (.i64 (intRect.topStart d)) := by
  cases d <;> rfl

theorem intRect_topEnd_equiv (rect intRect : RectCorners) (d : LayoutDirectionModel) :
    Jvm.runJvm (mkRectLerpHooks rect intRect) 25 RectExtensionsKt_topEnd_1_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/unit/IntRect"), (1, layoutDirVal d)]
        rectWhenMappingsHeap) =
      some (.i64 (intRect.topEnd d)) := by
  cases d <;> rfl

theorem intRect_centerStart_equiv (rect intRect : RectCorners) (d : LayoutDirectionModel) :
    Jvm.runJvm (mkRectLerpHooks rect intRect) 25 RectExtensionsKt_centerStart_1_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/unit/IntRect"), (1, layoutDirVal d)]
        rectWhenMappingsHeap) =
      some (.i64 (intRect.centerStart d)) := by
  cases d <;> rfl

theorem intRect_centerEnd_equiv (rect intRect : RectCorners) (d : LayoutDirectionModel) :
    Jvm.runJvm (mkRectLerpHooks rect intRect) 25 RectExtensionsKt_centerEnd_1_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/unit/IntRect"), (1, layoutDirVal d)]
        rectWhenMappingsHeap) =
      some (.i64 (intRect.centerEnd d)) := by
  cases d <;> rfl

theorem intRect_bottomStart_equiv (rect intRect : RectCorners) (d : LayoutDirectionModel) :
    Jvm.runJvm (mkRectLerpHooks rect intRect) 25 RectExtensionsKt_bottomStart_1_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/unit/IntRect"), (1, layoutDirVal d)]
        rectWhenMappingsHeap) =
      some (.i64 (intRect.bottomStart d)) := by
  cases d <;> rfl

theorem intRect_bottomEnd_equiv (rect intRect : RectCorners) (d : LayoutDirectionModel) :
    Jvm.runJvm (mkRectLerpHooks rect intRect) 25 RectExtensionsKt_bottomEnd_1_prog
      (initJvmState [(0, .allocRef "androidx/compose/ui/unit/IntRect"), (1, layoutDirVal d)]
        rectWhenMappingsHeap) =
      some (.i64 (intRect.bottomEnd d)) := by
  cases d <;> rfl

/-! ### IntSizeLerpKt: lerp(IntSize, IntSize, Float) -/

private theorem jvm_lshr32_eq_intSizeWidth (v : UInt64) :
    (UInt64.ofBitVec (v.toBitVec.sshiftRight ((32 : UInt32) &&& 63).toNat)).toUInt32.toInt32 =
      intSizeWidth v := by
  change (UInt64.ofBitVec (v.toBitVec.sshiftRight 32)).toUInt32.toInt32 = intSizeWidth v
  unfold intSizeWidth
  apply Int32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change ((v.toBitVec.sshiftRight 32).setWidth 32).getLsbD i = ((v.toBitVec >>> 32).setWidth 32).getLsbD i
  have hle : ¬ (64 ≤ i) := by omega
  have hadd : 32 + i < 64 := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_ushiftRight,
    hi, hle, hadd, decide_true, decide_false, Bool.not_false, Bool.true_and, ↓reduceIte]

private theorem jvm_andMask_eq_intSizeHeight (v : UInt64) :
    (v &&& 4294967295).toUInt32.toInt32 = intSizeHeight v := by
  unfold intSizeHeight
  bv_normalize

private theorem jvm_packIntSize_eq (w h : Int32) :
    ((UInt64.ofBitVec (w.toUInt32.toBitVec.signExtend 64) <<< ((32 : UInt32) &&& 63).toUInt64) |||
      (UInt64.ofBitVec (h.toUInt32.toBitVec.signExtend 64) &&& 4294967295)) =
      packIntSize w h := by
  unfold packIntSize
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (((w.toUInt32.toBitVec.signExtend 64) <<< 32) ||| ((h.toUInt32.toBitVec.signExtend 64) &&& 4294967295#64)).getLsbD i =
    (((w.toUInt32.toBitVec.setWidth 64) <<< 32) ||| (h.toUInt32.toBitVec.setWidth 64)).getLsbD i
  have hmask : (4294967295#64).getLsbD i = decide (i < 32) := by
    rw [BitVec.getLsbD_ofNat, show (4294967295 : Nat) = 2 ^ 32 - 1 by rfl, Nat.testBit_two_pow_sub_one]
    simp [hi]
  by_cases h32 : i < 32
  · simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_signExtend,
      BitVec.getLsbD_setWidth, hi, h32, hmask, decide_true, Bool.not_true, Bool.false_and, Bool.and_true,
      Bool.false_or, Bool.true_and, ↓reduceIte]
  · have hsub : i - 32 < 32 := by omega
    have hge : h.toUInt32.toBitVec.getLsbD i = false := by
      rw [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h.toUInt32.toBitVec.isLt (Nat.pow_le_pow_right (by omega) (by omega)))]
      rfl
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_signExtend,
      BitVec.getLsbD_setWidth, hi, h32, hsub, hmask, hge, decide_true, decide_false, Bool.not_false,
      Bool.true_and, Bool.and_false, Bool.or_false, ↓reduceIte]

theorem intSize_lerp_equiv
    (rect intRect : RectCorners)
    (offsetTimes offsetDiv : UInt64 → Float32 → UInt64)
    (lerpInt : Int32 → Int32 → Float32 → Int32)
    (start stop : UInt64) (fraction : Float32) :
    Jvm.runJvm (mkRectLerpHooks rect intRect offsetTimes offsetDiv lerpInt) 90
      IntSizeLerpKt_lerp_prog
      (initJvmState [(0, .i64 start), (2, .i64 stop), (4, .f32 fraction)]) =
      some (.i64 (lerpIntSizeModel lerpInt start stop fraction)) := by
  change some (JvmVal.i64 ((UInt64.ofBitVec
      ((lerpInt
          (UInt64.ofBitVec (start.toBitVec.sshiftRight ((32 : UInt32) &&& 63).toNat)).toUInt32.toInt32
          (UInt64.ofBitVec (stop.toBitVec.sshiftRight ((32 : UInt32) &&& 63).toNat)).toUInt32.toInt32
          fraction).toUInt32.toBitVec.signExtend 64) <<<
      ((32 : UInt32) &&& 63).toUInt64) |||
    (UInt64.ofBitVec
      ((lerpInt
          (start &&& 4294967295).toUInt32.toInt32
          (stop &&& 4294967295).toUInt32.toInt32
          fraction).toUInt32.toBitVec.signExtend 64) &&& 4294967295))) =
    some (JvmVal.i64 (lerpIntSizeModel lerpInt start stop fraction))
  rw [jvm_lshr32_eq_intSizeWidth, jvm_lshr32_eq_intSizeWidth,
    jvm_andMask_eq_intSizeHeight, jvm_andMask_eq_intSizeHeight, jvm_packIntSize_eq]
  rfl

end Geometry.KotlinJvmVerification
