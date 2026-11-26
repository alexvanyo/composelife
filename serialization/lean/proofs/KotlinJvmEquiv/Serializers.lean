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
import Jvm.Semantics
import JvmSemantics
import KotlinJvmBytecode
import models.SerializersModel
import theorems.SerializersModelTheorems

namespace Serialization.KotlinJvmVerification
open Serialization.JvmVerification
open Serialization.KotlinJvmBytecode
open Serialization.Model

set_option maxRecDepth 4000

def resolveSerProg : String → Option (List JvmInstr)
  | "com/alexvanyo/composelife/serialization/ClosedFloatRangeSerializer.deserialize:(Lkotlinx/serialization/encoding/Decoder;)Lkotlin/ranges/ClosedRange;" =>
    some ClosedFloatRangeSerializer_deserialize_prog
  | "com/alexvanyo/composelife/serialization/ClosedFloatRangeSerializer.serialize:(Lkotlinx/serialization/encoding/Encoder;Lkotlin/ranges/ClosedRange;)V" =>
    some ClosedFloatRangeSerializer_serialize_prog
  | "com/alexvanyo/composelife/serialization/IntOffsetSerializer.deserialize-Bjo55l4:(Lkotlinx/serialization/encoding/Decoder;)J" =>
    some IntOffsetSerializer_deserialize_prog
  | "com/alexvanyo/composelife/serialization/IntOffsetSerializer.serialize-I_oMVgE:(Lkotlinx/serialization/encoding/Encoder;J)V" =>
    some IntOffsetSerializer_serialize_prog
  | "com/alexvanyo/composelife/serialization/OffsetSerializer.deserialize-tuRUvjQ:(Lkotlinx/serialization/encoding/Decoder;)J" =>
    some OffsetSerializer_deserialize_prog
  | "com/alexvanyo/composelife/serialization/OffsetSerializer.serialize-Uv8p0NA:(Lkotlinx/serialization/encoding/Encoder;J)V" =>
    some OffsetSerializer_serialize_prog
  | "com/alexvanyo/composelife/serialization/RectSerializer.deserialize:(Lkotlinx/serialization/encoding/Decoder;)Landroidx/compose/ui/geometry/Rect;" =>
    some RectSerializer_deserialize_prog
  | "com/alexvanyo/composelife/serialization/RectSerializer.serialize:(Lkotlinx/serialization/encoding/Encoder;Landroidx/compose/ui/geometry/Rect;)V" =>
    some RectSerializer_serialize_prog
  | _ => none

def serHooks : Jvm.JvmHooks SerExt SerHeap := mkSerHooks resolveSerProg 80

/-- Heap invariant: `PrimitiveKind$LONG.INSTANCE` is not overridden in `jh.statics`. -/
def HasPrimitiveKindLongClean (jh : Jvm.JvmHeap SerExt) : Prop :=
  jh.getStatic? "kotlinx/serialization/descriptors/PrimitiveKind$LONG" "INSTANCE" = none

theorem emptyJvmHeap_primitiveKindLongClean : HasPrimitiveKindLongClean ({} : Jvm.JvmHeap SerExt) := rfl

private theorem runJvmRes_step_inl {Ext Heap : Type} {hooks : Jvm.JvmHooks Ext Heap}
    {fuel : Nat} {prog : List JvmInstr} {st st' : Jvm.JvmState Ext Heap} {instr : JvmInstr}
    (hfetch : prog[st.pc]? = some instr)
    (hnobr : Jvm.isBranchInstr instr = false)
    (hstep : Jvm.stepInstr hooks instr st = .inl (some st')) :
    Jvm.runJvmRes hooks (fuel + 1) prog st = Jvm.runJvmRes hooks fuel prog st' := by
  cases instr <;> simp [Jvm.isBranchInstr] at hnobr <;>
    simp [Jvm.runJvmRes, hfetch, hstep]

private theorem runJvmRes_step_inr {Ext Heap : Type} {hooks : Jvm.JvmHooks Ext Heap}
    {fuel : Nat} {prog : List JvmInstr} {st : Jvm.JvmState Ext Heap} {instr : JvmInstr} {v : Jvm.JvmVal Ext}
    (hfetch : prog[st.pc]? = some instr)
    (hnobr : Jvm.isBranchInstr instr = false)
    (hstep : Jvm.stepInstr hooks instr st = .inr (some v)) :
    Jvm.runJvmRes hooks (fuel + 1) prog st = some (v, st) := by
  cases instr <;> simp [Jvm.isBranchInstr] at hnobr <;>
    simp [Jvm.runJvmRes, hfetch, hstep]

private theorem runJvm_step_inl {Ext Heap : Type} {hooks : Jvm.JvmHooks Ext Heap}
    {fuel : Nat} {prog : List JvmInstr} {st st' : Jvm.JvmState Ext Heap} {instr : JvmInstr}
    (hfetch : prog[st.pc]? = some instr)
    (hnobr : Jvm.isBranchInstr instr = false)
    (hstep : Jvm.stepInstr hooks instr st = .inl (some st')) :
    Jvm.runJvm hooks (fuel + 1) prog st = Jvm.runJvm hooks fuel prog st' := by
  cases instr <;> simp [Jvm.isBranchInstr] at hnobr <;>
    simp [Jvm.runJvm, hfetch, hstep]

private theorem runJvm_step_inr {Ext Heap : Type} {hooks : Jvm.JvmHooks Ext Heap}
    {fuel : Nat} {prog : List JvmInstr} {st : Jvm.JvmState Ext Heap} {instr : JvmInstr} {v : Jvm.JvmVal Ext}
    (hfetch : prog[st.pc]? = some instr)
    (hnobr : Jvm.isBranchInstr instr = false)
    (hstep : Jvm.stepInstr hooks instr st = .inr (some v)) :
    Jvm.runJvm hooks (fuel + 1) prog st = some v := by
  cases instr <;> simp [Jvm.isBranchInstr] at hnobr <;>
    simp [Jvm.runJvm, hfetch, hstep]

private theorem jvmHeap_get_alloc {Ext : Type} (jh : Jvm.JvmHeap Ext) (obj : Jvm.HeapObj Ext) :
    (jh.alloc obj).2.get? (jh.alloc obj).1 = some obj := by
  simp [Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]

private theorem jvmHeap_get_set_same {Ext : Type} (jh : Jvm.JvmHeap Ext) (addr : Nat)
    (obj : Jvm.HeapObj Ext) (hlt : addr < jh.objects.size) :
    (jh.set addr obj).get? addr = some obj := by
  unfold Jvm.JvmHeap.set Jvm.JvmHeap.get?
  simp [hlt]

private theorem jvmHeap_size_set {Ext : Type} (jh : Jvm.JvmHeap Ext) (addr : Nat)
    (obj : Jvm.HeapObj Ext) :
    (jh.set addr obj).objects.size = jh.objects.size := by
  unfold Jvm.JvmHeap.set
  split <;> simp

private theorem jvmHeap_size_alloc {Ext : Type} (jh : Jvm.JvmHeap Ext) (obj : Jvm.HeapObj Ext) :
    (jh.alloc obj).1 < (jh.alloc obj).2.objects.size := by
  simp [Jvm.JvmHeap.alloc]

private theorem jvmHeap_getStatic_setStatic_same {Ext : Type} (jh : Jvm.JvmHeap Ext)
    (cls field : String) (v : Jvm.JvmVal Ext) :
    (jh.setStatic cls field v).getStatic? cls field = some v := by
  simp [Jvm.JvmHeap.setStatic, Jvm.JvmHeap.getStatic?]

private theorem list_find_filter_of_disjoint {α : Type} (p q : α → Bool) (l : List α)
    (h : ∀ x, p x = true → q x = true) :
    (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases hqa : q a with
    | true =>
      simp only [List.filter, hqa, List.find?]
      cases hpa : p a with
      | true => rfl
      | false => exact ih
    | false =>
      have hpa : p a = false := by
        cases hpa : p a with
        | false => rfl
        | true => exfalso; have := h a hpa; rw [hqa] at this; exact Bool.false_ne_true this
      simp only [List.filter, hqa, List.find?, hpa]
      exact ih

private theorem jvmHeap_getStatic_setStatic_ne {Ext : Type} (jh : Jvm.JvmHeap Ext)
    (cls1 f1 cls2 f2 : String) (v : Jvm.JvmVal Ext) (hne : (cls1, f1) ≠ (cls2, f2)) :
    (jh.setStatic cls1 f1 v).getStatic? cls2 f2 = jh.getStatic? cls2 f2 := by
  unfold Jvm.JvmHeap.setStatic Jvm.JvmHeap.getStatic?
  have hhead : (cls1 == cls2 && f1 == f2) = false := by
    cases hc : (cls1 == cls2) <;> cases hf : (f1 == f2) <;> simp_all
  simp only [List.find?, hhead]
  congr 1
  apply list_find_filter_of_disjoint
  intro ⟨c, f, _⟩ hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  rcases hp with ⟨rfl, rfl⟩
  have : (c == cls1 && f == f1) = false := by
    cases hc : (c == cls1) <;> cases hf : (f == f1) <;> simp_all
  simp [this]

private theorem jvm_lshr32_eq_unpackInt1 (v : UInt64) :
    (UInt64.ofBitVec (v.toBitVec.sshiftRight ((32 : UInt32) &&& 63).toNat)).toUInt32 =
      (unpackInt1 v).toUInt32 := by
  change (UInt64.ofBitVec (v.toBitVec.sshiftRight 32)).toUInt32 = (unpackInt1 v).toUInt32
  unfold unpackInt1
  bv_normalize

private theorem jvm_i2l_pack_eq_packInts (x y : Int32) :
    ((UInt64.ofBitVec (x.toUInt32.toBitVec.signExtend 64) <<< ((32 : UInt32) &&& 63).toUInt64) |||
      (UInt64.ofBitVec (y.toUInt32.toBitVec.signExtend 64) &&& 4294967295)) = packInts x y := by
  unfold packInts
  bv_normalize

private theorem jvm_i2l_pack_eq_packFloats (x y : Float32) :
    ((UInt64.ofBitVec (x.toBits.toBitVec.signExtend 64) <<< ((32 : UInt32) &&& 63).toUInt64) |||
      (UInt64.ofBitVec (y.toBits.toBitVec.signExtend 64) &&& 4294967295)) = packFloats x y := by
  unfold packFloats
  bv_normalize

private theorem stepInstr_primitiveSerialDescriptor
    {pc : Nat} {name : String} {rest : List SerVal} {locs : Nat → SerVal}
    {jh : Jvm.JvmHeap SerExt} {hp : SerHeap} :
    Jvm.stepInstr serBaseHooks
      (.invokestatic "kotlinx/serialization/descriptors/SerialDescriptorsKt" "PrimitiveSerialDescriptor"
        "(Ljava/lang/String;Lkotlinx/serialization/descriptors/PrimitiveKind;)Lkotlinx/serialization/descriptors/SerialDescriptor;")
      ⟨pc, .ext .primitiveKindLong :: .str name :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.serialDescriptor name (some "LONG")) :: rest, locs, jh, hp⟩) := rfl

private theorem stepInstr_serialDescriptor
    {pc : Nat} {name origName : String} {orig : Option String} {rest : List SerVal} {locs : Nat → SerVal}
    {jh : Jvm.JvmHeap SerExt} {hp : SerHeap} :
    Jvm.stepInstr serBaseHooks
      (.invokestatic "kotlinx/serialization/descriptors/SerialDescriptorsKt" "SerialDescriptor"
        "(Ljava/lang/String;Lkotlinx/serialization/descriptors/SerialDescriptor;)Lkotlinx/serialization/descriptors/SerialDescriptor;")
      ⟨pc, .ext (.serialDescriptor origName orig) :: .str name :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.serialDescriptor name (some origName)) :: rest, locs, jh, hp⟩) := rfl

private theorem stepInstr_serHooks_virt_ret
    {pc : Nat} {cls method desc : String} {recv dec retVal : SerVal} {rest : List SerVal}
    {locs : Nat → SerVal} {jh : Jvm.JvmHeap SerExt} {hp : SerHeap} {subEnd : SerState}
    (hcall : serHooks.stepInvokeVirtual ⟨pc, dec :: recv :: rest, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, retVal :: rest, locs, subEnd.jvmHeap, subEnd.heap⟩))
    (hgen : Jvm.stepInvokeVirtualGeneric serHooks ⟨pc, dec :: recv :: rest, locs, jh, hp⟩ cls method desc =
      serHooks.stepInvokeVirtual ⟨pc, dec :: recv :: rest, locs, jh, hp⟩ cls method desc) :
    Jvm.stepInstr serHooks (.invokevirtual cls method desc) ⟨pc, dec :: recv :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, retVal :: rest, locs, subEnd.jvmHeap, subEnd.heap⟩) := by
  dsimp only [Jvm.stepInstr]
  rw [hgen, hcall]

private theorem stepInstr_serHooks_virt_void
    {pc : Nat} {cls method desc : String} {recv enc val : SerVal} {rest : List SerVal}
    {locs : Nat → SerVal} {jh : Jvm.JvmHeap SerExt} {hp : SerHeap} {subEnd : SerState}
    (hcall : serHooks.stepInvokeVirtual ⟨pc, val :: enc :: recv :: rest, locs, jh, hp⟩ cls method desc =
      .inl (some ⟨pc + 1, rest, locs, subEnd.jvmHeap, subEnd.heap⟩))
    (hgen : Jvm.stepInvokeVirtualGeneric serHooks ⟨pc, val :: enc :: recv :: rest, locs, jh, hp⟩ cls method desc =
      serHooks.stepInvokeVirtual ⟨pc, val :: enc :: recv :: rest, locs, jh, hp⟩ cls method desc) :
    Jvm.stepInstr serHooks (.invokevirtual cls method desc) ⟨pc, val :: enc :: recv :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, rest, locs, subEnd.jvmHeap, subEnd.heap⟩) := by
  dsimp only [Jvm.stepInstr]
  rw [hgen, hcall]

private theorem stepInstr_checkcast_floatArray
    {pc : Nat} {arrAddr : Nat} {elems : Array Float32} {rest : List SerVal}
    {locs : Nat → SerVal} {jh : Jvm.JvmHeap SerExt} {hp : SerHeap}
    (hget : jh.get? arrAddr = some (.floatArray elems)) :
    Jvm.stepInstr serBaseHooks (.checkcast "[F") ⟨pc, .heapRef arrAddr :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef arrAddr :: rest, locs, jh, hp⟩) := by
  have hchk : jh.checkInstanceOf "[F" arrAddr serBaseHooks.isSubtypeOf = true := by
    unfold Jvm.JvmHeap.checkInstanceOf
    rw [hget]
    rfl
  dsimp only [Jvm.stepInstr, Jvm.evalCheckCast, Jvm.JvmHeap.checkCast]
  rw [hchk]
  rfl

private theorem stepInstr_floatArraySerialize
    {pc : Nat} {arrAddr encId : Nat} {elems : Array Float32} {rest : List SerVal}
    {locs : Nat → SerVal} {jh : Jvm.JvmHeap SerExt} {hp : SerHeap}
    (hget : jh.get? arrAddr = some (.floatArray elems)) :
    Jvm.stepInstr serBaseHooks
      (.invokeinterface "kotlinx/serialization/KSerializer" "serialize"
        "(Lkotlinx/serialization/encoding/Encoder;Ljava/lang/Object;)V")
      ⟨pc, .heapRef arrAddr :: .ext (.encoder encId) :: .ext .floatArraySerializer :: rest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, rest, locs, jh, { hp with encodedFloatArray := some elems }⟩) := by
  change (match jh.get? arrAddr with
    | some (.floatArray elems') =>
      Sum.inl (some (⟨pc + 1, rest, locs, jh, { hp with encodedFloatArray := some elems' }⟩ : SerState))
    | _ => Sum.inr none) = _
  rw [hget]

/-! ### ClosedFloatRangeSerializer -/

theorem closedFloatRangeSerializer_init_equiv (self : SerVal) (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 10 ClosedFloatRangeSerializer_init_prog
        (initSerJvmState [(0, self)] hp jh) = some (.unit, endSt) ∧
      endSt.heap = hp ∧ endSt.jvmHeap = jh := by
  exact ⟨_, rfl, rfl, rfl⟩

theorem closedFloatRangeSerializer_clinit_equiv (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
    (hclean : HasPrimitiveKindLongClean jh) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 20 ClosedFloatRangeSerializer_clinit_prog
        (initSerJvmState [] hp jh) = some (.unit, endSt) ∧
      endSt.jvmHeap.getStatic? "com/alexvanyo/composelife/serialization/ClosedFloatRangeSerializer" "descriptor" =
        some (.ext (.serialDescriptor "kotlin.ranges.ClosedFloatRange" (some "LONG"))) := by
  let jh1 := (jh.alloc (.instance "com/alexvanyo/composelife/serialization/ClosedFloatRangeSerializer" [])).2
  let jh2 := jh1.setStatic "com/alexvanyo/composelife/serialization/ClosedFloatRangeSerializer" "INSTANCE" (.heapRef jh.objects.size)
  let jh3 := jh2.setStatic "com/alexvanyo/composelife/serialization/ClosedFloatRangeSerializer" "descriptor"
    (.ext (.serialDescriptor "kotlin.ranges.ClosedFloatRange" (some "LONG")))
  have hpk : jh2.getStatic? "kotlinx/serialization/descriptors/PrimitiveKind$LONG" "INSTANCE" = none := by
    rw [jvmHeap_getStatic_setStatic_ne (hne := by decide)]
    exact hclean
  refine ⟨{ initSerJvmState [] hp jh with pc := 9, jvmHeap := jh3 }, ?_, jvmHeap_getStatic_setStatic_same _ _ _ _⟩
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 1, stack := [.heapRef jh.objects.size], jvmHeap := jh1 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 2, stack := [.heapRef jh.objects.size, .heapRef jh.objects.size], jvmHeap := jh1 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 3, stack := [.heapRef jh.objects.size], jvmHeap := jh1 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 4, stack := [], jvmHeap := jh2 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 5, stack := [.str "kotlin.ranges.ClosedFloatRange"], jvmHeap := jh2 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 6, stack := [.ext .primitiveKindLong, .str "kotlin.ranges.ClosedFloatRange"], jvmHeap := jh2 }) rfl rfl]
  · rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 7, stack := [.ext .primitiveKindLong, .str "kotlin.ranges.ClosedFloatRange"], jvmHeap := jh2 }) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 8, stack := [.ext (.serialDescriptor "kotlin.ranges.ClosedFloatRange" (some "LONG"))], jvmHeap := jh2 }) rfl rfl stepInstr_primitiveSerialDescriptor]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 9, stack := [], jvmHeap := jh3 }) rfl rfl rfl]
    exact runJvmRes_step_inr rfl rfl rfl
  · dsimp only [Jvm.stepInstr, serBaseHooks]; rw [hpk]; rfl

theorem closedFloatRangeSerializer_getDescriptor_equiv
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) (d : SerVal)
    (hdesc : jh.getStatic? "com/alexvanyo/composelife/serialization/ClosedFloatRangeSerializer" "descriptor" = some d) :
    Jvm.runJvm serBaseHooks 10 ClosedFloatRangeSerializer_getDescriptor_prog
      (initSerJvmState [] hp jh) = some d := by
  rw [runJvm_step_inl (st' := { initSerJvmState [] hp jh with pc := 1, stack := [d] }) rfl rfl]
  · exact runJvm_step_inr rfl rfl rfl
  · dsimp only [Jvm.stepInstr, initSerJvmState, Jvm.initJvmState, serBaseHooks]; rw [hdesc]

theorem closedFloatRangeSerializer_deserialize_equiv
    (self : SerVal) (decId : Nat) (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 80 ClosedFloatRangeSerializer_deserialize_prog
        (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh) =
        some (.ext (.closedFloatRange (deserializeClosedFloatRange hp.decodedLong)), endSt) ∧
      endSt.heap = hp ∧ endSt.jvmHeap = jh := by
  have heq :
      { start := Float32.ofBits (UInt64.ofBitVec (hp.decodedLong.toBitVec.sshiftRight ((32 : UInt32) &&& 63).toNat)).toUInt32,
        endInclusive := unpackFloat2 hp.decodedLong } =
      deserializeClosedFloatRange hp.decodedLong := by
    rw [jvm_lshr32_eq_unpackInt1]; rfl
  rw [← heq]
  exact ⟨_, rfl, rfl, rfl⟩

theorem closedFloatRangeSerializer_serialize_equiv
    (self : SerVal) (encId : Nat) (r : ClosedFloatRangeModel)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 80 ClosedFloatRangeSerializer_serialize_prog
        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.closedFloatRange r))] hp jh) =
        some (.unit, endSt) ∧
      endSt.heap.encodedLong = some (serializeClosedFloatRange r) := by
  refine ⟨_, rfl, ?_⟩
  change some ((UInt64.ofBitVec (r.start.toBits.toBitVec.signExtend 64) <<< ((32 : UInt32) &&& 63).toUInt64) |||
    (UInt64.ofBitVec (r.endInclusive.toBits.toBitVec.signExtend 64) &&& 4294967295)) =
    some (serializeClosedFloatRange r)
  rw [jvm_i2l_pack_eq_packFloats]
  rfl

theorem closedFloatRangeSerializer_deserialize_1_equiv
    (self : SerVal) (decId : Nat) (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    Jvm.runJvm serHooks 20 ClosedFloatRangeSerializer_deserialize_1_prog
      (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh) =
      some (.ext (.closedFloatRange (deserializeClosedFloatRange hp.decodedLong))) := by
  rcases closedFloatRangeSerializer_deserialize_equiv self decId hp jh with ⟨subEnd, hsubRun, _, _⟩
  rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 1, stack := [self] }) rfl rfl rfl]
  rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 2, stack := [.ext (.decoder decId), self] }) rfl rfl rfl]
  rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 3, stack := [.ext (.closedFloatRange (deserializeClosedFloatRange hp.decodedLong))], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }) rfl rfl]
  · exact runJvm_step_inr rfl rfl rfl
  · refine stepInstr_serHooks_virt_ret ?_ (by simp [Jvm.stepInvokeVirtualGeneric])
    change (match Jvm.runJvmRes serBaseHooks 80 ClosedFloatRangeSerializer_deserialize_prog
        (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh) with
      | some (retVal, endSt) =>
        Sum.inl (some { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 2 + 1, stack := [retVal], heap := endSt.heap, jvmHeap := endSt.jvmHeap })
      | none => Sum.inr none) = _
    rw [hsubRun]

theorem closedFloatRangeSerializer_serialize_1_equiv
    (self : SerVal) (encId : Nat) (r : ClosedFloatRangeModel)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serHooks 20 ClosedFloatRangeSerializer_serialize_1_prog
        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.closedFloatRange r))] hp jh) =
        some (.unit, endSt) ∧
      endSt.heap.encodedLong = some (serializeClosedFloatRange r) := by
  rcases closedFloatRangeSerializer_serialize_equiv self encId r hp jh with ⟨subEnd, hsubRun, henc⟩
  refine ⟨{ initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.closedFloatRange r))] hp jh with pc := 5, stack := [], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }, ?_, henc⟩
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.closedFloatRange r))] hp jh with pc := 1, stack := [self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.closedFloatRange r))] hp jh with pc := 2, stack := [.ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.closedFloatRange r))] hp jh with pc := 3, stack := [.ext (.closedFloatRange r), .ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.closedFloatRange r))] hp jh with pc := 4, stack := [.ext (.closedFloatRange r), .ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.closedFloatRange r))] hp jh with pc := 5, stack := [], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }) rfl rfl]
  · exact runJvmRes_step_inr rfl rfl rfl
  · refine stepInstr_serHooks_virt_void ?_ (by simp [Jvm.stepInvokeVirtualGeneric])
    change (match Jvm.runJvmRes serBaseHooks 80 ClosedFloatRangeSerializer_serialize_prog
        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.closedFloatRange r))] hp jh) with
      | some (_, endSt) =>
        Sum.inl (some { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.closedFloatRange r))] hp jh with pc := 4 + 1, stack := [], heap := endSt.heap, jvmHeap := endSt.jvmHeap })
      | none => Sum.inr none) = _
    rw [hsubRun]

/-! ### IntOffsetSerializer -/

theorem intOffsetSerializer_init_equiv (self : SerVal) (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 10 IntOffsetSerializer_init_prog
        (initSerJvmState [(0, self)] hp jh) = some (.unit, endSt) ∧
      endSt.heap = hp ∧ endSt.jvmHeap = jh := by
  exact ⟨_, rfl, rfl, rfl⟩

theorem intOffsetSerializer_clinit_equiv (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
    (hclean : HasPrimitiveKindLongClean jh) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 20 IntOffsetSerializer_clinit_prog
        (initSerJvmState [] hp jh) = some (.unit, endSt) ∧
      endSt.jvmHeap.getStatic? "com/alexvanyo/composelife/serialization/IntOffsetSerializer" "descriptor" =
        some (.ext (.serialDescriptor "androidx.compose.ui.unit.IntOffset" (some "LONG"))) := by
  let jh1 := (jh.alloc (.instance "com/alexvanyo/composelife/serialization/IntOffsetSerializer" [])).2
  let jh2 := jh1.setStatic "com/alexvanyo/composelife/serialization/IntOffsetSerializer" "INSTANCE" (.heapRef jh.objects.size)
  let jh3 := jh2.setStatic "com/alexvanyo/composelife/serialization/IntOffsetSerializer" "descriptor"
    (.ext (.serialDescriptor "androidx.compose.ui.unit.IntOffset" (some "LONG")))
  have hpk : jh2.getStatic? "kotlinx/serialization/descriptors/PrimitiveKind$LONG" "INSTANCE" = none := by
    rw [jvmHeap_getStatic_setStatic_ne (hne := by decide)]
    exact hclean
  refine ⟨{ initSerJvmState [] hp jh with pc := 9, jvmHeap := jh3 }, ?_, jvmHeap_getStatic_setStatic_same _ _ _ _⟩
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 1, stack := [.heapRef jh.objects.size], jvmHeap := jh1 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 2, stack := [.heapRef jh.objects.size, .heapRef jh.objects.size], jvmHeap := jh1 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 3, stack := [.heapRef jh.objects.size], jvmHeap := jh1 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 4, stack := [], jvmHeap := jh2 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 5, stack := [.str "androidx.compose.ui.unit.IntOffset"], jvmHeap := jh2 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 6, stack := [.ext .primitiveKindLong, .str "androidx.compose.ui.unit.IntOffset"], jvmHeap := jh2 }) rfl rfl]
  · rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 7, stack := [.ext .primitiveKindLong, .str "androidx.compose.ui.unit.IntOffset"], jvmHeap := jh2 }) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 8, stack := [.ext (.serialDescriptor "androidx.compose.ui.unit.IntOffset" (some "LONG"))], jvmHeap := jh2 }) rfl rfl stepInstr_primitiveSerialDescriptor]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 9, stack := [], jvmHeap := jh3 }) rfl rfl rfl]
    exact runJvmRes_step_inr rfl rfl rfl
  · dsimp only [Jvm.stepInstr, serBaseHooks]; rw [hpk]; rfl

theorem intOffsetSerializer_getDescriptor_equiv
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) (d : SerVal)
    (hdesc : jh.getStatic? "com/alexvanyo/composelife/serialization/IntOffsetSerializer" "descriptor" = some d) :
    Jvm.runJvm serBaseHooks 10 IntOffsetSerializer_getDescriptor_prog
      (initSerJvmState [] hp jh) = some d := by
  rw [runJvm_step_inl (st' := { initSerJvmState [] hp jh with pc := 1, stack := [d] }) rfl rfl]
  · exact runJvm_step_inr rfl rfl rfl
  · dsimp only [Jvm.stepInstr, initSerJvmState, Jvm.initJvmState, serBaseHooks]; rw [hdesc]

theorem intOffsetSerializer_deserialize_equiv
    (self : SerVal) (decId : Nat) (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 80 IntOffsetSerializer_deserialize_prog
        (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh) =
        some (.i64 hp.decodedLong, endSt) ∧
      endSt.heap = hp ∧ endSt.jvmHeap = jh := by
  have heq :
      ((UInt64.ofBitVec
          ((UInt64.ofBitVec (hp.decodedLong.toBitVec.sshiftRight ((32 : UInt32) &&& 63).toNat)).toUInt32.toBitVec.signExtend 64) <<<
          ((32 : UInt32) &&& 63).toUInt64) |||
        (UInt64.ofBitVec ((hp.decodedLong &&& 4294967295).toUInt32.toBitVec.signExtend 64) &&& 4294967295)) =
      hp.decodedLong := by
    rw [jvm_lshr32_eq_unpackInt1]
    have hlo : (hp.decodedLong &&& 4294967295).toUInt32 = (unpackInt2 hp.decodedLong).toUInt32 := rfl
    rw [hlo, jvm_i2l_pack_eq_packInts, unpack_packInts_roundtrip hp.decodedLong]
  rw [← heq]
  exact ⟨_, rfl, rfl, rfl⟩

theorem intOffsetSerializer_serialize_equiv
    (self : SerVal) (encId : Nat) (v : UInt64)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 80 IntOffsetSerializer_serialize_prog
        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .i64 v)] hp jh) =
        some (.unit, endSt) ∧
      endSt.heap.encodedLong = some v := by
  refine ⟨_, rfl, ?_⟩
  change some ((UInt64.ofBitVec ((unpackInt1 v).toUInt32.toBitVec.signExtend 64) <<< ((32 : UInt32) &&& 63).toUInt64) |||
    (UInt64.ofBitVec ((unpackInt2 v).toUInt32.toBitVec.signExtend 64) &&& 4294967295)) = some v
  rw [jvm_i2l_pack_eq_packInts, unpack_packInts_roundtrip v]

theorem intOffsetSerializer_deserialize_1_equiv
    (self : SerVal) (decId : Nat) (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    Jvm.runJvm serHooks 20 IntOffsetSerializer_deserialize_1_prog
      (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh) =
      some (.ext (.boxedIntOffset hp.decodedLong)) := by
  rcases intOffsetSerializer_deserialize_equiv self decId hp jh with ⟨subEnd, hsubRun, _, _⟩
  rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 1, stack := [self] }) rfl rfl rfl]
  rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 2, stack := [.ext (.decoder decId), self] }) rfl rfl rfl]
  rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 3, stack := [.i64 hp.decodedLong], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }) rfl rfl]
  · rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 4, stack := [.ext (.boxedIntOffset hp.decodedLong)], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }) rfl rfl rfl]
    exact runJvm_step_inr rfl rfl rfl
  · refine stepInstr_serHooks_virt_ret ?_ (by simp [Jvm.stepInvokeVirtualGeneric])
    change (match Jvm.runJvmRes serBaseHooks 80 IntOffsetSerializer_deserialize_prog
        (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh) with
      | some (retVal, endSt) =>
        Sum.inl (some { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 2 + 1, stack := [retVal], heap := endSt.heap, jvmHeap := endSt.jvmHeap })
      | none => Sum.inr none) = _
    rw [hsubRun]

theorem intOffsetSerializer_serialize_1_equiv
    (self : SerVal) (encId : Nat) (v : UInt64)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serHooks 20 IntOffsetSerializer_serialize_1_prog
        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedIntOffset v))] hp jh) =
        some (.unit, endSt) ∧
      endSt.heap.encodedLong = some v := by
  rcases intOffsetSerializer_serialize_equiv self encId v hp jh with ⟨subEnd, hsubRun, henc⟩
  refine ⟨{ initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedIntOffset v))] hp jh with pc := 6, stack := [], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }, ?_, henc⟩
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedIntOffset v))] hp jh with pc := 1, stack := [self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedIntOffset v))] hp jh with pc := 2, stack := [.ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedIntOffset v))] hp jh with pc := 3, stack := [.ext (.boxedIntOffset v), .ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedIntOffset v))] hp jh with pc := 4, stack := [.ext (.boxedIntOffset v), .ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedIntOffset v))] hp jh with pc := 5, stack := [.i64 v, .ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedIntOffset v))] hp jh with pc := 6, stack := [], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }) rfl rfl]
  · exact runJvmRes_step_inr rfl rfl rfl
  · refine stepInstr_serHooks_virt_void ?_ (by simp [Jvm.stepInvokeVirtualGeneric])
    change (match Jvm.runJvmRes serBaseHooks 80 IntOffsetSerializer_serialize_prog
        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .i64 v)] hp jh) with
      | some (_, endSt) =>
        Sum.inl (some { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedIntOffset v))] hp jh with pc := 5 + 1, stack := [], heap := endSt.heap, jvmHeap := endSt.jvmHeap })
      | none => Sum.inr none) = _
    rw [hsubRun]

/-! ### OffsetSerializer -/

theorem offsetSerializer_init_equiv (self : SerVal) (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 10 OffsetSerializer_init_prog
        (initSerJvmState [(0, self)] hp jh) = some (.unit, endSt) ∧
      endSt.heap = hp ∧ endSt.jvmHeap = jh := by
  exact ⟨_, rfl, rfl, rfl⟩

theorem offsetSerializer_clinit_equiv (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
    (hclean : HasPrimitiveKindLongClean jh) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 20 OffsetSerializer_clinit_prog
        (initSerJvmState [] hp jh) = some (.unit, endSt) ∧
      endSt.jvmHeap.getStatic? "com/alexvanyo/composelife/serialization/OffsetSerializer" "descriptor" =
        some (.ext (.serialDescriptor "androidx.compose.ui.unit.Offset" (some "LONG"))) := by
  let jh1 := (jh.alloc (.instance "com/alexvanyo/composelife/serialization/OffsetSerializer" [])).2
  let jh2 := jh1.setStatic "com/alexvanyo/composelife/serialization/OffsetSerializer" "INSTANCE" (.heapRef jh.objects.size)
  let jh3 := jh2.setStatic "com/alexvanyo/composelife/serialization/OffsetSerializer" "descriptor"
    (.ext (.serialDescriptor "androidx.compose.ui.unit.Offset" (some "LONG")))
  have hpk : jh2.getStatic? "kotlinx/serialization/descriptors/PrimitiveKind$LONG" "INSTANCE" = none := by
    rw [jvmHeap_getStatic_setStatic_ne (hne := by decide)]
    exact hclean
  refine ⟨{ initSerJvmState [] hp jh with pc := 9, jvmHeap := jh3 }, ?_, jvmHeap_getStatic_setStatic_same _ _ _ _⟩
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 1, stack := [.heapRef jh.objects.size], jvmHeap := jh1 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 2, stack := [.heapRef jh.objects.size, .heapRef jh.objects.size], jvmHeap := jh1 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 3, stack := [.heapRef jh.objects.size], jvmHeap := jh1 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 4, stack := [], jvmHeap := jh2 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 5, stack := [.str "androidx.compose.ui.unit.Offset"], jvmHeap := jh2 }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 6, stack := [.ext .primitiveKindLong, .str "androidx.compose.ui.unit.Offset"], jvmHeap := jh2 }) rfl rfl]
  · rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 7, stack := [.ext .primitiveKindLong, .str "androidx.compose.ui.unit.Offset"], jvmHeap := jh2 }) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 8, stack := [.ext (.serialDescriptor "androidx.compose.ui.unit.Offset" (some "LONG"))], jvmHeap := jh2 }) rfl rfl stepInstr_primitiveSerialDescriptor]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 9, stack := [], jvmHeap := jh3 }) rfl rfl rfl]
    exact runJvmRes_step_inr rfl rfl rfl
  · dsimp only [Jvm.stepInstr, serBaseHooks]; rw [hpk]; rfl

theorem offsetSerializer_getDescriptor_equiv
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) (d : SerVal)
    (hdesc : jh.getStatic? "com/alexvanyo/composelife/serialization/OffsetSerializer" "descriptor" = some d) :
    Jvm.runJvm serBaseHooks 10 OffsetSerializer_getDescriptor_prog
      (initSerJvmState [] hp jh) = some d := by
  rw [runJvm_step_inl (st' := { initSerJvmState [] hp jh with pc := 1, stack := [d] }) rfl rfl]
  · exact runJvm_step_inr rfl rfl rfl
  · dsimp only [Jvm.stepInstr, initSerJvmState, Jvm.initJvmState, serBaseHooks]; rw [hdesc]

theorem offsetSerializer_deserialize_equiv
    (self : SerVal) (decId : Nat) (x y : Float32) (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
    (hdec : hp.decodedLong = packFloats x y) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 80 OffsetSerializer_deserialize_prog
        (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh) =
        some (.i64 (packFloats x y), endSt) ∧
      endSt.heap = hp ∧ endSt.jvmHeap = jh := by
  have hrt := packFloats_unpack_roundtrip x y
  have heq :
      ((UInt64.ofBitVec
          ((Float32.ofBits (UInt64.ofBitVec (hp.decodedLong.toBitVec.sshiftRight ((32 : UInt32) &&& 63).toNat)).toUInt32).toBits.toBitVec.signExtend 64) <<<
          ((32 : UInt32) &&& 63).toUInt64) |||
        (UInt64.ofBitVec ((unpackFloat2 hp.decodedLong).toBits.toBitVec.signExtend 64) &&& 4294967295)) =
      packFloats x y := by
    rw [jvm_lshr32_eq_unpackInt1, jvm_i2l_pack_eq_packFloats, hdec]
    change packFloats (unpackFloat1 (packFloats x y)) (unpackFloat2 (packFloats x y)) = _
    rw [hrt.1, hrt.2]
  rw [← heq]
  exact ⟨_, rfl, rfl, rfl⟩

theorem offsetSerializer_serialize_equiv
    (self : SerVal) (encId : Nat) (x y : Float32)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 80 OffsetSerializer_serialize_prog
        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .i64 (packFloats x y))] hp jh) =
        some (.unit, endSt) ∧
      endSt.heap.encodedLong = some (packFloats x y) := by
  have hrt := packFloats_unpack_roundtrip x y
  refine ⟨_, rfl, ?_⟩
  change some ((UInt64.ofBitVec
      ((Float32.ofBits (UInt64.ofBitVec ((packFloats x y).toBitVec.sshiftRight ((32 : UInt32) &&& 63).toNat)).toUInt32).toBits.toBitVec.signExtend 64) <<<
      ((32 : UInt32) &&& 63).toUInt64) |||
    (UInt64.ofBitVec ((unpackFloat2 (packFloats x y)).toBits.toBitVec.signExtend 64) &&& 4294967295)) =
    some (packFloats x y)
  rw [jvm_lshr32_eq_unpackInt1, jvm_i2l_pack_eq_packFloats]
  change some (packFloats (unpackFloat1 (packFloats x y)) (unpackFloat2 (packFloats x y))) = _
  rw [hrt.1, hrt.2]

theorem offsetSerializer_deserialize_1_equiv
    (self : SerVal) (decId : Nat) (x y : Float32) (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
    (hdec : hp.decodedLong = packFloats x y) :
    Jvm.runJvm serHooks 20 OffsetSerializer_deserialize_1_prog
      (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh) =
      some (.ext (.boxedOffset (packFloats x y))) := by
  rcases offsetSerializer_deserialize_equiv self decId x y hp jh hdec with ⟨subEnd, hsubRun, _, _⟩
  rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 1, stack := [self] }) rfl rfl rfl]
  rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 2, stack := [.ext (.decoder decId), self] }) rfl rfl rfl]
  rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 3, stack := [.i64 (packFloats x y)], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }) rfl rfl]
  · rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 4, stack := [.ext (.boxedOffset (packFloats x y))], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }) rfl rfl rfl]
    exact runJvm_step_inr rfl rfl rfl
  · refine stepInstr_serHooks_virt_ret ?_ (by simp [Jvm.stepInvokeVirtualGeneric])
    change (match Jvm.runJvmRes serBaseHooks 80 OffsetSerializer_deserialize_prog
        (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh) with
      | some (retVal, endSt) =>
        Sum.inl (some { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 2 + 1, stack := [retVal], heap := endSt.heap, jvmHeap := endSt.jvmHeap })
      | none => Sum.inr none) = _
    rw [hsubRun]

theorem offsetSerializer_serialize_1_equiv
    (self : SerVal) (encId : Nat) (x y : Float32)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serHooks 20 OffsetSerializer_serialize_1_prog
        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedOffset (packFloats x y)))] hp jh) =
        some (.unit, endSt) ∧
      endSt.heap.encodedLong = some (packFloats x y) := by
  rcases offsetSerializer_serialize_equiv self encId x y hp jh with ⟨subEnd, hsubRun, henc⟩
  refine ⟨{ initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedOffset (packFloats x y)))] hp jh with pc := 6, stack := [], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }, ?_, henc⟩
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedOffset (packFloats x y)))] hp jh with pc := 1, stack := [self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedOffset (packFloats x y)))] hp jh with pc := 2, stack := [.ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedOffset (packFloats x y)))] hp jh with pc := 3, stack := [.ext (.boxedOffset (packFloats x y)), .ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedOffset (packFloats x y)))] hp jh with pc := 4, stack := [.ext (.boxedOffset (packFloats x y)), .ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedOffset (packFloats x y)))] hp jh with pc := 5, stack := [.i64 (packFloats x y), .ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedOffset (packFloats x y)))] hp jh with pc := 6, stack := [], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }) rfl rfl]
  · exact runJvmRes_step_inr rfl rfl rfl
  · refine stepInstr_serHooks_virt_void ?_ (by simp [Jvm.stepInvokeVirtualGeneric])
    change (match Jvm.runJvmRes serBaseHooks 80 OffsetSerializer_serialize_prog
        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .i64 (packFloats x y))] hp jh) with
      | some (_, endSt) =>
        Sum.inl (some { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.boxedOffset (packFloats x y)))] hp jh with pc := 5 + 1, stack := [], heap := endSt.heap, jvmHeap := endSt.jvmHeap })
      | none => Sum.inr none) = _
    rw [hsubRun]

/-! ### RectSerializer -/

def HasRectSerializerStatics (jh : Jvm.JvmHeap SerExt) : Prop :=
  jh.getStatic? "com/alexvanyo/composelife/serialization/RectSerializer" "delegateSerializer" =
    some (.ext .floatArraySerializer) ∧
  jh.getStatic? "com/alexvanyo/composelife/serialization/RectSerializer" "descriptor" =
    some (.ext (.serialDescriptor "androidx.compose.ui.geometry.Rect" (some "kotlin.FloatArray")))

theorem rectSerializer_init_equiv (self : SerVal) (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 10 RectSerializer_init_prog
        (initSerJvmState [(0, self)] hp jh) = some (.unit, endSt) ∧
      endSt.heap = hp ∧ endSt.jvmHeap = jh := by
  exact ⟨_, rfl, rfl, rfl⟩

theorem rectSerializer_getDescriptor_annotations_equiv (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    Jvm.runJvm serBaseHooks 5 RectSerializer_getDescriptor_annotations_prog
      (initSerJvmState [] hp jh) = some .unit := by
  rfl

theorem rectSerializer_clinit_equiv (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 20 RectSerializer_clinit_prog
        (initSerJvmState [] hp jh) = some (.unit, endSt) ∧
      HasRectSerializerStatics endSt.jvmHeap := by
  let jh1 := (jh.alloc (.instance "com/alexvanyo/composelife/serialization/RectSerializer" [])).2
  let jh2 := jh1.setStatic "com/alexvanyo/composelife/serialization/RectSerializer" "INSTANCE" (.heapRef jh.objects.size)
  let jh3 := jh2.setStatic "com/alexvanyo/composelife/serialization/RectSerializer" "delegateSerializer" (.ext .floatArraySerializer)
  let jh4 := jh3.setStatic "com/alexvanyo/composelife/serialization/RectSerializer" "descriptor"
    (.ext (.serialDescriptor "androidx.compose.ui.geometry.Rect" (some "kotlin.FloatArray")))
  have hdel : jh3.getStatic? "com/alexvanyo/composelife/serialization/RectSerializer" "delegateSerializer" =
      some (.ext .floatArraySerializer) :=
    jvmHeap_getStatic_setStatic_same _ _ _ _
  refine ⟨{ initSerJvmState [] hp jh with pc := 11, jvmHeap := jh4 }, ?_, ?_, ?_⟩
  · rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 1, stack := [.heapRef jh.objects.size], jvmHeap := jh1 }) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 2, stack := [.heapRef jh.objects.size, .heapRef jh.objects.size], jvmHeap := jh1 }) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 3, stack := [.heapRef jh.objects.size], jvmHeap := jh1 }) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 4, stack := [], jvmHeap := jh2 }) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 5, stack := [.ext .floatArraySerializer], jvmHeap := jh2 }) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 6, stack := [], jvmHeap := jh3 }) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 7, stack := [.str "androidx.compose.ui.geometry.Rect"], jvmHeap := jh3 }) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 8, stack := [.ext .floatArraySerializer, .str "androidx.compose.ui.geometry.Rect"], jvmHeap := jh3 }) rfl rfl]
    · rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 9, stack := [.ext (.serialDescriptor "kotlin.FloatArray" none), .str "androidx.compose.ui.geometry.Rect"], jvmHeap := jh3 }) rfl rfl rfl]
      rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 10, stack := [.ext (.serialDescriptor "androidx.compose.ui.geometry.Rect" (some "kotlin.FloatArray"))], jvmHeap := jh3 }) rfl rfl stepInstr_serialDescriptor]
      rw [runJvmRes_step_inl (st' := { initSerJvmState [] hp jh with pc := 11, stack := [], jvmHeap := jh4 }) rfl rfl rfl]
      exact runJvmRes_step_inr rfl rfl rfl
    · dsimp only [Jvm.stepInstr, serBaseHooks]; rw [hdel]
  · rw [jvmHeap_getStatic_setStatic_ne (hne := by decide)]
    exact hdel
  · exact jvmHeap_getStatic_setStatic_same _ _ _ _

theorem rectSerializer_getDescriptor_equiv
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) (hstat : HasRectSerializerStatics jh) :
    Jvm.runJvm serBaseHooks 10 RectSerializer_getDescriptor_prog
      (initSerJvmState [] hp jh) =
      some (.ext (.serialDescriptor "androidx.compose.ui.geometry.Rect" (some "kotlin.FloatArray"))) := by
  rcases hstat with ⟨_, hdesc⟩
  rw [runJvm_step_inl (st' := { initSerJvmState [] hp jh with pc := 1, stack := [.ext (.serialDescriptor "androidx.compose.ui.geometry.Rect" (some "kotlin.FloatArray"))] }) rfl rfl]
  · exact runJvm_step_inr rfl rfl rfl
  · dsimp only [Jvm.stepInstr, initSerJvmState, Jvm.initJvmState, serBaseHooks]; rw [hdesc]

theorem rectSerializer_deserialize_equiv
    (self : SerVal) (decId : Nat) (l t r b : Float32)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
    (hstat : HasRectSerializerStatics jh)
    (harr : hp.decodedFloatArray = #[l, t, r, b]) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 80 RectSerializer_deserialize_prog
        (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh) =
        some (.ext (.rect { left := l, top := t, right := r, bottom := b }), endSt) := by
  rcases hstat with ⟨hdel, _⟩
  let arrAddr := jh.objects.size
  let jh1 := (jh.alloc (.floatArray hp.decodedFloatArray)).2
  have hget1 : jh1.get? arrAddr = some (.floatArray #[l, t, r, b]) := by
    rw [← harr]; exact jvmHeap_get_alloc jh (.floatArray hp.decodedFloatArray)
  let rectAddr := jh1.objects.size
  let jh2 := (jh1.alloc (.instance "androidx/compose/ui/geometry/Rect" [])).2
  have hget2 : jh2.get? arrAddr = some (.floatArray #[l, t, r, b]) := by
    have hlt : arrAddr < jh1.objects.size := jvmHeap_size_alloc jh (.floatArray hp.decodedFloatArray)
    have hne : arrAddr ≠ jh1.objects.size := Nat.ne_of_lt hlt
    simp only [jh2, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?, Array.getElem?_push, hne, ↓reduceIte]
    exact hget1
  let locs0 := (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh).locals
  let locs1 := Jvm.setLocal locs0 2 (.heapRef arrAddr)
  refine ⟨⟨23, [.ext (.rect { left := l, top := t, right := r, bottom := b })], locs1, jh2, hp⟩, ?_⟩
  rw [runJvmRes_step_inl (st' := ⟨1, [.ext (.decoder decId)], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨2, [.str "decoder", .ext (.decoder decId)], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨3, [], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨4, [.ext .floatArraySerializer], locs0, jh, hp⟩) rfl rfl]
  · rw [runJvmRes_step_inl (st' := ⟨5, [.ext (.decoder decId), .ext .floatArraySerializer], locs0, jh, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨6, [.heapRef arrAddr], locs0, jh1, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨7, [.heapRef arrAddr], locs0, jh1, hp⟩) rfl rfl (stepInstr_checkcast_floatArray hget1)]
    rw [runJvmRes_step_inl (st' := ⟨8, [], locs1, jh1, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨9, [.heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨10, [.heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨11, [.heapRef arrAddr, .heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨12, [.i32 0, .heapRef arrAddr, .heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨13, [.f32 l, .heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl (Jvm.stepInstr_faload serBaseHooks hget2 rfl (by simp))]
    rw [runJvmRes_step_inl (st' := ⟨14, [.heapRef arrAddr, .f32 l, .heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨15, [.i32 1, .heapRef arrAddr, .f32 l, .heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨16, [.f32 t, .f32 l, .heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl (Jvm.stepInstr_faload serBaseHooks hget2 rfl (by simp))]
    rw [runJvmRes_step_inl (st' := ⟨17, [.heapRef arrAddr, .f32 t, .f32 l, .heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨18, [.i32 2, .heapRef arrAddr, .f32 t, .f32 l, .heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨19, [.f32 r, .f32 t, .f32 l, .heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl (Jvm.stepInstr_faload serBaseHooks hget2 rfl (by simp))]
    rw [runJvmRes_step_inl (st' := ⟨20, [.heapRef arrAddr, .f32 r, .f32 t, .f32 l, .heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨21, [.i32 3, .heapRef arrAddr, .f32 r, .f32 t, .f32 l, .heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨22, [.f32 b, .f32 r, .f32 t, .f32 l, .heapRef rectAddr, .heapRef rectAddr], locs1, jh2, hp⟩) rfl rfl (Jvm.stepInstr_faload serBaseHooks hget2 rfl (by simp))]
    rw [runJvmRes_step_inl (st' := ⟨23, [.ext (.rect { left := l, top := t, right := r, bottom := b })], locs1, jh2, hp⟩) rfl rfl]
    · exact runJvmRes_step_inr rfl rfl rfl
    · dsimp only [Jvm.stepInstr, Jvm.stepInvokeSpecialGeneric, serBaseHooks, Jvm.JvmVal.asF32?]; simp
  · dsimp only [Jvm.stepInstr, serBaseHooks]; rw [hdel]

theorem rectSerializer_serialize_equiv
    (self : SerVal) (encId : Nat) (r : RectModel)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
    (hstat : HasRectSerializerStatics jh) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 80 RectSerializer_serialize_prog
        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.rect r))] hp jh) =
        some (.unit, endSt) ∧
      endSt.heap.encodedFloatArray = some (serializeRect r) := by
  rcases hstat with ⟨hdel, _⟩
  let arrAddr := jh.objects.size
  let jh1 := (jh.alloc (.floatArray (Array.replicate 4 (0.0 : Float32)))).2
  have hlt1 : arrAddr < jh1.objects.size := jvmHeap_size_alloc jh _
  have hget1 : jh1.get? arrAddr = some (.floatArray #[0.0, 0.0, 0.0, 0.0]) :=
    jvmHeap_get_alloc jh _
  let jh2 := jh1.set arrAddr (.floatArray #[r.left, 0.0, 0.0, 0.0])
  have hlt2 : arrAddr < jh2.objects.size := by rw [jvmHeap_size_set]; exact hlt1
  have hget2 : jh2.get? arrAddr = some (.floatArray #[r.left, 0.0, 0.0, 0.0]) :=
    jvmHeap_get_set_same _ _ _ hlt1
  let jh3 := jh2.set arrAddr (.floatArray #[r.left, r.top, 0.0, 0.0])
  have hlt3 : arrAddr < jh3.objects.size := by rw [jvmHeap_size_set]; exact hlt2
  have hget3 : jh3.get? arrAddr = some (.floatArray #[r.left, r.top, 0.0, 0.0]) :=
    jvmHeap_get_set_same _ _ _ hlt2
  let jh4 := jh3.set arrAddr (.floatArray #[r.left, r.top, r.right, 0.0])
  have hlt4 : arrAddr < jh4.objects.size := by rw [jvmHeap_size_set]; exact hlt3
  have hget4 : jh4.get? arrAddr = some (.floatArray #[r.left, r.top, r.right, 0.0]) :=
    jvmHeap_get_set_same _ _ _ hlt3
  let jh5 := jh4.set arrAddr (.floatArray #[r.left, r.top, r.right, r.bottom])
  have hget5 : jh5.get? arrAddr = some (.floatArray #[r.left, r.top, r.right, r.bottom]) :=
    jvmHeap_get_set_same _ _ _ hlt4
  let locs0 := (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.rect r))] hp jh).locals
  let locs1 := Jvm.setLocal locs0 3 (.heapRef arrAddr)
  have hstore1 :
      Jvm.stepInstr serBaseHooks .fastore
        ⟨15, [.f32 r.left, .i32 0, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh1, hp⟩ =
        .inl (some ⟨16, [.ext (.encoder encId), .ext .floatArraySerializer], locs1, jh2, hp⟩) := by
    rw [Jvm.stepInstr_fastore serBaseHooks hget1 rfl (by simp)]
    dsimp only [jh2]; congr 4
  have hstore2 :
      Jvm.stepInstr serBaseHooks .fastore
        ⟨20, [.f32 r.top, .i32 1, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh2, hp⟩ =
        .inl (some ⟨21, [.ext (.encoder encId), .ext .floatArraySerializer], locs1, jh3, hp⟩) := by
    rw [Jvm.stepInstr_fastore serBaseHooks hget2 rfl (by simp)]
    dsimp only [jh3]; congr 4
  have hstore3 :
      Jvm.stepInstr serBaseHooks .fastore
        ⟨25, [.f32 r.right, .i32 2, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh3, hp⟩ =
        .inl (some ⟨26, [.ext (.encoder encId), .ext .floatArraySerializer], locs1, jh4, hp⟩) := by
    rw [Jvm.stepInstr_fastore serBaseHooks hget3 rfl (by simp)]
    dsimp only [jh4]; congr 4
  have hstore4 :
      Jvm.stepInstr serBaseHooks .fastore
        ⟨30, [.f32 r.bottom, .i32 3, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh4, hp⟩ =
        .inl (some ⟨31, [.ext (.encoder encId), .ext .floatArraySerializer], locs1, jh5, hp⟩) := by
    rw [Jvm.stepInstr_fastore serBaseHooks hget4 rfl (by simp)]
    dsimp only [jh5]; congr 4
  refine ⟨⟨33, [], locs1, jh5, { hp with encodedFloatArray := some (serializeRect r) }⟩, ?_, rfl⟩
  rw [runJvmRes_step_inl (st' := ⟨1, [.ext (.encoder encId)], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨2, [.str "encoder", .ext (.encoder encId)], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨3, [], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨4, [.ext (.rect r)], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨5, [.str "value", .ext (.rect r)], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨6, [], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨7, [.ext .floatArraySerializer], locs0, jh, hp⟩) rfl rfl]
  · rw [runJvmRes_step_inl (st' := ⟨8, [.ext (.encoder encId), .ext .floatArraySerializer], locs0, jh, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨9, [.i32 4, .ext (.encoder encId), .ext .floatArraySerializer], locs0, jh, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨10, [.heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs0, jh1, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨11, [.ext (.encoder encId), .ext .floatArraySerializer], locs1, jh1, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨12, [.heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh1, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨13, [.i32 0, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh1, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨14, [.ext (.rect r), .i32 0, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh1, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨15, [.f32 r.left, .i32 0, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh1, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨16, [.ext (.encoder encId), .ext .floatArraySerializer], locs1, jh2, hp⟩) rfl rfl hstore1]
    rw [runJvmRes_step_inl (st' := ⟨17, [.heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨18, [.i32 1, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨19, [.ext (.rect r), .i32 1, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨20, [.f32 r.top, .i32 1, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh2, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨21, [.ext (.encoder encId), .ext .floatArraySerializer], locs1, jh3, hp⟩) rfl rfl hstore2]
    rw [runJvmRes_step_inl (st' := ⟨22, [.heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh3, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨23, [.i32 2, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh3, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨24, [.ext (.rect r), .i32 2, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh3, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨25, [.f32 r.right, .i32 2, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh3, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨26, [.ext (.encoder encId), .ext .floatArraySerializer], locs1, jh4, hp⟩) rfl rfl hstore3]
    rw [runJvmRes_step_inl (st' := ⟨27, [.heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh4, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨28, [.i32 3, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh4, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨29, [.ext (.rect r), .i32 3, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh4, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨30, [.f32 r.bottom, .i32 3, .heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh4, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨31, [.ext (.encoder encId), .ext .floatArraySerializer], locs1, jh5, hp⟩) rfl rfl hstore4]
    rw [runJvmRes_step_inl (st' := ⟨32, [.heapRef arrAddr, .ext (.encoder encId), .ext .floatArraySerializer], locs1, jh5, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨33, [], locs1, jh5, { hp with encodedFloatArray := some (serializeRect r) }⟩) rfl rfl (stepInstr_floatArraySerialize hget5)]
    exact runJvmRes_step_inr rfl rfl rfl
  · dsimp only [Jvm.stepInstr, serBaseHooks]; rw [hdel]

theorem rectSerializer_deserialize_1_equiv
    (self : SerVal) (decId : Nat) (l t r b : Float32)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
    (hstat : HasRectSerializerStatics jh)
    (harr : hp.decodedFloatArray = #[l, t, r, b]) :
    Jvm.runJvm serHooks 20 RectSerializer_deserialize_1_prog
      (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh) =
      some (.ext (.rect { left := l, top := t, right := r, bottom := b })) := by
  rcases rectSerializer_deserialize_equiv self decId l t r b hp jh hstat harr with ⟨subEnd, hsubRun⟩
  rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 1, stack := [self] }) rfl rfl rfl]
  rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 2, stack := [.ext (.decoder decId), self] }) rfl rfl rfl]
  rw [runJvm_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 3, stack := [.ext (.rect { left := l, top := t, right := r, bottom := b })], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }) rfl rfl]
  · exact runJvm_step_inr rfl rfl rfl
  · refine stepInstr_serHooks_virt_ret ?_ (by simp [Jvm.stepInvokeVirtualGeneric])
    change (match Jvm.runJvmRes serBaseHooks 80 RectSerializer_deserialize_prog
        (initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh) with
      | some (retVal, endSt) =>
        Sum.inl (some { initSerJvmState [(0, self), (1, .ext (.decoder decId))] hp jh with pc := 2 + 1, stack := [retVal], heap := endSt.heap, jvmHeap := endSt.jvmHeap })
      | none => Sum.inr none) = _
    rw [hsubRun]

theorem rectSerializer_serialize_1_equiv
    (self : SerVal) (encId : Nat) (r : RectModel)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
    (hstat : HasRectSerializerStatics jh) :
    ∃ endSt,
      Jvm.runJvmRes serHooks 20 RectSerializer_serialize_1_prog
        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.rect r))] hp jh) =
        some (.unit, endSt) ∧
      endSt.heap.encodedFloatArray = some (serializeRect r) := by
  rcases rectSerializer_serialize_equiv self encId r hp jh hstat with ⟨subEnd, hsubRun, henc⟩
  refine ⟨{ initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.rect r))] hp jh with pc := 5, stack := [], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }, ?_, henc⟩
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.rect r))] hp jh with pc := 1, stack := [self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.rect r))] hp jh with pc := 2, stack := [.ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.rect r))] hp jh with pc := 3, stack := [.ext (.rect r), .ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.rect r))] hp jh with pc := 4, stack := [.ext (.rect r), .ext (.encoder encId), self] }) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.rect r))] hp jh with pc := 5, stack := [], heap := subEnd.heap, jvmHeap := subEnd.jvmHeap }) rfl rfl]
  · exact runJvmRes_step_inr rfl rfl rfl
  · refine stepInstr_serHooks_virt_void ?_ (by simp [Jvm.stepInvokeVirtualGeneric])
    change (match Jvm.runJvmRes serBaseHooks 80 RectSerializer_serialize_prog
        (initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.rect r))] hp jh) with
      | some (_, endSt) =>
        Sum.inl (some { initSerJvmState [(0, self), (1, .ext (.encoder encId)), (2, .ext (.rect r))] hp jh with pc := 4 + 1, stack := [], heap := endSt.heap, jvmHeap := endSt.jvmHeap })
      | none => Sum.inr none) = _
    rw [hsubRun]

/-! ### SurrogatingSerializerKt$SurrogatingSerializer$1 -/

private def surrCls : String :=
  "com/alexvanyo/composelife/serialization/SurrogatingSerializerKt$SurrogatingSerializer$1"

theorem surrogatingSerializer_init_equiv
    (serialName descName : String) (surrId fromId toId : Nat)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt) :
    let (selfAddr, jh0) := jh.alloc (.instance surrCls [])
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 30 SurrogatingSerializerKt_SurrogatingSerializer_1_init_prog
        (initSerJvmState
          [(0, .heapRef selfAddr),
           (1, .str serialName),
           (2, .ext (.surrogateSer surrId descName)),
           (3, .ext (.fn1 fromId)),
           (4, .ext (.fn1 toId))] hp jh0) =
        some (.unit, endSt) ∧
      endSt.jvmHeap.get? selfAddr =
        some (.instance surrCls
          [("descriptor", .ext (.serialDescriptor serialName (some descName))),
           ("$convertToSurrogate", .ext (.fn1 toId)),
           ("$convertFromSurrogate", .ext (.fn1 fromId)),
           ("$surrogateSerializer", .ext (.surrogateSer surrId descName))]) := by
  dsimp only
  let selfAddr := jh.objects.size
  let jh0 := (jh.alloc (.instance surrCls [])).2
  have hlt0 : selfAddr < jh0.objects.size := jvmHeap_size_alloc jh _
  have hget0 : jh0.get? selfAddr = some (.instance surrCls []) := jvmHeap_get_alloc jh _
  let f1 : List (String × SerVal) := [("$surrogateSerializer", .ext (.surrogateSer surrId descName))]
  let jh1 := jh0.set selfAddr (.instance surrCls f1)
  have hlt1 : selfAddr < jh1.objects.size := by rw [jvmHeap_size_set]; exact hlt0
  have hget1 : jh1.get? selfAddr = some (.instance surrCls f1) := jvmHeap_get_set_same _ _ _ hlt0
  let f2 : List (String × SerVal) := ("$convertFromSurrogate", .ext (.fn1 fromId)) :: f1
  let jh2 := jh1.set selfAddr (.instance surrCls f2)
  have hlt2 : selfAddr < jh2.objects.size := by rw [jvmHeap_size_set]; exact hlt1
  have hget2 : jh2.get? selfAddr = some (.instance surrCls f2) := jvmHeap_get_set_same _ _ _ hlt1
  let f3 : List (String × SerVal) := ("$convertToSurrogate", .ext (.fn1 toId)) :: f2
  let jh3 := jh2.set selfAddr (.instance surrCls f3)
  have hlt3 : selfAddr < jh3.objects.size := by rw [jvmHeap_size_set]; exact hlt2
  have hget3 : jh3.get? selfAddr = some (.instance surrCls f3) := jvmHeap_get_set_same _ _ _ hlt2
  let f4 : List (String × SerVal) := ("descriptor", .ext (.serialDescriptor serialName (some descName))) :: f3
  let jh4 := jh3.set selfAddr (.instance surrCls f4)
  have hget4 : jh4.get? selfAddr = some (.instance surrCls f4) := jvmHeap_get_set_same _ _ _ hlt3
  let locs0 := (initSerJvmState
    [(0, .heapRef selfAddr), (1, .str serialName), (2, .ext (.surrogateSer surrId descName)),
     (3, .ext (.fn1 fromId)), (4, .ext (.fn1 toId))] hp jh0).locals
  refine ⟨⟨17, [], locs0, jh4, hp⟩, ?_, hget4⟩
  rw [runJvmRes_step_inl (st' := ⟨1, [.heapRef selfAddr], locs0, jh0, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨2, [.ext (.surrogateSer surrId descName), .heapRef selfAddr], locs0, jh0, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨3, [], locs0, jh1, hp⟩) rfl rfl]
  · rw [runJvmRes_step_inl (st' := ⟨4, [.heapRef selfAddr], locs0, jh1, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨5, [.ext (.fn1 fromId), .heapRef selfAddr], locs0, jh1, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨6, [], locs0, jh2, hp⟩) rfl rfl]
    · rw [runJvmRes_step_inl (st' := ⟨7, [.heapRef selfAddr], locs0, jh2, hp⟩) rfl rfl rfl]
      rw [runJvmRes_step_inl (st' := ⟨8, [.ext (.fn1 toId), .heapRef selfAddr], locs0, jh2, hp⟩) rfl rfl rfl]
      rw [runJvmRes_step_inl (st' := ⟨9, [], locs0, jh3, hp⟩) rfl rfl]
      · rw [runJvmRes_step_inl (st' := ⟨10, [.heapRef selfAddr], locs0, jh3, hp⟩) rfl rfl rfl]
        rw [runJvmRes_step_inl (st' := ⟨11, [], locs0, jh3, hp⟩) rfl rfl rfl]
        rw [runJvmRes_step_inl (st' := ⟨12, [.heapRef selfAddr], locs0, jh3, hp⟩) rfl rfl rfl]
        rw [runJvmRes_step_inl (st' := ⟨13, [.str serialName, .heapRef selfAddr], locs0, jh3, hp⟩) rfl rfl rfl]
        rw [runJvmRes_step_inl (st' := ⟨14, [.ext (.surrogateSer surrId descName), .str serialName, .heapRef selfAddr], locs0, jh3, hp⟩) rfl rfl rfl]
        rw [runJvmRes_step_inl (st' := ⟨15, [.ext (.serialDescriptor descName none), .str serialName, .heapRef selfAddr], locs0, jh3, hp⟩) rfl rfl rfl]
        rw [runJvmRes_step_inl (st' := ⟨16, [.ext (.serialDescriptor serialName (some descName)), .heapRef selfAddr], locs0, jh3, hp⟩) rfl rfl stepInstr_serialDescriptor]
        rw [runJvmRes_step_inl (st' := ⟨17, [], locs0, jh4, hp⟩) rfl rfl]
        · exact runJvmRes_step_inr rfl rfl rfl
        · dsimp only [Jvm.stepInstr]; rw [hget3]; rfl
      · dsimp only [Jvm.stepInstr]; rw [hget2]; rfl
    · dsimp only [Jvm.stepInstr]; rw [hget1]; rfl
  · dsimp only [Jvm.stepInstr]; rw [hget0]; rfl

theorem surrogatingSerializer_getDescriptor_equiv
    (selfAddr : Nat) (descVal : SerVal) (fields : List (String × SerVal))
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
    (hobj : jh.get? selfAddr = some (.instance surrCls (("descriptor", descVal) :: fields))) :
    Jvm.runJvm serBaseHooks 10 SurrogatingSerializerKt_SurrogatingSerializer_1_getDescriptor_prog
      (initSerJvmState [(0, .heapRef selfAddr)] hp jh) = some descVal := by
  let locs0 := (initSerJvmState [(0, .heapRef selfAddr)] hp jh).locals
  rw [runJvm_step_inl (st' := ⟨1, [.heapRef selfAddr], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvm_step_inl (st' := ⟨2, [descVal], locs0, jh, hp⟩) rfl rfl]
  · exact runJvm_step_inr rfl rfl rfl
  · dsimp only [Jvm.stepInstr]; rw [hobj]; rfl

theorem surrogatingSerializer_deserialize_equiv
    (selfAddr surrId fromId toId decId : Nat) (serialName descName : String)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
    (hobj : jh.get? selfAddr =
      some (.instance surrCls
        [("descriptor", .ext (.serialDescriptor serialName (some descName))),
         ("$convertToSurrogate", .ext (.fn1 toId)),
         ("$convertFromSurrogate", .ext (.fn1 fromId)),
         ("$surrogateSerializer", .ext (.surrogateSer surrId descName))])) :
    Jvm.runJvm serBaseHooks 20 SurrogatingSerializerKt_SurrogatingSerializer_1_deserialize_prog
      (initSerJvmState [(0, .heapRef selfAddr), (1, .ext (.decoder decId))] hp jh) =
      some (.ext (.payload (hp.fn1Eval fromId hp.decodedSurrogate))) := by
  let locs0 := (initSerJvmState [(0, .heapRef selfAddr), (1, .ext (.decoder decId))] hp jh).locals
  rw [runJvm_step_inl (st' := ⟨1, [.ext (.decoder decId)], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvm_step_inl (st' := ⟨2, [.str "decoder", .ext (.decoder decId)], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvm_step_inl (st' := ⟨3, [], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvm_step_inl (st' := ⟨4, [.heapRef selfAddr], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvm_step_inl (st' := ⟨5, [.ext (.fn1 fromId)], locs0, jh, hp⟩) rfl rfl]
  · rw [runJvm_step_inl (st' := ⟨6, [.heapRef selfAddr, .ext (.fn1 fromId)], locs0, jh, hp⟩) rfl rfl rfl]
    rw [runJvm_step_inl (st' := ⟨7, [.ext (.surrogateSer surrId descName), .ext (.fn1 fromId)], locs0, jh, hp⟩) rfl rfl]
    · rw [runJvm_step_inl (st' := ⟨8, [.ext (.decoder decId), .ext (.surrogateSer surrId descName), .ext (.fn1 fromId)], locs0, jh, hp⟩) rfl rfl rfl]
      rw [runJvm_step_inl (st' := ⟨9, [.ext (.payload hp.decodedSurrogate), .ext (.fn1 fromId)], locs0, jh, hp⟩) rfl rfl rfl]
      rw [runJvm_step_inl (st' := ⟨10, [.ext (.payload (hp.fn1Eval fromId hp.decodedSurrogate))], locs0, jh, hp⟩) rfl rfl rfl]
      exact runJvm_step_inr rfl rfl rfl
    · dsimp only [Jvm.stepInstr]; rw [hobj]; rfl
  · dsimp only [Jvm.stepInstr]; rw [hobj]; rfl

theorem surrogatingSerializer_serialize_equiv
    (selfAddr surrId fromId toId encId : Nat) (serialName descName : String) (x : SerPayload)
    (hp : SerHeap) (jh : Jvm.JvmHeap SerExt)
    (hobj : jh.get? selfAddr =
      some (.instance surrCls
        [("descriptor", .ext (.serialDescriptor serialName (some descName))),
         ("$convertToSurrogate", .ext (.fn1 toId)),
         ("$convertFromSurrogate", .ext (.fn1 fromId)),
         ("$surrogateSerializer", .ext (.surrogateSer surrId descName))])) :
    ∃ endSt,
      Jvm.runJvmRes serBaseHooks 20 SurrogatingSerializerKt_SurrogatingSerializer_1_serialize_prog
        (initSerJvmState [(0, .heapRef selfAddr), (1, .ext (.encoder encId)), (2, .ext (.payload x))] hp jh) =
        some (.unit, endSt) ∧
      endSt.heap.encodedSurrogate = some (hp.fn1Eval toId x) := by
  let locs0 := (initSerJvmState [(0, .heapRef selfAddr), (1, .ext (.encoder encId)), (2, .ext (.payload x))] hp jh).locals
  refine ⟨⟨11, [], locs0, jh, { hp with encodedSurrogate := some (hp.fn1Eval toId x) }⟩, ?_, rfl⟩
  rw [runJvmRes_step_inl (st' := ⟨1, [.ext (.encoder encId)], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨2, [.str "encoder", .ext (.encoder encId)], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨3, [], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨4, [.heapRef selfAddr], locs0, jh, hp⟩) rfl rfl rfl]
  rw [runJvmRes_step_inl (st' := ⟨5, [.ext (.surrogateSer surrId descName)], locs0, jh, hp⟩) rfl rfl]
  · rw [runJvmRes_step_inl (st' := ⟨6, [.ext (.encoder encId), .ext (.surrogateSer surrId descName)], locs0, jh, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨7, [.heapRef selfAddr, .ext (.encoder encId), .ext (.surrogateSer surrId descName)], locs0, jh, hp⟩) rfl rfl rfl]
    rw [runJvmRes_step_inl (st' := ⟨8, [.ext (.fn1 toId), .ext (.encoder encId), .ext (.surrogateSer surrId descName)], locs0, jh, hp⟩) rfl rfl]
    · rw [runJvmRes_step_inl (st' := ⟨9, [.ext (.payload x), .ext (.fn1 toId), .ext (.encoder encId), .ext (.surrogateSer surrId descName)], locs0, jh, hp⟩) rfl rfl rfl]
      rw [runJvmRes_step_inl (st' := ⟨10, [.ext (.payload (hp.fn1Eval toId x)), .ext (.encoder encId), .ext (.surrogateSer surrId descName)], locs0, jh, hp⟩) rfl rfl rfl]
      rw [runJvmRes_step_inl (st' := ⟨11, [], locs0, jh, { hp with encodedSurrogate := some (hp.fn1Eval toId x) }⟩) rfl rfl rfl]
      exact runJvmRes_step_inr rfl rfl rfl
    · dsimp only [Jvm.stepInstr]; rw [hobj]; rfl
  · dsimp only [Jvm.stepInstr]; rw [hobj]; rfl

end Serialization.KotlinJvmVerification
