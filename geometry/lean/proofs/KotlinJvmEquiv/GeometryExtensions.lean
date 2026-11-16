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
import Jvm.Tactics
import JvmSemantics
import KotlinJvmBytecode
import models.GeometryExtensionsModel
import theorems.GeometryExtensionsModelTheorems

namespace Geometry.KotlinJvmVerification
open Geometry.JvmVerification
open Geometry.KotlinJvmBytecode
open Geometry.KotlinModel

/-- Heap invariant stating `GeometryExtensionsKt` static neighbor offset lists are initialized. -/
def HasGeometryNeighborLuts (jh : Jvm.JvmHeap Empty) : Prop :=
  (∃ listAddr arrAddr,
    jh.getStatic? "com/alexvanyo/composelife/geometry/GeometryExtensionsKt" "mooreNeighborOffsets" = some (.heapRef listAddr) ∧
    jh.get? listAddr = some (.instance "java/util/List" [("arr", .heapRef arrAddr)]) ∧
    jh.get? arrAddr = some (.objArray "androidx/compose/ui/unit/IntOffset"
      (mooreNeighborOffsetsModel.map (fun (dx, dy) => Jvm.JvmVal.boxedLong (packOffset dx dy))).toArray)) ∧
  (∃ listAddr arrAddr,
    jh.getStatic? "com/alexvanyo/composelife/geometry/GeometryExtensionsKt" "vonNeumannNeighborOffsets" = some (.heapRef listAddr) ∧
    jh.get? listAddr = some (.instance "java/util/List" [("arr", .heapRef arrAddr)]) ∧
    jh.get? arrAddr = some (.objArray "androidx/compose/ui/unit/IntOffset"
      (vonNeumannNeighborOffsetsModel.map (fun (dx, dy) => Jvm.JvmVal.boxedLong (packOffset dx dy))).toArray))

/-- Decode a `"java/util/Set"` of boxed `IntOffset` longs into packed `List UInt64`. -/
def extractPackedSet? (jh : Jvm.JvmHeap Empty) : JvmVal → Option (List UInt64)
  | .heapRef addr =>
    match jh.get? addr with
    | some (.instance "java/util/Set" fields) =>
      match (fields.find? (fun (f, _) => f == "arr")).map Prod.snd with
      | some (.heapRef arrAddr) =>
        match jh.get? arrAddr with
        | some (.objArray _ elems) =>
          elems.toList.mapM fun
            | .boxedLong v => some v
            | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- Bridge lemma: `GeometryExtensionsKt.chebyshevDistance` JVM bytecode matches `chebyshevDistanceModel`. -/
theorem chebyshevDistance_equiv (o : UInt64) (jh : Jvm.JvmHeap Empty := {}) :
    runJvm 15 GeometryExtensionsKt_chebyshevDistance_prog (initJvmState [(0, .i64 o)] jh) =
      some (.i32 (chebyshevDistanceModel o)) := rfl

/-- Bridge lemma: `GeometryExtensionsKt.manhattanDistance` JVM bytecode matches `manhattanDistanceModel`. -/
theorem manhattanDistance_equiv (o : UInt64) (jh : Jvm.JvmHeap Empty := {}) :
    runJvm 15 GeometryExtensionsKt_manhattanDistance_prog (initJvmState [(0, .i64 o)] jh) =
      some (.i32 (manhattanDistanceModel o)) := rfl

/-- Bridge lemma: `<clinit>` initializes `GeometryExtensionsKt`'s neighbor offset LUTs on the JVM heap. -/
theorem clinit_GeometryExtensionsKt_equiv :
    ∃ st',
      runJvmRes 100 GeometryExtensionsKt_clinit_prog (initJvmState [] {}) = some (.unit, st') ∧
      HasGeometryNeighborLuts st'.jvmHeap := by
  refine ⟨_, rfl, ⟨1, 0, rfl, rfl, rfl⟩, ⟨3, 2, rfl, rfl, rfl⟩⟩

private def emptyEq : Empty → Empty → Bool := fun _ _ => false

private def neighborEpilogueTail : List JvmInstr :=
  [ .aload 5, .checkcast "java/util/List", .nop, .checkcast "java/lang/Iterable"
  , .invokestatic "kotlin/collections/CollectionsKt" "toSet" "(Ljava/lang/Iterable;)Ljava/util/Set;"
  , .areturn ]

private def neighborIterMidTail : List JvmInstr :=
  [ .lload 9, .lload 0
  , .invokestatic "androidx/compose/ui/unit/IntOffset" "plus-qkQi6aY" "(JJ)J"
  , .invokestatic "androidx/compose/ui/unit/IntOffset" "box-impl" "(J)Landroidx/compose/ui/unit/IntOffset;"
  , .aload 12, .swap, .invokeinterface "java/util/Collection" "add" "(Ljava/lang/Object;)Z", .pop, .goto 20
  ] ++ neighborEpilogueTail

private def neighborLoopTail : List JvmInstr :=
  [ .aload 7, .invokeinterface "java/util/Iterator" "hasNext" "()Z", .ifeq 43
  , .aload 7, .invokeinterface "java/util/Iterator" "next" "()Ljava/lang/Object;", .astore 8
  , .aload 5, .aload 8, .checkcast "androidx/compose/ui/unit/IntOffset"
  , .invokevirtual "androidx/compose/ui/unit/IntOffset" "unbox-impl" "()J", .lstore 9, .astore 12
  , .iconst 0, .istore 11
  ] ++ neighborIterMidTail

private def neighborProgAfter0 : List JvmInstr :=
  [ .checkcast "java/lang/Iterable", .astore 2, .iconst 0, .istore 3, .aload 2, .astore 4
  , .newClass "java/util/ArrayList", .dup, .aload 2, .iconst 10
  , .invokestatic "kotlin/collections/CollectionsKt" "collectionSizeOrDefault" "(Ljava/lang/Iterable;I)I"
  , .invokespecial "java/util/ArrayList" "<init>" "(I)V"
  , .checkcast "java/util/Collection", .astore 5, .iconst 0, .istore 6, .aload 4
  , .invokeinterface "java/lang/Iterable" "iterator" "()Ljava/util/Iterator;", .astore 7
  ] ++ neighborLoopTail

private def neighborProgram (fieldName : String) : List JvmInstr :=
  .getstatic "com/alexvanyo/composelife/geometry/GeometryExtensionsKt" fieldName "Ljava/util/List;" :: neighborProgAfter0

private theorem drop20_neighborProgram (fieldName : String) :
    (neighborProgram fieldName).drop 20 = neighborLoopTail := by
  rfl

private theorem drop43_neighborProgram (fieldName : String) :
    (neighborProgram fieldName).drop 43 = neighborEpilogueTail := by
  rfl

private theorem dedupJvmVals_boxedLong_acc
    (acc ps : List UInt64) (hnodup : (acc ++ ps).Nodup) :
    ps.foldl
        (fun (cur : List JvmVal) x =>
          let jx := Jvm.JvmVal.boxedLong x
          if cur.any (fun y => Jvm.JvmVal.beqVal emptyEq jx y) then cur else cur ++ [jx])
        (acc.map Jvm.JvmVal.boxedLong) =
      (acc ++ ps).map Jvm.JvmVal.boxedLong := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have hp_notin : p ∉ acc := by
      intro hmem
      have hnd := List.nodup_append.mp hnodup
      exact hnd.2.2 p hmem p List.mem_cons_self rfl
    have hnot : (acc.map Jvm.JvmVal.boxedLong).any
        (fun y => Jvm.JvmVal.beqVal emptyEq (Jvm.JvmVal.boxedLong p) y) = false := by
      rw [Bool.eq_false_iff]
      intro htrue
      rw [List.any_eq_true] at htrue
      rcases htrue with ⟨y, hy, hbeq⟩
      rw [List.mem_map] at hy
      rcases hy with ⟨q, hq, hqeq⟩
      subst hqeq
      have hpq : p = q := by simpa [Jvm.JvmVal.beqVal, emptyEq] using hbeq
      subst hpq
      exact hp_notin hq
    rw [hnot]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hmap : acc.map (Jvm.JvmVal.boxedLong (Ext := Empty)) ++ [Jvm.JvmVal.boxedLong p] =
        (acc ++ [p]).map Jvm.JvmVal.boxedLong := by
      simp [List.map_append]
    rw [hmap]
    have hnodup' : ((acc ++ [p]) ++ ps).Nodup := by simpa [List.append_assoc] using hnodup
    simpa [List.append_assoc] using ih (acc ++ [p]) hnodup'

private theorem dedupJvmVals_boxedLong_nodup (ps : List UInt64) (hnodup : ps.Nodup) :
    dedupJvmVals (Jvm.JvmVal.beqVal emptyEq) (ps.map Jvm.JvmVal.boxedLong) =
      ps.map Jvm.JvmVal.boxedLong := by
  dsimp [dedupJvmVals]
  have h1 : (ps.map Jvm.JvmVal.boxedLong).foldl
      (fun acc x =>
        if acc.any (fun y => Jvm.JvmVal.beqVal emptyEq x y) then acc else acc ++ [x]) [] =
      ps.foldl
        (fun acc x =>
          let jx := Jvm.JvmVal.boxedLong x
          if acc.any (fun y => Jvm.JvmVal.beqVal emptyEq jx y) then acc else acc ++ [jx])
        ([] : List JvmVal) := by
    rw [List.foldl_map]
  rw [h1]
  exact dedupJvmVals_boxedLong_acc [] ps (by simpa using hnodup)

private theorem packedOffsets_nodup (o : UInt64) (offsets : List (Int32 × Int32)) (hn : offsets.Nodup) :
    (offsets.map fun (dx, dy) => addPackedOffset (packOffset dx dy) o).Nodup := by
  refine List.Nodup.map ?_ hn
  intro d1 d2 heq
  have hx : d1.1 = d2.1 := by simpa [addPackedOffset, offsetX_pack] using congrArg offsetX heq
  have hy : d1.2 = d2.2 := by simpa [addPackedOffset, offsetY_pack] using congrArg offsetY heq
  exact Prod.ext hx hy

private def nextIterLocs (dstListAddr : Nat) (dx dy : Int32) (locs : Nat → JvmVal) :
    Nat → JvmVal :=
  Jvm.setLocal (Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs
    8 (Jvm.JvmVal.boxedLong (packOffset dx dy)))
    9 (.i64 (packOffset dx dy)))
    12 (.heapRef dstListAddr))
    11 (.i32 0)

private theorem nextIterLocs_0 (o : UInt64) (dstListAddr : Nat) (dx dy : Int32) (locs : Nat → JvmVal)
    (h0 : locs 0 = .i64 o) :
    nextIterLocs dstListAddr dx dy locs 0 = .i64 o := by
  simpa [nextIterLocs, Jvm.setLocal] using h0

private theorem nextIterLocs_5 (dstListAddr : Nat) (dx dy : Int32) (locs : Nat → JvmVal)
    (h5 : locs 5 = .heapRef dstListAddr) :
    nextIterLocs dstListAddr dx dy locs 5 = .heapRef dstListAddr := by
  simpa [nextIterLocs, Jvm.setLocal] using h5

private theorem nextIterLocs_7 {dstListAddr : Nat} (dx dy : Int32) (locs : Nat → JvmVal)
    {itAddr : Nat} (h7 : locs 7 = .heapRef itAddr) :
    nextIterLocs dstListAddr dx dy locs 7 = .heapRef itAddr := by
  simpa [nextIterLocs, Jvm.setLocal] using h7

private theorem nextIterLocs_9 (dstListAddr : Nat) (dx dy : Int32) (locs : Nat → JvmVal) :
    nextIterLocs dstListAddr dx dy locs 9 = .i64 (packOffset dx dy) := by
  simp [nextIterLocs, Jvm.setLocal]

private theorem nextIterLocs_12 (dstListAddr : Nat) (dx dy : Int32) (locs : Nat → JvmVal) :
    nextIterLocs dstListAddr dx dy locs 12 = .heapRef dstListAddr := by
  simp [nextIterLocs, Jvm.setLocal]

private theorem setLocal_self (locs : Nat → JvmVal) (idx : Nat) (v : JvmVal) :
    Jvm.setLocal locs idx v idx = v := by
  simp [Jvm.setLocal]

private theorem setLocal_ne (locs : Nat → JvmVal) {i idx : Nat} (v : JvmVal)
    (hne : i ≠ idx) :
    Jvm.setLocal locs idx v i = locs i := by
  simp [Jvm.setLocal, hne]

local instance : Jvm.HasDefaultIsZero geomHooks := ⟨rfl⟩

private theorem runJvmResFast_nop {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.nop :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_dup {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.dup :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest ⟨pc + 1, v :: v :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_pop {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.pop :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_swap {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {a b : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (ha : a.isCat2 = false := by rfl) (hb : b.isCat2 = false := by rfl) :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.swap :: rest) ⟨pc0, a :: b :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest ⟨pc + 1, b :: a :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) ?_ rfl
  unfold Jvm.stepInstr
  dsimp only
  rw [ha, hb]
  rfl

private theorem runJvmResFast_iconst {f pc pc0 : Nat} {c : UInt32} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.iconst c :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest ⟨pc + 1, .i32 c :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_aload {f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.aload idx :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_lload {f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.lload idx :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_astore {f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.astore idx :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, stk, Jvm.setLocal locs idx v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_lstore {f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.lstore idx :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, stk, Jvm.setLocal locs idx v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_istore {f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.istore idx :: rest) ⟨pc0, v :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, stk, Jvm.setLocal locs idx v, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_getstatic {f pc pc0 : Nat} {cls field desc : String}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} {v : JvmVal}
    (hstat : jh.getStatic? cls field = some v) :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.getstatic cls field desc :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest ⟨pc + 1, v :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) ?_ rfl
  unfold Jvm.stepInstr
  dsimp only
  rw [hstat]

private theorem runJvmResFast_newClass {f pc pc0 : Nat} {cls : String}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (hne : (cls == "java/lang/StringBuilder") = false := by rfl) :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.newClass cls :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest ⟨pc + 1, .allocRef cls :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) ?_ rfl
  unfold Jvm.stepInstr
  dsimp only
  rw [hne]
  rfl

private theorem runJvmResFast_checkcast_boxedLong {f pc pc0 : Nat} {cls : String} {x : UInt64}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (hc : geomHooks.checkCast cls (.boxedLong x) = some (.boxedLong x) := by rfl) :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.checkcast cls :: rest)
        ⟨pc0, .boxedLong x :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .boxedLong x :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) ?_ rfl
  unfold Jvm.stepInstr Jvm.evalCheckCast
  have hc' := hc
  dsimp only at hc' ⊢
  rw [hc']

private theorem runJvmResFast_checkcast_instance {f pc pc0 addr : Nat} {targetCls objCls : String}
    {fields : List (String × JvmVal)} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit}
    (hget : jh.get? addr = some (.instance objCls fields))
    (hm : Jvm.HeapObj.matchesType geomHooks.isSubtypeOf targetCls (.instance objCls fields) = true := by rfl) :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.checkcast targetCls :: rest)
        ⟨pc0, .heapRef addr :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .heapRef addr :: stk, locs, jh, hp⟩ := by
  refine Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) ?_ rfl
  unfold Jvm.stepInstr Jvm.evalCheckCast Jvm.JvmHeap.checkCast Jvm.JvmHeap.checkInstanceOf
  dsimp only
  rw [hget]
  simp [hm]

private theorem runJvmResFast_iload {f pc pc0 idx : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.iload idx :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest ⟨pc + 1, locs idx :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_lconst {f pc pc0 : Nat} {c : UInt64} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.lconst c :: rest) ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest ⟨pc + 1, .i64 c :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_lshr {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {va : UInt64} {vb : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.lshr :: rest)
        ⟨pc0, .i32 vb :: .i64 va :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .i64 (UInt64.ofBitVec (va.toBitVec.sshiftRight (vb &&& 63).toNat)) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_land {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {va vb : UInt64} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.land :: rest)
        ⟨pc0, .i64 vb :: .i64 va :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .i64 (va &&& vb) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_l2i {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {va : UInt64} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.l2i :: rest)
        ⟨pc0, .i64 va :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 va.toUInt32 :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_f2d {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {va : Float32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.f2d :: rest)
        ⟨pc0, .f32 va :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .f64 va.toFloat :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_d2f {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {va : Float} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.d2f :: rest)
        ⟨pc0, .f64 va :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .f32 va.toFloat32 :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_f2i {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {va : Float32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.f2i :: rest)
        ⟨pc0, .f32 va :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .i32 (Jvm.float32ToI32 va) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_fsub {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {va vb : Float32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.fsub :: rest)
        ⟨pc0, .f32 vb :: .f32 va :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .f32 (va - vb) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_fmul {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {va vb : Float32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.fmul :: rest)
        ⟨pc0, .f32 vb :: .f32 va :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 1) rest
        ⟨pc + 1, .f32 (va * vb) :: stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr geomHooks rfl (by simp) rfl rfl

private theorem geomHooks_iteZero? (v : JvmVal) (t e : Option JvmVal) :
    geomHooks.iteZero? v t e =
      match geomHooks.isZero? v with | some true => t | some false => e | none => none := by
  dsimp [geomHooks, Jvm.JvmHooks.iteZero?, Jvm.JvmHooks.isZero?]
  cases hv : Jvm.JvmVal.asI32? v with
  | none => rfl
  | some x => by_cases hx : (x == 0) = true <;> simp [Jvm.defaultIteVal, hx] <;> split <;> rfl

private theorem geomHooks_iteNonZero? (v : JvmVal) (t e : Option JvmVal) :
    geomHooks.iteNonZero? v t e =
      match geomHooks.isZero? v with | some true => e | some false => t | none => none := by
  dsimp [geomHooks, Jvm.JvmHooks.iteNonZero?, Jvm.JvmHooks.isZero?]
  cases hv : Jvm.JvmVal.asI32? v with
  | none => rfl
  | some x => by_cases hx : (x == 0) = true <;> simp [Jvm.defaultIteVal, hx] <;> split <;> rfl

private theorem runJvmResFast_lreturn {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : UInt64} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.lreturn :: rest)
        ⟨pc0, .i64 v :: stk, locs, jh, hp⟩ =
      some (.i64 v, ⟨pc, .i64 v :: stk, locs, jh, hp⟩) := by
  unfold Jvm.runJvmResFast Jvm.stepInstr
  rfl

private theorem runJvmResFast_freturn {f pc pc0 : Nat} {prog rest : List JvmInstr}
    {v : Float32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 1) prog pc (.freturn :: rest)
        ⟨pc0, .f32 v :: stk, locs, jh, hp⟩ =
      some (.f32 v, ⟨pc, .f32 v :: stk, locs, jh, hp⟩) := by
  unfold Jvm.runJvmResFast Jvm.stepInstr
  rfl

private theorem u64_sshiftRight32_toUInt32 (p : UInt64) :
    (UInt64.ofBitVec (p.toBitVec.sshiftRight ((32 : UInt32) &&& 63).toNat)).toUInt32 =
      (p >>> 32).toUInt32 := by
  rcases p with ⟨bp⟩
  apply congrArg UInt32.ofBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hsh : ((32 : UInt32) &&& 63).toNat = 32 := rfl
  change ((bp.sshiftRight ((32 : UInt32) &&& 63).toNat).setWidth 32).getLsbD i =
    ((bp >>> 32).setWidth 32).getLsbD i
  rw [hsh]
  have h1 : 32 + i < 64 := by omega
  have hnot : ¬ (64 ≤ i) := by omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight, BitVec.getLsbD_ushiftRight,
    hi, h1, hnot, decide_true, decide_false, Bool.not_false, Bool.true_and, ↓reduceIte]

private theorem u64_and_mask32_toUInt32 (p : UInt64) :
    (p &&& 4294967295).toUInt32 = p.toUInt32 := by
  rcases p with ⟨bp⟩
  apply congrArg UInt32.ofBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change ((bp &&& 4294967295#64).setWidth 32).getLsbD i = (bp.setWidth 32).getLsbD i
  have hm : (4294967295#64).getLsbD i = true := by
    change (4294967295 : Nat).testBit i = true
    rw [show (4294967295 : Nat) = 2 ^ 32 - 1 by decide, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, hi, decide_true, Bool.true_and,
    hm, Bool.and_true]

private def unpackLocs (locs : Nat → JvmVal) (t : Nat) (p : UInt64) (lowBits : UInt32) :
    Nat → JvmVal :=
  Jvm.setLocal
    (Jvm.setLocal
      (Jvm.setLocal
        (Jvm.setLocal
          (Jvm.setLocal
            (Jvm.setLocal locs t (.i64 p))
            (t + 2) (.i32 0))
          (t + 3) (.i64 p))
        (t + 5) (.i32 0))
      (t + 6) (.i32 lowBits))
    (t + 7) (.i32 0)

private theorem unpackLocs_lt (locs : Nat → JvmVal) {t s : Nat} (p : UInt64)
    (lowBits : UInt32) (hs : s < t) :
    unpackLocs locs t p lowBits s = locs s := by
  dsimp [unpackLocs]
  repeat rw [setLocal_ne _ _ (by omega)]

private def unpackOffsetXBlock (slot t : Nat) : List JvmInstr :=
  [ .lload slot, .lstore t, .iconst 0, .istore (t + 2),
    .lload t, .lstore (t + 3), .iconst 0, .istore (t + 5),
    .lload (t + 3), .iconst 32, .lshr, .l2i, .istore (t + 6),
    .iconst 0, .istore (t + 7), .iload (t + 6),
    .invokestatic "java/lang/Float" "intBitsToFloat" "(I)F", .nop, .nop ]

private def unpackOffsetYBlock (slot t : Nat) : List JvmInstr :=
  [ .lload slot, .lstore t, .iconst 0, .istore (t + 2),
    .lload t, .lstore (t + 3), .iconst 0, .istore (t + 5),
    .lload (t + 3), .lconst 4294967295, .land, .l2i, .istore (t + 6),
    .iconst 0, .istore (t + 7), .iload (t + 6),
    .invokestatic "java/lang/Float" "intBitsToFloat" "(I)F", .nop, .nop ]

private def floorToIntBlock : List JvmInstr :=
  [ .f2d, .invokestatic "java/lang/Math" "floor" "(D)D", .d2f, .f2i ]

private theorem runJvmResFast_unpackOffsetXBlock {f pc pc0 slot t : Nat}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} {p : UInt64}
    (hslot : locs slot = .i64 p) :
    Jvm.runJvmResFast geomHooks (f + 19) prog pc (unpackOffsetXBlock slot t ++ rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 19) rest
        ⟨pc + 19, .f32 (offsetFloatX p) :: stk, unpackLocs locs t p (p >>> 32).toUInt32, jh, hp⟩ := by
  dsimp [unpackOffsetXBlock, unpackLocs]
  rw [show f + 19 = (f + 18) + 1 by omega, runJvmResFast_lload, hslot]
  rw [show f + 18 = (f + 17) + 1 by omega, runJvmResFast_lstore]
  rw [show f + 17 = (f + 16) + 1 by omega, runJvmResFast_iconst]
  rw [show f + 16 = (f + 15) + 1 by omega, runJvmResFast_istore]
  rw [show f + 15 = (f + 14) + 1 by omega, runJvmResFast_lload,
    setLocal_ne _ _ (by omega), setLocal_self]
  rw [show f + 14 = (f + 13) + 1 by omega, runJvmResFast_lstore]
  rw [show f + 13 = (f + 12) + 1 by omega, runJvmResFast_iconst]
  rw [show f + 12 = (f + 11) + 1 by omega, runJvmResFast_istore]
  rw [show f + 11 = (f + 10) + 1 by omega, runJvmResFast_lload,
    setLocal_ne _ _ (by omega), setLocal_self]
  rw [show f + 10 = (f + 9) + 1 by omega, runJvmResFast_iconst]
  rw [show f + 9 = (f + 8) + 1 by omega, runJvmResFast_lshr]
  rw [show f + 8 = (f + 7) + 1 by omega, runJvmResFast_l2i, u64_sshiftRight32_toUInt32 p]
  rw [show f + 7 = (f + 6) + 1 by omega, runJvmResFast_istore]
  rw [show f + 6 = (f + 5) + 1 by omega, runJvmResFast_iconst]
  rw [show f + 5 = (f + 4) + 1 by omega, runJvmResFast_istore]
  rw [show f + 4 = (f + 3) + 1 by omega, runJvmResFast_iload,
    setLocal_ne _ _ (by omega), setLocal_self]
  rw [show f + 3 = (f + 2) + 1 by omega, Jvm.runJvmResFast_invokestatic_step geomHooks rfl]
  rw [show f + 2 = (f + 1) + 1 by omega, runJvmResFast_nop]
  rw [runJvmResFast_nop]
  rfl

private theorem runJvmResFast_unpackOffsetYBlock {f pc pc0 slot t : Nat}
    {prog rest : List JvmInstr} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap Empty} {hp : Unit} {p : UInt64}
    (hslot : locs slot = .i64 p) :
    Jvm.runJvmResFast geomHooks (f + 19) prog pc (unpackOffsetYBlock slot t ++ rest)
        ⟨pc0, stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 19) rest
        ⟨pc + 19, .f32 (offsetFloatY p) :: stk, unpackLocs locs t p p.toUInt32, jh, hp⟩ := by
  dsimp [unpackOffsetYBlock, unpackLocs]
  rw [show f + 19 = (f + 18) + 1 by omega, runJvmResFast_lload, hslot]
  rw [show f + 18 = (f + 17) + 1 by omega, runJvmResFast_lstore]
  rw [show f + 17 = (f + 16) + 1 by omega, runJvmResFast_iconst]
  rw [show f + 16 = (f + 15) + 1 by omega, runJvmResFast_istore]
  rw [show f + 15 = (f + 14) + 1 by omega, runJvmResFast_lload,
    setLocal_ne _ _ (by omega), setLocal_self]
  rw [show f + 14 = (f + 13) + 1 by omega, runJvmResFast_lstore]
  rw [show f + 13 = (f + 12) + 1 by omega, runJvmResFast_iconst]
  rw [show f + 12 = (f + 11) + 1 by omega, runJvmResFast_istore]
  rw [show f + 11 = (f + 10) + 1 by omega, runJvmResFast_lload,
    setLocal_ne _ _ (by omega), setLocal_self]
  rw [show f + 10 = (f + 9) + 1 by omega, runJvmResFast_lconst]
  rw [show f + 9 = (f + 8) + 1 by omega, runJvmResFast_land]
  rw [show f + 8 = (f + 7) + 1 by omega, runJvmResFast_l2i, u64_and_mask32_toUInt32 p]
  rw [show f + 7 = (f + 6) + 1 by omega, runJvmResFast_istore]
  rw [show f + 6 = (f + 5) + 1 by omega, runJvmResFast_iconst]
  rw [show f + 5 = (f + 4) + 1 by omega, runJvmResFast_istore]
  rw [show f + 4 = (f + 3) + 1 by omega, runJvmResFast_iload,
    setLocal_ne _ _ (by omega), setLocal_self]
  rw [show f + 3 = (f + 2) + 1 by omega, Jvm.runJvmResFast_invokestatic_step geomHooks rfl]
  rw [show f + 2 = (f + 1) + 1 by omega, runJvmResFast_nop]
  rw [runJvmResFast_nop]
  rfl

private theorem runJvmResFast_floorToIntBlock {f pc pc0 : Nat}
    {prog rest : List JvmInstr} {x : Float32} {stk : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap Empty} {hp : Unit} :
    Jvm.runJvmResFast geomHooks (f + 4) prog pc (floorToIntBlock ++ rest)
        ⟨pc0, .f32 x :: stk, locs, jh, hp⟩ =
      Jvm.runJvmResFast geomHooks f prog (pc + 4) rest
        ⟨pc + 4, .i32 (float32ToInt32Model x.toFloat.floor.toFloat32).toUInt32 :: stk, locs, jh, hp⟩ := by
  dsimp [floorToIntBlock]
  rw [show f + 4 = (f + 3) + 1 by omega, runJvmResFast_f2d]
  rw [show f + 3 = (f + 2) + 1 by omega, Jvm.runJvmResFast_invokestatic_step geomHooks rfl]
  rw [show f + 2 = (f + 1) + 1 by omega, runJvmResFast_d2f]
  rw [runJvmResFast_f2i]
  rfl

/-- Bridge lemma: `GeometryExtensionsKt.floor` JVM bytecode matches `floorModel`. -/
theorem floor_equiv (o : UInt64) (jh : Jvm.JvmHeap Empty := {}) :
    runJvm 55 GeometryExtensionsKt_floor_prog (initJvmState [(0, .i64 o)] jh) =
      some (.i64 (floorModel o)) := by
  let locs0 : Nat → JvmVal := Jvm.setLocal (fun _ => .i32 0) 0 (.i64 o)
  let locs1 := unpackLocs locs0 2 o (o >>> 32).toUInt32
  let locs2 := unpackLocs locs1 2 o o.toUInt32
  have hloc0 : locs0 0 = .i64 o := rfl
  have hloc1 : locs1 0 = .i64 o := (unpackLocs_lt locs0 _ _ (by omega)).trans hloc0
  have hfast :
      Jvm.runJvmResFast geomHooks 55 GeometryExtensionsKt_floor_prog 0 GeometryExtensionsKt_floor_prog (initJvmState [(0, .i64 o)] jh) =
        some (.i64 (floorModel o),
          { pc := 47, stack := [.i64 (floorModel o)], locals := locs2, jvmHeap := jh, heap := () }) := by
    have hprog :
        GeometryExtensionsKt_floor_prog =
          unpackOffsetXBlock 0 2 ++
            (floorToIntBlock ++
              (unpackOffsetYBlock 0 2 ++
                (floorToIntBlock ++
                  [.invokestatic "com/alexvanyo/composelife/geometry/IntOffset_jbKt" "IntOffset" "(II)J",
                   .lreturn]))) := rfl
    rw [hprog]
    dsimp [initJvmState, Jvm.initJvmState, List.foldl]
    change Jvm.runJvmResFast geomHooks 55 _ 0 _ ⟨0, [], locs0, jh, ()⟩ = _
    rw [show (55 : Nat) = 36 + 19 by omega, runJvmResFast_unpackOffsetXBlock hloc0]
    rw [show (36 : Nat) = 32 + 4 by omega, runJvmResFast_floorToIntBlock]
    rw [show (32 : Nat) = 13 + 19 by omega, runJvmResFast_unpackOffsetYBlock hloc1]
    rw [show (13 : Nat) = 9 + 4 by omega, runJvmResFast_floorToIntBlock]
    rw [show (9 : Nat) = 8 + 1 by omega, Jvm.runJvmResFast_invokestatic_step geomHooks rfl]
    rw [show (8 : Nat) = 7 + 1 by omega, runJvmResFast_lreturn]
    rfl
  dsimp only [runJvm]
  rw [Jvm.runJvm_eq_runJvmRes geomHooks geomHooks_iteZero? geomHooks_iteNonZero?,
    Jvm.runJvmRes_of_runJvmResFast0 geomHooks _ _ _ _ rfl hfast]
  rfl

/-- Bridge lemma: `GeometryExtensionsKt.sideOfLine` JVM bytecode matches `sideOfLineModel`. -/
theorem sideOfLine_equiv (point startPt endPt : UInt64) (jh : Jvm.JvmHeap Empty := {}) :
    runJvm 200 GeometryExtensionsKt_sideOfLine_prog
        (initJvmState [(0, .i64 point), (2, .i64 startPt), (4, .i64 endPt)] jh) =
      some (.f32 (sideOfLineModel point startPt endPt)) := by
  let locs0 : Nat → JvmVal :=
    Jvm.setLocal
      (Jvm.setLocal
        (Jvm.setLocal (fun _ => .i32 0) 0 (.i64 point))
        2 (.i64 startPt))
      4 (.i64 endPt)
  let l1 := unpackLocs locs0 6 endPt (endPt >>> 32).toUInt32
  let l2 := unpackLocs l1 6 startPt (startPt >>> 32).toUInt32
  let l3 := unpackLocs l2 6 point point.toUInt32
  let l4 := unpackLocs l3 6 startPt startPt.toUInt32
  let l5 := unpackLocs l4 6 endPt endPt.toUInt32
  let l6 := unpackLocs l5 6 startPt startPt.toUInt32
  let l7 := unpackLocs l6 6 point (point >>> 32).toUInt32
  let l8 := unpackLocs l7 6 startPt (startPt >>> 32).toUInt32
  have h0_0 : locs0 0 = .i64 point := rfl
  have h0_2 : locs0 2 = .i64 startPt := rfl
  have h0_4 : locs0 4 = .i64 endPt := rfl
  have h1_2 : l1 2 = .i64 startPt := (unpackLocs_lt _ _ _ (by omega)).trans h0_2
  have h2_0 : l2 0 = .i64 point := (unpackLocs_lt _ _ _ (by omega)).trans ((unpackLocs_lt _ _ _ (by omega)).trans h0_0)
  have h3_2 : l3 2 = .i64 startPt := (unpackLocs_lt _ _ _ (by omega)).trans ((unpackLocs_lt _ _ _ (by omega)).trans h1_2)
  have h4_4 : l4 4 = .i64 endPt :=
    (unpackLocs_lt _ _ _ (by omega)).trans ((unpackLocs_lt _ _ _ (by omega)).trans
      ((unpackLocs_lt _ _ _ (by omega)).trans ((unpackLocs_lt _ _ _ (by omega)).trans h0_4)))
  have h5_2 : l5 2 = .i64 startPt := (unpackLocs_lt _ _ _ (by omega)).trans ((unpackLocs_lt _ _ _ (by omega)).trans h3_2)
  have h6_0 : l6 0 = .i64 point :=
    (unpackLocs_lt _ _ _ (by omega)).trans ((unpackLocs_lt _ _ _ (by omega)).trans
      ((unpackLocs_lt _ _ _ (by omega)).trans ((unpackLocs_lt _ _ _ (by omega)).trans h2_0)))
  have h7_2 : l7 2 = .i64 startPt := (unpackLocs_lt _ _ _ (by omega)).trans ((unpackLocs_lt _ _ _ (by omega)).trans h5_2)
  have hfast :
      Jvm.runJvmResFast geomHooks 200 GeometryExtensionsKt_sideOfLine_prog 0 GeometryExtensionsKt_sideOfLine_prog
          (initJvmState [(0, .i64 point), (2, .i64 startPt), (4, .i64 endPt)] jh) =
        some (.f32 (sideOfLineModel point startPt endPt),
          { pc := 160, stack := [.f32 (sideOfLineModel point startPt endPt)], locals := l8, jvmHeap := jh, heap := () }) := by
    have hprog :
        GeometryExtensionsKt_sideOfLine_prog =
          unpackOffsetXBlock 4 6 ++
            (unpackOffsetXBlock 2 6 ++
              (.fsub ::
                (unpackOffsetYBlock 0 6 ++
                  (unpackOffsetYBlock 2 6 ++
                    (.fsub :: .fmul ::
                      (unpackOffsetYBlock 4 6 ++
                        (unpackOffsetYBlock 2 6 ++
                          (.fsub ::
                            (unpackOffsetXBlock 0 6 ++
                              (unpackOffsetXBlock 2 6 ++
                                [.fsub, .fmul, .fsub,
                                 .invokestatic "java/lang/Math" "signum" "(F)F",
                                 .freturn])))))))))) := rfl
    rw [hprog]
    dsimp [initJvmState, Jvm.initJvmState, List.foldl]
    change Jvm.runJvmResFast geomHooks 200 _ 0 _ ⟨0, [], locs0, jh, ()⟩ = _
    rw [show (200 : Nat) = 181 + 19 by omega, runJvmResFast_unpackOffsetXBlock h0_4]
    rw [show (181 : Nat) = 162 + 19 by omega, runJvmResFast_unpackOffsetXBlock h1_2]
    rw [show (162 : Nat) = 161 + 1 by omega, runJvmResFast_fsub]
    rw [show (161 : Nat) = 142 + 19 by omega, runJvmResFast_unpackOffsetYBlock h2_0]
    rw [show (142 : Nat) = 123 + 19 by omega, runJvmResFast_unpackOffsetYBlock h3_2]
    rw [show (123 : Nat) = 122 + 1 by omega, runJvmResFast_fsub]
    rw [show (122 : Nat) = 121 + 1 by omega, runJvmResFast_fmul]
    rw [show (121 : Nat) = 102 + 19 by omega, runJvmResFast_unpackOffsetYBlock h4_4]
    rw [show (102 : Nat) = 83 + 19 by omega, runJvmResFast_unpackOffsetYBlock h5_2]
    rw [show (83 : Nat) = 82 + 1 by omega, runJvmResFast_fsub]
    rw [show (82 : Nat) = 63 + 19 by omega, runJvmResFast_unpackOffsetXBlock h6_0]
    rw [show (63 : Nat) = 44 + 19 by omega, runJvmResFast_unpackOffsetXBlock h7_2]
    rw [show (44 : Nat) = 43 + 1 by omega, runJvmResFast_fsub]
    rw [show (43 : Nat) = 42 + 1 by omega, runJvmResFast_fmul]
    rw [show (42 : Nat) = 41 + 1 by omega, runJvmResFast_fsub]
    rw [show (41 : Nat) = 40 + 1 by omega, Jvm.runJvmResFast_invokestatic_step geomHooks rfl]
    rw [show (40 : Nat) = 39 + 1 by omega, runJvmResFast_freturn]
    rfl
  dsimp only [runJvm]
  rw [Jvm.runJvm_eq_runJvmRes geomHooks geomHooks_iteZero? geomHooks_iteNonZero?,
    Jvm.runJvmRes_of_runJvmResFast0 geomHooks _ _ _ _ rfl hfast]
  rfl

private theorem step_neighbor_iter_head {fieldName : String} {jh : Jvm.JvmHeap Empty}
    {srcArrAddr dstListAddr itAddr : Nat}
    {srcElems : Array JvmVal} {idx : Nat} {dx dy : Int32}
    {locs : Nat → JvmVal}
    (hlt : idx < srcElems.size)
    (hsrc : jh.get? srcArrAddr = some (.objArray "androidx/compose/ui/unit/IntOffset" srcElems))
    (helem : srcElems[idx] = Jvm.JvmVal.boxedLong (packOffset dx dy))
    (hit : jh.get? itAddr = some (.instance "java/util/Iterator"
      [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat idx))]))
    (hidx_lt : idx < 2 ^ 32)
    (hloc5 : locs 5 = .heapRef dstListAddr)
    (hloc7 : locs 7 = .heapRef itAddr)
    {fuel : Nat} :
    Jvm.runJvmResFast geomHooks (fuel + 14) (neighborProgram fieldName) 20 neighborLoopTail
        { pc := 20, stack := [], locals := locs, jvmHeap := jh, heap := () } =
      Jvm.runJvmResFast geomHooks fuel (neighborProgram fieldName) 34 neighborIterMidTail
        { pc := 34
        , stack := []
        , locals := nextIterLocs dstListAddr dx dy locs
        , jvmHeap :=
            jh.set itAddr (.instance "java/util/Iterator"
              [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat (idx + 1)))])
        , heap := () } := by
  have hmod : (UInt32.ofNat idx).toNat = idx := Nat.mod_eq_of_lt hidx_lt
  have hadd1 : UInt32.ofNat idx + 1 = UInt32.ofNat (idx + 1) := by
    apply UInt32.toNat.inj
    simp [UInt32.toNat_add, hmod]
  dsimp [neighborLoopTail]
  -- pc 20: aload 7
  rw [show fuel + 14 = (fuel + 13) + 1 by omega]
  rw [runJvmResFast_aload, hloc7]
  -- pc 21: hasNext
  rw [show fuel + 13 = (fuel + 12) + 1 by omega]
  rw [Jvm.runJvmResFast_invokeinterface_step geomHooks (by
    simp [Jvm.stepInvokeInterfaceGeneric, hit, hsrc,
      show idx % 4294967296 = idx from Nat.mod_eq_of_lt hidx_lt, hlt]
    exact ⟨rfl, rfl, rfl⟩)]
  -- pc 22: ifeq 43 (fallthrough since .i32 1 ≠ 0)
  rw [show fuel + 12 = (fuel + 11) + 1 by omega]
  rw [Jvm.runJvmResFast_ifeq_fallthrough geomHooks rfl]
  -- pc 23: aload 7
  rw [show fuel + 11 = (fuel + 10) + 1 by omega]
  rw [runJvmResFast_aload, hloc7]
  -- pc 24: next
  rw [show fuel + 10 = (fuel + 9) + 1 by omega]
  rw [Jvm.runJvmResFast_invokeinterface_step geomHooks (by
    simp [Jvm.stepInvokeInterfaceGeneric, hit, hsrc,
      show idx % 4294967296 = idx from Nat.mod_eq_of_lt hidx_lt, hlt]
    rw [helem, hadd1]
    exact ⟨rfl, rfl, rfl⟩)]
  -- pc 25: astore 8
  rw [show fuel + 9 = (fuel + 8) + 1 by omega]
  rw [runJvmResFast_astore]
  -- pc 26: aload 5
  rw [show fuel + 8 = (fuel + 7) + 1 by omega]
  rw [runJvmResFast_aload, setLocal_ne _ _ (by omega), hloc5]
  -- pc 27: aload 8
  rw [show fuel + 7 = (fuel + 6) + 1 by omega]
  rw [runJvmResFast_aload, setLocal_self]
  -- pc 28: checkcast IntOffset
  rw [show fuel + 6 = (fuel + 5) + 1 by omega]
  rw [runJvmResFast_checkcast_boxedLong]
  -- pc 29: invokevirtual unbox-impl
  rw [show fuel + 5 = (fuel + 4) + 1 by omega]
  rw [Jvm.runJvmResFast_invokevirtual_step geomHooks (by
    simp [Jvm.stepInvokeVirtualGeneric]
    exact ⟨rfl, rfl, rfl⟩)]
  -- pc 30: lstore 9
  rw [show fuel + 4 = (fuel + 3) + 1 by omega]
  rw [runJvmResFast_lstore]
  -- pc 31: astore 12
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [runJvmResFast_astore]
  -- pc 32: iconst 0
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [runJvmResFast_iconst]
  -- pc 33: istore 11
  rw [runJvmResFast_istore]
  simp only [hadd1]
  rfl

private theorem step_neighbor_iter_tail {fieldName : String} {jh1 : Jvm.JvmHeap Empty}
    {dstArrAddr dstListAddr : Nat} {dstElems : Array JvmVal}
    {dx dy : Int32} {o : UInt64} {locs : Nat → JvmVal}
    (hdstList1 : jh1.get? dstListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef dstArrAddr)]))
    (hdstArr1 : jh1.get? dstArrAddr = some (.objArray "java/lang/Object" dstElems))
    (hloc0 : locs 0 = .i64 o)
    {fuel : Nat} :
    Jvm.runJvmResFast geomHooks (fuel + 9) (neighborProgram fieldName) 34 neighborIterMidTail
        { pc := 34
        , stack := []
        , locals := nextIterLocs dstListAddr dx dy locs
        , jvmHeap := jh1
        , heap := () } =
      Jvm.runJvmResFast geomHooks fuel (neighborProgram fieldName) 20 neighborLoopTail
        { pc := 20
        , stack := []
        , locals := nextIterLocs dstListAddr dx dy locs
        , jvmHeap :=
            jh1.set dstArrAddr
              (.objArray "java/lang/Object" (dstElems.push (Jvm.JvmVal.boxedLong (addPackedOffset (packOffset dx dy) o))))
        , heap := () } := by
  dsimp [neighborIterMidTail]
  -- pc 34: lload 9
  rw [show fuel + 9 = (fuel + 8) + 1 by omega]
  rw [runJvmResFast_lload, nextIterLocs_9]
  -- pc 35: lload 0
  rw [show fuel + 8 = (fuel + 7) + 1 by omega]
  rw [runJvmResFast_lload, nextIterLocs_0 _ _ _ _ _ hloc0]
  -- pc 36: invokestatic plus-qkQi6aY
  rw [show fuel + 7 = (fuel + 6) + 1 by omega]
  have hsum :
      packIntOffset (unpackIntOffsetX (packOffset dx dy) + unpackIntOffsetX o)
          (unpackIntOffsetY (packOffset dx dy) + unpackIntOffsetY o) =
        addPackedOffset (packOffset dx dy) o := rfl
  rw [Jvm.runJvmResFast_invokestatic_step geomHooks (by
    simp [Jvm.stepInvokeStaticGeneric, stepIntOffsetStatic, Jvm.JvmVal.asI64?, hsum]
    exact ⟨rfl, rfl, rfl⟩)]
  -- pc 37: invokestatic box-impl
  rw [show fuel + 6 = (fuel + 5) + 1 by omega]
  rw [Jvm.runJvmResFast_invokestatic_step geomHooks (by
    simp [Jvm.stepInvokeStaticGeneric, stepIntOffsetStatic, Jvm.JvmVal.asI64?]
    exact ⟨rfl, rfl, rfl⟩)]
  -- pc 38: aload 12
  rw [show fuel + 5 = (fuel + 4) + 1 by omega]
  rw [runJvmResFast_aload, nextIterLocs_12]
  -- pc 39: swap
  rw [show fuel + 4 = (fuel + 3) + 1 by omega]
  rw [runJvmResFast_swap]
  -- pc 40: Collection.add
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [Jvm.runJvmResFast_invokeinterface_step geomHooks (by
    simp [Jvm.stepInvokeInterfaceGeneric, Jvm.isArrayElemCompat, Jvm.JvmVal.isRef, hdstList1, hdstArr1]
    exact ⟨rfl, rfl, rfl⟩)]
  -- pc 41: pop
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [runJvmResFast_pop]
  -- pc 42: goto 20
  rw [Jvm.runJvmResFast_goto geomHooks, drop20_neighborProgram]

private theorem step_neighbor_iter {fieldName : String} {jh : Jvm.JvmHeap Empty}
    {srcArrAddr dstArrAddr dstListAddr itAddr : Nat}
    {srcElems dstElems : Array JvmVal} {idx : Nat} {dx dy : Int32} {o : UInt64}
    {locs : Nat → JvmVal}
    (hlt : idx < srcElems.size)
    (hsrc : jh.get? srcArrAddr = some (.objArray "androidx/compose/ui/unit/IntOffset" srcElems))
    (helem : srcElems[idx] = Jvm.JvmVal.boxedLong (packOffset dx dy))
    (hit : jh.get? itAddr = some (.instance "java/util/Iterator"
      [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat idx))]))
    (hdstList : jh.get? dstListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef dstArrAddr)]))
    (hdstArr : jh.get? dstArrAddr = some (.objArray "java/lang/Object" dstElems))
    (hdstList_ne_it : dstListAddr ≠ itAddr)
    (hdstArr_ne_it : dstArrAddr ≠ itAddr)
    (hidx_lt : idx < 2 ^ 32)
    (hloc0 : locs 0 = .i64 o)
    (hloc5 : locs 5 = .heapRef dstListAddr)
    (hloc7 : locs 7 = .heapRef itAddr)
    {fuel : Nat} :
    Jvm.runJvmResFast geomHooks (fuel + 23) (neighborProgram fieldName) 20 neighborLoopTail
        { pc := 20, stack := [], locals := locs, jvmHeap := jh, heap := () } =
      Jvm.runJvmResFast geomHooks fuel (neighborProgram fieldName) 20 neighborLoopTail
        { pc := 20
        , stack := []
        , locals := nextIterLocs dstListAddr dx dy locs
        , jvmHeap :=
            (jh.set itAddr (.instance "java/util/Iterator"
              [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat (idx + 1)))])).set dstArrAddr
              (.objArray "java/lang/Object" (dstElems.push (Jvm.JvmVal.boxedLong (addPackedOffset (packOffset dx dy) o))))
        , heap := () } := by
  let jh1 := jh.set itAddr (.instance "java/util/Iterator"
    [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat (idx + 1)))])
  have hdstList1 : jh1.get? dstListAddr =
      some (.instance "java/util/ArrayList" [("arr", .heapRef dstArrAddr)]) := by
    dsimp [jh1]; rw [Jvm.jvmHeap_get?_set_ne _ _ hdstList_ne_it, hdstList]
  have hdstArr1 : jh1.get? dstArrAddr =
      some (.objArray "java/lang/Object" dstElems) := by
    dsimp [jh1]; rw [Jvm.jvmHeap_get?_set_ne _ _ hdstArr_ne_it, hdstArr]
  rw [show fuel + 23 = (fuel + 9) + 14 by omega]
  rw [step_neighbor_iter_head hlt hsrc helem hit hidx_lt hloc5 hloc7]
  exact step_neighbor_iter_tail hdstList1 hdstArr1 hloc0

private theorem neighbor_loop_run {fieldName : String}
    {srcArrAddr dstArrAddr dstListAddr itAddr : Nat}
    {srcElems : Array JvmVal} {offsets : List (Int32 × Int32)} {o : UInt64}
    (hsrc_size : srcElems.size = offsets.length)
    (hsrc_elems : srcElems.toList = offsets.map (fun (dx, dy) => Jvm.JvmVal.boxedLong (packOffset dx dy)))
    (hsrc_lt32 : offsets.length < 2 ^ 32)
    (hsrc_ne_it : srcArrAddr ≠ itAddr)
    (hsrc_ne_dstArr : srcArrAddr ≠ dstArrAddr)
    (hdstList_ne_it : dstListAddr ≠ itAddr)
    (hdstList_ne_dstArr : dstListAddr ≠ dstArrAddr)
    (hdstArr_ne_it : dstArrAddr ≠ itAddr) :
    ∀ (rem : Nat) (k : Nat) (jh : Jvm.JvmHeap Empty) (dstElems : Array JvmVal) (locs : Nat → JvmVal),
      k ≤ offsets.length →
      rem = offsets.length - k →
      jh.get? srcArrAddr = some (.objArray "androidx/compose/ui/unit/IntOffset" srcElems) →
      jh.get? itAddr = some (.instance "java/util/Iterator"
        [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat k))]) →
      jh.get? dstListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef dstArrAddr)]) →
      jh.get? dstArrAddr = some (.objArray "java/lang/Object" dstElems) →
      dstElems.toList =
        (offsets.take k).map (fun (dx, dy) => Jvm.JvmVal.boxedLong (addPackedOffset (packOffset dx dy) o)) →
      locs 0 = .i64 o →
      locs 5 = .heapRef dstListAddr →
      locs 7 = .heapRef itAddr →
      ∃ jh_end finalElems locs_end,
        jh_end.get? srcArrAddr = some (.objArray "androidx/compose/ui/unit/IntOffset" srcElems) ∧
        jh_end.get? itAddr = some (.instance "java/util/Iterator"
          [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat offsets.length))]) ∧
        jh_end.get? dstListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef dstArrAddr)]) ∧
        jh_end.get? dstArrAddr = some (.objArray "java/lang/Object" finalElems) ∧
        finalElems.toList =
          offsets.map (fun (dx, dy) => Jvm.JvmVal.boxedLong (addPackedOffset (packOffset dx dy) o)) ∧
        locs_end 0 = .i64 o ∧
        locs_end 5 = .heapRef dstListAddr ∧
        locs_end 7 = .heapRef itAddr ∧
        Jvm.runJvmResFast geomHooks (rem * 23 + 10) (neighborProgram fieldName) 20 neighborLoopTail
            { pc := 20, stack := [], locals := locs, jvmHeap := jh, heap := () } =
          Jvm.runJvmResFast geomHooks 10 (neighborProgram fieldName) 20 neighborLoopTail
            { pc := 20, stack := [], locals := locs_end, jvmHeap := jh_end, heap := () } := by
  intro rem
  induction rem with
  | zero =>
    intro k jh dstElems locs hk hrem hsrc hit hdstList hdstArr hdst_elems h0 h5 h7
    have hk_eq : k = offsets.length := by omega
    subst hk_eq
    exact ⟨jh, dstElems, locs, hsrc, hit, hdstList, hdstArr, by simpa using hdst_elems, h0, h5, h7, rfl⟩
  | succ rem' ih =>
    intro k jh dstElems locs hk hrem hsrc hit hdstList hdstArr hdst_elems h0 h5 h7
    have hk_lt : k < offsets.length := by omega
    have hlt_src : k < srcElems.size := by rw [hsrc_size]; exact hk_lt
    let dx := (offsets[k]'hk_lt).1
    let dy := (offsets[k]'hk_lt).2
    have helem : srcElems[k]'hlt_src = Jvm.JvmVal.boxedLong (packOffset dx dy) := by
      have h1 : srcElems[k]'hlt_src = srcElems.toList[k]'(by simpa [hsrc_size] using hk_lt) := rfl
      rw [h1]
      simp [hsrc_elems, List.getElem_map, dx, dy]
    let jh1 := jh.set itAddr (.instance "java/util/Iterator"
      [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat (k + 1)))])
    let dstElems' := dstElems.push (Jvm.JvmVal.boxedLong (addPackedOffset (packOffset dx dy) o))
    let jh2 := jh1.set dstArrAddr (.objArray "java/lang/Object" dstElems')
    let locs' := nextIterLocs dstListAddr dx dy locs
    have hstep := step_neighbor_iter (fieldName := fieldName)
      (fuel := rem' * 23 + 10) hlt_src hsrc helem hit hdstList hdstArr
      hdstList_ne_it hdstArr_ne_it (by omega) h0 h5 h7
    have hsrc2 : jh2.get? srcArrAddr = some (.objArray "androidx/compose/ui/unit/IntOffset" srcElems) := by
      dsimp [jh2, jh1]
      rw [Jvm.jvmHeap_get?_set_ne _ _ hsrc_ne_dstArr, Jvm.jvmHeap_get?_set_ne _ _ hsrc_ne_it, hsrc]
    have hit2 : jh2.get? itAddr = some (.instance "java/util/Iterator"
        [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat (k + 1)))]) := by
      dsimp [jh2, jh1]
      rw [Jvm.jvmHeap_get?_set_ne _ _ hdstArr_ne_it.symm]
      exact Jvm.jvmHeap_get?_set_self hit
    have hdstList2 : jh2.get? dstListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef dstArrAddr)]) := by
      dsimp [jh2, jh1]
      rw [Jvm.jvmHeap_get?_set_ne _ _ hdstList_ne_dstArr, Jvm.jvmHeap_get?_set_ne _ _ hdstList_ne_it, hdstList]
    have hdstArr2 : jh2.get? dstArrAddr = some (.objArray "java/lang/Object" dstElems') := by
      dsimp [jh2, jh1]
      exact Jvm.jvmHeap_get?_set_self (by rw [Jvm.jvmHeap_get?_set_ne _ _ hdstArr_ne_it, hdstArr])
    have hdst_elems' :
        dstElems'.toList =
          (offsets.take (k + 1)).map (fun (dx, dy) => Jvm.JvmVal.boxedLong (addPackedOffset (packOffset dx dy) o)) := by
      dsimp [dstElems']
      rw [Array.toList_push, hdst_elems, List.take_succ_eq_append_getElem hk_lt, List.map_append, List.map_singleton]
    rcases ih (k + 1) jh2 dstElems' locs' hk_lt (by omega) hsrc2 hit2 hdstList2 hdstArr2 hdst_elems'
        (nextIterLocs_0 o dstListAddr dx dy locs h0)
        (nextIterLocs_5 dstListAddr dx dy locs h5)
        (nextIterLocs_7 dx dy locs h7) with
      ⟨jh_end, finalElems, locs_end, hsrc_e, hit_e, hdstList_e, hdstArr_e, hfin_e, h0e, h5e, h7e, hrun⟩
    refine ⟨jh_end, finalElems, locs_end, hsrc_e, hit_e, hdstList_e, hdstArr_e, hfin_e, h0e, h5e, h7e, ?_⟩
    rw [show (rem' + 1) * 23 + 10 = (rem' * 23 + 10) + 23 by omega]
    rw [hstep]
    exact hrun

private theorem mapM_unbox_boxedLong {α : Type} (g : JvmVal → Option UInt64)
    (hg : ∀ v, g (.boxedLong v) = some v) (f : α → UInt64) (xs : List α) :
    List.mapM (g ∘ fun x => Jvm.JvmVal.boxedLong (f x)) xs = some (xs.map f) := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [Function.comp_apply, hg, List.mapM_cons, ih]

private theorem run_neighbor_epilogue {fieldName : String}
    {srcArrAddr dstArrAddr dstListAddr itAddr : Nat}
    {srcElems finalElems : Array JvmVal} {offsets : List (Int32 × Int32)} {o : UInt64}
    {jh_end : Jvm.JvmHeap Empty} {locs_end : Nat → JvmVal}
    (hsrc_size : srcElems.size = offsets.length)
    (hsrc_lt32 : offsets.length < 2 ^ 32)
    (hnodup : offsets.Nodup)
    (hsrc_e : jh_end.get? srcArrAddr = some (.objArray "androidx/compose/ui/unit/IntOffset" srcElems))
    (hit_e : jh_end.get? itAddr = some (.instance "java/util/Iterator"
      [("arr", .heapRef srcArrAddr), ("idx", .i32 (UInt32.ofNat offsets.length))]))
    (hdstList_e : jh_end.get? dstListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef dstArrAddr)]))
    (hdstArr_e : jh_end.get? dstArrAddr = some (.objArray "java/lang/Object" finalElems))
    (hfin_e : finalElems.toList =
      offsets.map (fun (dx, dy) => Jvm.JvmVal.boxedLong (addPackedOffset (packOffset dx dy) o)))
    (h5e : locs_end 5 = .heapRef dstListAddr)
    (h7e : locs_end 7 = .heapRef itAddr) :
    ∃ setAddr st',
      Jvm.runJvmResFast geomHooks 10 (neighborProgram fieldName) 20 neighborLoopTail
          { pc := 20, stack := [], locals := locs_end, jvmHeap := jh_end, heap := () } =
        some (.heapRef setAddr, st') ∧
      extractPackedSet? st'.jvmHeap (.heapRef setAddr) =
        some (offsets.map fun (dx, dy) => addPackedOffset (packOffset dx dy) o) := by
  dsimp [neighborLoopTail]
  -- pc 20: aload 7
  rw [show (10 : Nat) = 9 + 1 by omega]
  rw [runJvmResFast_aload, h7e]
  -- pc 21: hasNext (= 0)
  rw [show (9 : Nat) = 8 + 1 by omega]
  rw [Jvm.runJvmResFast_invokeinterface_step geomHooks (by
    simp [Jvm.stepInvokeInterfaceGeneric, hit_e, hsrc_e,
      show offsets.length % 4294967296 = offsets.length from Nat.mod_eq_of_lt hsrc_lt32,
      show ¬ offsets.length < srcElems.size by rw [hsrc_size]; omega]
    exact ⟨rfl, rfl, rfl⟩)]
  -- pc 22: ifeq 43 (branch!)
  rw [show (8 : Nat) = 7 + 1 by omega]
  rw [Jvm.runJvmResFast_ifeq_branch geomHooks rfl]
  rw [drop43_neighborProgram]
  dsimp [neighborEpilogueTail]
  -- pc 43: aload 5
  rw [show (7 : Nat) = 6 + 1 by omega]
  rw [runJvmResFast_aload, h5e]
  -- pc 44: checkcast List
  rw [show (6 : Nat) = 5 + 1 by omega]
  rw [runJvmResFast_checkcast_instance hdstList_e]
  -- pc 45: nop
  rw [show (5 : Nat) = 4 + 1 by omega]
  rw [runJvmResFast_nop]
  -- pc 46: checkcast Iterable
  rw [show (4 : Nat) = 3 + 1 by omega]
  rw [runJvmResFast_checkcast_instance hdstList_e]
  -- pc 47: invokestatic CollectionsKt.toSet
  have hdedup :
      (dedupJvmVals (Jvm.JvmVal.beqVal emptyEq) finalElems.toList).toArray =
        (offsets.map fun (dx, dy) => Jvm.JvmVal.boxedLong (addPackedOffset (packOffset dx dy) o)).toArray := by
    rw [hfin_e]
    have hmap : offsets.map (fun (dx, dy) =>
        Jvm.JvmVal.boxedLong (Ext := Empty) (addPackedOffset (packOffset dx dy) o)) =
        (offsets.map fun (dx, dy) => addPackedOffset (packOffset dx dy) o).map Jvm.JvmVal.boxedLong := by
      simp [List.map_map]
    rw [hmap, dedupJvmVals_boxedLong_nodup _ (packedOffsets_nodup o offsets hnodup)]
  -- `toSet` only deduplicates by `beqVal` when every element's `equals` is modeled (boxed longs are).
  have hmodeled : finalElems.all (·.equalsModeled jh_end) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    intro v hv
    rw [← Array.mem_toList_iff, hfin_e, List.mem_map] at hv
    obtain ⟨_, _, rfl⟩ := hv
    rfl
  rw [show (3 : Nat) = 2 + 1 by omega]
  rw [Jvm.runJvmResFast_invokestatic_step geomHooks (by
    simp [Jvm.stepInvokeStaticGeneric, Jvm.extractListArray?, hdstList_e, hdstArr_e, hmodeled]
    exact ⟨rfl, rfl, rfl⟩)]
  -- pc 48: areturn
  let dedupArr := (dedupJvmVals (Jvm.JvmVal.beqVal emptyEq) finalElems.toList).toArray
  let setArrAddr := (jh_end.alloc (.objArray "java/lang/Object" dedupArr)).1
  let h1 := (jh_end.alloc (.objArray "java/lang/Object" dedupArr)).2
  let setAddr := (h1.alloc (.instance "java/util/Set" [("arr", .heapRef setArrAddr)])).1
  let h2 := (h1.alloc (.instance "java/util/Set" [("arr", .heapRef setArrAddr)])).2
  refine ⟨setAddr, _, rfl, ?_⟩
  change extractPackedSet? h2 (.heapRef setAddr) = _
  have hget_set : h2.get? setAddr = some (.instance "java/util/Set" [("arr", .heapRef setArrAddr)]) :=
    Jvm.jvmHeap_get?_alloc_self h1 _
  have hget_arr : h2.get? setArrAddr = some (.objArray "java/lang/Object" dedupArr) := by
    dsimp [h2, setArrAddr]
    rw [Jvm.jvmHeap_get?_alloc_old _ _ (Jvm.jvmHeap_alloc_fst_lt jh_end _)]
    exact Jvm.jvmHeap_get?_alloc_self jh_end _
  simp only [extractPackedSet?, hget_set, List.find?]
  simp [hget_arr, dedupArr, hdedup, List.mapM_map]
  exact mapM_unbox_boxedLong _ (fun _ => rfl) _ offsets

private theorem run_neighbor_program {fieldName : String}
    {jh : Jvm.JvmHeap Empty} {srcListAddr srcArrAddr : Nat}
    {srcElems : Array JvmVal} {offsets : List (Int32 × Int32)} (o : UInt64)
    (hstat : jh.getStatic? "com/alexvanyo/composelife/geometry/GeometryExtensionsKt" fieldName = some (.heapRef srcListAddr))
    (hlist : jh.get? srcListAddr = some (.instance "java/util/List" [("arr", .heapRef srcArrAddr)]))
    (harr : jh.get? srcArrAddr = some (.objArray "androidx/compose/ui/unit/IntOffset" srcElems))
    (hsrc_size : srcElems.size = offsets.length)
    (hsrc_elems : srcElems.toList = offsets.map (fun (dx, dy) => Jvm.JvmVal.boxedLong (packOffset dx dy)))
    (hsrc_lt31 : offsets.length < 2 ^ 31)
    (hnodup : offsets.Nodup) :
    ∃ setAddr st',
      runJvmRes (offsets.length * 23 + 30) (neighborProgram fieldName) (initJvmState [(0, .i64 o)] jh) =
        some (.heapRef setAddr, st') ∧
      extractPackedSet? st'.jvmHeap (.heapRef setAddr) =
        some (offsets.map fun (dx, dy) => addPackedOffset (packOffset dx dy) o) := by
  let dstArrAddr := jh.objects.size
  let jh1 := (jh.alloc (.objArray "java/lang/Object" #[])).2
  let dstListAddr := jh.objects.size + 1
  let jh2 := (jh1.alloc (.instance "java/util/ArrayList" [("arr", .heapRef dstArrAddr)])).2
  let itAddr := jh.objects.size + 2
  let jh3 := (jh2.alloc (.instance "java/util/Iterator"
    [("arr", .heapRef srcArrAddr), ("idx", .i32 0)])).2
  have hjh1_sz : jh1.objects.size = jh.objects.size + 1 := by simp [jh1, Jvm.JvmHeap.alloc]
  have hjh2_sz : jh2.objects.size = jh.objects.size + 2 := by simp [jh2, jh1, Jvm.JvmHeap.alloc]
  have hsrc_lt_sz : srcArrAddr < jh.objects.size := Jvm.jvmHeap_get?_some_lt harr
  have hlist_lt_sz : srcListAddr < jh.objects.size := Jvm.jvmHeap_get?_some_lt hlist
  have hsrc_jh2 : jh2.get? srcArrAddr = some (.objArray "androidx/compose/ui/unit/IntOffset" srcElems) := by
    dsimp [jh2, jh1]
    rw [Jvm.jvmHeap_get?_alloc_old _ _ (by simp [Jvm.JvmHeap.alloc]; omega)]
    rw [Jvm.jvmHeap_get?_alloc_old _ _ hsrc_lt_sz]
    exact harr
  have hlist_jh2 : jh2.get? srcListAddr = some (.instance "java/util/List" [("arr", .heapRef srcArrAddr)]) := by
    dsimp [jh2, jh1]
    rw [Jvm.jvmHeap_get?_alloc_old _ _ (by simp [Jvm.JvmHeap.alloc]; omega)]
    rw [Jvm.jvmHeap_get?_alloc_old _ _ hlist_lt_sz]
    exact hlist
  have hsrc_jh3 : jh3.get? srcArrAddr = some (.objArray "androidx/compose/ui/unit/IntOffset" srcElems) := by
    dsimp [jh3]; rw [Jvm.jvmHeap_get?_alloc_old _ _ (by rw [hjh2_sz]; omega)]; exact hsrc_jh2
  have hdstArr_jh3 : jh3.get? dstArrAddr = some (.objArray "java/lang/Object" #[]) := by
    dsimp [jh3, jh2, dstArrAddr]
    rw [Jvm.jvmHeap_get?_alloc_old _ _ (by rw [hjh2_sz]; omega)]
    rw [Jvm.jvmHeap_get?_alloc_old _ _ (by rw [hjh1_sz]; omega)]
    exact Jvm.jvmHeap_get?_alloc_self jh _
  have hdstList_jh3 : jh3.get? dstListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef dstArrAddr)]) := by
    dsimp [jh3, jh2, dstListAddr, dstArrAddr]
    rw [Jvm.jvmHeap_get?_alloc_old _ _ (by rw [hjh2_sz]; omega)]
    rw [← hjh1_sz]
    exact Jvm.jvmHeap_get?_alloc_self jh1 _
  have hit_jh3 : jh3.get? itAddr = some (.instance "java/util/Iterator"
      [("arr", .heapRef srcArrAddr), ("idx", .i32 0)]) := by
    dsimp [jh3, itAddr]
    rw [← hjh2_sz]
    exact Jvm.jvmHeap_get?_alloc_self jh2 _
  let locs0 := (initJvmState [(0, .i64 o)] jh).locals
  let locsAfter10 := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locs0 2 (.heapRef srcListAddr)) 3 (.i32 0)) 4 (.heapRef srcListAddr)
  let locsAfter19 := Jvm.setLocal (Jvm.setLocal (Jvm.setLocal locsAfter10 5 (.heapRef dstListAddr)) 6 (.i32 0)) 7 (.heapRef itAddr)
  have hlocs10_4 : locsAfter10 4 = .heapRef srcListAddr := by simp [locsAfter10, Jvm.setLocal]
  have hlocs19_0 : locsAfter19 0 = .i64 o := rfl
  have hlocs19_5 : locsAfter19 5 = .heapRef dstListAddr := by simp [locsAfter19, Jvm.setLocal]
  have hlocs19_7 : locsAfter19 7 = .heapRef itAddr := by simp [locsAfter19, Jvm.setLocal]
  have hprologue :
      Jvm.runJvmResFast geomHooks (offsets.length * 23 + 30) (neighborProgram fieldName) 0
          (neighborProgram fieldName) (initJvmState [(0, .i64 o)] jh) =
        Jvm.runJvmResFast geomHooks (offsets.length * 23 + 10) (neighborProgram fieldName) 20 neighborLoopTail
          { pc := 20, stack := [], locals := locsAfter19, jvmHeap := jh3, heap := () } := by
    dsimp [neighborProgram, initJvmState, Jvm.initJvmState]
    -- pc 0: getstatic
    rw [show offsets.length * 23 + 30 = (offsets.length * 23 + 29) + 1 by omega]
    rw [runJvmResFast_getstatic hstat]
    dsimp [neighborProgAfter0]
    -- pc 1: checkcast Iterable
    rw [show offsets.length * 23 + 29 = (offsets.length * 23 + 28) + 1 by omega]
    rw [runJvmResFast_checkcast_instance hlist]
    -- pc 2: astore 2
    rw [show offsets.length * 23 + 28 = (offsets.length * 23 + 27) + 1 by omega]
    rw [runJvmResFast_astore]
    -- pc 3: iconst 0
    rw [show offsets.length * 23 + 27 = (offsets.length * 23 + 26) + 1 by omega]
    rw [runJvmResFast_iconst]
    -- pc 4: istore 3
    rw [show offsets.length * 23 + 26 = (offsets.length * 23 + 25) + 1 by omega]
    rw [runJvmResFast_istore]
    -- pc 5: aload 2
    rw [show offsets.length * 23 + 25 = (offsets.length * 23 + 24) + 1 by omega]
    rw [runJvmResFast_aload, setLocal_ne _ _ (by omega), setLocal_self]
    -- pc 6: astore 4
    rw [show offsets.length * 23 + 24 = (offsets.length * 23 + 23) + 1 by omega]
    rw [runJvmResFast_astore]
    -- pc 7: newClass ArrayList
    rw [show offsets.length * 23 + 23 = (offsets.length * 23 + 22) + 1 by omega]
    rw [runJvmResFast_newClass]
    -- pc 8: dup
    rw [show offsets.length * 23 + 22 = (offsets.length * 23 + 21) + 1 by omega]
    rw [runJvmResFast_dup]
    -- pc 9: aload 2
    rw [show offsets.length * 23 + 21 = (offsets.length * 23 + 20) + 1 by omega]
    rw [runJvmResFast_aload, setLocal_ne _ _ (by omega), setLocal_ne _ _ (by omega), setLocal_self]
    -- pc 10: iconst 10
    rw [show offsets.length * 23 + 20 = (offsets.length * 23 + 19) + 1 by omega]
    rw [runJvmResFast_iconst]
    -- pc 11: collectionSizeOrDefault
    rw [show offsets.length * 23 + 19 = (offsets.length * 23 + 18) + 1 by omega]
    rw [Jvm.runJvmResFast_invokestatic_step geomHooks (by
      simp [Jvm.stepInvokeStaticGeneric, Jvm.extractListArray?, hlist, harr]
      exact ⟨rfl, rfl, rfl⟩)]
    -- pc 12: invokespecial ArrayList.<init>(I)V
    have hcap_nn : (UInt32.ofNat srcElems.size).toBitVec.slt 0#32 = false :=
      Jvm.ui32_slt_zero_of_lt srcElems.size (by omega)
    rw [show offsets.length * 23 + 18 = (offsets.length * 23 + 17) + 1 by omega]
    rw [Jvm.runJvmResFast_invokespecial_step geomHooks (by
      simp [Jvm.stepInvokeSpecialGeneric, hcap_nn]
      exact ⟨rfl, rfl, rfl⟩)]
    have h12_arr : (jh.alloc (.objArray "java/lang/Object" #[])).1 = dstArrAddr := rfl
    have h12_heap : (jh.alloc (.objArray "java/lang/Object" #[])).2 = jh1 := rfl
    rw [h12_arr, h12_heap]
    have h12_addr :
        (jh1.alloc (.instance "java/util/ArrayList" [("arr", .heapRef dstArrAddr)])).1 = dstListAddr := hjh1_sz
    have h12_heap2 :
        (jh1.alloc (.instance "java/util/ArrayList" [("arr", .heapRef dstArrAddr)])).2 = jh2 := rfl
    rw [h12_addr, h12_heap2]
    -- pc 13: checkcast Collection
    have hdstList_jh2 : jh2.get? dstListAddr = some (.instance "java/util/ArrayList" [("arr", .heapRef dstArrAddr)]) := by
      dsimp [jh2, dstListAddr, dstArrAddr]
      rw [← hjh1_sz]
      exact Jvm.jvmHeap_get?_alloc_self jh1 _
    rw [show offsets.length * 23 + 17 = (offsets.length * 23 + 16) + 1 by omega]
    rw [runJvmResFast_checkcast_instance hdstList_jh2]
    -- pc 14: astore 5
    rw [show offsets.length * 23 + 16 = (offsets.length * 23 + 15) + 1 by omega]
    rw [runJvmResFast_astore]
    -- pc 15: iconst 0
    rw [show offsets.length * 23 + 15 = (offsets.length * 23 + 14) + 1 by omega]
    rw [runJvmResFast_iconst]
    -- pc 16: istore 6
    rw [show offsets.length * 23 + 14 = (offsets.length * 23 + 13) + 1 by omega]
    rw [runJvmResFast_istore]
    -- pc 17: aload 4
    rw [show offsets.length * 23 + 13 = (offsets.length * 23 + 12) + 1 by omega]
    rw [runJvmResFast_aload, setLocal_ne _ _ (by omega), setLocal_ne _ _ (by omega), setLocal_self]
    -- pc 18: invokeinterface Iterable.iterator
    rw [show offsets.length * 23 + 12 = (offsets.length * 23 + 11) + 1 by omega]
    rw [Jvm.runJvmResFast_invokeinterface_step geomHooks (by
      simp [Jvm.stepInvokeInterfaceGeneric, Jvm.extractListArray?, hlist_jh2, hsrc_jh2]
      exact ⟨rfl, rfl, rfl⟩)]
    have h18_addr :
        (jh2.alloc (.instance "java/util/Iterator" [("arr", .heapRef srcArrAddr), ("idx", .i32 0)])).1 =
          itAddr := hjh2_sz
    have h18_heap :
        (jh2.alloc (.instance "java/util/Iterator" [("arr", .heapRef srcArrAddr), ("idx", .i32 0)])).2 =
          jh3 := rfl
    rw [h18_addr, h18_heap]
    -- pc 19: astore 7
    rw [show offsets.length * 23 + 11 = (offsets.length * 23 + 10) + 1 by omega]
    rw [runJvmResFast_astore]
    rfl
  rcases neighbor_loop_run (fieldName := fieldName) hsrc_size hsrc_elems (by omega)
      (srcArrAddr := srcArrAddr) (dstArrAddr := dstArrAddr) (dstListAddr := dstListAddr) (itAddr := itAddr)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      offsets.length 0 jh3 #[] locsAfter19 (Nat.zero_le _) rfl hsrc_jh3 hit_jh3 hdstList_jh3 hdstArr_jh3
      (by simp) hlocs19_0 hlocs19_5 hlocs19_7 with
    ⟨jh_end, finalElems, locs_end, hsrc_e, hit_e, hdstList_e, hdstArr_e, hfin_e, _h0e, h5e, h7e, hloop⟩
  rcases run_neighbor_epilogue (fieldName := fieldName)
      hsrc_size (by omega) hnodup hsrc_e hit_e hdstList_e hdstArr_e hfin_e h5e h7e with
    ⟨setAddr, st', hepi, hextract⟩
  refine ⟨setAddr, st', ?_, hextract⟩
  exact Jvm.runJvmRes_of_runJvmResFast0 geomHooks _ _ _ _ rfl (hprologue.trans (hloop.trans hepi))

/-- Bridge lemma: `GeometryExtensionsKt.getMooreNeighbors` JVM bytecode matches `getMooreNeighborsModel`. -/
theorem getMooreNeighbors_equiv (o : UInt64) {jh : Jvm.JvmHeap Empty}
    (hlut : HasGeometryNeighborLuts jh) :
    ∃ setAddr st',
      runJvmRes 214 GeometryExtensionsKt_getMooreNeighbors_prog (initJvmState [(0, .i64 o)] jh) =
        some (.heapRef setAddr, st') ∧
      extractPackedSet? st'.jvmHeap (.heapRef setAddr) = some (getMooreNeighborsModel o) := by
  rcases hlut.1 with ⟨listAddr, arrAddr, hstat, hlist, harr⟩
  have hnp : GeometryExtensionsKt_getMooreNeighbors_prog = neighborProgram "mooreNeighborOffsets" := rfl
  have hnd : mooreNeighborOffsetsModel.Nodup := by dsimp [mooreNeighborOffsetsModel]; simp
  have hlen : mooreNeighborOffsetsModel.length * 23 + 30 = 214 := rfl
  rw [hnp, ← hlen]
  simpa [getMooreNeighborsModel] using run_neighbor_program o hstat hlist harr
    (by simp) (by simp) (by decide) hnd

/-- Bridge lemma: `GeometryExtensionsKt.getVonNeumannNeighbors` JVM bytecode matches `getVonNeumannNeighborsModel`. -/
theorem getVonNeumannNeighbors_equiv (o : UInt64) {jh : Jvm.JvmHeap Empty}
    (hlut : HasGeometryNeighborLuts jh) :
    ∃ setAddr st',
      runJvmRes 122 GeometryExtensionsKt_getVonNeumannNeighbors_prog (initJvmState [(0, .i64 o)] jh) =
        some (.heapRef setAddr, st') ∧
      extractPackedSet? st'.jvmHeap (.heapRef setAddr) = some (getVonNeumannNeighborsModel o) := by
  rcases hlut.2 with ⟨listAddr, arrAddr, hstat, hlist, harr⟩
  have hnp : GeometryExtensionsKt_getVonNeumannNeighbors_prog = neighborProgram "vonNeumannNeighborOffsets" := rfl
  have hnd : vonNeumannNeighborOffsetsModel.Nodup := by dsimp [vonNeumannNeighborOffsetsModel]; simp
  have hlen : vonNeumannNeighborOffsetsModel.length * 23 + 30 = 122 := rfl
  rw [hnp, ← hlen]
  simpa [getVonNeumannNeighborsModel] using run_neighbor_program o hstat hlist harr
    (by simp) (by simp) (by decide) hnd

/-- End-to-end JVM bytecode norm equivalence `L∞ ≤ L1 ≤ 2 · L∞` on compiled `GeometryExtensionsKt`. -/
theorem chebyshev_manhattan_norm_equiv_bytecode (p : UInt64)
    (hx : offsetX p ≠ Int32.minValue) (hy : offsetY p ≠ Int32.minValue)
    (hsum : (offsetX p).toInt.natAbs + (offsetY p).toInt.natAbs < 2 ^ 31) :
    ∃ dInf d1 : UInt32,
      runJvm 15 GeometryExtensionsKt_chebyshevDistance_prog (initJvmState [(0, .i64 p)]) = some (.i32 dInf) ∧
      runJvm 15 GeometryExtensionsKt_manhattanDistance_prog (initJvmState [(0, .i64 p)]) = some (.i32 d1) ∧
      dInf.toInt32.toInt ≤ d1.toInt32.toInt ∧
      d1.toInt32.toInt ≤ 2 * dInf.toInt32.toInt := by
  refine ⟨chebyshevDistanceModel p, manhattanDistanceModel p,
    chebyshevDistance_equiv p, manhattanDistance_equiv p, norm_equivalence p hx hy hsum⟩

/-- End-to-end JVM bytecode theorem: executing `<clinit>` then `getMooreNeighbors` produces 8 Chebyshev-unit neighbors. -/
theorem getMooreNeighbors_bytecode_unit_sphere (o : UInt64) :
    ∃ st0 setAddr st1 neighbors,
      runJvmRes 100 GeometryExtensionsKt_clinit_prog (initJvmState [] {}) = some (.unit, st0) ∧
      runJvmRes 214 GeometryExtensionsKt_getMooreNeighbors_prog (initJvmState [(0, .i64 o)] st0.jvmHeap) =
        some (.heapRef setAddr, st1) ∧
      extractPackedSet? st1.jvmHeap (.heapRef setAddr) = some neighbors ∧
      neighbors.length = 8 ∧
      neighbors.Nodup ∧
      ∀ n ∈ neighbors,
        runJvm 15 GeometryExtensionsKt_chebyshevDistance_prog (initJvmState [(0, .i64 (subPackedOffset n o))]) = some (.i32 1) := by
  rcases clinit_GeometryExtensionsKt_equiv with ⟨st0, hclinit, hluts⟩
  rcases getMooreNeighbors_equiv o hluts with ⟨setAddr, st1, hrun, hextract⟩
  refine ⟨st0, setAddr, st1, getMooreNeighborsModel o, hclinit, hrun, hextract,
    (getMooreNeighborsModel_spec o).1, (getMooreNeighborsModel_spec o).2, ?_⟩
  intro n hn
  rw [chebyshevDistance_equiv, getMooreNeighborsModel_chebyshev_one o n hn]

/-- End-to-end JVM bytecode theorem: Von Neumann neighbors from compiled bytecode are 4 Manhattan-unit cells forming a subset of Moore neighbors. -/
theorem getVonNeumannNeighbors_bytecode_unit_sphere_subset (o : UInt64) :
    ∃ st0 vSet mSet stV stM vNeighbors mNeighbors,
      runJvmRes 100 GeometryExtensionsKt_clinit_prog (initJvmState [] {}) = some (.unit, st0) ∧
      runJvmRes 122 GeometryExtensionsKt_getVonNeumannNeighbors_prog (initJvmState [(0, .i64 o)] st0.jvmHeap) =
        some (.heapRef vSet, stV) ∧
      runJvmRes 214 GeometryExtensionsKt_getMooreNeighbors_prog (initJvmState [(0, .i64 o)] st0.jvmHeap) =
        some (.heapRef mSet, stM) ∧
      extractPackedSet? stV.jvmHeap (.heapRef vSet) = some vNeighbors ∧
      extractPackedSet? stM.jvmHeap (.heapRef mSet) = some mNeighbors ∧
      vNeighbors.length = 4 ∧
      vNeighbors.Nodup ∧
      (∀ n ∈ vNeighbors,
        runJvm 15 GeometryExtensionsKt_manhattanDistance_prog (initJvmState [(0, .i64 (subPackedOffset n o))]) = some (.i32 1)) ∧
      (∀ n ∈ vNeighbors, n ∈ mNeighbors) := by
  rcases clinit_GeometryExtensionsKt_equiv with ⟨st0, hclinit, hluts⟩
  rcases getVonNeumannNeighbors_equiv o hluts with ⟨vSet, stV, hrunV, hextractV⟩
  rcases getMooreNeighbors_equiv o hluts with ⟨mSet, stM, hrunM, hextractM⟩
  refine ⟨st0, vSet, mSet, stV, stM, getVonNeumannNeighborsModel o, getMooreNeighborsModel o,
    hclinit, hrunV, hrunM, hextractV, hextractM,
    (getVonNeumannNeighborsModel_spec o).1, (getVonNeumannNeighborsModel_spec o).2, ?_,
    getVonNeumannNeighborsModel_subset_moore o⟩
  intro n hn
  rw [manhattanDistance_equiv, getVonNeumannNeighborsModel_manhattan_one o n hn]

end Geometry.KotlinJvmVerification
