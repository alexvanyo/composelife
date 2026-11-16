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

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

/-! ### Family 3: FlatHashLife keys/cursor + Life106 + Plaintext -/

private theorem setLocal_eq_self {locs : Nat → JvmVal} {idx : Nat} {val : JvmVal}
    (h : locs idx = val) : setLocal locs idx val = locs := by
  funext i; dsimp [setLocal]; split <;> simp_all

private theorem jvmHeap_alloc_set_self {Ext : Type} (jh : Jvm.JvmHeap Ext) (x y : Jvm.HeapObj Ext) :
    (jh.alloc x).snd.set jh.objects.size y = (jh.alloc y).snd := by
  simp only [Jvm.JvmHeap.alloc, Jvm.JvmHeap.set]
  have hlt : jh.objects.size < (jh.objects.push x).size := by simp [Array.size_push]
  simp only [hlt, ↓reduceDIte]
  congr 1
  ext i h1 h2
  · simp [Array.size_set, Array.size_push]
  · simp only [Array.getElem_set, Array.getElem_push]
    split
    · split <;> first | rfl | omega
    · simp only [Array.size_set, Array.size_push] at h1 h2
      split
      · rfl
      · rename_i hne hlti
        have hltj : i < jh.objects.size := by omega
        exact absurd hltj hlti

private theorem jvmHeap_set_size {Ext : Type} (jh : Jvm.JvmHeap Ext) (idx : Nat) (obj : Jvm.HeapObj Ext) :
    (jh.set idx obj).objects.size = jh.objects.size := by
  simp only [Jvm.JvmHeap.set]
  split <;> simp [Array.size_set]

private theorem jvmHeap_alloc_size {Ext : Type} (jh : Jvm.JvmHeap Ext) (obj : Jvm.HeapObj Ext) :
    (jh.alloc obj).snd.objects.size = jh.objects.size + 1 := by
  simp [Jvm.JvmHeap.alloc, Array.size_push]

private theorem compareUnsigned_slt_zero (a b : UInt32) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32 = decide (a < b) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b <;> simp [h1, h2]

private theorem compareUnsigned64_slt_zero (a b : UInt64) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32 = decide (a < b) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b <;> simp [h1, h2]

private theorem compareUnsigned64_sle_zero (a b : UInt64) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.sle 0#32 = decide (a ≤ b) := by
  by_cases h1 : a == b
  · have hab : a = b := LawfulBEq.eq_of_beq h1; subst hab; simp
  · by_cases h2 : a < b
    · have hl : a ≤ b := UInt64.le_of_lt h2; simp [h1, h2, hl]
    · have hn : ¬(a ≤ b) := by
        intro hle
        have hab : a = b := UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by
          have hle' : a.toBitVec.toNat ≤ b.toBitVec.toNat := UInt64.le_iff_toNat_le.mp hle
          have hlt' : ¬(a.toBitVec.toNat < b.toBitVec.toNat) := fun h => h2 (UInt64.lt_iff_toNat_lt.mpr h)
          exact Nat.le_antisymm hle' (Nat.le_of_not_lt hlt')))
        exact h1 (beq_iff_eq.mpr hab)
      simp [h1, h2, hn]

private theorem U64ListRep_encodeU64List (jh : Jvm.JvmHeap AlgExt) (xs : List UInt64) :
    let (v, jh') := encodeU64List jh xs
    U64ListRep jh' v xs ∧ jh'.objects.size = jh.objects.size + xs.length + 1 := by
  induction xs generalizing jh with
  | nil =>
    dsimp [encodeU64List]
    refine ⟨.nil _ _ (jvmHeap_get?_alloc_self _ _), by simp [Jvm.JvmHeap.alloc]⟩
  | cons hd tl ih =>
    dsimp [encodeU64List]
    have hih := ih jh
    rcases henc : encodeU64List jh tl with ⟨tlV, jh1⟩
    rw [henc] at hih
    dsimp only at hih ⊢
    rcases hih with ⟨hrep, hsz⟩
    have hal := U64ListRep.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .boxedULong hd, tlV]) hrep
    refine ⟨.cons _ jh1.objects.size hd tl tlV (jvmHeap_get?_alloc_self _ _) hal, ?_⟩
    simp [Jvm.JvmHeap.alloc, hsz]; omega

private theorem U64ListRep_encodeU64List_preserves
    {jh : Jvm.JvmHeap AlgExt} {v : JvmVal} {xs : List UInt64} (ys : List UInt64)
    (h : U64ListRep jh v xs) :
    U64ListRep (encodeU64List jh ys).2 v xs := by
  induction ys generalizing jh with
  | nil =>
    dsimp [encodeU64List]
    exact U64ListRep.alloc _ h
  | cons hd tl ih =>
    dsimp [encodeU64List]
    exact U64ListRep.alloc _ (ih h)

private theorem U64ListRep_encodeU64List_size_le (jh : Jvm.JvmHeap AlgExt) (xs : List UInt64) :
    jh.objects.size ≤ (encodeU64List jh xs).2.objects.size := by
  have h := (U64ListRep_encodeU64List jh xs).2
  omega

private theorem stepStatic_longCompareUnsigned_heap
    {pc : Nat} {a b : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .i64 b :: .i64 a :: rest, locs, jh, hp⟩
        "java/lang/Long" "compareUnsigned" "(JJ)I" =
      .inl (some ⟨pc + 1,
        .i32 (if a == b then 0 else if a < b then 4294967295 else 1) :: rest, locs, jh, hp⟩) := rfl

private theorem stepVirtual_ulong_unbox_heap
    {pc : Nat} {v : UInt64} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .boxedULong v :: rest, locs, jh, hp⟩
        "kotlin/ULong" "unbox-impl" "()J" =
      .inl (some ⟨pc + 1, .i64 v :: rest, locs, jh, hp⟩) := rfl

private theorem stepSpecial_pair_init_heap
    {pc : Nat} {a b : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial ⟨pc, b :: a :: .allocRef "kotlin/Pair" :: .allocRef "kotlin/Pair" :: rest, locs, jh, hp⟩
        "kotlin/Pair" "<init>" "(Ljava/lang/Object;Ljava/lang/Object;)V" =
      .inl (some ⟨pc + 1, .pair a b :: rest, locs, jh, hp⟩) := rfl

private theorem stepStatic_splitKeys_heap
    {pc : Nat} {keysVal nwVal neVal swVal seVal : JvmVal} {midY midX : UInt64}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {keys nw ne sw se : List UInt64}
    (hkeys : decodeU64List jh (jh.objects.size + 2) keysVal = some keys)
    (hnw : decodeU64List jh (jh.objects.size + 2) nwVal = some nw)
    (hne : decodeU64List jh (jh.objects.size + 2) neVal = some ne)
    (hsw : decodeU64List jh (jh.objects.size + 2) swVal = some sw)
    (hse : decodeU64List jh (jh.objects.size + 2) seVal = some se) :
    stepInvokeStatic ⟨pc, seVal :: swVal :: neVal :: nwVal :: .i64 midY :: .i64 midX :: keysVal :: rest,
        locs, jh, hp⟩
        "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt" "f_Algorithm_splitKeys-0vDo7DQ"
        "(Ljava/lang/Object;JJLjava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)Lkotlin/Pair;" =
      let r := Algorithm.splitKeys keys midX midY nw ne sw se
      let (nwV, h1) := encodeU64List jh r.1
      let (neV, h2) := encodeU64List h1 r.2.1
      let (swV, h3) := encodeU64List h2 r.2.2.1
      let (seV, h4) := encodeU64List h3 r.2.2.2
      .inl (some ⟨pc + 1, .pair nwV (.pair neV (.pair swV seV)) :: rest, locs, h4, hp⟩) := by
  refine Eq.trans (b :=
    let fuel := jh.objects.size + 2
    match decodeU64List jh fuel keysVal, decodeU64List jh fuel nwVal, decodeU64List jh fuel neVal,
          decodeU64List jh fuel swVal, decodeU64List jh fuel seVal with
    | some keys, some nw, some ne, some sw, some se =>
      let r := Algorithm.splitKeys keys midX midY nw ne sw se
      let (nwV, h1) := encodeU64List jh r.1
      let (neV, h2) := encodeU64List h1 r.2.1
      let (swV, h3) := encodeU64List h2 r.2.2.1
      let (seV, h4) := encodeU64List h3 r.2.2.2
      .inl (some ⟨pc + 1, .pair nwV (.pair neV (.pair swV seV)) :: rest, locs, h4, hp⟩)
    | _, _, _, _, _ => .inr none) rfl ?_
  dsimp only
  rw [hkeys, hnw, hne, hsw, hse]

private theorem stepStatic_leafFromKeys_heap
    {pc : Nat} {leaf y0 x0 : UInt64} {keysVal : JvmVal}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {keys : List UInt64}
    (hkeys : decodeU64List jh (jh.objects.size + 2) keysVal = some keys) :
    stepInvokeStatic ⟨pc, .i64 leaf :: .i64 y0 :: .i64 x0 :: keysVal :: rest, locs, jh, hp⟩
        "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt" "f_Algorithm_leafFromKeys-tc6d2E8" "(Ljava/lang/Object;JJJ)J" =
      .inl (some ⟨pc + 1, .i64 (Algorithm.leafFromKeys keys x0 y0 leaf) :: rest,
        locs, jh, hp⟩) := by
  refine Eq.trans (b := match decodeU64List jh (jh.objects.size + 2) keysVal with
    | some keys => .inl (some ⟨pc + 1, .i64 (Algorithm.leafFromKeys keys x0 y0 leaf) :: rest,
        locs, jh, hp⟩)
    | none => .inr none) rfl ?_
  rw [hkeys]

private theorem stepStatic_keysToMacroCell_heap
    {pc : Nat} {empty : Algorithm.MacroCell} {h : UInt32} {y0 x0 : UInt64} {keysVal : JvmVal}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {keys : List UInt64}
    (hkeys : decodeU64List jh (jh.objects.size + 2) keysVal = some keys) :
    stepInvokeStatic ⟨pc, .ext (.mc empty) :: .i32 h :: .i64 y0 :: .i64 x0 :: keysVal :: rest, locs, jh, hp⟩
        "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt" "f_Algorithm_keysToMacroCell-kVUmbH8"
        "(Ljava/lang/Object;JJILcom/alexvanyo/composelife/model/MacroCell;)Lcom/alexvanyo/composelife/model/MacroCell;" =
      .inl (some ⟨pc + 1,
        .ext (.mc (Algorithm.keysToMacroCell keys x0 y0 h empty)) :: rest,
        locs, jh, hp⟩) := by
  refine Eq.trans (b := match decodeU64List jh (jh.objects.size + 2) keysVal with
    | some keys => .inl (some ⟨pc + 1,
        .ext (.mc (Algorithm.keysToMacroCell keys x0 y0 h empty)) :: rest,
        locs, jh, hp⟩)
    | none => .inr none) rfl ?_
  rw [hkeys]

private theorem stepStatic_relativeKeysLoop_heap
    {pc : Nat} {accVal : JvmVal} {minY minX : UInt64} {limit i : UInt32} {cId : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena} {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {cells : Array UInt64} {acc : List UInt64}
    (hu : u64[cId]? = some cells)
    (hacc : decodeU64List jh (jh.objects.size + 2) accVal = some acc) :
    stepInvokeStatic ⟨pc, accVal :: .i64 minY :: .i64 minX :: .i32 limit :: .i32 i :: .ext (.u64Ref cId) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩
        "com/alexvanyo/composelife/algorithm/FlatHashLifeLeanKt" "f_Algorithm_relativeKeysLoop-CBMCY-A"
        "([JIIJJLjava/lang/Object;)Ljava/lang/Object;" =
      let res := Algorithm.relativeKeysLoop cells i limit minX minY acc
      let (resVal, h') := encodeU64List jh res
      .inl (some ⟨pc + 1, resVal :: rest, locs, h', ⟨ar, u64, asc⟩⟩) := by
  refine Eq.trans (b := match u64[cId]?, decodeU64List jh (jh.objects.size + 2) accVal with
    | some cells, some acc =>
      let res := Algorithm.relativeKeysLoop cells i limit minX minY acc
      let (resVal, h') := encodeU64List jh res
      .inl (some ⟨pc + 1, resVal :: rest, locs, h', ⟨ar, u64, asc⟩⟩)
    | _, _ => .inr none) rfl ?_
  rw [hu, hacc]

/-! ### FlatHashLifeArena.cellCursorStart -/

def decodeCellFrame (jh : Jvm.JvmHeap AlgExt) : JvmVal → Option Algorithm.CellFrame
  | .heapRef addr =>
    match jh.get? addr with
    | some (.instance "com/alexvanyo/composelife/algorithm/CellFrame$Node" flds) =>
      match List.lookup "f0" flds, List.lookup "f1" flds, List.lookup "f2" flds, List.lookup "f3" flds with
      | some (.i32 f0), some (.i64 f1), some (.i64 f2), some (.i32 f3) =>
        some (.node f0 f1.toInt64 f2.toInt64 f3)
      | _, _, _, _ => none
    | _ => none
  | _ => none

def decodeCellFrames (jh : Jvm.JvmHeap AlgExt) : Nat → JvmVal → Option (List Algorithm.CellFrame)
  | 0, _ => none
  | fuel + 1, .heapRef addr =>
    match jh.get? addr with
    | some (.objArray _ elems) =>
      if _ : 0 < elems.size then
        match elems[0] with
        | .boxedInt 0 => some []
        | .boxedInt 1 =>
          if _ : 2 < elems.size then
            match decodeCellFrame jh elems[1], decodeCellFrames jh fuel elems[2] with
            | some f, some tl => some (f :: tl)
            | _, _ => none
          else none
        | _ => none
      else none
    | _ => none
  | _, _ => none

theorem cellCursorStart___redArg_equiv
    (arena : Algorithm.FlatHashLifeArena) (rootId : UInt32) (ox oy : Int32)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
    ∃ st', runJvmResFast 80 f_Algorithm_FlatHashLifeArena_cellCursorStart___redArg_prog 0
        f_Algorithm_FlatHashLifeArena_cellCursorStart___redArg_prog
        ⟨0, [], setLocal (setLocal (setLocal locs 0 (.i32 rootId)) 1 (.i32 ox.toUInt32)) 2 (.i32 oy.toUInt32), jh, hp⟩ =
      some (.heapRef jh.objects.size, st') ∧
      decodeCellFrames st'.jvmHeap 3 (.heapRef jh.objects.size) =
        some (arena.cellCursorStart rootId ox oy) := by
  let nodeObj : Jvm.HeapObj AlgExt :=
    .instance "com/alexvanyo/composelife/algorithm/CellFrame$Node"
      [("f0", .i32 rootId),
       ("f1", .i64 (UInt64.ofBitVec (BitVec.signExtend 64 ox.toUInt32.toBitVec))),
       ("f2", .i64 (UInt64.ofBitVec (BitVec.signExtend 64 oy.toUInt32.toBitVec))),
       ("f3", .i32 64)]
  let nilObj : Jvm.HeapObj AlgExt := .objArray "java/lang/Object" #[.boxedInt 0]
  let hdObj : Jvm.HeapObj AlgExt :=
    .objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1), .heapRef (jh.objects.size + 2)]
  let h0 := (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 1, .null, .null])).snd
  let h1 := ((h0.alloc nodeObj).snd.set jh.objects.size
    (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1), .null]))
  let h2 := (h1.alloc nilObj).snd
  let h3 := h2.set jh.objects.size hdObj
  have hsz0 : h0.objects.size = jh.objects.size + 1 := jvmHeap_alloc_size _ _
  have hsz1 : h1.objects.size = jh.objects.size + 2 := by
    dsimp [h1, h0]
    rw [jvmHeap_set_size, jvmHeap_alloc_size, jvmHeap_alloc_size]
  have hsz2 : h2.objects.size = jh.objects.size + 3 := by
    dsimp [h2]
    rw [jvmHeap_alloc_size, hsz1]
  have hget0 : (h0.alloc nodeObj).snd.get? jh.objects.size =
      some (.objArray "java/lang/Object" #[.boxedInt 1, .null, .null]) := by
    rw [jvmHeap_get?_alloc_lt _ _ (by rw [hsz0]; omega)]
    exact jvmHeap_get?_alloc_self _ _
  have hget3 : h2.get? jh.objects.size =
      some (.objArray "java/lang/Object" #[.boxedInt 1, .heapRef (jh.objects.size + 1), .null]) := by
    dsimp [h2]
    rw [jvmHeap_get?_alloc_lt _ _ (by rw [hsz1]; omega)]
    exact jvmHeap_get?_set_self hget0
  have hrun : runJvmResFast 80 f_Algorithm_FlatHashLifeArena_cellCursorStart___redArg_prog 0
      f_Algorithm_FlatHashLifeArena_cellCursorStart___redArg_prog
      ⟨0, [], setLocal (setLocal (setLocal locs 0 (.i32 rootId)) 1 (.i32 ox.toUInt32)) 2 (.i32 oy.toUInt32), jh, hp⟩ =
      some (.heapRef jh.objects.size,
        ⟨34, [.heapRef jh.objects.size],
          setLocal (setLocal (setLocal (setLocal (setLocal locs 0 (.i32 rootId))
            1 (.i32 ox.toUInt32)) 2 (.i32 oy.toUInt32))
            3 (.heapRef jh.objects.size)) 4 (.heapRef (jh.objects.size + 2)),
          h3, hp⟩) := by
    split_res_fuel 1
    heap_step_blk f_Algorithm_FlatHashLifeArena_cellCursorStart___redArg_prog
    rw [runJvmResFast_anewarray_obj (hslt := by decide)]
    split_res_fuel 5
    heap_step_blk f_Algorithm_FlatHashLifeArena_cellCursorStart___redArg_prog
    rw [runJvmResFast_aastore (hget := jvmHeap_get?_alloc_self _ _) (hslt := by decide) (hlt := by decide)]
    rw [show (Array.replicate (UInt32.toNat 3) JvmVal.null).set (UInt32.toNat 0) (JvmVal.boxedInt 1) =
        #[.boxedInt 1, .null, .null] from rfl]
    rw [jvmHeap_alloc_set_self]
    split_res_fuel 15
    heap_step_blk f_Algorithm_FlatHashLifeArena_cellCursorStart___redArg_prog
    rw [runJvmResFast_invokespecial_step (hs := stepSpecial_cellFrameNode_init)]
    dsimp only
    rw [runJvmResFast_aastore (hget := hget0) (hslt := by decide) (hlt := by decide)]
    rw [hsz0]
    rw [show (#[.boxedInt 1, .null, .null] : Array JvmVal).set (UInt32.toNat 1) (.heapRef (jh.objects.size + 1)) =
        #[.boxedInt 1, .heapRef (jh.objects.size + 1), .null] from rfl]
    split_res_fuel 6
    heap_step_blk f_Algorithm_FlatHashLifeArena_cellCursorStart___redArg_prog
    rw [runJvmResFast_anewarray_obj (hslt := by decide)]
    split_res_fuel 5
    heap_step_blk f_Algorithm_FlatHashLifeArena_cellCursorStart___redArg_prog
    rw [runJvmResFast_aastore (hget := jvmHeap_get?_alloc_self _ _) (hslt := by decide) (hlt := by decide)]
    dsimp only
    rw [show (Array.replicate (UInt32.toNat 1) JvmVal.null).set (UInt32.toNat 0) (JvmVal.boxedInt 0) =
        #[.boxedInt 0] from rfl]
    rw [jvmHeap_alloc_set_self, hsz1]
    split_res_fuel 3
    heap_step_blk f_Algorithm_FlatHashLifeArena_cellCursorStart___redArg_prog
    dsimp only
    rw [runJvmResFast_aastore (hget := hget3) (hslt := by decide) (hlt := by simp)]
    rw [show (#[.boxedInt 1, .heapRef (jh.objects.size + 1), .null] : Array JvmVal).set (UInt32.toNat 2)
        (.heapRef (jh.objects.size + 2)) =
        #[.boxedInt 1, .heapRef (jh.objects.size + 1), .heapRef (jh.objects.size + 2)] from rfl]
    split_res_fuel 2
    rfl
  refine ⟨_, hrun, ?_⟩
  dsimp only [Algorithm.FlatHashLifeArena.cellCursorStart]
  have hh3_0 : h3.get? jh.objects.size = some hdObj :=
    jvmHeap_get?_set_self hget3
  have hh3_1 : h3.get? (jh.objects.size + 1) = some nodeObj := by
    dsimp [h3, h2]
    rw [jvmHeap_get?_set_ne _ _ (by omega)]
    rw [jvmHeap_get?_alloc_lt _ _ (by rw [hsz1]; omega)]
    dsimp [h1]
    rw [jvmHeap_get?_set_ne _ _ (by omega)]
    rw [← hsz0]
    exact jvmHeap_get?_alloc_self _ _
  have hh3_2 : h3.get? (jh.objects.size + 2) = some nilObj := by
    dsimp [h3, h2]
    rw [jvmHeap_get?_set_ne _ _ (by omega)]
    rw [← hsz1]
    exact jvmHeap_get?_alloc_self _ _
  have harr0 : (#[JvmVal.boxedInt 1, .heapRef (jh.objects.size + 1), .heapRef (jh.objects.size + 2)] :
      Array JvmVal)[0] = .boxedInt 1 := rfl
  have harr1 : (#[JvmVal.boxedInt 1, .heapRef (jh.objects.size + 1), .heapRef (jh.objects.size + 2)] :
      Array JvmVal)[1] = .heapRef (jh.objects.size + 1) := rfl
  have harr2 : (#[JvmVal.boxedInt 1, .heapRef (jh.objects.size + 1), .heapRef (jh.objects.size + 2)] :
      Array JvmVal)[2] = .heapRef (jh.objects.size + 2) := rfl
  have hdec2 : decodeCellFrames h3 2 (.heapRef (jh.objects.size + 2)) = some [] := by
    dsimp only [decodeCellFrames]
    rw [hh3_2]
    dsimp only [nilObj]
    have ha0 : (#[JvmVal.boxedInt 0] : Array JvmVal)[0] = .boxedInt 0 := rfl
    simp [ha0]
  dsimp only [decodeCellFrames]
  rw [hh3_0]
  dsimp only [hdObj]
  simp [harr0, harr1, harr2, hdec2, decodeCellFrame, hh3_1, nodeObj, List.lookup]

private theorem U64ListRep.isCompat {jh jh' : Jvm.JvmHeap AlgExt} {v : JvmVal} {xs : List UInt64}
    (h : U64ListRep jh v xs) :
    Jvm.isArrayElemCompat algHooks jh' "java/lang/Object" v = true := by
  cases h <;> rfl

/-! ### relativeKeysLoop -/

private theorem relativeKeysLoop_loop (rem fuel : Nat)
    (cId : Nat) (cells : Array UInt64) (i limit : UInt32) (minX minY : UInt64)
    (acc : List UInt64) (accVal : JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hu : u64[cId]? = some cells)
    (hacc : U64ListRep jh accVal acc)
    (hi : i ≤ limit) (hlim : limit.toNat ≤ cells.size) (hlim31 : limit.toNat < 2 ^ 31)
    (hrem : limit.toNat - i.toNat ≤ rem) (hf : rem * 95 + 15 ≤ fuel) :
    ∃ v st', runJvmResFast fuel f_Algorithm_relativeKeysLoop_prog 3 (f_Algorithm_relativeKeysLoop_prog.drop 3)
        ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 0 (.ext (.u64Ref cId)))
          1 (.i32 i)) 2 (.i32 limit)) 3 (.i64 minX)) 5 (.i64 minY)) 7 accVal,
          jh, ⟨ar, u64, asc⟩⟩ =
      some (v, st') ∧
      U64ListRep st'.jvmHeap v (Algorithm.relativeKeysLoop cells i limit minX minY acc) ∧
      st'.heap = ⟨ar, u64, asc⟩ := by
  induction rem generalizing i acc accVal jh fuel locs with
  | zero =>
    have hieq : i = limit := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by
      have h1 := UInt32.le_iff_toNat_le.mp hi
      change i.toNat = limit.toNat; omega))
    subst hieq
    have hcu : (if i == i then (0 : UInt32) else if i < i then 4294967295 else 1).toBitVec.slt 0#32 = false := by
      rw [compareUnsigned_slt_zero]; simp
    have hrun : runJvmResFast fuel f_Algorithm_relativeKeysLoop_prog 3
        (f_Algorithm_relativeKeysLoop_prog.drop 3)
        ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 0 (.ext (.u64Ref cId)))
          1 (.i32 i)) 2 (.i32 i)) 3 (.i64 minX)) 5 (.i64 minY)) 7 accVal,
          jh, ⟨ar, u64, asc⟩⟩ =
        some (accVal, ⟨8, [accVal], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
          0 (.ext (.u64Ref cId))) 1 (.i32 i)) 2 (.i32 i)) 3 (.i64 minX)) 5 (.i64 minY)) 7 accVal,
          jh, ⟨ar, u64, asc⟩⟩) := by
      split_res_fuel 5
      heap_step_blk f_Algorithm_relativeKeysLoop_prog
      simp only [hcu, Bool.false_eq_true, ↓reduceIte]
      split_res_fuel 2
      rfl
    refine ⟨accVal, _, hrun, ?_, rfl⟩
    rw [Algorithm.relativeKeysLoop.eq_1]
    simp [UInt32.lt_irrefl, hacc]
  | succ rem ih =>
    by_cases hlt : i < limit
    · have hlt_nat : i.toNat < limit.toNat := UInt32.lt_iff_toNat_lt.mp hlt
      have hi1_nat : (i + 1).toNat = i.toNat + 1 := ui32_add1_toNat hlt
      have hcu : (if i == limit then (0 : UInt32) else if i < limit then 4294967295 else 1).toBitVec.slt 0#32 = true := by
        rw [compareUnsigned_slt_zero]; simp [hlt]
      let k := cells[i.toNat]!
      let rk := ((k >>> 32 - minX) <<< 32) + ((k &&& 4294967295) - minY)
      let newObj : Jvm.HeapObj AlgExt :=
        .objArray "java/lang/Object" #[.boxedInt 1, .boxedULong rk, accVal]
      let jh' := (jh.alloc newObj).snd
      have hacc' : U64ListRep jh' (.heapRef jh.objects.size) (rk :: acc) :=
        .cons _ jh.objects.size rk acc accVal (jvmHeap_get?_alloc_self _ _) (U64ListRep.alloc _ hacc)
      let locsBase := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
        0 (.ext (.u64Ref cId)))
        1 (.i32 i)) 2 (.i32 limit)) 3 (.i64 minX)) 5 (.i64 minY)) 7 accVal)
        8 (.i64 k)) 10 (.ext (.u64Ref cId))) 11 (.i32 (i + 1))) 12 (.i32 limit))
        13 (.i64 minX)) 15 (.i64 minY)) 18 (.heapRef jh.objects.size))
        17 (.heapRef jh.objects.size)
      have hstep : runJvmResFast fuel f_Algorithm_relativeKeysLoop_prog 3
          (f_Algorithm_relativeKeysLoop_prog.drop 3)
          ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 0 (.ext (.u64Ref cId)))
            1 (.i32 i)) 2 (.i32 limit)) 3 (.i64 minX)) 5 (.i64 minY)) 7 accVal,
            jh, ⟨ar, u64, asc⟩⟩ =
          runJvmResFast (fuel - 72) f_Algorithm_relativeKeysLoop_prog 3
            (f_Algorithm_relativeKeysLoop_prog.drop 3)
            ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locsBase 0 (.ext (.u64Ref cId)))
              1 (.i32 (i + 1))) 2 (.i32 limit)) 3 (.i64 minX)) 5 (.i64 minY)) 7 (.heapRef jh.objects.size),
              jh', ⟨ar, u64, asc⟩⟩ := by
        split_res_fuel 5
        heap_step_blk f_Algorithm_relativeKeysLoop_prog
        simp only [hcu, ↓reduceIte]
        split_res_fuel 4
        heap_step_blk f_Algorithm_relativeKeysLoop_prog
        rw [runJvmResFast_invokestatic_step (hs := stepStatic_ulongArrGetU64_heap hu)]
        dsimp only
        split_res_fuel 20
        heap_step_blk f_Algorithm_relativeKeysLoop_prog
        rw [runJvmResFast_anewarray_obj (hslt := by decide)]
        split_res_fuel 6
        heap_step_blk f_Algorithm_relativeKeysLoop_prog
        rw [runJvmResFast_aastore (hget := jvmHeap_get?_alloc_self _ _) (hslt := by decide) (hlt := by decide)]
        dsimp only
        rw [show (Array.replicate (UInt32.toNat 3) JvmVal.null).set (UInt32.toNat 0) (.boxedInt 1) =
            #[.boxedInt 1, .null, .null] from rfl]
        rw [jvmHeap_alloc_set_self]
        split_res_fuel 32
        heap_step_blk f_Algorithm_relativeKeysLoop_prog
        rw [show ((32 : UInt32) &&& 63).toUInt64 = 32 from rfl]
        rw [runJvmResFast_aastore (hget := jvmHeap_get?_alloc_self _ _) (hslt := by decide) (hlt := by decide)]
        dsimp only
        rw [show (#[.boxedInt 1, .null, .null] : Array JvmVal).set (UInt32.toNat 1) (.boxedULong rk) =
            #[.boxedInt 1, .boxedULong rk, .null] from rfl]
        rw [jvmHeap_alloc_set_self]
        split_res_fuel 6
        heap_step_blk f_Algorithm_relativeKeysLoop_prog
        rw [runJvmResFast_aastore (hget := jvmHeap_get?_alloc_self _ _) (hslt := by decide) (hlt := by simp)
          (hcompat := hacc.isCompat)]
        dsimp only
        rw [show (#[.boxedInt 1, .boxedULong rk, .null] : Array JvmVal).set (UInt32.toNat 2) accVal =
            #[.boxedInt 1, .boxedULong rk, accVal] from rfl]
        rw [jvmHeap_alloc_set_self]
        split_res_fuel 20
        heap_step_blk f_Algorithm_relativeKeysLoop_prog
        rw [Nat.succ_eq_add_one]
        simp only [nat_add_eq_add]
        rw [show fuel - 5 + 1 - 4 + 1 - 20 + 4 - 6 - 32 + 8 - 6 + 2 - 20 + 4 + 1 = fuel - 72 from by omega]
        rfl
      have hih := ih (fuel := fuel - 72) (i := i + 1) (acc := rk :: acc)
        (accVal := .heapRef jh.objects.size) (locs := locsBase) (jh := jh')
        hacc' (UInt32.le_iff_toNat_le.mpr (by rw [hi1_nat]; omega)) (by rw [hi1_nat]; omega) (by omega)
      rcases hih with ⟨v, st', hrun', hrep', hhp'⟩
      refine ⟨v, st', hstep.trans hrun', ?_, hhp'⟩
      rw [Algorithm.relativeKeysLoop.eq_1]
      simp only [hlt, ↓reduceDIte]
      exact hrep'
    · have hieq : i = limit := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by
        have h1 := UInt32.le_iff_toNat_le.mp hi
        have h2 := mt UInt32.lt_iff_toNat_lt.mpr hlt
        change i.toNat = limit.toNat; omega))
      subst hieq
      have hcu : (if i == i then (0 : UInt32) else if i < i then 4294967295 else 1).toBitVec.slt 0#32 = false := by
        rw [compareUnsigned_slt_zero]; simp
      have hrun : runJvmResFast fuel f_Algorithm_relativeKeysLoop_prog 3
          (f_Algorithm_relativeKeysLoop_prog.drop 3)
          ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 0 (.ext (.u64Ref cId)))
            1 (.i32 i)) 2 (.i32 i)) 3 (.i64 minX)) 5 (.i64 minY)) 7 accVal,
            jh, ⟨ar, u64, asc⟩⟩ =
          some (accVal, ⟨8, [accVal], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs
            0 (.ext (.u64Ref cId))) 1 (.i32 i)) 2 (.i32 i)) 3 (.i64 minX)) 5 (.i64 minY)) 7 accVal,
            jh, ⟨ar, u64, asc⟩⟩) := by
        split_res_fuel 5
        heap_step_blk f_Algorithm_relativeKeysLoop_prog
        simp only [hcu, Bool.false_eq_true, ↓reduceIte]
        split_res_fuel 2
        rfl
      refine ⟨accVal, _, hrun, ?_, rfl⟩
      rw [Algorithm.relativeKeysLoop.eq_1]
      simp [UInt32.lt_irrefl, hacc]

theorem relativeKeysLoop_equiv
    (cId : Nat) (cells : Array UInt64) (i limit : UInt32) (minX minY : UInt64)
    (acc : List UInt64) (accVal : JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena) (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hu : u64[cId]? = some cells)
    (hacc : U64ListRep jh accVal acc)
    (hi : i ≤ limit) (hlim : limit.toNat ≤ cells.size) (hlim31 : limit.toNat < 2 ^ 31) :
    ∃ v st', runJvmResFast (limit.toNat * 95 + 25) f_Algorithm_relativeKeysLoop_prog 0
        f_Algorithm_relativeKeysLoop_prog
        ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 0 (.ext (.u64Ref cId)))
          1 (.i32 i)) 2 (.i32 limit)) 3 (.i64 minX)) 5 (.i64 minY)) 7 accVal,
          jh, ⟨ar, u64, asc⟩⟩ =
      some (v, st') ∧
      U64ListRep st'.jvmHeap v (Algorithm.relativeKeysLoop cells i limit minX minY acc) ∧
      st'.heap = ⟨ar, u64, asc⟩ := by
  have hpre : runJvmResFast (limit.toNat * 95 + 25) f_Algorithm_relativeKeysLoop_prog 0
      f_Algorithm_relativeKeysLoop_prog
      ⟨0, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 0 (.ext (.u64Ref cId)))
        1 (.i32 i)) 2 (.i32 limit)) 3 (.i64 minX)) 5 (.i64 minY)) 7 accVal,
        jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast (limit.toNat * 95 + 22) f_Algorithm_relativeKeysLoop_prog 3
        (f_Algorithm_relativeKeysLoop_prog.drop 3)
        ⟨3, [], setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 0 (.ext (.u64Ref cId)))
          1 (.i32 i)) 2 (.i32 limit)) 3 (.i64 minX)) 5 (.i64 minY)) 7 accVal,
          jh, ⟨ar, u64, asc⟩⟩ := by
    rw [show limit.toNat * 95 + 25 = ((limit.toNat * 95 + 22) + 1) + 1 + 1 from by omega]
    conv => lhs; arg 4; rw [f_Algorithm_relativeKeysLoop_prog]
    rw [runJvmResFast_step_nonbranch _ _ _ (.aload 0) _ _ rfl (by simp)]
    dsimp only [stepInstr, Jvm.stepInstr]
    simp only [setLocal, ↓reduceIte]
    rw [runJvmResFast_step_nonbranch _ _ _ (.ldcStr "cells") _ _ rfl (by simp)]
    dsimp only [stepInstr, Jvm.stepInstr]
    simp only [↓reduceIte]
    rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNullParameter rfl)]
    rfl
  rcases relativeKeysLoop_loop limit.toNat (limit.toNat * 95 + 22) cId cells i limit minX minY acc accVal locs
    jh ar u64 asc hu hacc hi hlim hlim31 (by omega) (by omega) with ⟨v, st', hrun, hrep, hhp⟩
  exact ⟨v, st', hpre.trans hrun, hrep, hhp⟩

/-! ### Sub-batch 2A helpers -/

local macro "norm_res_fuel" : tactic =>
  `(tactic| (conv => lhs; try zeta; arg 1; simp only [Nat.succ_eq_add_one, nat_add_eq_add]))

private theorem u64_shl_and63 (a : UInt64) (x : UInt32) :
    a <<< (x &&& (63 : UInt32)).toUInt64 = a <<< x.toUInt64 := by
  apply UInt64.eq_of_toBitVec_eq
  change a.toBitVec <<< ((x &&& 63).toUInt64.toBitVec % 64#64) =
         a.toBitVec <<< (x.toUInt64.toBitVec % 64#64)
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_umod]
  change (x &&& 63).toUInt64.toNat % (64 % 2 ^ 64) = x.toUInt64.toNat % (64 % 2 ^ 64)
  have h64 : (64 % 2 ^ 64 : Nat) = 64 := rfl
  rw [h64, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  change (x.toNat &&& (63 : UInt32).toNat) % 64 = x.toNat % 64
  have h63 : (63 : UInt32).toNat = 2 ^ 6 - 1 := rfl
  rw [h63, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_mod_of_dvd x.toNat (by decide)

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

private theorem jvmHeap_set_set_self {Ext : Type} (jh : Jvm.JvmHeap Ext) (idx : Nat)
    (a b : Jvm.HeapObj Ext) :
    (jh.set idx a).set idx b = jh.set idx b := by
  cases jh with
  | mk objs =>
    simp only [Jvm.JvmHeap.set]
    split <;> rename_i h1
    · have h2 : idx < (objs.set idx a h1).size := by simpa [Array.size_set] using h1
      simp only [h2, ↓reduceDIte, Array.set_set]
    · rfl

private theorem U64ListRep_preserve_alloc_set
    {jh0 : Jvm.JvmHeap AlgExt} {v : JvmVal} {xs : List UInt64} {arr0 arr : Jvm.HeapObj AlgExt}
    (h : U64ListRep jh0 v xs) :
    U64ListRep ((jh0.alloc arr0).2.set jh0.objects.size arr) v xs := by
  induction h with
  | nil addr hget =>
    exact .nil _ addr (by
      have hlt : addr < jh0.objects.size := (Array.getElem?_eq_some_iff.mp hget).1
      rw [jvmHeap_get?_set_ne (jh0.alloc arr0).2 (obj := arr) (by omega), jvmHeap_get?_alloc_lt _ _ hlt]
      exact hget)
  | cons addr hd tl tlVal hget _ ih =>
    exact .cons _ addr hd tl tlVal (by
      have hlt : addr < jh0.objects.size := (Array.getElem?_eq_some_iff.mp hget).1
      rw [jvmHeap_get?_set_ne (jh0.alloc arr0).2 (obj := arr) (by omega), jvmHeap_get?_alloc_lt _ _ hlt]
      exact hget) ih

private theorem splitKeys_cons_heap
    (jh0 : Jvm.JvmHeap AlgExt) (k : UInt64) (oldListV : JvmVal) :
    ((((jh0.alloc (.objArray "java/lang/Object" (Array.replicate 3 .null))).2.set
        jh0.objects.size (.objArray "java/lang/Object" ((Array.replicate 3 .null).set 0 (.boxedInt 1)))).set
        jh0.objects.size (.objArray "java/lang/Object"
          (((Array.replicate 3 .null).set 0 (.boxedInt 1)).set 1 (.boxedULong k)))).set
        jh0.objects.size (.objArray "java/lang/Object"
          ((((Array.replicate 3 .null).set 0 (.boxedInt 1)).set 1 (.boxedULong k)).set 2 oldListV))) =
      (jh0.alloc (.objArray "java/lang/Object" (Array.replicate 3 .null))).2.set jh0.objects.size
        (.objArray "java/lang/Object" #[.boxedInt 1, .boxedULong k, oldListV]) := by
  rw [jvmHeap_set_set_self, jvmHeap_set_set_self]
  rfl

private theorem splitKeys_cons_u64list
    {jh0 : Jvm.JvmHeap AlgExt} {k : UInt64} {oldListV : JvmVal} {oldList : List UInt64}
    (hold : U64ListRep jh0 oldListV oldList) :
    U64ListRep ((jh0.alloc (.objArray "java/lang/Object" (Array.replicate 3 .null))).2.set jh0.objects.size
      (.objArray "java/lang/Object" #[.boxedInt 1, .boxedULong k, oldListV]))
      (.heapRef jh0.objects.size) (k :: oldList) :=
  .cons _ jh0.objects.size k oldList oldListV
    (jvmHeap_get?_set_self (jvmHeap_get?_alloc_self _ _))
    (U64ListRep_preserve_alloc_set hold)

@[irreducible] private def midBox (x : Option (JvmVal × JvmState)) :
    Option (JvmVal × JvmState) := x

private theorem midBox_eq_self (x : Option (JvmVal × JvmState)) : x = midBox x := by
  unfold midBox; rfl

private theorem runRes_chain_box {f : Nat} {prog : List JvmInstr} {pc : Nat} {instrs : List JvmInstr}
    {st : JvmState} {mid : Option (JvmVal × JvmState)} {Q : JvmVal → JvmState → Prop}
    (h1 : runJvmResFast f prog pc instrs st = midBox mid)
    (h2 : ∃ r s, mid = some (r, s) ∧ Q r s) :
    ∃ r s, runJvmResFast f prog pc instrs st = some (r, s) ∧ Q r s := by
  unfold midBox at h1
  exact h1 ▸ h2

private theorem finish_splitKeys_ih {fuel' : Nat} {prog : List JvmInstr} {pc : Nat} {instrs : List JvmInstr}
    {locs' : Nat → JvmVal} {jh jh' : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {nw' ne' sw' se' : List UInt64}
    (hstep :
      ∃ rv st', runJvmResFast fuel' prog pc instrs ⟨0, [], locs', jh', hp⟩ = some (rv, st') ∧
        st'.heap = hp ∧
        ∃ a b c d, rv = .pair a (.pair b (.pair c d)) ∧
          U64ListRep st'.jvmHeap a nw' ∧ U64ListRep st'.jvmHeap b ne' ∧
          U64ListRep st'.jvmHeap c sw' ∧ U64ListRep st'.jvmHeap d se' ∧
          jh'.objects.size ≤ st'.jvmHeap.objects.size)
    (hsz : jh.objects.size ≤ jh'.objects.size) :
    ∃ rv st', runJvmResFast fuel' prog pc instrs ⟨0, [], locs', jh', hp⟩ = some (rv, st') ∧
      st'.heap = hp ∧
      ∃ a b c d, rv = .pair a (.pair b (.pair c d)) ∧
        U64ListRep st'.jvmHeap a nw' ∧ U64ListRep st'.jvmHeap b ne' ∧
        U64ListRep st'.jvmHeap c sw' ∧ U64ListRep st'.jvmHeap d se' ∧
        jh.objects.size ≤ st'.jvmHeap.objects.size := by
  rcases hstep with ⟨rv, st', hr, hhp, a, b, c, d, rveq, ha, hb, hc, hd, hsz'⟩
  exact ⟨rv, st', hr, hhp, a, b, c, d, rveq, ha, hb, hc, hd, Nat.le_trans hsz hsz'⟩

private theorem splitKeys_loop (keys : List UInt64) :
    ∀ fuel midX midY nw ne sw se keysV nwV neV swV seV (locs : Nat → JvmVal)
      (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap),
      U64ListRep jh keysV keys →
      U64ListRep jh nwV nw →
      U64ListRep jh neV ne →
      U64ListRep jh swV sw →
      U64ListRep jh seV se →
      locs 0 = keysV →
      locs 1 = .i64 midX →
      locs 3 = .i64 midY →
      locs 5 = nwV →
      locs 6 = neV →
      locs 7 = swV →
      locs 8 = seV →
      fuel ≥ (keys.length + 1) * 120 →
      ∃ resVal st',
        runJvmResFast fuel f_Algorithm_splitKeys_prog 0 f_Algorithm_splitKeys_prog
          ⟨0, [], locs, jh, hp⟩ =
          some (resVal, st') ∧
        st'.heap = hp ∧
        ∃ nw' ne' sw' se',
          resVal = .pair nw' (.pair ne' (.pair sw' se')) ∧
          U64ListRep st'.jvmHeap nw' (Algorithm.splitKeys keys midX midY nw ne sw se).1 ∧
          U64ListRep st'.jvmHeap ne' (Algorithm.splitKeys keys midX midY nw ne sw se).2.1 ∧
          U64ListRep st'.jvmHeap sw' (Algorithm.splitKeys keys midX midY nw ne sw se).2.2.1 ∧
          U64ListRep st'.jvmHeap se' (Algorithm.splitKeys keys midX midY nw ne sw se).2.2.2 ∧
          jh.objects.size ≤ st'.jvmHeap.objects.size := by
  induction keys with
  | nil =>
    intro fuel midX midY nw ne sw se keysV nwV neV swV seV locs jh hp
      hkeys hnw hne hsw hse h0 h1 h3 h5 h6 h7 h8 hfuel
    rcases hp with ⟨ar, u64, asc⟩
    cases hkeys with
    | nil addr hget =>
      have hrun : ∃ st', runJvmResFast fuel f_Algorithm_splitKeys_prog 0 f_Algorithm_splitKeys_prog
          ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
          some (.pair nwV (.pair neV (.pair swV seV)), st') ∧
          st'.jvmHeap = jh ∧ st'.heap = ⟨ar, u64, asc⟩ := by
        have hlocs : locs = fun n =>
            if n == 0 then .heapRef addr
            else if n == 5 then nwV
            else if n == 6 then neV
            else if n == 7 then swV
            else if n == 8 then seV
            else locs n := by
          funext n
          match n with
          | 0 => exact h0
          | 5 => exact h5
          | 6 => exact h6
          | 7 => exact h7
          | 8 => exact h8
          | 1 | 2 | 3 | 4 | (_ + 9) => rfl
        let locs26 : Nat → JvmVal := fun n =>
          if n == 0 then .heapRef addr
          else if n == 5 then nwV
          else if n == 6 then neV
          else if n == 7 then swV
          else if n == 8 then seV
          else locs n
        refine ⟨⟨26, [.pair nwV (.pair neV (.pair swV seV))], locs26, jh, ⟨ar, u64, asc⟩⟩,
          ?_, rfl, rfl⟩
        split_res_fuel 30
        conv => lhs; rw [hlocs]
        dsimp only [f_Algorithm_splitKeys_prog]
        heap_step_nonbranch_chunks
        norm_res_fuel
        rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
        heap_step_nonbranch_chunks
        norm_res_fuel
        rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
        heap_step_nonbranch_chunks
        norm_res_fuel
        rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
        heap_step_blk f_Algorithm_splitKeys_prog
        rw [show Jvm.tableswitchTarget 0 0 [13, 27] 287 = 13 from by decide]
        norm_res_fuel
        split_res_fuel 14
        rfl
      rcases hrun with ⟨st', hrun, hjh, hhp⟩
      exact ⟨_, st', hrun, hhp, nwV, neV, swV, seV, rfl, hjh.symm ▸ hnw, hjh.symm ▸ hne,
        hjh.symm ▸ hsw, hjh.symm ▸ hse, by rw [hjh]; exact Nat.le_refl _⟩
  | cons k rest ih =>
    intro fuel midX midY nw ne sw se keysV nwV neV swV seV locs jh hp
      hkeys hnw hne hsw hse h0 h1 h3 h5 h6 h7 h8 hfuel
    rcases hp with ⟨ar, u64, asc⟩
    cases hkeys with
    | cons addr _ _ tlVal hget htl =>
      rw [Algorithm.splitKeys.eq_2]
      have hsh : ((32 : UInt32) &&& 63).toUInt64 = 32 := rfl
      let locs0 : Nat → JvmVal := fun n =>
        if n == 0 then .heapRef addr
        else if n == 1 then .i64 midX
        else if n == 3 then .i64 midY
        else if n == 5 then nwV
        else if n == 6 then neV
        else if n == 7 then swV
        else if n == 8 then seV
        else locs n
      have hlocs : locs = locs0 := by
        funext n
        match n with
        | 0 => exact h0
        | 1 => exact h1
        | 3 => exact h3
        | 5 => exact h5
        | 6 => exact h6
        | 7 => exact h7
        | 8 => exact h8
        | 2 | 4 | (_ + 9) => rfl
      by_cases hY : midY ≤ Algorithm.keyLo k <;> by_cases hX : midX ≤ Algorithm.keyHi k
      · have hYge : Algorithm.keyLo k ≥ midY := hY
        have hXge : Algorithm.keyHi k ≥ midX := hX
        simp only [hYge, hXge, ↓reduceIte]
        refine runRes_chain_box (mid := ?mid1) ?h1_1 ?h2_1
        case h1_1 =>
          rw [show fuel = (fuel - 120) + 120 from
            (Nat.sub_add_cancel (by simp only [List.length_cons] at hfuel; omega)).symm]
          rw [hlocs]
          dsimp only [f_Algorithm_splitKeys_prog, locs0]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
          heap_step_blk f_Algorithm_splitKeys_prog; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_instanceof_step (res := 0) rfl]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [ite_eq_left (by decide)]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
          heap_step_nonbranch_chunks
          conv => lhs; arg 5; simp only [Algorithm.keyLo]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [compareUnsigned64_sle_zero]
          rw [ite_eq_left (show decide (midY ≤ k &&& 4294967295) = true from decide_eq_true hY)]
          norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_instanceof_step (res := 0) rfl]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [ite_eq_left (by decide)]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
          heap_step_nonbranch_chunks
          conv => lhs; arg 5; simp only [hsh, Algorithm.keyHi]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [compareUnsigned64_sle_zero]
          rw [ite_eq_left (show decide (midX ≤ k >>> 32) = true from decide_eq_true hX)]
          norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_anewarray_obj (by decide)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aastore (jvmHeap_get?_alloc_self _ _) (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aastore (jvmHeap_get?_set_self (jvmHeap_get?_alloc_self _ _))
            (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aastore
            (jvmHeap_get?_set_self (jvmHeap_get?_set_self (jvmHeap_get?_alloc_self _ _)))
            (by decide) (by simp [UInt32.toNat])
            (hse.isCompat)]
          heap_step_blk f_Algorithm_splitKeys_prog
          norm_res_fuel
          conv => lhs; arg 5; arg 4; erw [splitKeys_cons_heap]
          exact midBox_eq_self _
        case h2_1 =>
          refine finish_splitKeys_ih (ih _ midX midY nw ne sw (k :: se) tlVal nwV neV swV (.heapRef jh.objects.size)
            _ _ ⟨ar, u64, asc⟩ (U64ListRep_preserve_alloc_set htl) (U64ListRep_preserve_alloc_set hnw)
            (U64ListRep_preserve_alloc_set hne) (U64ListRep_preserve_alloc_set hsw)
            (splitKeys_cons_u64list hse) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
          all_goals first
            | (dsimp only [setLocal]; try simp only [show (2 : UInt32).toNat = 2 from by decide]; rfl)
            | (simp only [jvmHeap_set_size, jvmHeap_alloc_size]; omega)
            | (try simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hfuel ⊢; omega)
      · have hYge : Algorithm.keyLo k ≥ midY := hY
        simp only [hYge, hX, ↓reduceIte]
        refine runRes_chain_box (mid := ?mid2) ?h1_2 ?h2_2
        case h1_2 =>
          rw [show fuel = (fuel - 120) + 120 from
            (Nat.sub_add_cancel (by simp only [List.length_cons] at hfuel; omega)).symm]
          rw [hlocs]
          dsimp only [f_Algorithm_splitKeys_prog, locs0]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
          heap_step_blk f_Algorithm_splitKeys_prog; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_instanceof_step (res := 0) rfl]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [ite_eq_left (by decide)]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
          heap_step_nonbranch_chunks
          conv => lhs; arg 5; simp only [Algorithm.keyLo]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [compareUnsigned64_sle_zero]
          rw [ite_eq_left (show decide (midY ≤ k &&& 4294967295) = true from decide_eq_true hY)]
          norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_instanceof_step (res := 0) rfl]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [ite_eq_left (by decide)]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
          heap_step_nonbranch_chunks
          conv => lhs; arg 5; simp only [hsh, Algorithm.keyHi]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [compareUnsigned64_sle_zero]
          rw [ite_eq_right (show ¬decide (midX ≤ k >>> 32) = true from by simp only [decide_eq_true_eq]; exact hX)]
          norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_anewarray_obj (by decide)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aastore (jvmHeap_get?_alloc_self _ _) (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aastore (jvmHeap_get?_set_self (jvmHeap_get?_alloc_self _ _))
            (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aastore
            (jvmHeap_get?_set_self (jvmHeap_get?_set_self (jvmHeap_get?_alloc_self _ _)))
            (by decide) (by simp [UInt32.toNat])
            (hsw.isCompat)]
          heap_step_blk f_Algorithm_splitKeys_prog
          norm_res_fuel
          conv => lhs; arg 5; arg 4; erw [splitKeys_cons_heap]
          exact midBox_eq_self _
        case h2_2 =>
          refine finish_splitKeys_ih (ih _ midX midY nw ne (k :: sw) se tlVal nwV neV (.heapRef jh.objects.size) seV
            _ _ ⟨ar, u64, asc⟩ (U64ListRep_preserve_alloc_set htl) (U64ListRep_preserve_alloc_set hnw)
            (U64ListRep_preserve_alloc_set hne) (splitKeys_cons_u64list hsw)
            (U64ListRep_preserve_alloc_set hse) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
          all_goals first
            | (dsimp only [setLocal]; try simp only [show (2 : UInt32).toNat = 2 from by decide]; rfl)
            | (simp only [jvmHeap_set_size, jvmHeap_alloc_size]; omega)
            | (try simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hfuel ⊢; omega)
      · have hXge : Algorithm.keyHi k ≥ midX := hX
        simp only [hY, hXge, ↓reduceIte]
        refine runRes_chain_box (mid := ?mid3) ?h1_3 ?h2_3
        case h1_3 =>
          rw [show fuel = (fuel - 120) + 120 from
            (Nat.sub_add_cancel (by simp only [List.length_cons] at hfuel; omega)).symm]
          rw [hlocs]
          dsimp only [f_Algorithm_splitKeys_prog, locs0]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
          heap_step_blk f_Algorithm_splitKeys_prog; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_instanceof_step (res := 0) rfl]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [ite_eq_left (by decide)]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
          heap_step_nonbranch_chunks
          conv => lhs; arg 5; simp only [Algorithm.keyLo]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [compareUnsigned64_sle_zero]
          rw [ite_eq_right (show ¬decide (midY ≤ k &&& 4294967295) = true from by simp only [decide_eq_true_eq]; exact hY)]
          norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_instanceof_step (res := 0) rfl]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [ite_eq_left (by decide)]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
          heap_step_nonbranch_chunks
          conv => lhs; arg 5; simp only [hsh, Algorithm.keyHi]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [compareUnsigned64_sle_zero]
          rw [ite_eq_left (show decide (midX ≤ k >>> 32) = true from decide_eq_true hX)]
          norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_anewarray_obj (by decide)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aastore (jvmHeap_get?_alloc_self _ _) (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aastore (jvmHeap_get?_set_self (jvmHeap_get?_alloc_self _ _))
            (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aastore
            (jvmHeap_get?_set_self (jvmHeap_get?_set_self (jvmHeap_get?_alloc_self _ _)))
            (by decide) (by simp [UInt32.toNat])
            (hne.isCompat)]
          heap_step_blk f_Algorithm_splitKeys_prog
          norm_res_fuel
          conv => lhs; arg 5; arg 4; erw [splitKeys_cons_heap]
          exact midBox_eq_self _
        case h2_3 =>
          refine finish_splitKeys_ih (ih _ midX midY nw (k :: ne) sw se tlVal nwV (.heapRef jh.objects.size) swV seV
            _ _ ⟨ar, u64, asc⟩ (U64ListRep_preserve_alloc_set htl) (U64ListRep_preserve_alloc_set hnw)
            (splitKeys_cons_u64list hne) (U64ListRep_preserve_alloc_set hsw)
            (U64ListRep_preserve_alloc_set hse) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
          all_goals first
            | (dsimp only [setLocal]; try simp only [show (2 : UInt32).toNat = 2 from by decide]; rfl)
            | (simp only [jvmHeap_set_size, jvmHeap_alloc_size]; omega)
            | (try simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hfuel ⊢; omega)
      · simp only [hY, hX, ↓reduceIte]
        refine runRes_chain_box (mid := ?mid4) ?h1_4 ?h2_4
        case h1_4 =>
          rw [show fuel = (fuel - 120) + 120 from
            (Nat.sub_add_cancel (by simp only [List.length_cons] at hfuel; omega)).symm]
          rw [hlocs]
          dsimp only [f_Algorithm_splitKeys_prog, locs0]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
          heap_step_blk f_Algorithm_splitKeys_prog; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aaload hget (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_instanceof_step (res := 0) rfl]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [ite_eq_left (by decide)]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
          heap_step_nonbranch_chunks
          conv => lhs; arg 5; simp only [Algorithm.keyLo]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [compareUnsigned64_sle_zero]
          rw [ite_eq_right (show ¬decide (midY ≤ k &&& 4294967295) = true from by simp only [decide_eq_true_eq]; exact hY)]
          norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_instanceof_step (res := 0) rfl]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [ite_eq_left (by decide)]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
          heap_step_nonbranch_chunks
          conv => lhs; arg 5; simp only [hsh, Algorithm.keyHi]
          heap_step_blk f_Algorithm_splitKeys_prog
          rw [compareUnsigned64_sle_zero]
          rw [ite_eq_right (show ¬decide (midX ≤ k >>> 32) = true from by simp only [decide_eq_true_eq]; exact hX)]
          norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_anewarray_obj (by decide)]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aastore (jvmHeap_get?_alloc_self _ _) (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aastore (jvmHeap_get?_set_self (jvmHeap_get?_alloc_self _ _))
            (by decide) (by simp [UInt32.toNat])]
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_aastore
            (jvmHeap_get?_set_self (jvmHeap_get?_set_self (jvmHeap_get?_alloc_self _ _)))
            (by decide) (by simp [UInt32.toNat])
            (hnw.isCompat)]
          heap_step_blk f_Algorithm_splitKeys_prog
          norm_res_fuel
          conv => lhs; arg 5; arg 4; erw [splitKeys_cons_heap]
          exact midBox_eq_self _
        case h2_4 =>
          refine finish_splitKeys_ih (ih _ midX midY (k :: nw) ne sw se tlVal (.heapRef jh.objects.size) neV swV seV
            _ _ ⟨ar, u64, asc⟩ (U64ListRep_preserve_alloc_set htl) (splitKeys_cons_u64list hnw)
            (U64ListRep_preserve_alloc_set hne) (U64ListRep_preserve_alloc_set hsw)
            (U64ListRep_preserve_alloc_set hse) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
          all_goals first
            | (dsimp only [setLocal]; try simp only [show (2 : UInt32).toNat = 2 from by decide]; rfl)
            | (simp only [jvmHeap_set_size, jvmHeap_alloc_size]; omega)
            | (try simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hfuel ⊢; omega)

theorem splitKeys_equiv
    (keys nw ne sw se : List UInt64) (midX midY : UInt64)
    (keysV nwV neV swV seV : JvmVal) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hkeys : U64ListRep jh keysV keys)
    (hnw : U64ListRep jh nwV nw) (hne : U64ListRep jh neV ne)
    (hsw : U64ListRep jh swV sw) (hse : U64ListRep jh seV se)
    (h0 : locs 0 = keysV) (h1 : locs 1 = .i64 midX) (h3 : locs 3 = .i64 midY)
    (h5 : locs 5 = nwV) (h6 : locs 6 = neV) (h7 : locs 7 = swV) (h8 : locs 8 = seV) :
    ∃ resVal st',
      runJvmResFast ((keys.length + 1) * 120) f_Algorithm_splitKeys_prog 0 f_Algorithm_splitKeys_prog
        ⟨0, [], locs, jh, hp⟩ = some (resVal, st') ∧
      st'.heap = hp ∧
      ∃ nw' ne' sw' se',
        resVal = .pair nw' (.pair ne' (.pair sw' se')) ∧
        U64ListRep st'.jvmHeap nw' (Algorithm.splitKeys keys midX midY nw ne sw se).1 ∧
        U64ListRep st'.jvmHeap ne' (Algorithm.splitKeys keys midX midY nw ne sw se).2.1 ∧
        U64ListRep st'.jvmHeap sw' (Algorithm.splitKeys keys midX midY nw ne sw se).2.2.1 ∧
        U64ListRep st'.jvmHeap se' (Algorithm.splitKeys keys midX midY nw ne sw se).2.2.2 ∧
        jh.objects.size ≤ st'.jvmHeap.objects.size :=
  splitKeys_loop keys ((keys.length + 1) * 120) midX midY nw ne sw se keysV nwV neV swV seV locs jh hp
    hkeys hnw hne hsw hse h0 h1 h3 h5 h6 h7 h8 (Nat.le_refl _)

/-! ### leafFromKeys, keysToMacroCell, cellsToMacroCell -/

private theorem u64_shift32_eq_keyHi (k : UInt64) :
    k >>> (32 : UInt32).toUInt64 = Algorithm.keyHi k := rfl

private theorem u64_andMask32_eq_keyLo (k : UInt64) :
    k &&& (4294967295 : UInt64) = Algorithm.keyLo k := rfl

private theorem runJvmResFast_ifle_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : v.toBitVec.sle 0#32 = true) :
    runJvmResFast (f + 1) prog pc (.ifle tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_ifle_branch algHooks hv

private theorem runJvmResFast_ifle_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : v.toBitVec.sle 0#32 = false) :
    runJvmResFast (f + 1) prog pc (.ifle tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_ifle_fallthrough algHooks hv

private theorem runJvmResFast_iflt_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : v.toBitVec.slt 0#32 = true) :
    runJvmResFast (f + 1) prog pc (.iflt tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_iflt_branch algHooks hv

private theorem runJvmResFast_iflt_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : v.toBitVec.slt 0#32 = false) :
    runJvmResFast (f + 1) prog pc (.iflt tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_iflt_fallthrough algHooks hv

private theorem runJvmResFast_ifeq_branch {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hv : v = 0) :
    runJvmResFast (f + 1) prog pc (.ifeq tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_ifeq_branch algHooks hv

private theorem runJvmResFast_goto {f pc tgt : Nat} {prog rest : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.goto tgt :: rest) ⟨pc, stk, locs, jh, hp⟩ =
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_goto algHooks

private theorem runJvmResFast_tableswitch {f pc dflt : Nat} {low : Int32} {targets : List Nat}
    {prog rest : List JvmInstr} {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.tableswitch low targets dflt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      let tgt := Jvm.tableswitchTarget v low targets dflt
      runJvmResFast f prog tgt (prog.drop tgt) ⟨tgt, stk, locs, jh, hp⟩ := by
  rw [runJvmResFast_at_branch_cons (hbr := rfl)]
  exact evalResBranchInstrCons_tableswitch f prog pc low targets dflt rest pc v stk locs jh hp

private theorem cmpUnsigned_sle0_iff (a b : UInt64) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.sle 0#32 =
      decide (a ≤ b) := by
  by_cases heq : a = b
  · subst heq; simp
  · have hne : (a == b) = false := beq_false_of_ne heq
    by_cases hlt : a < b
    · have hle : a ≤ b := UInt64.le_of_lt hlt
      simp [hne, hlt, hle]
    · have hnle : ¬(a ≤ b) := fun h => by
        rcases UInt64.lt_or_eq_of_le h with h1 | h1
        · exact hlt h1
        · exact heq h1
      simp [hne, hlt, hnle]

private theorem cmpUnsigned_slt0_iff (a b : UInt64) :
    (if a == b then (0 : UInt32) else if a < b then 4294967295 else 1).toBitVec.slt 0#32 =
      decide (a < b) := by
  by_cases hlt : a < b
  · have hne : (a == b) = false := beq_false_of_ne (UInt64.ne_of_lt hlt)
    simp [hne, hlt]
  · by_cases heq : a = b
    · subst heq; simp [hlt]
    · have hne : (a == b) = false := beq_false_of_ne heq
      simp [hne, hlt]

private theorem leafFromKeys_pre {fuel : Nat} {k x0 : UInt64} {kId : Nat} {tlVal : JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h0 : locs 0 = .heapRef kId)
    (hgetK : jh.get? kId = some (.objArray "java/lang/Object" #[.boxedInt 1, .boxedULong k, tlVal]))
    (h1 : locs 1 = .i64 x0) (hf : fuel ≥ 130) :
    let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 7 (.boxedULong k))
      8 tlVal) 11 (.boxedULong k)) 12 (.i32 0)) 9 (.i64 k)) 11 (.i64 (Algorithm.keyHi k))
    runJvmResFast fuel f_Algorithm_leafFromKeys_prog 0 f_Algorithm_leafFromKeys_prog
      ⟨0, [], locs, jh, hp⟩ =
    runJvmResFast (fuel - 130 + 85) f_Algorithm_leafFromKeys_prog 52
      (f_Algorithm_leafFromKeys_prog.drop 52)
      ⟨52, [.i32 (if x0 == Algorithm.keyHi k then 0 else if x0 < Algorithm.keyHi k then 4294967295 else 1)],
        locs1, jh, hp⟩ := by
  dsimp only
  conv => lhs; arg 1; rw [show fuel = (fuel - 130) + 130 from (Nat.sub_add_cancel hf).symm]
  conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [h0]
  rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [h0, runJvmResFast_checkcast_objArray hgetK (Or.inl rfl)]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_aaload hgetK (by decide) (by simp)]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_tableswitch]
  rw [show Jvm.tableswitchTarget 1 0 [13, 15] 185 = 15 from by decide]
  norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [h0, runJvmResFast_checkcast_objArray hgetK (Or.inl rfl)]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_aaload hgetK (by decide) (by simp)]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [h0, runJvmResFast_checkcast_objArray hgetK (Or.inl rfl)]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_aaload hgetK (by decide) (by simp)]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_instanceof_step (res := 0) rfl]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_ifeq_branch rfl]
  norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
  rw [← setLocal_eq_self h1]
  heap_step_nonbranch_chunks; norm_res_fuel
  have hsh32 : ((32 : UInt32) &&& 63).toUInt64 = (32 : UInt32).toUInt64 := rfl
  have ha1 : (#[JvmVal.boxedInt 1, JvmVal.boxedULong k, tlVal] : Array JvmVal)[UInt32.toNat 1] =
      .boxedULong k := rfl
  have ha2 : (#[JvmVal.boxedInt 1, JvmVal.boxedULong k, tlVal] : Array JvmVal)[UInt32.toNat 2] =
      tlVal := rfl
  conv => lhs; arg 5; simp only [ha1, ha2, hsh32, u64_shift32_eq_keyHi]
  conv => rhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]

private theorem leafFromKeys_step74 {f : Nat} {k x0 : UInt64} {tlVal : JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h1 : locs 1 = .i64 x0)
    (hifle1 : (if x0 == Algorithm.keyHi k then (0 : UInt32)
      else if x0 < Algorithm.keyHi k then 4294967295 else 1).toBitVec.sle 0#32 = true) :
    let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 7 (.boxedULong k))
      8 tlVal) 11 (.boxedULong k)) 12 (.i32 0)) 9 (.i64 k)) 11 (.i64 (Algorithm.keyHi k))
    runJvmResFast (f + 85) f_Algorithm_leafFromKeys_prog 52 (f_Algorithm_leafFromKeys_prog.drop 52)
      ⟨52, [.i32 (if x0 == Algorithm.keyHi k then 0 else if x0 < Algorithm.keyHi k then 4294967295 else 1)],
        locs1, jh, hp⟩ =
    runJvmResFast (f + 78) f_Algorithm_leafFromKeys_prog 74 (f_Algorithm_leafFromKeys_prog.drop 74)
      ⟨74, [.i32 (if Algorithm.keyHi k == x0 + 8 then 0 else if Algorithm.keyHi k < x0 + 8 then 4294967295 else 1)],
        locs1, jh, hp⟩ := by
  dsimp only
  conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
  rw [runJvmResFast_ifle_branch hifle1]
  norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
  rw [← setLocal_eq_self h1]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => rhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]

private theorem leafFromKeys_step117 {f : Nat} {k x0 y0 : UInt64} {tlVal : JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h3 : locs 3 = .i64 y0)
    (hiflt1 : (if Algorithm.keyHi k == x0 + 8 then (0 : UInt32)
      else if Algorithm.keyHi k < x0 + 8 then 4294967295 else 1).toBitVec.slt 0#32 = true) :
    let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 7 (.boxedULong k))
      8 tlVal) 11 (.boxedULong k)) 12 (.i32 0)) 9 (.i64 k)) 11 (.i64 (Algorithm.keyHi k))
    let locs2 := setLocal (setLocal (setLocal (setLocal locs1 15 (.boxedULong k))
      16 (.i32 0)) 13 (.i64 k)) 15 (.i64 (Algorithm.keyLo k))
    runJvmResFast (f + 78) f_Algorithm_leafFromKeys_prog 74 (f_Algorithm_leafFromKeys_prog.drop 74)
      ⟨74, [.i32 (if Algorithm.keyHi k == x0 + 8 then 0 else if Algorithm.keyHi k < x0 + 8 then 4294967295 else 1)],
        locs1, jh, hp⟩ =
    runJvmResFast (f + 55) f_Algorithm_leafFromKeys_prog 117 (f_Algorithm_leafFromKeys_prog.drop 117)
      ⟨117, [.i32 (if y0 == Algorithm.keyLo k then 0 else if y0 < Algorithm.keyLo k then 4294967295 else 1)],
        locs2, jh, hp⟩ := by
  dsimp only
  conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
  rw [runJvmResFast_iflt_branch hiflt1]
  norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_instanceof_step (res := 0) rfl]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_ifeq_branch rfl]
  norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
  rw [← setLocal_eq_self h3]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => rhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
  rw [u64_andMask32_eq_keyLo]

private theorem leafFromKeys_step139 {f : Nat} {k y0 : UInt64} {tlVal : JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h3 : locs 3 = .i64 y0)
    (hifle2 : (if y0 == Algorithm.keyLo k then (0 : UInt32)
      else if y0 < Algorithm.keyLo k then 4294967295 else 1).toBitVec.sle 0#32 = true) :
    let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 7 (.boxedULong k))
      8 tlVal) 11 (.boxedULong k)) 12 (.i32 0)) 9 (.i64 k)) 11 (.i64 (Algorithm.keyHi k))
    let locs2 := setLocal (setLocal (setLocal (setLocal locs1 15 (.boxedULong k))
      16 (.i32 0)) 13 (.i64 k)) 15 (.i64 (Algorithm.keyLo k))
    runJvmResFast (f + 55) f_Algorithm_leafFromKeys_prog 117 (f_Algorithm_leafFromKeys_prog.drop 117)
      ⟨117, [.i32 (if y0 == Algorithm.keyLo k then 0 else if y0 < Algorithm.keyLo k then 4294967295 else 1)],
        locs2, jh, hp⟩ =
    runJvmResFast (f + 48) f_Algorithm_leafFromKeys_prog 139 (f_Algorithm_leafFromKeys_prog.drop 139)
      ⟨139, [.i32 (if Algorithm.keyLo k == y0 + 8 then 0 else if Algorithm.keyLo k < y0 + 8 then 4294967295 else 1)],
        locs2, jh, hp⟩ := by
  dsimp only
  conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
  rw [runJvmResFast_ifle_branch hifle2]
  norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
  rw [← setLocal_eq_self h3]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => rhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]

private theorem leafFromKeys_loop (keys : List UInt64) :
    ∀ (fuel : Nat) (x0 y0 leaf : UInt64) (keysV : JvmVal)
      (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap),
      U64ListRep jh keysV keys →
      locs 0 = keysV → locs 1 = .i64 x0 → locs 3 = .i64 y0 → locs 5 = .i64 leaf →
      fuel ≥ keys.length * 140 + 20 →
      ∃ r st',
        runJvmResFast fuel f_Algorithm_leafFromKeys_prog 0 f_Algorithm_leafFromKeys_prog
          ⟨0, [], locs, jh, hp⟩ = some (r, st') ∧
        r = .i64 (Algorithm.leafFromKeys keys x0 y0 leaf) ∧
        st'.jvmHeap = jh ∧
        st'.heap = hp := by
  induction keys with
  | nil =>
    intro fuel x0 y0 leaf keysV locs jh hp hkeys h0 h1 h3 h5 hfuel
    cases hkeys with
    | nil addr hget =>
      have hrun : runJvmResFast fuel f_Algorithm_leafFromKeys_prog 0 f_Algorithm_leafFromKeys_prog
          ⟨0, [], locs, jh, hp⟩ =
        some (.i64 leaf, ⟨14, [.i64 leaf], locs, jh, hp⟩) := by
        rw [show fuel = (fuel - 20) + 20 from (Nat.sub_add_cancel (by simp at hfuel; omega)).symm]
        dsimp only [f_Algorithm_leafFromKeys_prog]
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [h0]
        rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [h0, runJvmResFast_checkcast_objArray hget (Or.inl rfl)]
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_aaload hget (by decide) (by decide)]
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]
        heap_step_nonbranch_chunks; norm_res_fuel
        rw [runJvmResFast_tableswitch]
        rw [show Jvm.tableswitchTarget 0 0 [13, 15] 185 = 13 from by decide]
        norm_res_fuel; dsimp only [List.drop]
        heap_step_nonbranch_chunks
        rw [h5]
      exact ⟨.i64 leaf, _, hrun, rfl, rfl, rfl⟩
  | cons k rest ih =>
    intro fuel x0 y0 leaf keysV locs jh hp hkeys h0 h1 h3 h5 hfuel
    cases hkeys with
    | cons kId _ _ tlVal hgetK htl =>
      rw [Algorithm.leafFromKeys.eq_2]
      let locs1 := setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 7 (.boxedULong k))
        8 tlVal) 11 (.boxedULong k)) 12 (.i32 0)) 9 (.i64 k)) 11 (.i64 (Algorithm.keyHi k))
      have hpre := leafFromKeys_pre (hp := hp) h0 hgetK h1
        (by simp only [List.length_cons] at hfuel; omega : fuel ≥ 130)
      by_cases hx0 : x0 ≤ Algorithm.keyHi k
      · have hifle1 : (if x0 == Algorithm.keyHi k then (0 : UInt32)
            else if x0 < Algorithm.keyHi k then 4294967295 else 1).toBitVec.sle 0#32 = true := by
          rw [cmpUnsigned_sle0_iff]; simp [hx0]
        have h74 := leafFromKeys_step74 (f := fuel - 130) (tlVal := tlVal) (jh := jh) (hp := hp) h1 hifle1
        by_cases hx8 : Algorithm.keyHi k < x0 + 8
        · have hiflt1 : (if Algorithm.keyHi k == x0 + 8 then (0 : UInt32)
              else if Algorithm.keyHi k < x0 + 8 then 4294967295 else 1).toBitVec.slt 0#32 = true := by
            rw [cmpUnsigned_slt0_iff]; simp [hx8]
          let locs2 := setLocal (setLocal (setLocal (setLocal locs1 15 (.boxedULong k))
            16 (.i32 0)) 13 (.i64 k)) 15 (.i64 (Algorithm.keyLo k))
          have h118 := leafFromKeys_step117 (f := fuel - 130) (tlVal := tlVal) (jh := jh) (hp := hp) h3 hiflt1
          by_cases hy0 : y0 ≤ Algorithm.keyLo k
          · have hifle2 : (if y0 == Algorithm.keyLo k then (0 : UInt32)
                else if y0 < Algorithm.keyLo k then 4294967295 else 1).toBitVec.sle 0#32 = true := by
              rw [cmpUnsigned_sle0_iff]; simp [hy0]
            have h139 := leafFromKeys_step139 (f := fuel - 130) (tlVal := tlVal) (jh := jh) (hp := hp) h3 hifle2
            by_cases hy8 : Algorithm.keyLo k < y0 + 8
            · have hiflt2 : (if Algorithm.keyLo k == y0 + 8 then (0 : UInt32)
                  else if Algorithm.keyLo k < y0 + 8 then 4294967295 else 1).toBitVec.slt 0#32 = true := by
                rw [cmpUnsigned_slt0_iff]; simp [hy8]
              have hcond : (decide (x0 ≤ Algorithm.keyHi k) && decide (Algorithm.keyHi k < x0 + 8) &&
                  decide (y0 ≤ Algorithm.keyLo k) && decide (Algorithm.keyLo k < y0 + 8)) = true := by
                simp [hx0, hx8, hy0, hy8]
              simp only [hcond, ↓reduceIte]
              rw [hpre, h74, h118, h139]
              refine runRes_chain_box (mid := ?mid1) ?h1_1 ?h2_1
              case h1_1 =>
                conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
                rw [runJvmResFast_iflt_branch hiflt2]
                norm_res_fuel
                conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
                rw [← setLocal_eq_self h1, ← setLocal_eq_self h3, ← setLocal_eq_self h5]
                heap_step_nonbranch_chunks; norm_res_fuel
                rw [runJvmResFast_invokestatic_step (hs := stepStatic_leafWithCell_heap)]
                heap_step_nonbranch_chunks; norm_res_fuel
                rw [runJvmResFast_goto, List.drop_zero]
                rw [setLocal_eq_self h5, setLocal_eq_self h3, setLocal_eq_self h1]
                exact midBox_eq_self _
              case h2_1 =>
                refine ih _ x0 y0 _ tlVal _ jh hp htl ?_ ?_ ?_ ?_ ?_
                · simp [setLocal]
                · simp [setLocal]
                · simp [setLocal]
                · simp [setLocal]
                · simp only [List.length_cons] at hfuel; omega
            · have hiflt2 : (if Algorithm.keyLo k == y0 + 8 then (0 : UInt32)
                  else if Algorithm.keyLo k < y0 + 8 then 4294967295 else 1).toBitVec.slt 0#32 = false := by
                rw [cmpUnsigned_slt0_iff]; simp [hy8]
              have hcond : (decide (x0 ≤ Algorithm.keyHi k) && decide (Algorithm.keyHi k < x0 + 8) &&
                  decide (y0 ≤ Algorithm.keyLo k) && decide (Algorithm.keyLo k < y0 + 8)) = false := by
                simp [hy8]
              simp only [hcond]
              rw [hpre, h74, h118, h139]
              refine runRes_chain_box (mid := ?mid2) ?h1_2 ?h2_2
              case h1_2 =>
                conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
                rw [runJvmResFast_iflt_fallthrough hiflt2]
                norm_res_fuel
                heap_step_nonbranch_chunks; norm_res_fuel
                rw [runJvmResFast_goto, List.drop_zero]
                exact midBox_eq_self _
              case h2_2 =>
                refine ih _ x0 y0 leaf tlVal _ jh hp htl ?_ ?_ ?_ ?_ ?_
                · simp [setLocal]
                · simp [setLocal, h1]
                · simp [setLocal, h3]
                · simp [setLocal, h5]
                · simp only [List.length_cons] at hfuel; omega
          · have hifle2 : (if y0 == Algorithm.keyLo k then (0 : UInt32)
                else if y0 < Algorithm.keyLo k then 4294967295 else 1).toBitVec.sle 0#32 = false := by
              rw [cmpUnsigned_sle0_iff]; simp [hy0]
            have hcond : (decide (x0 ≤ Algorithm.keyHi k) && decide (Algorithm.keyHi k < x0 + 8) &&
                decide (y0 ≤ Algorithm.keyLo k) && decide (Algorithm.keyLo k < y0 + 8)) = false := by
              simp [hy0]
            simp only [hcond]
            rw [hpre, h74, h118]
            refine runRes_chain_box (mid := ?mid3) ?h1_3 ?h2_3
            case h1_3 =>
              conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
              rw [runJvmResFast_ifle_fallthrough hifle2]
              norm_res_fuel
              heap_step_nonbranch_chunks; norm_res_fuel
              rw [runJvmResFast_goto, List.drop_zero]
              exact midBox_eq_self _
            case h2_3 =>
              refine ih _ x0 y0 leaf tlVal _ jh hp htl ?_ ?_ ?_ ?_ ?_
              · simp [setLocal]
              · simp [setLocal, h1]
              · simp [setLocal, h3]
              · simp [setLocal, h5]
              · simp only [List.length_cons] at hfuel; omega
        · have hiflt1 : (if Algorithm.keyHi k == x0 + 8 then (0 : UInt32)
              else if Algorithm.keyHi k < x0 + 8 then 4294967295 else 1).toBitVec.slt 0#32 = false := by
            rw [cmpUnsigned_slt0_iff]; simp [hx8]
          have hcond : (decide (x0 ≤ Algorithm.keyHi k) && decide (Algorithm.keyHi k < x0 + 8) &&
              decide (y0 ≤ Algorithm.keyLo k) && decide (Algorithm.keyLo k < y0 + 8)) = false := by
            simp [hx8]
          simp only [hcond]
          rw [hpre, h74]
          refine runRes_chain_box (mid := ?mid4) ?h1_4 ?h2_4
          case h1_4 =>
            conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
            rw [runJvmResFast_iflt_fallthrough hiflt1]
            norm_res_fuel
            heap_step_nonbranch_chunks; norm_res_fuel
            rw [runJvmResFast_goto, List.drop_zero]
            exact midBox_eq_self _
          case h2_4 =>
            refine ih _ x0 y0 leaf tlVal _ jh hp htl ?_ ?_ ?_ ?_ ?_
            · simp [setLocal]
            · simp [setLocal, h1]
            · simp [setLocal, h3]
            · simp [setLocal, h5]
            · simp only [List.length_cons] at hfuel; omega
      · have hifle1 : (if x0 == Algorithm.keyHi k then (0 : UInt32)
            else if x0 < Algorithm.keyHi k then 4294967295 else 1).toBitVec.sle 0#32 = false := by
          rw [cmpUnsigned_sle0_iff]; simp [hx0]
        have hcond : (decide (x0 ≤ Algorithm.keyHi k) && decide (Algorithm.keyHi k < x0 + 8) &&
            decide (y0 ≤ Algorithm.keyLo k) && decide (Algorithm.keyLo k < y0 + 8)) = false := by
          simp [hx0]
        simp only [hcond]
        rw [hpre]
        refine runRes_chain_box (mid := ?mid5) ?h1_5 ?h2_5
        case h1_5 =>
          conv => lhs; arg 4; dsimp only [f_Algorithm_leafFromKeys_prog, List.drop]
          rw [runJvmResFast_ifle_fallthrough hifle1]
          norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rw [runJvmResFast_goto, List.drop_zero]
          exact midBox_eq_self _
        case h2_5 =>
          refine ih _ x0 y0 leaf tlVal _ jh hp htl ?_ ?_ ?_ ?_ ?_
          · simp [setLocal]
          · simp [setLocal, h1]
          · simp [setLocal, h3]
          · simp [setLocal, h5]
          · simp only [List.length_cons] at hfuel; omega

theorem leafFromKeys_equiv
    (keys : List UInt64) (x0 y0 leaf : UInt64) (keysV : JvmVal)
    (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hkeys : U64ListRep jh keysV keys)
    (h0 : locs 0 = keysV) (h1 : locs 1 = .i64 x0) (h3 : locs 3 = .i64 y0) (h5 : locs 5 = .i64 leaf) :
    ∃ st',
      runJvmResFast (keys.length * 140 + 20) f_Algorithm_leafFromKeys_prog 0 f_Algorithm_leafFromKeys_prog
        ⟨0, [], locs, jh, hp⟩ =
        some (.i64 (Algorithm.leafFromKeys keys x0 y0 leaf), st') ∧
      st'.jvmHeap = jh ∧
      st'.heap = hp := by
  rcases leafFromKeys_loop keys (keys.length * 140 + 20) x0 y0 leaf keysV locs jh hp hkeys h0 h1 h3 h5
    (Nat.le_refl _) with ⟨r, st', hr, rfl, h1', h2'⟩
  exact ⟨st', hr, h1', h2'⟩

private theorem nodup_filter_length_le :
    ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ a ∈ l, a < n) → l.length ≤ n
  | 0, l, _, hlt => by
    cases l with
    | nil => simp
    | cons a _ => exact absurd (hlt a (by simp)) (by omega)
  | n + 1, l, hnd, hlt => by
    have hsub : l.length ≤ (l.filter (· != n)).length + 1 := by
      clear hlt
      induction l with
      | nil => simp
      | cons a tl ih =>
        rw [List.nodup_cons] at hnd
        rw [List.filter_cons]
        by_cases ha : a = n
        · subst ha
          have hf : tl.filter (· != a) = tl := by
            refine List.filter_eq_self.mpr ?_
            intro x hx
            rw [bne_iff_ne]
            exact fun heq => hnd.1 (heq ▸ hx)
          simp [hf]
        · have hb : (a != n) = true := bne_iff_ne.mpr ha
          simp only [hb, ↓reduceIte, List.length_cons]
          have := ih hnd.2
          omega
    have hlt' : ∀ a ∈ l.filter (· != n), a < n := by
      intro a ha
      rw [List.mem_filter] at ha
      have h1 := hlt a ha.1
      have h2 : a ≠ n := bne_iff_ne.mp ha.2
      omega
    have hrec := nodup_filter_length_le n (l.filter (· != n)) (hnd.filter _) hlt'
    omega

private theorem U64ListRep_det {jh : Jvm.JvmHeap AlgExt} :
    ∀ {v : JvmVal} {xs ys : List UInt64},
      U64ListRep jh v xs → U64ListRep jh v ys → xs = ys
  | _, _, _, .nil _ _ _, .nil _ _ _ => rfl
  | _, _, _, .nil _ _ hget1, .cons _ _ _ _ _ hget2 _ => by
    rw [hget1] at hget2; cases hget2
  | _, _, _, .cons _ _ _ _ _ hget1 _, .nil _ _ hget2 => by
    rw [hget1] at hget2; cases hget2
  | _, _, _, .cons _ _ _ _ _ hget1 htl1, .cons _ _ _ _ _ hget2 htl2 => by
    rw [hget1] at hget2
    simp only [Option.some.injEq, Jvm.HeapObj.objArray.injEq, Array.mk.injEq,
      List.cons.injEq, and_true, true_and] at hget2
    rcases hget2 with ⟨hleft, rfl⟩
    cases hleft
    congr 1
    exact U64ListRep_det htl1 htl2

private theorem heap_get?_lt_size {Ext : Type} {jh : Jvm.JvmHeap Ext} {a : Nat} {x : Jvm.HeapObj Ext}
    (h : jh.get? a = some x) : a < jh.objects.size :=
  Nat.lt_of_not_le fun hle => by
    have hn : jh.objects[a]? = none := Array.getElem?_eq_none hle
    change jh.objects[a]? = some x at h
    rw [hn] at h
    cases h

private theorem U64ListRep_addrs {jh : Jvm.JvmHeap AlgExt} {v : JvmVal} {xs : List UInt64}
    (h : U64ListRep jh v xs) :
    ∃ addrs : List Nat, addrs.length = xs.length + 1 ∧ addrs.Nodup ∧
      ∀ a ∈ addrs, a < jh.objects.size ∧ ∃ ys, U64ListRep jh (.heapRef a) ys ∧ ys.length ≤ xs.length := by
  induction h with
  | @nil addr hget =>
    refine ⟨[addr], rfl, by simp [List.nodup_cons], ?_⟩
    intro a ha
    rw [List.mem_singleton] at ha
    subst ha
    exact ⟨heap_get?_lt_size hget, [], .nil _ a hget, Nat.le_refl 0⟩
  | @cons addr hd tl tlVal hget htl ih =>
    rcases ih with ⟨addrs, hlen, hnd, hinv⟩
    refine ⟨addr :: addrs, by simp [hlen], ?_, ?_⟩
    · rw [List.nodup_cons]
      refine ⟨?_, hnd⟩
      intro hmem
      rcases (hinv addr hmem).2 with ⟨ys, hys, hle⟩
      have heq := U64ListRep_det (.cons _ addr hd tl tlVal hget htl) hys
      rw [← heq] at hle
      simp only [List.length_cons] at hle
      omega
    · intro a ha
      rw [List.mem_cons] at ha
      rcases ha with rfl | hmem
      · exact ⟨heap_get?_lt_size hget, hd :: tl, .cons _ a hd tl tlVal hget htl, Nat.le_refl _⟩
      · rcases hinv a hmem with ⟨hlt, ys, hys, hle⟩
        exact ⟨hlt, ys, hys, Nat.le_trans hle (Nat.le_succ _)⟩

private theorem U64ListRep.decode_self {jh : Jvm.JvmHeap AlgExt} {v : JvmVal} {xs : List UInt64}
    (h : U64ListRep jh v xs) :
    decodeU64List jh (jh.objects.size + 2) v = some xs := by
  rcases U64ListRep_addrs h with ⟨addrs, hlen, hnd, hinv⟩
  have hle := nodup_filter_length_le jh.objects.size addrs hnd (fun a ha => (hinv a ha).1)
  exact U64ListRep.decode h (jh.objects.size + 2) (by omega)

private theorem u64_shl_u32_and63 (h : UInt32) :
    (1 : UInt64) <<< ((h + 3) &&& 63).toUInt64 = (1 : UInt64) <<< (h + 3).toUInt64 := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_shiftLeft]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, UInt64.toNat_toBitVec, UInt32.toNat_toUInt64,
    UInt32.toNat_and, show (63 : UInt32).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, show (64 : BitVec 64).toNat = 64 from rfl]
  omega

private theorem runJvmResFast_ifeq_fallthrough {f pc tgt : Nat} {prog rest : List JvmInstr}
    {v : UInt32} {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h : (v == 0) = false) :
    runJvmResFast (f + 1) prog pc (.ifeq tgt :: rest) ⟨pc, .i32 v :: stk, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, stk, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_ifeq_fallthrough algHooks h

private theorem runJvmResFast_checkcast_pair {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {a b : JvmVal} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.checkcast "kotlin/Pair" :: rest)
        ⟨pc0, .pair a b :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .pair a b :: stkRest, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem runJvmResFast_checkcast_mcCellNode {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {ch : UInt32} {nw ne sw se : Algorithm.MacroCell}
    {stkRest : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc
        (.checkcast "com/alexvanyo/composelife/model/MacroCell$CellNode" :: rest)
        ⟨pc0, .ext (.mc (.cellNode ch nw ne sw se)) :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .ext (.mc (.cellNode ch nw ne sw se)) :: stkRest, locs, jh, hp⟩ :=
  Jvm.runJvmResFast_step_of_stepInstr algHooks rfl (by simp) rfl rfl

private theorem keysToMacroCell_zero_or_leaf
    {x0 y0 : UInt64} {keys : List UInt64} {keysV : JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {f : Nat}
    (hkeys : U64ListRep jh keysV keys)
    (h0 : locs 0 = keysV) (h1 : locs 1 = .i64 x0) (h3 : locs 3 = .i64 y0) :
    ∃ st',
      runJvmResFast (f + 45) f_Algorithm_keysToMacroCell_prog 129
        (f_Algorithm_keysToMacroCell_prog.drop 129) ⟨129, [], locs, jh, hp⟩ =
        some (.ext (.mc (Algorithm.makeLevel4Node
          (Algorithm.leafFromKeys keys x0 y0 0)
          (Algorithm.leafFromKeys keys (x0 + 8) y0 0)
          (Algorithm.leafFromKeys keys x0 (y0 + 8) 0)
          (Algorithm.leafFromKeys keys (x0 + 8) (y0 + 8) 0))), st') ∧
      st'.heap = hp := by
  refine ⟨?st', ?_, ?_⟩
  rotate_left 1
  · have hkdec := hkeys.decode_self
    conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog, List.drop]
    conv => lhs; arg 1; rw [show f + 45 = (f + 41) + 4 by omega]
    rw [← setLocal_eq_self h0, ← setLocal_eq_self h1, ← setLocal_eq_self h3]
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_leafFromKeys_heap hkdec)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_leafFromKeys_heap hkdec)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_leafFromKeys_heap hkdec)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_leafFromKeys_heap hkdec)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step stepStatic_makeLevel4Node_heap]; norm_res_fuel
    conv => lhs; arg 1; rw [show f + 6 + 1 - 1 = (f + 5) + 1 by omega]
    rfl
  · rfl

private theorem keysToMacroCell_tail
    {x0 y0 midX midY : UInt64} {h : UInt32} {emptyChild : Algorithm.MacroCell}
    {nwL neL swL seL : List UInt64} {nwV neV swV seV : JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {f : Nat}
    (hnw : U64ListRep jh nwV nwL) (hne : U64ListRep jh neV neL)
    (hsw : U64ListRep jh swV swL) (hse : U64ListRep jh seV seL)
    (h1 : locs 1 = .i64 x0) (h3 : locs 3 = .i64 y0) (h5 : locs 5 = .i32 h)
    (h9 : locs 9 = .i64 midX) (h11 : locs 11 = .i64 midY)
    (h14 : locs 14 = .pair nwV (.pair neV (.pair swV seV)))
    (h15 : locs 15 = .ext (.mc emptyChild)) :
    ∃ st',
      runJvmResFast (f + 56) f_Algorithm_keysToMacroCell_prog 74
        (f_Algorithm_keysToMacroCell_prog.drop 74)
        ⟨74, [.pair neV (.pair swV seV)], locs, jh, hp⟩ =
        some (.ext (.mc (Algorithm.makeCellNode
          (Algorithm.keysToMacroCell nwL x0 y0 (h - 1) emptyChild)
          (Algorithm.keysToMacroCell neL midX y0 (h - 1) emptyChild)
          (Algorithm.keysToMacroCell swL x0 midY (h - 1) emptyChild)
          (Algorithm.keysToMacroCell seL midX midY (h - 1) emptyChild))), st') ∧
      st'.heap = hp := by
  refine ⟨?st', ?_, ?_⟩
  rotate_left 1
  · have dnw := hnw.decode_self
    have dne := hne.decode_self
    have dsw := hsw.decode_self
    have dse := hse.decode_self
    conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog, List.drop]
    conv => lhs; arg 1; rw [show f + 56 = (f + 30) + 26 by omega]
    rw [← setLocal_eq_self h1, ← setLocal_eq_self h3, ← setLocal_eq_self h5,
      ← setLocal_eq_self h9, ← setLocal_eq_self h11, ← setLocal_eq_self h14, ← setLocal_eq_self h15]
    split_res_fuel 1
    rw [runJvmResFast_checkcast_pair]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_checkcast_pair]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; dsimp only
    conv => lhs; arg 5; dsimp only [Nat.add]
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; dsimp only
    conv => lhs; arg 5; arg 1; simp only [Nat.succ_eq_add_one]
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_keysToMacroCell_heap dnw)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; dsimp only
    conv => lhs; arg 5; arg 1; simp only [Nat.succ_eq_add_one]
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_keysToMacroCell_heap dne)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; dsimp only
    conv => lhs; arg 5; arg 1; simp only [Nat.succ_eq_add_one]
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_keysToMacroCell_heap dsw)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; dsimp only
    conv => lhs; arg 5; arg 1; simp only [Nat.succ_eq_add_one]
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_keysToMacroCell_heap dse)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    conv => lhs; arg 3; dsimp only
    conv => lhs; arg 5; arg 1; simp only [Nat.succ_eq_add_one]
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step stepStatic_makeCellNode_heap]; norm_res_fuel
    conv => lhs; arg 1; rw [show f + 2 + 1 - 1 = (f + 1) + 1 by omega]
    rfl
  · rfl

private theorem setLocal_overwrite {Ext : Type} (l : Nat → Jvm.JvmVal Ext) (k : Nat) (x y : Jvm.JvmVal Ext) :
    setLocal (setLocal l k x) k y = setLocal l k y := by
  funext i; simp only [setLocal]; split <;> rfl

private theorem setLocal_comm {Ext : Type} (l : Nat → Jvm.JvmVal Ext) {a b : Nat} (hab : a ≠ b)
    (x y : Jvm.JvmVal Ext) :
    setLocal (setLocal l a x) b y = setLocal (setLocal l b y) a x := by
  funext i
  simp only [setLocal]
  split <;> split <;> simp_all [Ne.symm]

private theorem arr1_null_lt0 :
    UInt32.toNat 0 < (Array.replicate (UInt32.toNat 1) (@JvmVal.null AlgExt)).size := by
  decide

private theorem arr1_set0_boxedInt0
    (h : UInt32.toNat 0 < (Array.replicate (UInt32.toNat 1) (@JvmVal.null AlgExt)).size) :
    (Array.replicate (UInt32.toNat 1) (@JvmVal.null AlgExt)).set
        (UInt32.toNat 0) (@JvmVal.boxedInt AlgExt 0) h =
      #[(@JvmVal.boxedInt AlgExt 0)] := by
  have h1 : UInt32.toNat 1 = 1 := rfl
  have h0 : UInt32.toNat 0 = 0 := rfl
  simp only [h1, h0]
  rfl

theorem keysToMacroCell_equiv
    (keys : List UInt64) (x0 y0 : UInt64) (h : UInt32) (empty : Algorithm.MacroCell)
    (keysV : JvmVal) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap)
    (hkeys : U64ListRep jh keysV keys)
    (h0 : locs 0 = keysV) (h1 : locs 1 = .i64 x0) (h3 : locs 3 = .i64 y0)
    (h5 : locs 5 = .i32 h) (h6 : locs 6 = .ext (.mc empty)) :
    ∃ st',
      runJvmResFast 180 f_Algorithm_keysToMacroCell_prog 0 f_Algorithm_keysToMacroCell_prog
        ⟨0, [], locs, jh, hp⟩ =
        some (.ext (.mc (Algorithm.keysToMacroCell keys x0 y0 h empty)), st') ∧
      st'.heap = hp := by
  cases hkeys with
  | nil addr hget =>
    simp only [Algorithm.keysToMacroCell]
    refine ⟨?st', ?_, ?_⟩
    rotate_left 1
    · conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog]
      heap_step_nonbranch_chunks; norm_res_fuel
      simp only [h6]
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [h0]
      split_res_fuel 1
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [h0]
      split_res_fuel 1
      rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      split_res_fuel 1
      rw [runJvmResFast_aaload hget (by decide) (by decide)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      split_res_fuel 1
      rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      split_res_fuel 1
      rw [runJvmResFast_tableswitch, show Jvm.tableswitchTarget 0 0 [16, 18] 169 = 16 from by decide]
      norm_res_fuel
      conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog, List.drop]
      heap_step_nonbranch_chunks; norm_res_fuel
      simp only [h6]
      rfl
    · rfl
  | cons addr hd tl tlVal hget htl =>
    have hkeys' : U64ListRep jh (.heapRef addr) (hd :: tl) := .cons _ addr hd tl tlVal hget htl
    have hpre19 :
        runJvmResFast 180 f_Algorithm_keysToMacroCell_prog 0 f_Algorithm_keysToMacroCell_prog
          ⟨0, [], locs, jh, hp⟩ =
        runJvmResFast 163 f_Algorithm_keysToMacroCell_prog 19
          (f_Algorithm_keysToMacroCell_prog.drop 19) ⟨19, [.i32 h], locs, jh, hp⟩ := by
      conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog]
      heap_step_nonbranch_chunks; norm_res_fuel
      simp only [h6]
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [h0]
      split_res_fuel 1
      rw [runJvmResFast_invokestatic_step (hs := stepStatic_checkNotNull_heap rfl)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      rw [h0]
      split_res_fuel 1
      rw [runJvmResFast_checkcast_objArray hget (Or.inl rfl)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      split_res_fuel 1
      rw [runJvmResFast_aaload hget (by decide) (by simp)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      split_res_fuel 1
      rw [runJvmResFast_checkcast_boxedInt (Or.inl rfl)]; norm_res_fuel
      heap_step_nonbranch_chunks; norm_res_fuel
      split_res_fuel 1
      rw [runJvmResFast_tableswitch, show Jvm.tableswitchTarget 1 0 [16, 18] 169 = 18 from by decide]
      norm_res_fuel
      conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog, List.drop]
      heap_step_nonbranch_chunks; norm_res_fuel
      simp only [h5]
      rfl
    rw [hpre19]
    by_cases hh : h = 0
    · subst hh
      simp only [Algorithm.keysToMacroCell, ↓reduceDIte]
      have hpre129 :
          runJvmResFast 163 f_Algorithm_keysToMacroCell_prog 19
            (f_Algorithm_keysToMacroCell_prog.drop 19) ⟨19, [.i32 0], locs, jh, hp⟩ =
          runJvmResFast (117 + 45) f_Algorithm_keysToMacroCell_prog 129
            (f_Algorithm_keysToMacroCell_prog.drop 129) ⟨129, [], locs, jh, hp⟩ := by
        conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog, List.drop]
        split_res_fuel 1
        rw [runJvmResFast_ifeq_branch rfl]
      rw [hpre129]
      exact keysToMacroCell_zero_or_leaf (f := 117) hkeys' h0 h1 h3
    · simp only [Algorithm.keysToMacroCell, hh, ↓reduceDIte]
      have hne0 : (h == 0) = false := beq_false_of_ne hh
      obtain ⟨jh1, hjh1⟩ : ∃ x, x = (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2 := ⟨_, rfl⟩
      let half := (1 : UInt64) <<< ((h + 3) &&& 63).toUInt64
      have hhalf : half = (1 : UInt64) <<< (h + 3).toUInt64 := u64_shl_u32_and63 h
      obtain ⟨parts, hparts⟩ :
          ∃ p, p = Algorithm.splitKeys (hd :: tl) (x0 + half) (y0 + half) [] [] [] [] := ⟨_, rfl⟩
      rcases henc1 : encodeU64List jh1 parts.1 with ⟨nwV, jh2⟩
      rcases henc2 : encodeU64List jh2 parts.2.1 with ⟨neV, jh3⟩
      rcases henc3 : encodeU64List jh3 parts.2.2.1 with ⟨swV, jh4⟩
      rcases henc4 : encodeU64List jh4 parts.2.2.2 with ⟨seV, jh5⟩
      let locs1 :=
        setLocal (setLocal (setLocal (setLocal (setLocal (setLocal locs 7 (.i64 half))
          9 (.i64 (x0 + half))) 11 (.i64 (y0 + half)))
          13 (.heapRef jh.objects.size)) 14 (.pair nwV (.pair neV (.pair swV seV))))
          15 .null
      have hpre61 :
          runJvmResFast 163 f_Algorithm_keysToMacroCell_prog 19
            (f_Algorithm_keysToMacroCell_prog.drop 19) ⟨19, [.i32 h], locs, jh, hp⟩ =
          runJvmResFast 121 f_Algorithm_keysToMacroCell_prog 61
            (f_Algorithm_keysToMacroCell_prog.drop 61)
            ⟨61, [.ext (.mc empty)], locs1, jh5, hp⟩ := by
        conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog, List.drop]
        split_res_fuel 1
        rw [runJvmResFast_ifeq_fallthrough hne0]
        conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog, List.drop]
        rw [← setLocal_eq_self h0, ← setLocal_eq_self h1, ← setLocal_eq_self h3,
          ← setLocal_eq_self h5, ← setLocal_eq_self h6]
        heap_step_nonbranch_chunks; norm_res_fuel
        split_res_fuel 1
        rw [runJvmResFast_anewarray_obj (hslt := by decide)]; norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        split_res_fuel 1
        rw [runJvmResFast_aastore (hget := jvmHeap_get?_alloc_self _ _) (hslt := by decide) (hlt := arr1_null_lt0)]
        rw [jvmHeap_alloc_set_self, arr1_set0_boxedInt0, ← hjh1]
        norm_res_fuel
        heap_step_nonbranch_chunks; norm_res_fuel
        have hkeys1 : U64ListRep jh1 (.heapRef addr) (hd :: tl) :=
          hjh1 ▸ U64ListRep.alloc _ hkeys'
        have hnil1 : U64ListRep jh1 (.heapRef jh.objects.size) [] :=
          hjh1 ▸ .nil _ _ (jvmHeap_get?_alloc_self _ _)
        split_res_fuel 1
        rw [runJvmResFast_invokestatic_step
          (stepStatic_splitKeys_heap hkeys1.decode_self hnil1.decode_self hnil1.decode_self hnil1.decode_self hnil1.decode_self)]
        norm_res_fuel
        rw [← hparts, henc1, henc2, henc3, henc4]
        heap_step_nonbranch_chunks; norm_res_fuel
        congr 1
        · rw [setLocal_comm _ (by decide : (14 : Nat) ≠ 13), setLocal_overwrite]
          rw [setLocal_eq_self h6, setLocal_eq_self h5, setLocal_eq_self h3,
            setLocal_eq_self h1, setLocal_eq_self h0]
      rw [hpre61]
      have hnw : U64ListRep jh5 nwV parts.1 := by
        have r1 := (U64ListRep_encodeU64List jh1 parts.1).1
        rw [henc1] at r1
        have r2 := U64ListRep_encodeU64List_preserves parts.2.1 r1
        rw [henc2] at r2
        have r3 := U64ListRep_encodeU64List_preserves parts.2.2.1 r2
        rw [henc3] at r3
        have r4 := U64ListRep_encodeU64List_preserves parts.2.2.2 r3
        rw [henc4] at r4
        exact r4
      have hne : U64ListRep jh5 neV parts.2.1 := by
        have r2 := (U64ListRep_encodeU64List jh2 parts.2.1).1
        rw [henc2] at r2
        have r3 := U64ListRep_encodeU64List_preserves parts.2.2.1 r2
        rw [henc3] at r3
        have r4 := U64ListRep_encodeU64List_preserves parts.2.2.2 r3
        rw [henc4] at r4
        exact r4
      have hsw : U64ListRep jh5 swV parts.2.2.1 := by
        have r3 := (U64ListRep_encodeU64List jh3 parts.2.2.1).1
        rw [henc3] at r3
        have r4 := U64ListRep_encodeU64List_preserves parts.2.2.2 r3
        rw [henc4] at r4
        exact r4
      have hse : U64ListRep jh5 seV parts.2.2.2 := by
        have r4 := (U64ListRep_encodeU64List jh4 parts.2.2.2).1
        rw [henc4] at r4
        exact r4
      cases empty with
      | level4Node eh e0 e1 e2 e3 =>
        simp only [Algorithm.nwChild]
        have hpre74 :
            runJvmResFast 121 f_Algorithm_keysToMacroCell_prog 61
              (f_Algorithm_keysToMacroCell_prog.drop 61)
              ⟨61, [.ext (.mc (.level4Node eh e0 e1 e2 e3))], locs1, jh5, hp⟩ =
            runJvmResFast (59 + 56) f_Algorithm_keysToMacroCell_prog 74
              (f_Algorithm_keysToMacroCell_prog.drop 74)
              ⟨74, [.pair neV (.pair swV seV)],
                setLocal locs1 15 (.ext (.mc (.level4Node eh e0 e1 e2 e3))), jh5, hp⟩ := by
          conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog, List.drop]
          split_res_fuel 1
          rw [runJvmResFast_instanceof_step (res := 0) rfl]; norm_res_fuel
          split_res_fuel 1
          rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
          conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog, List.drop]
          heap_step_nonbranch_chunks; norm_res_fuel
          simp only [h6]
          heap_step_nonbranch_chunks; norm_res_fuel
          rfl
        rw [hpre74, ← hhalf, ← hparts]
        exact keysToMacroCell_tail (f := 59) hnw hne hsw hse
          (by simp [locs1, setLocal, h1]) (by simp [locs1, setLocal, h3]) (by simp [locs1, setLocal, h5])
          (by simp [locs1, setLocal]) (by simp [locs1, setLocal]) (by simp [locs1, setLocal])
          (by simp [setLocal])
      | cellNode eh enw ene esw ese =>
        simp only [Algorithm.nwChild]
        have hpre74 :
            runJvmResFast 121 f_Algorithm_keysToMacroCell_prog 61
              (f_Algorithm_keysToMacroCell_prog.drop 61)
              ⟨61, [.ext (.mc (.cellNode eh enw ene esw ese))], locs1, jh5, hp⟩ =
            runJvmResFast (54 + 56) f_Algorithm_keysToMacroCell_prog 74
              (f_Algorithm_keysToMacroCell_prog.drop 74)
              ⟨74, [.pair neV (.pair swV seV)],
                setLocal (setLocal locs1 17 (.ext (.mc enw))) 15 (.ext (.mc enw)), jh5, hp⟩ := by
          conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog, List.drop]
          split_res_fuel 1
          rw [runJvmResFast_instanceof_step (res := 1) rfl]; norm_res_fuel
          split_res_fuel 1
          rw [runJvmResFast_ifeq_fallthrough (by decide)]; norm_res_fuel
          conv => lhs; arg 4; dsimp only [f_Algorithm_keysToMacroCell_prog, List.drop]
          heap_step_nonbranch_chunks; norm_res_fuel
          simp only [h6]
          split_res_fuel 1
          rw [runJvmResFast_checkcast_mcCellNode]; norm_res_fuel
          split_res_fuel 1
          rw [runJvmResFast_invokevirtual_step stepVirtual_mcCellNodeGetNw]; norm_res_fuel
          heap_step_nonbranch_chunks; norm_res_fuel
          rfl
        rw [hpre74, ← hhalf, ← hparts]
        exact keysToMacroCell_tail (f := 54) hnw hne hsw hse
          (by simp [locs1, setLocal, h1]) (by simp [locs1, setLocal, h3]) (by simp [locs1, setLocal, h5])
          (by simp [locs1, setLocal]) (by simp [locs1, setLocal]) (by simp [locs1, setLocal])
          (by simp [setLocal])

private theorem runJvmResFast_checkcast_mc {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {rest : List JvmInstr} {pc0 : Nat} {mc : Algorithm.MacroCell}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    runJvmResFast (f + 1) prog pc (.checkcast "com/alexvanyo/composelife/model/MacroCell" :: rest)
        ⟨pc0, .ext (.mc mc) :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, .ext (.mc mc) :: stkRest, locs, jh, hp⟩ :=
  runJvmResFast_checkcast_step (by cases mc <;> rfl)

private theorem cellsToMacroCell_tail
    {cells : Array UInt64} {cid : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    {minX minY spanVal : UInt64} {f : Nat}
    (hu : u64[cid]? = some cells)
    (h0 : locs 0 = .ext (.u64Ref cid))
    (h1 : locs 1 = .i32 cells.size.toUInt32)
    (h10 : locs 10 = .i64 minX) (h12 : locs 12 = .i64 minY) :
    ∃ st',
      runJvmResFast (f + 45) f_Algorithm_cellsToMacroCell_prog 82
        (f_Algorithm_cellsToMacroCell_prog.drop 82)
        ⟨82, [.i32 5, .i64 (spanVal + 1)], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (let span := spanVal + 1
              let lvl := Algorithm.levelForSpanLoop span 5
              let mc := Algorithm.keysToMacroCell
                (Algorithm.relativeKeysLoop cells 0 cells.size.toUInt32 minX minY [])
                0 0 (lvl - 4) (Algorithm.emptyAtHeight (lvl - 4))
              .pair (.boxedULong minX) (.pair (.boxedULong minY) (.ext (.mc mc))), st') ∧
      st'.heap = ⟨ar, u64, asc⟩ := by
  obtain ⟨jh1, hjh1⟩ : ∃ x, x = (jh.alloc (.objArray "java/lang/Object" #[.boxedInt 0])).2 := ⟨_, rfl⟩
  obtain ⟨rk, hrk⟩ :
      ∃ x, x = Algorithm.relativeKeysLoop cells 0 cells.size.toUInt32 minX minY [] := ⟨_, rfl⟩
  rcases henc : encodeU64List jh1 rk with ⟨rkV, jh2⟩
  refine ⟨?st', ?_, ?_⟩
  rotate_left 1
  · conv => lhs; arg 4; dsimp only [f_Algorithm_cellsToMacroCell_prog, List.drop]
    conv => lhs; arg 1; rw [show f + 45 = (f + 2) + 43 by omega]
    rw [← setLocal_eq_self h0, ← setLocal_eq_self h1, ← setLocal_eq_self h10, ← setLocal_eq_self h12]
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step stepStatic_levelForSpanLoop_heap]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_anewarray_obj (hslt := by decide)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_aastore (hget := jvmHeap_get?_alloc_self _ _) (hslt := by decide) (hlt := arr1_null_lt0)]
    rw [jvmHeap_alloc_set_self, arr1_set0_boxedInt0, ← hjh1]
    norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    have hnil1 : U64ListRep jh1 (.heapRef jh.objects.size) [] :=
      hjh1 ▸ .nil _ _ (jvmHeap_get?_alloc_self _ _)
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_relativeKeysLoop_heap hu hnil1.decode_self)]; norm_res_fuel
    rw [← hrk, henc]
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step stepStatic_emptyAtHeight_heap]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    have hrkRep : U64ListRep jh2 rkV rk := by
      have r := (U64ListRep_encodeU64List jh1 rk).1
      rw [henc] at r
      exact r
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step (stepStatic_keysToMacroCell_heap hrkRep.decode_self)]; norm_res_fuel
    rw [show f + 13 + 1 - 1 = (f + 1) + 12 from by omega]
    heap_step_one_chunk; norm_res_fuel
    rfl
  · rfl

private theorem cellsToMacroCell_pre8
    (cells : Array UInt64) (cid : Nat) (locs : Nat → JvmVal)
    (jh : Jvm.JvmHeap AlgExt) (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hu : u64[cid]? = some cells) (h0 : locs 0 = .ext (.u64Ref cid)) :
    runJvmResFast 180 f_Algorithm_cellsToMacroCell_prog 0 f_Algorithm_cellsToMacroCell_prog
        ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast 172 f_Algorithm_cellsToMacroCell_prog 8
        (f_Algorithm_cellsToMacroCell_prog.drop 8)
        ⟨8, [.i32 cells.size.toUInt32], setLocal locs 1 (.i32 cells.size.toUInt32),
          jh, ⟨ar, u64, asc⟩⟩ := by
  conv => lhs; arg 4; dsimp only [f_Algorithm_cellsToMacroCell_prog]
  heap_step_nonbranch_chunks; norm_res_fuel
  simp only [h0]
  heap_step_nonbranch_chunks; norm_res_fuel
  simp only [h0]
  split_res_fuel 1
  rw [runJvmResFast_invokestatic_step (stepStatic_ulongArrGetSize_heap hu)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  rfl

private theorem cellsToMacroCell_zero
    (cells : Array UInt64) (hn0 : cells.size.toUInt32 = 0)
    (cid : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hu : u64[cid]? = some cells) (h0 : locs 0 = .ext (.u64Ref cid)) :
    ∃ st',
      runJvmResFast 180 f_Algorithm_cellsToMacroCell_prog 0 f_Algorithm_cellsToMacroCell_prog
          ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (let r := Algorithm.cellsToMacroCell cells
              .pair (.boxedULong r.1) (.pair (.boxedULong r.2.1) (.ext (.mc r.2.2))), st') ∧
      st'.heap = ⟨ar, u64, asc⟩ := by
  refine ⟨?st', ?_, ?_⟩
  rotate_left 1
  · rw [cellsToMacroCell_pre8 cells cid locs jh ar u64 asc hu h0]
    conv => lhs; arg 4; dsimp only [f_Algorithm_cellsToMacroCell_prog, List.drop]
    split_res_fuel 1
    rw [runJvmResFast_ifeq_branch hn0]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_cellsToMacroCell_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_invokestatic_step stepStatic_cellsToMacroCell_closed2_heap]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_instanceof_step (res := 0) rfl]; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_cellsToMacroCell_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_checkcast_pair]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_instanceof_step (res := 0) rfl]; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_ifeq_branch rfl]; norm_res_fuel
    conv => lhs; arg 4; dsimp only [f_Algorithm_cellsToMacroCell_prog, List.drop]
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    split_res_fuel 1
    rw [runJvmResFast_checkcast_mc]; norm_res_fuel
    heap_step_nonbranch_chunks; norm_res_fuel
    simp only [Algorithm.cellsToMacroCell, hn0, beq_self_eq_true, ↓reduceIte]
    rfl
  · rfl

private theorem cellsToMacroCell_pre71
    (cells : Array UInt64) (hne0 : (cells.size.toUInt32 == 0) = false)
    (cid : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hu : u64[cid]? = some cells) (h0 : locs 0 = .ext (.u64Ref cid))
    (cb : UInt64 × UInt64 × UInt64 × UInt64)
    (hcb : cb = Algorithm.cellBoundsLoop cells 1 cells.size.toUInt32
      (Algorithm.keyHi cells[0]!) (Algorithm.keyLo cells[0]!)
      (Algorithm.keyHi cells[0]!) (Algorithm.keyLo cells[0]!)) :
    runJvmResFast 180 f_Algorithm_cellsToMacroCell_prog 0 f_Algorithm_cellsToMacroCell_prog
        ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
      runJvmResFast 109 f_Algorithm_cellsToMacroCell_prog 71
        (f_Algorithm_cellsToMacroCell_prog.drop 71)
        ⟨71, [.i32 (if (cb.2.2.1 - cb.1 == cb.2.2.2 - cb.2.1) = true then 0
            else if cb.2.2.1 - cb.1 < cb.2.2.2 - cb.2.1 then 4294967295 else 1)],
          setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
            (setLocal (setLocal (setLocal locs 1 (.i32 cells.size.toUInt32)) 2 (.i64 cells[0]!))
              4 (.i64 (Algorithm.keyHi cells[0]!))) 6 (.i64 (Algorithm.keyLo cells[0]!)))
              8 (.pair (.boxedULong cb.1) (.pair (.boxedULong cb.2.1) (.pair (.boxedULong cb.2.2.1) (.boxedULong cb.2.2.2)))))
              9 (.pair (.boxedULong cb.2.1) (.pair (.boxedULong cb.2.2.1) (.boxedULong cb.2.2.2))))
              10 (.i64 cb.1)) 12 (.i64 cb.2.1))
              14 (.pair (.boxedULong cb.2.2.1) (.boxedULong cb.2.2.2))) 15 (.i64 0))
              17 (.i64 (cb.2.2.1 - cb.1))) 19 (.i64 (cb.2.2.2 - cb.2.1)),
          jh, ⟨ar, u64, asc⟩⟩ := by
  rw [cellsToMacroCell_pre8 cells cid locs jh ar u64 asc hu h0]
  conv => lhs; arg 4; dsimp only [f_Algorithm_cellsToMacroCell_prog, List.drop]
  split_res_fuel 1
  rw [runJvmResFast_ifeq_fallthrough hne0]; norm_res_fuel
  conv => lhs; arg 4; dsimp only [f_Algorithm_cellsToMacroCell_prog, List.drop]
  heap_step_nonbranch_chunks; norm_res_fuel
  simp only [h0]
  split_res_fuel 1
  rw [runJvmResFast_invokestatic_step (stepStatic_ulongArrGetU64_heap hu)]; norm_res_fuel
  have hz : (0 : UInt32).toNat = 0 := rfl
  have hsh : ((32 : UInt32) &&& 63).toUInt64 = 32 := rfl
  rw [hz]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; simp only [hsh]
  simp only [h0]
  heap_step_nonbranch_chunks; norm_res_fuel
  conv => lhs; arg 5; simp only [hsh]
  split_res_fuel 1
  rw [runJvmResFast_invokestatic_step (stepStatic_cellBoundsLoop_heap hu)]; norm_res_fuel
  have hkh : ∀ x : UInt64, x >>> 32 = Algorithm.keyHi x := fun _ => rfl
  have hkl : ∀ x : UInt64, x &&& 4294967295 = Algorithm.keyLo x := fun _ => rfl
  conv => lhs; arg 5; simp only [hkh, hkl]
  rw [← hcb]
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_pair]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_pair]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]; norm_res_fuel
  heap_step_nonbranch_chunks; norm_res_fuel
  split_res_fuel 1
  rw [runJvmResFast_checkcast_boxedULong (Or.inl rfl)]
  heap_step_nonbranch_chunks; norm_res_fuel
  rfl

theorem cellsToMacroCell_equiv
    (cells : Array UInt64) (hsz : cells.size < 2 ^ 32)
    (cid : Nat) (locs : Nat → JvmVal) (jh : Jvm.JvmHeap AlgExt)
    (ar : List Algorithm.FlatHashLifeArena)
    (u64 : List (Array UInt64)) (asc : List Algorithm.AsciiBytes)
    (hu : u64[cid]? = some cells) (h0 : locs 0 = .ext (.u64Ref cid)) :
    ∃ st',
      runJvmResFast 180 f_Algorithm_cellsToMacroCell_prog 0 f_Algorithm_cellsToMacroCell_prog
          ⟨0, [], locs, jh, ⟨ar, u64, asc⟩⟩ =
        some (let r := Algorithm.cellsToMacroCell cells
              .pair (.boxedULong r.1) (.pair (.boxedULong r.2.1) (.ext (.mc r.2.2))), st') ∧
      st'.heap = ⟨ar, u64, asc⟩ := by
  by_cases hzero : cells.size = 0
  · have hn0 : cells.size.toUInt32 = 0 := by simp [hzero]
    exact cellsToMacroCell_zero cells hn0 cid locs jh ar u64 asc hu h0
  · have hne : cells.size.toUInt32 ≠ 0 := by
      intro h
      have hm := congrArg UInt32.toNat h
      rw [show cells.size.toUInt32.toNat = cells.size % 2 ^ 32 from rfl, Nat.mod_eq_of_lt hsz,
        show (0 : UInt32).toNat = 0 from rfl] at hm
      exact hzero hm
    have hne0 : (cells.size.toUInt32 == 0) = false := beq_false_of_ne hne
    obtain ⟨cb, hcb⟩ :
        ∃ cb, cb = Algorithm.cellBoundsLoop cells 1 cells.size.toUInt32
          (Algorithm.keyHi cells[0]!) (Algorithm.keyLo cells[0]!)
          (Algorithm.keyHi cells[0]!) (Algorithm.keyLo cells[0]!) := ⟨_, rfl⟩
    let locs71 :=
      setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal
        (setLocal (setLocal (setLocal locs 1 (.i32 cells.size.toUInt32)) 2 (.i64 cells[0]!))
          4 (.i64 (Algorithm.keyHi cells[0]!))) 6 (.i64 (Algorithm.keyLo cells[0]!)))
          8 (.pair (.boxedULong cb.1) (.pair (.boxedULong cb.2.1) (.pair (.boxedULong cb.2.2.1) (.boxedULong cb.2.2.2)))))
          9 (.pair (.boxedULong cb.2.1) (.pair (.boxedULong cb.2.2.1) (.boxedULong cb.2.2.2))))
          10 (.i64 cb.1)) 12 (.i64 cb.2.1))
          14 (.pair (.boxedULong cb.2.2.1) (.boxedULong cb.2.2.2))) 15 (.i64 0))
          17 (.i64 (cb.2.2.1 - cb.1))) 19 (.i64 (cb.2.2.2 - cb.2.1))
    have hpre71 := cellsToMacroCell_pre71 cells hne0 cid locs jh ar u64 asc hu h0 cb hcb
    have hdxdy :
        Algorithm.cellsToMacroCell cells =
          let span := max (cb.2.2.1 - cb.1) (cb.2.2.2 - cb.2.1) + 1
          let lvl := Algorithm.levelForSpanLoop span 5
          (cb.1, cb.2.1,
            Algorithm.keysToMacroCell
              (Algorithm.relativeKeysLoop cells 0 cells.size.toUInt32 cb.1 cb.2.1 [])
              0 0 (lvl - 4) (Algorithm.emptyAtHeight (lvl - 4))) := by
      simp only [Algorithm.cellsToMacroCell, hne0, Bool.false_eq_true, ↓reduceIte, ← hcb]
    rw [hdxdy]
    by_cases hle : cb.2.2.1 - cb.1 ≤ cb.2.2.2 - cb.2.1
    · have hmax : max (cb.2.2.1 - cb.1) (cb.2.2.2 - cb.2.1) = cb.2.2.2 - cb.2.1 := by
        dsimp only [max, Max.max]; simp [hle]
      rw [hpre71, hmax]
      have hpre82 :
          runJvmResFast 109 f_Algorithm_cellsToMacroCell_prog 71
              (f_Algorithm_cellsToMacroCell_prog.drop 71)
              ⟨71, [.i32 (if (cb.2.2.1 - cb.1 == cb.2.2.2 - cb.2.1) = true then 0
                  else if cb.2.2.1 - cb.1 < cb.2.2.2 - cb.2.1 then 4294967295 else 1)],
                locs71, jh, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast (56 + 45) f_Algorithm_cellsToMacroCell_prog 82
              (f_Algorithm_cellsToMacroCell_prog.drop 82)
              ⟨82, [.i32 5, .i64 (cb.2.2.2 - cb.2.1 + 1)],
                setLocal locs71 15 (.i64 (cb.2.2.2 - cb.2.1)), jh, ⟨ar, u64, asc⟩⟩ := by
        conv => lhs; arg 4; dsimp only [f_Algorithm_cellsToMacroCell_prog, List.drop]
        split_res_fuel 1
        rw [runJvmResFast_ifle_branch (by rw [compareUnsigned64_sle_zero]; exact decide_eq_true hle)]
        norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_cellsToMacroCell_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        congr 1
      rw [hpre82]
      exact cellsToMacroCell_tail (f := 56) hu
        (by simp [locs71, setLocal, h0]) (by simp [locs71, setLocal])
        (by simp [locs71, setLocal]) (by simp [locs71, setLocal])
    · have hmax : max (cb.2.2.1 - cb.1) (cb.2.2.2 - cb.2.1) = cb.2.2.1 - cb.1 := by
        dsimp only [max, Max.max]; simp [hle]
      rw [hpre71, hmax]
      have hpre82 :
          runJvmResFast 109 f_Algorithm_cellsToMacroCell_prog 71
              (f_Algorithm_cellsToMacroCell_prog.drop 71)
              ⟨71, [.i32 (if (cb.2.2.1 - cb.1 == cb.2.2.2 - cb.2.1) = true then 0
                  else if cb.2.2.1 - cb.1 < cb.2.2.2 - cb.2.1 then 4294967295 else 1)],
                locs71, jh, ⟨ar, u64, asc⟩⟩ =
            runJvmResFast (55 + 45) f_Algorithm_cellsToMacroCell_prog 82
              (f_Algorithm_cellsToMacroCell_prog.drop 82)
              ⟨82, [.i32 5, .i64 (cb.2.2.1 - cb.1 + 1)],
                setLocal locs71 15 (.i64 (cb.2.2.1 - cb.1)), jh, ⟨ar, u64, asc⟩⟩ := by
        conv => lhs; arg 4; dsimp only [f_Algorithm_cellsToMacroCell_prog, List.drop]
        split_res_fuel 1
        rw [runJvmResFast_ifle_fallthrough (by rw [compareUnsigned64_sle_zero]; exact decide_eq_false hle)]
        norm_res_fuel
        conv => lhs; arg 4; dsimp only [f_Algorithm_cellsToMacroCell_prog, List.drop]
        heap_step_nonbranch_chunks; norm_res_fuel
        congr 1
      rw [hpre82]
      exact cellsToMacroCell_tail (f := 55) hu
        (by simp [locs71, setLocal, h0]) (by simp [locs71, setLocal])
        (by simp [locs71, setLocal]) (by simp [locs71, setLocal])

end Algorithm.JvmVerification
