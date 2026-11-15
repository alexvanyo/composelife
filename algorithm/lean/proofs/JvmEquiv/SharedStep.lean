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

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

/-! ### Shared Generic & Domain Stepping Helpers (Heap & Result Decoders) -/

theorem runJvmResFast_checkcast_step {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {ty : String} {rest : List JvmInstr} {pc0 : Nat} {v v' : JvmVal}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h1 : Jvm.stepInstr algHooks (.checkcast ty) ⟨pc, v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, v' :: stkRest, locs, jh, hp⟩)) :
    runJvmResFast (f + 1) prog pc (.checkcast ty :: rest)
        ⟨pc0, v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest ⟨pc + 1, v' :: stkRest, locs, jh, hp⟩ := by
  simp only [runJvmResFast, Jvm.runJvmResFast]
  rw [show Jvm.stepInstr algHooks (.checkcast ty) ⟨pc, v :: stkRest, locs, jh, hp⟩ =
    .inl (some ⟨pc + 1, v' :: stkRest, locs, jh, hp⟩) from h1]
  simp only [↓reduceIte]

theorem runJvmResFast_instanceof_step {f : Nat} {prog : List JvmInstr} {pc : Nat}
    {ty : String} {rest : List JvmInstr} {pc0 : Nat} {v : JvmVal} {res : UInt32}
    {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (h1 : Jvm.stepInstr algHooks (.instanceof ty) ⟨pc, v :: stkRest, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 res :: stkRest, locs, jh, hp⟩)) :
    runJvmResFast (f + 1) prog pc (.instanceof ty :: rest)
        ⟨pc0, v :: stkRest, locs, jh, hp⟩ =
      runJvmResFast f prog (pc + 1) rest
        ⟨pc + 1, .i32 res :: stkRest, locs, jh, hp⟩ := by
  simp only [runJvmResFast, Jvm.runJvmResFast]
  rw [show Jvm.stepInstr algHooks (.instanceof ty) ⟨pc, v :: stkRest, locs, jh, hp⟩ =
    .inl (some ⟨pc + 1, .i32 res :: stkRest, locs, jh, hp⟩) from h1]
  simp only [↓reduceIte]

/-! ### String & Array Static Helpers -/

theorem stepStatic_stringsEncodeToByteArray
    {pc : Nat} {s : String} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .str s :: stkRest, locs, jh, hp⟩
      "kotlin/text/StringsKt" "encodeToByteArray" "(Ljava/lang/String;)[B" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
        (jh.alloc (.byteArray s.toUTF8.data)).2, hp⟩) := rfl

theorem stepStatic_stringValueOfInt
    {pc : Nat} {v : JvmVal} {stkRest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, v :: stkRest, locs, jh, hp⟩
      "java/lang/String" "valueOf" "(I)Ljava/lang/String;" =
      .inl (some ⟨pc + 1, .str (Jvm.i32ToDecimalString v.asI32) :: stkRest, locs, jh, hp⟩) := rfl

theorem stepStatic_arraysCopyOf_obj
    {pc : Nat} {newLen : UInt32} {addr : Nat} {stkRest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {elemCls : String} {elems : Array JvmVal}
    (hslt : newLen.toBitVec.slt 0#32 = false)
    (hget : jh.get? addr = some (.objArray elemCls elems)) :
    stepInvokeStatic ⟨pc, .i32 newLen :: .heapRef addr :: stkRest, locs, jh, hp⟩
      "java/util/Arrays" "copyOf" "([Ljava/lang/Object;I)[Ljava/lang/Object;" =
      let copied := Array.ofFn (n := newLen.toNat)
        (fun i => if h : i.val < elems.size then elems[i.val] else .null)
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stkRest, locs,
        (jh.alloc (.objArray elemCls copied)).2, hp⟩) := by
  simp only [stepInvokeStatic, Jvm.stepInstr, Jvm.stepInvokeStaticGeneric,
    Jvm.JvmVal.asI32, hslt, hget, Jvm.JvmHeap.alloc]
  rfl

theorem i32ToDecimalString_eq_toString (v : UInt32) :
    Jvm.i32ToDecimalString v = toString v.toInt32 := by
  simp only [Jvm.i32ToDecimalString, toString]
  have hi : v.toInt32.toInt =
      if v < 0x80000000 then (v.toNat : Int) else (v.toNat : Int) - 2 ^ 32 := by
    have h1 : v.toInt32.toInt = v.toBitVec.toInt := rfl
    rw [h1, BitVec.toInt]
    change (if 2 * v.toNat < 2 ^ 32 then (v.toNat : Int) else (v.toNat : Int) - 2 ^ 32) = _
    by_cases h : v < 0x80000000
    · have hlt : v.toNat < 2 ^ 31 := by
        have : (0x80000000 : UInt32).toNat = 2 ^ 31 := rfl
        rw [UInt32.lt_iff_toNat_lt, this] at h; exact h
      have h2 : 2 * v.toNat < 2 ^ 32 := by omega
      simp [h, h2]
    · have hge : ¬(v.toNat < 2 ^ 31) := by
        have : (0x80000000 : UInt32).toNat = 2 ^ 31 := rfl
        rw [UInt32.lt_iff_toNat_lt, this] at h; exact h
      have h2 : ¬(2 * v.toNat < 2 ^ 32) := by omega
      simp [h, h2]
  by_cases h : v < 0x80000000
  · simp [h, hi]
    exact (Int.toNat_of_nonneg (Int.natCast_nonneg _)).symm ▸ by
      change v.toNat.repr = Int.repr (Int.ofNat v.toNat); simp [Int.repr]
  · have hvlt : v.toNat < 2 ^ 32 := UInt32.toNat_lt v
    have hge : 2 ^ 31 ≤ v.toNat := by
      have : (0x80000000 : UInt32).toNat = 2 ^ 31 := rfl
      rw [UInt32.lt_iff_toNat_lt, this] at h; omega
    have hneg : (v.toNat : Int) - 2 ^ 32 = Int.negSucc (2 ^ 32 - v.toNat - 1) := by omega
    have hsuc : (2 ^ 32 - v.toNat - 1).succ = 0x100000000 - v.toNat := by omega
    simp only [h, ↓reduceIte] at hi
    rw [hi, hneg]
    simp only [h, ↓reduceIte, Int.repr, hsuc]

/-! ### Pair, ULongArray, U64Buf, GrowBuf & Domain Step Helpers -/

theorem stepVirtual_pairGetSecond
    {pc : Nat} {a b : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .pair a b :: rest, locs, jh, hp⟩
      "kotlin/Pair" "getSecond" "()Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, b :: rest, locs, jh, hp⟩) := rfl

theorem stepVirtual_mcCellNodeGetNw
    {pc : Nat} {h : UInt32} {nw ne sw se : Algorithm.MacroCell} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeVirtual ⟨pc, .ext (.mc (.cellNode h nw ne sw se)) :: rest, locs, jh, hp⟩
      "com/alexvanyo/composelife/model/MacroCell$CellNode" "getNw"
      "()Lcom/alexvanyo/composelife/model/MacroCell;" =
      .inl (some ⟨pc + 1, .ext (.mc nw) :: rest, locs, jh, hp⟩) := rfl

theorem stepSpecial_cellFrameNode_init
    {pc : Nat} {marker k f2 f1 f0 : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeSpecial
        ⟨pc, marker :: k :: f2 :: f1 :: f0 ::
          .allocRef "com/alexvanyo/composelife/algorithm/CellFrame$Node" ::
          .allocRef "com/alexvanyo/composelife/algorithm/CellFrame$Node" :: rest,
          locs, jh, hp⟩
      "com/alexvanyo/composelife/algorithm/CellFrame$Node" "<init>"
      "(IJJILkotlin/jvm/internal/DefaultConstructorMarker;)V" =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: rest, locs,
        (jh.alloc (.instance "com/alexvanyo/composelife/algorithm/CellFrame$Node"
          [("f0", f0), ("f1", f1), ("f2", f2), ("f3", k)])).2, hp⟩) := rfl

theorem stepStatic_ulongArrGetSize_heap
    {pc : Nat} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} {arr : Array UInt64}
    (hu : u64[id]? = some arr) :
    stepInvokeStatic ⟨pc, .ext (.u64Ref id) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULongArray" "getSize-impl" "([J)I" =
      .inl (some ⟨pc + 1, .i32 arr.size.toUInt32 :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have h1 : stepInvokeStatic ⟨pc, .ext (.u64Ref id) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULongArray" "getSize-impl" "([J)I" =
      match u64[id]? with
      | some arr => .inl (some ⟨pc + 1, .i32 arr.size.toUInt32 :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [h1, hu]

theorem stepStatic_ulongArrGetU64_heap
    {pc : Nat} {idx : JvmVal} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} {arr : Array UInt64}
    (hu : u64[id]? = some arr) :
    stepInvokeStatic ⟨pc, idx :: .ext (.u64Ref id) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" =
      .inl (some ⟨pc + 1, .i64 arr[idx.asI32.toNat]! :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have h1 : stepInvokeStatic ⟨pc, idx :: .ext (.u64Ref id) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      "kotlin/ULongArray" "get-s-VKNKU" "([JI)J" =
      match u64[id]? with
      | some arr => .inl (some ⟨pc + 1, .i64 arr[idx.asI32.toNat]! :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [h1, hu]

theorem stepStatic_u64BufEmpty_heap
    {pc : Nat} {cls : String} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt") :
    stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      cls "f_Algorithm_U64Buf_empty" "()[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref u64.length) :: rest, locs, jh,
        ⟨ar, u64 ++ [Algorithm.U64Buf.empty], asc⟩⟩) := by
  rcases hcls with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem stepStatic_u64BufPush_heap
    {pc : Nat} {cls : String} {x : JvmVal} {id : Nat} {rest : List JvmVal}
    {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
    {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} {arr : Array UInt64}
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (hu : u64[id]? = some arr) :
    stepInvokeStatic ⟨pc, x :: .ext (.u64Ref id) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      cls "f_Algorithm_U64Buf_push-3yFGk1Y" "([JJ)[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref u64.length) :: rest, locs, jh,
        ⟨ar, u64 ++ [Algorithm.U64Buf.push arr x.asI64], asc⟩⟩) := by
  rcases hcls with rfl | rfl | rfl | rfl | rfl <;>
    (refine Eq.trans (b := match u64[id]? with
      | some arr => Sum.inl (some (⟨pc + 1, .ext (.u64Ref u64.length) :: rest, locs, jh,
          ⟨ar, u64 ++ [Algorithm.U64Buf.push arr x.asI64], asc⟩⟩ : JvmState))
      | none => Sum.inr none) rfl (by rw [hu]))

theorem stepStatic_u64BufToArray_heap
    {pc : Nat} {cls : String} {id : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} {arr : Array UInt64}
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (hu : u64[id]? = some arr) :
    stepInvokeStatic ⟨pc, .ext (.u64Ref id) :: rest, locs, jh, ⟨ar, u64, asc⟩⟩
      cls "f_Algorithm_U64Buf_toArray-QwZRm1k" "([J)[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref u64.length) :: rest, locs, jh,
        ⟨ar, u64 ++ [Algorithm.U64Buf.toArray arr], asc⟩⟩) := by
  rcases hcls with rfl | rfl | rfl | rfl | rfl <;>
    (refine Eq.trans (b := match u64[id]? with
      | some arr => Sum.inl (some (⟨pc + 1, .ext (.u64Ref u64.length) :: rest, locs, jh,
          ⟨ar, u64 ++ [Algorithm.U64Buf.toArray arr], asc⟩⟩ : JvmState))
      | none => Sum.inr none) rfl (by rw [hu]))

theorem stepStatic_noCells_heap
    {pc : Nat} {cls : String} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes}
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt") :
    stepInvokeStatic ⟨pc, rest, locs, jh, ⟨ar, u64, asc⟩⟩
      cls "f_Algorithm_noCells" "()[J" =
      .inl (some ⟨pc + 1, .ext (.u64Ref u64.length) :: rest, locs, jh,
        ⟨ar, u64 ++ [#[]], asc⟩⟩) := by
  rcases hcls with rfl | rfl <;> rfl

theorem stepStatic_growBufEmpty_heap
    {pc : Nat} {cls : String} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hcls : cls = "Life105LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt") :
    stepInvokeStatic ⟨pc, .null :: rest, locs, jh, hp⟩
      cls "f_Algorithm_GrowBuf_empty___redArg" "(Ljava/lang/Object;)Ljava/lang/Object;" =
      .inl (some ⟨pc + 1, .ext (.strGrowBuf Algorithm.GrowBuf.empty) :: rest, locs, jh, hp⟩) := by
  rcases hcls with rfl | rfl | rfl | rfl <;> rfl

theorem stepStatic_skipSpaces_heap
    {pc : Nat} {cls : String} {limit pos : JvmVal} {addr : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, limit :: pos :: .heapRef addr :: rest, locs, jh, hp⟩
      cls "f_Algorithm_skipSpaces-BltQuoY" "([BII)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.skipSpaces ⟨elems⟩ pos.asI32 limit.asI32) :: rest,
        locs, jh, hp⟩) := by
  rcases hcls with rfl | rfl | rfl | rfl | rfl <;>
    (change (match decodeBytes (⟨pc, limit :: pos :: .heapRef addr :: rest, locs, jh, hp⟩ : JvmState)
        (.heapRef addr) with
      | some bytes =>
        Sum.inl (some (⟨pc + 1, .i32 (Algorithm.skipSpaces bytes pos.asI32 limit.asI32) :: rest,
          locs, jh, hp⟩ : JvmState))
      | none => Sum.inr none) = _
     simp only [decodeBytes, hget])

theorem stepStatic_parseInt32At_heap
    {pc : Nat} {cls : String} {limit pos : JvmVal} {addr : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "RleLeanKt")
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, limit :: pos :: .heapRef addr :: rest, locs, jh, hp⟩
      cls "f_Algorithm_parseInt32At-BltQuoY" "([BII)Ljava/lang/Object;" =
      let optPair := (Algorithm.parseInt32At ⟨elems⟩ pos.asI32 limit.asI32).map fun r =>
        (.boxedInt r.val.toUInt32, .boxedUInt r.next)
      let (res, h') := encodeOptScalarPair jh optPair
      .inl (some ⟨pc + 1, res :: rest, locs, h', hp⟩) := by
  rcases hcls with rfl | rfl | rfl <;>
    (change (match decodeBytes (⟨pc, limit :: pos :: .heapRef addr :: rest, locs, jh, hp⟩ : JvmState)
        (.heapRef addr) with
      | some bytes =>
        let optPair := (Algorithm.parseInt32At bytes pos.asI32 limit.asI32).map
          fun (r : Algorithm.ParsedInt32) => (JvmVal.boxedInt r.val.toUInt32, JvmVal.boxedUInt r.next)
        let (res, h') := encodeOptScalarPair jh optPair
        Sum.inl (some (⟨pc + 1, res :: rest, locs, h', hp⟩ : JvmState))
      | none => Sum.inr none) = _
     simp only [decodeBytes, hget])

theorem stepStatic_countChars_heap
    {pc : Nat} {n p limit : JvmVal} {addr : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, n :: p :: limit :: .heapRef addr :: rest, locs, jh, hp⟩
      "PlaintextLeanKt" "f_Algorithm_countChars-7IvYBaQ" "([BIII)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.countChars ⟨elems⟩ limit.asI32 p.asI32 n.asI32) :: rest,
        locs, jh, hp⟩) := by
  have hfn : stepInvokeStatic ⟨pc, n :: p :: limit :: .heapRef addr :: rest, locs, jh, hp⟩
      "PlaintextLeanKt" "f_Algorithm_countChars-7IvYBaQ" "([BIII)I" =
      match decodeBytes ⟨pc, n :: p :: limit :: .heapRef addr :: rest, locs, jh, hp⟩ (.heapRef addr) with
      | some bytes =>
        .inl (some ⟨pc + 1, .i32 (Algorithm.countChars bytes limit.asI32 p.asI32 n.asI32) :: rest,
          locs, jh, hp⟩)
      | none => .inr none := rfl
  rw [hfn]; simp only [decodeBytes, hget]

theorem stepStatic_decodeCharAt_heap
    {pc : Nat} {cls : String} {limit p : JvmVal} {addr : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {elems : Array UInt8}
    (hcls : cls = "Life105LeanKt" ∨ cls = "Life106LeanKt" ∨ cls = "MacroCellLeanKt" ∨
      cls = "PlaintextLeanKt" ∨ cls = "RleLeanKt")
    (hget : jh.get? addr = some (.byteArray elems)) :
    stepInvokeStatic ⟨pc, limit :: p :: .heapRef addr :: rest, locs, jh, hp⟩
      cls "f_Algorithm_decodeCharAt-BltQuoY" "([BII)Lkotlin/Pair;" =
      let r := Algorithm.decodeCharAt ⟨elems⟩ p.asI32 limit.asI32
      .inl (some ⟨pc + 1, .pair (.boxedUInt r.1) (.boxedUInt r.2) :: rest, locs, jh, hp⟩) := by
  rcases hcls with rfl | rfl | rfl | rfl | rfl <;>
    (refine Eq.trans (b := match jh.get? addr with
      | some (.byteArray el) =>
        let r := Algorithm.decodeCharAt ⟨el⟩ p.asI32 limit.asI32
        .inl (some ⟨pc + 1, .pair (.boxedUInt r.1) (.boxedUInt r.2) :: rest, locs, jh, hp⟩)
      | _ => .inr none) rfl ?_
     rw [hget])

theorem stepStatic_leafWithCell_heap
    {pc : Nat} {isAlive y x leaf : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, isAlive :: y :: x :: leaf :: rest, locs, jh, hp⟩
      "FlatHashLifeLeanKt" "f_Algorithm_leafWithCell-9LuH6mI" "(JIIZ)J" =
      .inl (some ⟨pc + 1, .i64 (Algorithm.leafWithCell leaf.asI64 x.asI32 y.asI32 (isAlive.asI32 != 0)) :: rest,
        locs, jh, hp⟩) := rfl

theorem stepStatic_makeLevel4Node_heap
    {pc : Nat} {se sw ne nw : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, se :: sw :: ne :: nw :: rest, locs, jh, hp⟩
      "FlatHashLifeLeanKt" "f_Algorithm_makeLevel4Node-2jIhpxI"
      "(JJJJ)Lcom/alexvanyo/composelife/model/MacroCell;" =
      .inl (some ⟨pc + 1, .ext (.mc (Algorithm.makeLevel4Node nw.asI64 ne.asI64 sw.asI64 se.asI64)) :: rest,
        locs, jh, hp⟩) := rfl

theorem stepStatic_makeCellNode_heap
    {pc : Nat} {se sw ne nw : Algorithm.MacroCell} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, .ext (.mc se) :: .ext (.mc sw) :: .ext (.mc ne) :: .ext (.mc nw) :: rest,
        locs, jh, hp⟩
      "FlatHashLifeLeanKt" "f_Algorithm_makeCellNode"
      "(Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;Lcom/alexvanyo/composelife/model/MacroCell;)Lcom/alexvanyo/composelife/model/MacroCell;" =
      .inl (some ⟨pc + 1, .ext (.mc (Algorithm.makeCellNode nw ne sw se)) :: rest, locs, jh, hp⟩) := rfl

theorem stepStatic_emptyAtHeight_heap
    {pc : Nat} {h : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, h :: rest, locs, jh, hp⟩
      "FlatHashLifeLeanKt" "f_Algorithm_emptyAtHeight-WZ4Q5Ns"
      "(I)Lcom/alexvanyo/composelife/model/MacroCell;" =
      .inl (some ⟨pc + 1, .ext (.mc (Algorithm.emptyAtHeight h.asI32)) :: rest, locs, jh, hp⟩) := rfl

theorem stepStatic_cellBoundsLoop_heap
    {pc : Nat} {maxY maxX minY minX limit i : JvmVal} {cId : Nat}
    {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {ar : List Algorithm.FlatHashLifeArena}
    {u64 : List (Array UInt64)} {asc : List Algorithm.AsciiBytes} {cells : Array UInt64}
    (hu : u64[cId]? = some cells) :
    stepInvokeStatic ⟨pc, maxY :: maxX :: minY :: minX :: limit :: i :: .ext (.u64Ref cId) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩
      "FlatHashLifeLeanKt" "f_Algorithm_cellBoundsLoop-Z0bPxiI" "([JIIJJJJ)Lkotlin/Pair;" =
      let r := Algorithm.cellBoundsLoop cells i.asI32 limit.asI32 minX.asI64 minY.asI64 maxX.asI64 maxY.asI64
      let boxed := .pair (.boxedULong r.1)
        (.pair (.boxedULong r.2.1) (.pair (.boxedULong r.2.2.1) (.boxedULong r.2.2.2)))
      .inl (some ⟨pc + 1, boxed :: rest, locs, jh, ⟨ar, u64, asc⟩⟩) := by
  have h1 : stepInvokeStatic ⟨pc, maxY :: maxX :: minY :: minX :: limit :: i :: .ext (.u64Ref cId) :: rest,
        locs, jh, ⟨ar, u64, asc⟩⟩
      "FlatHashLifeLeanKt" "f_Algorithm_cellBoundsLoop-Z0bPxiI" "([JIIJJJJ)Lkotlin/Pair;" =
      match u64[cId]? with
      | some cells =>
        let r := Algorithm.cellBoundsLoop cells i.asI32 limit.asI32 minX.asI64 minY.asI64 maxX.asI64 maxY.asI64
        let boxed := .pair (.boxedULong r.1)
          (.pair (.boxedULong r.2.1) (.pair (.boxedULong r.2.2.1) (.boxedULong r.2.2.2)))
        .inl (some ⟨pc + 1, boxed :: rest, locs, jh, ⟨ar, u64, asc⟩⟩)
      | none => .inr none := rfl
  rw [h1, hu]

theorem stepStatic_levelForSpanLoop_heap
    {pc : Nat} {lvl span : JvmVal} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, lvl :: span :: rest, locs, jh, hp⟩
      "FlatHashLifeLeanKt" "f_Algorithm_levelForSpanLoop-8GdB7C8" "(JI)I" =
      .inl (some ⟨pc + 1, .i32 (Algorithm.levelForSpanLoop span.asI64 lvl.asI32) :: rest,
        locs, jh, hp⟩) := rfl

theorem stepStatic_cellsToMacroCell_closed2_heap
    {pc : Nat} {rest : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} :
    stepInvokeStatic ⟨pc, rest, locs, jh, hp⟩
      "FlatHashLifeLeanKt" "f_Algorithm_cellsToMacroCell___closed__2" "()Lkotlin/Pair;" =
      .inl (some ⟨pc + 1,
        .pair (.boxedULong 2147483648) (.pair (.boxedULong 2147483648) (.ext (.mc (Algorithm.emptyAtHeight 1)))) :: rest,
        locs, jh, hp⟩) := rfl

/-! ### Heap U64List Representation (`List UInt64`) & Life106/Plaintext Decoders -/

inductive U64ListRep : Jvm.JvmHeap AlgExt → JvmVal → List UInt64 → Prop where
  | nil (jh : Jvm.JvmHeap AlgExt) (addr : Nat)
      (hget : jh.get? addr = some (.objArray "java/lang/Object" #[.boxedInt 0])) :
      U64ListRep jh (.heapRef addr) []
  | cons (jh : Jvm.JvmHeap AlgExt) (addr : Nat) (hd : UInt64) (tl : List UInt64) (tlVal : JvmVal)
      (hget : jh.get? addr = some (.objArray "java/lang/Object" #[.boxedInt 1, .boxedULong hd, tlVal]))
      (htl : U64ListRep jh tlVal tl) :
      U64ListRep jh (.heapRef addr) (hd :: tl)

theorem U64ListRep.alloc {jh : Jvm.JvmHeap AlgExt} {v : JvmVal} {xs : List UInt64}
    (obj : Jvm.HeapObj AlgExt) (h : U64ListRep jh v xs) :
    U64ListRep (jh.alloc obj).2 v xs := by
  induction h with
  | nil addr hget =>
    exact .nil _ addr (by
      have hlt : addr < jh.objects.size := (Array.getElem?_eq_some_iff.mp hget).1
      rw [jvmHeap_get?_alloc_lt jh obj hlt]; exact hget)
  | cons addr hd tl tlVal hget _ ih =>
    exact .cons _ addr hd tl tlVal (by
      have hlt : addr < jh.objects.size := (Array.getElem?_eq_some_iff.mp hget).1
      rw [jvmHeap_get?_alloc_lt jh obj hlt]; exact hget) ih

theorem U64ListRep.set_eq_of_lt {jh : Jvm.JvmHeap AlgExt} {v : JvmVal} {xs : List UInt64}
    (setAddr : Nat) (obj : Jvm.HeapObj AlgExt)
    (h : U64ListRep jh v xs) (hlt : jh.objects.size ≤ setAddr) :
    U64ListRep (jh.set setAddr obj) v xs := by
  induction h with
  | nil addr hget =>
    exact .nil _ addr (by simp [Jvm.JvmHeap.set, Nat.not_lt_of_ge hlt, hget])
  | cons addr hd tl tlVal hget _ ih =>
    exact .cons _ addr hd tl tlVal
      (by simp [Jvm.JvmHeap.set, Nat.not_lt_of_ge hlt, hget]) ih

theorem U64ListRep.decode {jh : Jvm.JvmHeap AlgExt} {v : JvmVal} {xs : List UInt64}
    (h : U64ListRep jh v xs) (bound : Nat) (hb : xs.length < bound) :
    decodeU64List jh bound v = some xs := by
  induction h generalizing bound with
  | nil addr hget =>
    cases bound with
    | zero => omega
    | succ b => simp [decodeU64List, hget]
  | cons addr hd tl tlVal hget _ ih =>
    cases bound with
    | zero => omega
    | succ b =>
      have ih1 := ih b (by simp at hb; omega)
      simp [decodeU64List, hget, ih1, unboxI64]

def decodeLife106Status (h : Jvm.JvmHeap AlgExt) : JvmVal → Option Algorithm.Life106Status
  | .allocRef "com/alexvanyo/composelife/model/Life106Status$Ok" => some .ok
  | .allocRef "com/alexvanyo/composelife/model/Life106Status$EmptyFile" => some .emptyFile
  | .heapRef a =>
    match h.get? a with
    | some (.instance "com/alexvanyo/composelife/model/Life106Status$InvalidHeader" flds) =>
      match flds.lookup "line" with
      | some (.str s) => some (.invalidHeader s)
      | _ => none
    | some (.instance "com/alexvanyo/composelife/model/Life106Status$InvalidLine" flds) =>
      match flds.lookup "lineIndex", flds.lookup "line" with
      | some ln, some (.str s) => some (.invalidLine ln.asI32 s)
      | _, _ => none
    | _ => none
  | _ => none

def decodeLife106Result (st : JvmState) : JvmVal → Option Algorithm.Life106Result
  | .heapRef a =>
    match st.jvmHeap.get? a with
    | some (.instance "com/alexvanyo/composelife/model/Life106Result" flds) =>
      match flds.lookup "status", flds.lookup "cells" with
      | some sv, some (.ext (.u64Ref cid)) =>
        match decodeLife106Status st.jvmHeap sv, st.heap.u64Arrays[cid]? with
        | some s, some cells => some ⟨s, cells⟩
        | _, _ => none
      | _, _ => none
    | _ => none
  | _ => none

theorem decodeLife106Result_encode
    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (res : Algorithm.Life106Result) :
    let (v, jh', u64s') := encodeLife106Result jh hp.u64Arrays res
    decodeLife106Result ⟨0, [], fun _ => .null, jh', { hp with u64Arrays := u64s' }⟩ v = some res := by
  rcases res with ⟨st, cells⟩
  cases st with
  | ok | emptyFile =>
    dsimp [encodeLife106Result, decodeLife106Result, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]
    rw [Array.getElem?_push_size]
    simp [decodeLife106Status, List.lookup]
  | invalidHeader line =>
    dsimp [encodeLife106Result, decodeLife106Result, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]
    rw [Array.getElem?_push_size]
    simp [decodeLife106Status, Jvm.JvmHeap.get?, List.lookup]
    rw [Array.getElem?_push_lt (by simp [Array.size_push] : jh.objects.size < (jh.objects.push _).size)]
    simp [Array.getElem_push, List.lookup]
  | invalidLine ln line =>
    dsimp [encodeLife106Result, decodeLife106Result, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?]
    rw [Array.getElem?_push_size]
    simp [decodeLife106Status, Jvm.JvmHeap.get?, List.lookup]
    rw [Array.getElem?_push_lt (by simp [Array.size_push] : jh.objects.size < (jh.objects.push _).size)]
    simp [Array.getElem_push, List.lookup, Jvm.JvmVal.asI32]

def decodePlaintextResult (st : JvmState) : JvmVal → Option Algorithm.PlaintextResult
  | .heapRef a =>
    match st.jvmHeap.get? a with
    | some (.instance "com/alexvanyo/composelife/model/PlaintextResult" flds) =>
      match flds.lookup "warnings", flds.lookup "cells" with
      | some (.heapRef wAddr), some (.ext (.u64Ref cid)) =>
        match st.jvmHeap.get? wAddr, st.heap.u64Arrays[cid]? with
        | some (.objArray _ warnVals), some cells =>
          (warnVals.toList.mapM (decodePlaintextWarning st.jvmHeap)).map fun ws =>
            ⟨ws.toArray, cells⟩
        | _, _ => none
      | some (.strArr #[]), some (.ext (.u64Ref cid)) =>
        st.heap.u64Arrays[cid]?.map fun cells => ⟨#[], cells⟩
      | _, _ => none
    | _ => none
  | _ => none

end Algorithm.JvmVerification
