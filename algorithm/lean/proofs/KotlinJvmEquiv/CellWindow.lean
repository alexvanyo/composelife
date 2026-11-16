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

import KotlinJvmBytecode
import models.CellWindowModel
import proofs.KotlinJvmEquiv.AlgKotlinProgs

namespace Algorithm.KotlinJvmVerification
open Algorithm.JvmVerification
open Algorithm.KotlinJvmBytecode
open Algorithm.KotlinModel

/-! # `CellWindow` (hand-written Kotlin value class): JVM bytecode equivalence

`CellWindow` is a `@JvmInline value class` over `IntRect`, so its members compile to static `-impl` methods taking
the `IntRect` (`.ext (.intRect l t r b)`), plus the boxed class's instance methods (`getIntRect`, `unbox-impl`,
`hashCode`, `equals`, the private constructor) that read the `intRect` field of a boxed `CellWindow`.

Each theorem runs a lifted program under `mkAlgKotlinHooks rp d sf`. Programs that call other `CellWindow` methods
are proven for every resolver `rp` that maps the lifted methods to their programs (`ResolvesCellWindowProgs`), at a
call depth `d` and callee fuel `sf` large enough for the calls, so calls between `CellWindow` methods run the
callee's real bytecode. The model is `CellWindowModel` (`models/CellWindowModel.lean`); the Compose values it is
encoded as are `cellWindowIntRect` (an `IntRect`) and `cellWindowOffset` (a packed `IntOffset`/`IntSize`).

`containedPoints-impl` is proven for every window, through both loops, for any fuel from
`cellWindowContainedPointsFuel`: it returns a fresh `ArrayList` of the model's points in row-major order and leaves
the rest of the heap unchanged (`CwFrame`).

`toString-impl` and `toString` are not related to a model: they build the string with an `invokedynamic`
`makeConcatWithConstants` taking the `IntRect`, which `jvm-lean`'s string concatenation does not model (it fails
closed on object arguments). Their theorems only state that the runs halt with no result.
-/

/-! ## Encodings and environment -/

/-- The `IntRect` a cell window `w` is represented by on the JVM (the value class's underlying value). -/
def cellWindowIntRect (w : CellWindowModel) : JvmVal :=
  .ext (.intRect w.left.toUInt32 w.top.toUInt32 w.right.toUInt32 w.bottom.toUInt32)

/-- The JVM class of a boxed `CellWindow`. -/
def cellWindowClass : String := "com/alexvanyo/composelife/model/CellWindow"

/-- The heap object of a boxed `CellWindow` wrapping `w` (what `box-impl` allocates). -/
def boxedCellWindowObj (w : CellWindowModel) : Jvm.HeapObj AlgExt :=
  .instance cellWindowClass [("intRect", cellWindowIntRect w)]

/-- The packed `IntOffset(x, y)` (also the packing of `IntSize(x, y)`), as in `:geometry`'s model (`packOffset`). -/
def cellWindowOffset (x y : Int32) : JvmVal := .i64 (geomPackOffset x y)

/-- `IntRect.center` of the window: `IntOffset(left + width / 2, top + height / 2)` (truncating division). -/
def cellWindowCenter (w : CellWindowModel) : Int32 × Int32 :=
  (w.left + w.width / 2, w.top + w.height / 2)

/-- `IntRect.hashCode()` of the window (a data class of four `Int`s). -/
def cellWindowHashCode (w : CellWindowModel) : Int32 :=
  ((w.left * 31 + w.top) * 31 + w.right) * 31 + w.bottom

/-- `rp` resolves every lifted method of the hand-written Kotlin (in particular `CellWindow`'s) to its program. -/
def ResolvesCellWindowProgs (rp : String → Option (List JvmInstr)) : Prop :=
  ∀ tag prog, algKotlinProgLookup tag = some prog → rp tag = some prog

theorem algKotlinProgLookup_resolvesCellWindowProgs : ResolvesCellWindowProgs algKotlinProgLookup :=
  fun _ _ h => h

/-- The result value and final JVM heap of a run. -/
def cellWindowRunOut (r : JvmVal × JvmState) : JvmVal × Jvm.JvmHeap AlgExt := (r.1, r.2.jvmHeap)

/-! ## Stepping lemmas

Runs are stated as `∃ p, Jvm.runJvmRes H fuel prog st = some p ∧ P p`; each lemma takes one step and leaves the
rest of the run as the new goal. -/

section Stepping

variable {H : Jvm.JvmHooks AlgExt AlgHeap} {fuel : Nat} {prog : List JvmInstr} {st st' : JvmState}
  {instr : JvmInstr} {P : JvmVal × JvmState → Prop}

private theorem run_step (hget : prog[st.pc]? = some instr) (hnb : Jvm.isBranchInstr instr = false)
    (hs : Jvm.stepInstr H instr st = .inl (some st'))
    (h : ∃ p, Jvm.runJvmRes H fuel prog st' = some p ∧ P p) :
    ∃ p, Jvm.runJvmRes H (fuel + 1) prog st = some p ∧ P p := by
  rw [Jvm.runJvmRes_nonbranch H fuel prog st instr hget hnb, hs]
  exact h

private theorem run_ret {v : JvmVal} (hget : prog[st.pc]? = some instr) (hnb : Jvm.isBranchInstr instr = false)
    (hs : Jvm.stepInstr H instr st = .inr (some v)) (h : P (v, st)) :
    ∃ p, Jvm.runJvmRes H (fuel + 1) prog st = some p ∧ P p := by
  rw [Jvm.runJvmRes_nonbranch H fuel prog st instr hget hnb, hs]
  exact ⟨_, rfl, h⟩

private theorem run_step_none (hget : prog[st.pc]? = some instr) (hnb : Jvm.isBranchInstr instr = false)
    (hs : Jvm.stepInstr H instr st = .inl (some st')) (h : Jvm.runJvmRes H fuel prog st' = none) :
    Jvm.runJvmRes H (fuel + 1) prog st = none := by
  rw [Jvm.runJvmRes_nonbranch H fuel prog st instr hget hnb, hs]
  exact h

private theorem run_fail (hget : prog[st.pc]? = some instr) (hnb : Jvm.isBranchInstr instr = false)
    (hs : Jvm.stepInstr H instr st = .inr none) :
    Jvm.runJvmRes H (fuel + 1) prog st = none := by
  rw [Jvm.runJvmRes_nonbranch H fuel prog st instr hget hnb, hs]

private theorem run_goto {t : Nat} (hget : prog[st.pc]? = some (.goto t)) :
    Jvm.runJvmRes H (fuel + 1) prog st = Jvm.runJvmRes H fuel prog { st with pc := t } := by
  simp [Jvm.runJvmRes, hget]
  rfl

private theorem run_if_icmpgt {t : Nat} {a b : UInt32} {rest : List JvmVal}
    (hget : prog[st.pc]? = some (.if_icmpgt t)) (hstk : st.stack = .i32 b :: .i32 a :: rest) :
    Jvm.runJvmRes H (fuel + 1) prog st =
      if b.toBitVec.slt a.toBitVec then Jvm.runJvmRes H fuel prog { st with pc := t, stack := rest }
      else Jvm.runJvmRes H fuel prog { st with pc := st.pc + 1, stack := rest } := by
  simp [Jvm.runJvmRes, hget, hstk]

variable {rp : String → Option (List JvmInstr)} {d sf : Nat}

private theorem run_ifne {t : Nat} {v : JvmVal} {x : UInt32} {rest : List JvmVal}
    (hget : prog[st.pc]? = some (.ifne t)) (hstk : st.stack = v :: rest) (hv : Jvm.JvmVal.asI32? v = some x) :
    Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (fuel + 1) prog st =
      if x == 0 then Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel prog { st with pc := st.pc + 1, stack := rest }
      else Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel prog { st with pc := t, stack := rest } := by
  cases d <;> simp [Jvm.runJvmRes, hget, hstk, mkAlgKotlinHooks, algKotlinHooksWith, hv] <;> split <;> simp_all

private theorem run_ifeq {t : Nat} {v : JvmVal} {x : UInt32} {rest : List JvmVal}
    (hget : prog[st.pc]? = some (.ifeq t)) (hstk : st.stack = v :: rest) (hv : Jvm.JvmVal.asI32? v = some x) :
    Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (fuel + 1) prog st =
      if x == 0 then Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel prog { st with pc := t, stack := rest }
      else Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel prog { st with pc := st.pc + 1, stack := rest } := by
  cases d <;> simp [Jvm.runJvmRes, hget, hstk, mkAlgKotlinHooks, algKotlinHooksWith, hv] <;> split <;> simp_all

/-- `desc` does not describe a `void` method (`algKotlinAfterCall` then pushes the result). -/
private theorem cw_endsWith_V_false {desc : String} (h : ¬ ")V".toList <:+ desc.toList) :
    desc.endsWith ")V" = false := by
  rw [String.endsWith, String.Slice.endsWith_string_eq_false_iff]
  simpa using h

private theorem hooks_isSubtypeOf : (mkAlgKotlinHooks rp d sf).isSubtypeOf = algKotlinIsSubtypeOf := by
  cases d <;> rfl

/-- A call to a lifted, non-`void` `CellWindow` static method runs the callee's program and pushes its result. -/
private theorem stepInstr_static_cellWindow {method desc : String} {tags : List Char} {callee : List JvmInstr}
    {res : JvmVal} {endSt : JvmState}
    (hrp : rp (algKotlinTag "CellWindow" method desc) = some callee)
    (htags : Jvm.parseMethodParamTags desc = tags) (hvoid : desc.endsWith ")V" = false)
    (hlen : tags.length ≤ st.stack.length)
    (hrun : Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) sf callee
      { pc := 0, stack := [],
        locals := (algKotlinParamSlots 0 tags (st.stack.take tags.length).reverse).foldl
            (fun loc (i, v) => Jvm.setLocal loc i v) (fun _ => .i32 0),
        jvmHeap := st.jvmHeap, heap := st.heap } = some (res, endSt)) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf) (.invokestatic "com/alexvanyo/composelife/model/CellWindow" method desc) st =
      .inl (some { st with
        pc := st.pc + 1, stack := res :: st.stack.drop tags.length,
        jvmHeap := endSt.jvmHeap, heap := endSt.heap }) := by
  subst htags
  have hlt : ¬ st.stack.length < (Jvm.parseMethodParamTags desc).length := by omega
  rw [show Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf) (.invokestatic "com/alexvanyo/composelife/model/CellWindow" method desc) st =
    (mkAlgKotlinHooks rp (d + 1) sf).stepInvokeStatic st "CellWindow" method desc from rfl]
  simp only [mkAlgKotlinHooks, algKotlinHooksWith, show isAlgKotlinLiftedClass "CellWindow" = true from rfl,
    ↓reduceIte, hlt, hrp, Option.map_some, hrun, algKotlinAfterCall, hvoid, Bool.false_eq_true]

/-- A call to a lifted `CellWindow` static method whose callee fails, fails. -/
private theorem stepInstr_static_cellWindow_fail {method desc : String} {tags : List Char}
    {callee : List JvmInstr}
    (hrp : rp (algKotlinTag "CellWindow" method desc) = some callee)
    (htags : Jvm.parseMethodParamTags desc = tags)
    (hlen : tags.length ≤ st.stack.length)
    (hrun : Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) sf callee
      { pc := 0, stack := [],
        locals := (algKotlinParamSlots 0 tags (st.stack.take tags.length).reverse).foldl
            (fun loc (i, v) => Jvm.setLocal loc i v) (fun _ => .i32 0),
        jvmHeap := st.jvmHeap, heap := st.heap } = none) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf) (.invokestatic "com/alexvanyo/composelife/model/CellWindow" method desc) st = .inr none := by
  subst htags
  have hlt : ¬ st.stack.length < (Jvm.parseMethodParamTags desc).length := by omega
  rw [show Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf) (.invokestatic "com/alexvanyo/composelife/model/CellWindow" method desc) st =
    (mkAlgKotlinHooks rp (d + 1) sf).stepInvokeStatic st "CellWindow" method desc from rfl]
  simp only [mkAlgKotlinHooks, algKotlinHooksWith, show isAlgKotlinLiftedClass "CellWindow" = true from rfl,
    ↓reduceIte, hlt, hrp, Option.map_some, hrun]

/-- `stepInstr_static_cellWindow` for a one-argument method. -/
private theorem stepInstr_static1_cellWindow {method desc : String} {callee : List JvmInstr}
    {res v : JvmVal} {endSt : JvmState} {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hrp : rp (algKotlinTag "CellWindow" method desc) = some callee)
    (htags : Jvm.parseMethodParamTags desc = ['L']) (hvoid : desc.endsWith ")V" = false)
    (hrun : Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) sf callee
      { pc := 0, stack := [], locals := Jvm.setLocal (fun _ => .i32 0) 0 v, jvmHeap := jh, heap := hp } =
        some (res, endSt)) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf) (.invokestatic "com/alexvanyo/composelife/model/CellWindow" method desc)
        ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, res :: stk, locs, endSt.jvmHeap, endSt.heap⟩) :=
  stepInstr_static_cellWindow hrp htags hvoid (by simp) hrun

/-- `stepInstr_static_cellWindow_fail` for a one-argument method. -/
private theorem stepInstr_static1_cellWindow_fail {method desc : String} {callee : List JvmInstr}
    {v : JvmVal} {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hrp : rp (algKotlinTag "CellWindow" method desc) = some callee)
    (htags : Jvm.parseMethodParamTags desc = ['L'])
    (hrun : Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) sf callee
      { pc := 0, stack := [], locals := Jvm.setLocal (fun _ => .i32 0) 0 v, jvmHeap := jh, heap := hp } = none) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf) (.invokestatic "com/alexvanyo/composelife/model/CellWindow" method desc)
        ⟨pc, v :: stk, locs, jh, hp⟩ = .inr none :=
  stepInstr_static_cellWindow_fail hrp htags (by simp) hrun

/-- `stepInstr_static_cellWindow` for a two-argument method. -/
private theorem stepInstr_static2_cellWindow {method desc : String} {callee : List JvmInstr}
    {res a b : JvmVal} {endSt : JvmState} {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hrp : rp (algKotlinTag "CellWindow" method desc) = some callee)
    (htags : Jvm.parseMethodParamTags desc = ['L', 'L']) (hvoid : desc.endsWith ")V" = false)
    (hrun : Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) sf callee
      { pc := 0, stack := [], locals := Jvm.setLocal (Jvm.setLocal (fun _ => .i32 0) 0 a) 1 b, jvmHeap := jh,
        heap := hp } = some (res, endSt)) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf) (.invokestatic "com/alexvanyo/composelife/model/CellWindow" method desc)
        ⟨pc, b :: a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, res :: stk, locs, endSt.jvmHeap, endSt.heap⟩) :=
  stepInstr_static_cellWindow hrp htags hvoid (by simp) hrun

/-- A call to a lifted, non-`void`, parameterless `CellWindow` instance method on a non-null receiver. -/
private theorem stepInstr_virtual0_cellWindow {method desc : String} {callee : List JvmInstr}
    {res recv : JvmVal} {endSt : JvmState} {pc : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hrp : rp (algKotlinTag "CellWindow" method desc) = some callee)
    (htags : Jvm.parseMethodParamTags desc = []) (hvoid : desc.endsWith ")V" = false)
    (hnn : Jvm.JvmVal.isNull recv = false)
    (hrun : Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) sf callee
      { pc := 0, stack := [], locals := Jvm.setLocal (fun _ => .i32 0) 0 recv, jvmHeap := jh, heap := hp } =
        some (res, endSt)) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf) (.invokevirtual "com/alexvanyo/composelife/model/CellWindow" method desc)
        ⟨pc, recv :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, res :: stk, locs, endSt.jvmHeap, endSt.heap⟩) := by
  rw [show Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf) (.invokevirtual "com/alexvanyo/composelife/model/CellWindow" method desc)
      ⟨pc, recv :: stk, locs, jh, hp⟩ =
    (mkAlgKotlinHooks rp (d + 1) sf).stepInvokeVirtual ⟨pc, recv :: stk, locs, jh, hp⟩ "CellWindow" method desc
    from rfl]
  simp only [mkAlgKotlinHooks, algKotlinHooksWith, show isAlgKotlinLiftedClass "CellWindow" = true from rfl,
    ↓reduceIte, htags, List.length_nil, Nat.zero_add, List.take_succ_cons, List.take_zero, List.reverse_singleton,
    List.length_cons, hnn, Bool.false_eq_true, hrp, Option.map_some,
    algKotlinParamSlots, List.foldl, hrun, algKotlinAfterCall, hvoid, List.drop_succ_cons, List.drop_zero]
  simp

/-- The lifted private constructor `CellWindow.<init>(IntRect)` called on a fresh `new CellWindow`. -/
private theorem stepInstr_init_cellWindow {callee : List JvmInstr} {v res : JvmVal} {endSt : JvmState} {pc : Nat}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (hrp : rp (algKotlinTag "CellWindow" "<init>" "(Landroidx/compose/ui/unit/IntRect;)V") = some callee)
    (hrun : Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) sf callee
      { pc := 0, stack := [],
        locals := Jvm.setLocal (Jvm.setLocal (fun _ => .i32 0) 0 (.heapRef jh.objects.size)) 1 v,
        jvmHeap := (jh.alloc (.instance cellWindowClass [])).2, heap := hp } = some (res, endSt)) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf)
        (.invokespecial "com/alexvanyo/composelife/model/CellWindow" "<init>" "(Landroidx/compose/ui/unit/IntRect;)V")
        ⟨pc, v :: .allocRef cellWindowClass :: .allocRef cellWindowClass :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stk, locs, endSt.jvmHeap, endSt.heap⟩) := by
  rw [show Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf)
      (.invokespecial "com/alexvanyo/composelife/model/CellWindow" "<init>" "(Landroidx/compose/ui/unit/IntRect;)V")
      ⟨pc, v :: .allocRef cellWindowClass :: .allocRef cellWindowClass :: stk, locs, jh, hp⟩ =
    (mkAlgKotlinHooks rp (d + 1) sf).stepInvokeSpecial
      ⟨pc, v :: .allocRef cellWindowClass :: .allocRef cellWindowClass :: stk, locs, jh, hp⟩
      "CellWindow" "<init>" "(Landroidx/compose/ui/unit/IntRect;)V" from rfl]
  have htags : Jvm.parseMethodParamTags "(Landroidx/compose/ui/unit/IntRect;)V" = ['L'] := rfl
  have hn : normalizeAlgKotlinClass cellWindowClass = "CellWindow" := rfl
  have hn' : normalizeAlgKotlinClass "CellWindow" = "CellWindow" := rfl
  simp only [mkAlgKotlinHooks, algKotlinHooksWith, show isAlgKotlinLiftedClass "CellWindow" = true from rfl,
    htags, hn, hn', beq_self_eq_true, Bool.and_self, ↓reduceIte, List.length_cons, List.length_nil,
    Nat.zero_add, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, List.reverse_singleton,
    List.foldl, Jvm.JvmHeap.alloc, hrp, Option.map_some,
    show algKotlinParamSlots 1 ['L'] [v] = [(1, v)] from rfl]
  simp only [Jvm.JvmHeap.alloc] at hrun
  simp only [hrun]

/-- `getfield intRect` of a boxed `CellWindow`. -/
private theorem stepInstr_getfield_cw {pc a : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {w : CellWindowModel}
    (ha : jh.get? a = some (boxedCellWindowObj w)) :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf)
        (.getfield "com/alexvanyo/composelife/model/CellWindow" "intRect" "Landroidx/compose/ui/unit/IntRect;") ⟨pc, .heapRef a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, cellWindowIntRect w :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr
  simp [ha, boxedCellWindowObj, hooks_isSubtypeOf, cellWindowClass]

/-- `putfield intRect` of an instance of `CellWindow`. -/
private theorem stepInstr_putfield_cw {pc a : Nat} {v : JvmVal} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {fs : List (String × JvmVal)}
    (ha : jh.get? a = some (.instance cellWindowClass fs)) :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf)
        (.putfield "com/alexvanyo/composelife/model/CellWindow" "intRect" "Landroidx/compose/ui/unit/IntRect;")
        ⟨pc, v :: .heapRef a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, stk, locs,
        jh.set a (.instance cellWindowClass (("intRect", v) :: fs.filter (fun (f, _) => f != "intRect"))), hp⟩) := by
  unfold Jvm.stepInstr
  simp [ha, Jvm.HeapObj.setField, hooks_isSubtypeOf, cellWindowClass]

/-- `instanceof CellWindow` of a boxed `CellWindow`. -/
private theorem stepInstr_instanceof_cw {pc a : Nat} {stk : List JvmVal} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {w : CellWindowModel}
    (ha : jh.get? a = some (boxedCellWindowObj w)) :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf) (.instanceof "com/alexvanyo/composelife/model/CellWindow")
        ⟨pc, .heapRef a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 1 :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr
  simp [Jvm.evalInstanceOf, Jvm.JvmHeap.checkInstanceOf, ha, boxedCellWindowObj, cellWindowClass,
    Jvm.HeapObj.matchesType]

/-- `checkcast` of a reference to an instance whose class is a subtype of the target. -/
private theorem stepInstr_checkcast_inst {cls c : String} {fs : List (String × JvmVal)} {pc a : Nat}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    (ha : jh.get? a = some (.instance c fs))
    (hsub : (cls == c || cls == "java/lang/Object" || algKotlinIsSubtypeOf c cls) = true) :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf) (.checkcast cls) ⟨pc, .heapRef a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef a :: stk, locs, jh, hp⟩) := by
  unfold Jvm.stepInstr
  simp only [Jvm.evalCheckCast, Jvm.JvmHeap.checkCast, Jvm.JvmHeap.checkInstanceOf, ha,
    Jvm.HeapObj.matchesType, hooks_isSubtypeOf, hsub, ↓reduceIte]

end Stepping

/-- One non-branching step whose hook result is computed by `rfl`. -/
macro "cw_step" : tactic => `(tactic| (refine run_step rfl rfl rfl ?_; try dsimp only))

/-- `cw_step`, then rewrites with the given local-slot facts. -/
macro "cw_step" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (refine run_step rfl rfl rfl ?_; try dsimp only; try simp only [$hs,*]))

/-- A step of a run that fails. -/
macro "cw_stepn" : tactic => `(tactic| (refine run_step_none rfl rfl rfl ?_; try dsimp only))

/-- `cw_stepn`, then rewrites with the given local-slot facts. -/
macro "cw_stepn" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (refine run_step_none rfl rfl rfl ?_; try dsimp only; try simp only [$hs,*]))

/-- A `goto`. -/
macro "cw_goto" : tactic => `(tactic| (rw [run_goto rfl]; try dsimp only))

/-- An `ifne`/`ifeq` on a concrete `Int` value. -/
macro "cw_ifne" : tactic =>
  `(tactic| (rw [run_ifne rfl rfl rfl]; simp only [show ((1 : UInt32) == 0) = false from rfl,
    show ((0 : UInt32) == 0) = true from rfl, Bool.false_eq_true, ↓reduceIte]; try dsimp only))
macro "cw_ifeq" : tactic =>
  `(tactic| (rw [run_ifeq rfl rfl rfl]; simp only [show ((1 : UInt32) == 0) = false from rfl,
    show ((0 : UInt32) == 0) = true from rfl, Bool.false_eq_true, ↓reduceIte]; try dsimp only))

/-- A return instruction ending the run, whose result and heaps are the expected ones by `rfl`. -/
macro "cw_ret" : tactic => `(tactic| exact run_ret rfl rfl rfl ⟨rfl, rfl, rfl⟩)

/-- A run that ends with result `v` and leaves both heaps as they were. -/
private theorem map_out_of_ex {r : Option (JvmVal × JvmState)} {v : JvmVal} {jh : Jvm.JvmHeap AlgExt}
    {hp : AlgHeap} (h : ∃ p, r = some p ∧ p.1 = v ∧ p.2.jvmHeap = jh ∧ p.2.heap = hp) :
    r.map cellWindowRunOut = some (v, jh) := by
  obtain ⟨⟨v', e⟩, he, hv, hj, -⟩ := h
  simp only at hv hj
  simp [he, cellWindowRunOut, hv, hj]

private theorem initKotlinJvmState_eq (slots : List (Nat × JvmVal)) (jh : Jvm.JvmHeap AlgExt) :
    initKotlinJvmState slots jh =
      ⟨0, [], slots.foldl (fun loc (i, v) => Jvm.setLocal loc i v) (fun _ => .i32 0), jh, {}⟩ := rfl

/-! ## Static getters on the underlying `IntRect` -/

section Getters

variable (rp : String → Option (List JvmInstr)) (d sf k : Nat) (w : CellWindowModel) (jh : Jvm.JvmHeap AlgExt)

/-- Runs a three-instruction getter (`aload 0`, `invokevirtual`, return) whose hook needs no heap. -/
macro "cw_getter" d:ident : tactic =>
  `(tactic| (apply map_out_of_ex (hp := {}); cases $d:ident <;> (cw_step; cw_step; cw_ret)))

theorem cellWindow_getTop_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getTop_impl_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (.i32 w.top.toUInt32, jh) := by cw_getter d

theorem cellWindow_getLeft_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getLeft_impl_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (.i32 w.left.toUInt32, jh) := by cw_getter d

theorem cellWindow_getBottom_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getBottom_impl_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (.i32 w.bottom.toUInt32, jh) := by cw_getter d

theorem cellWindow_getRight_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getRight_impl_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (.i32 w.right.toUInt32, jh) := by cw_getter d

theorem cellWindow_getWidth_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getWidth_impl_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (.i32 w.width.toUInt32, jh) := by cw_getter d

theorem cellWindow_getHeight_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getHeight_impl_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (.i32 w.height.toUInt32, jh) := by cw_getter d

theorem cellWindow_getSize_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getSize_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (cellWindowOffset w.width w.height, jh) := by cw_getter d

theorem cellWindow_getTopLeft_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getTopLeft_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (cellWindowOffset w.left w.top, jh) := by cw_getter d

theorem cellWindow_getTopRight_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getTopRight_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (cellWindowOffset w.right w.top, jh) := by cw_getter d

theorem cellWindow_getBottomRight_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getBottomRight_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (cellWindowOffset w.right w.bottom, jh) := by cw_getter d

theorem cellWindow_getBottomLeft_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getBottomLeft_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (cellWindowOffset w.left w.bottom, jh) := by cw_getter d

theorem cellWindow_getCenter_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getCenter_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (cellWindowOffset (cellWindowCenter w).1 (cellWindowCenter w).2, jh) := by cw_getter d

theorem cellWindow_hashCodeImpl_equiv :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_hashCode_impl_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (.i32 (cellWindowHashCode w).toUInt32, jh) := by cw_getter d

end Getters

/-! ### Getters on any local slots (for the callers inside `CellWindow`) -/

section GetterRuns

variable {rp : String → Option (List JvmInstr)} {d sf k : Nat} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
  {hp : AlgHeap} {l t r b : UInt32}

private theorem run_getTopImpl (h0 : locs 0 = .ext (.intRect l t r b)) :
    ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getTop_impl_prog ⟨0, [], locs, jh, hp⟩ = some p ∧
      p.1 = .i32 t ∧ p.2.jvmHeap = jh ∧ p.2.heap = hp := by
  cases d <;> (cw_step [h0]; cw_step; cw_ret)

private theorem run_getBottomImpl (h0 : locs 0 = .ext (.intRect l t r b)) :
    ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getBottom_impl_prog ⟨0, [], locs, jh, hp⟩ = some p ∧
      p.1 = .i32 b ∧ p.2.jvmHeap = jh ∧ p.2.heap = hp := by
  cases d <;> (cw_step [h0]; cw_step; cw_ret)

private theorem run_getLeftImpl (h0 : locs 0 = .ext (.intRect l t r b)) :
    ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getLeft_impl_prog ⟨0, [], locs, jh, hp⟩ = some p ∧
      p.1 = .i32 l ∧ p.2.jvmHeap = jh ∧ p.2.heap = hp := by
  cases d <;> (cw_step [h0]; cw_step; cw_ret)

private theorem run_getRightImpl (h0 : locs 0 = .ext (.intRect l t r b)) :
    ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getRight_impl_prog ⟨0, [], locs, jh, hp⟩ = some p ∧
      p.1 = .i32 r ∧ p.2.jvmHeap = jh ∧ p.2.heap = hp := by
  cases d <;> (cw_step [h0]; cw_step; cw_ret)

private theorem run_hashCodeImpl (h0 : locs 0 = .ext (.intRect l t r b)) :
    ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_hashCode_impl_prog ⟨0, [], locs, jh, hp⟩ = some p ∧
      p.1 = .i32 (intRectHashCode l t r b) ∧ p.2.jvmHeap = jh ∧ p.2.heap = hp := by
  cases d <;> (cw_step [h0]; cw_step; cw_ret)

end GetterRuns

/-! ## `constructor-impl`: the `init` block's `require`s -/

private theorem slt_toUInt32_eq (a b : Int32) : b.toUInt32.toBitVec.slt a.toUInt32.toBitVec = !decide (a ≤ b) := by
  rw [Jvm.int32_toUInt32_toBitVec, Jvm.int32_toUInt32_toBitVec]
  by_cases h : a ≤ b
  · have : b.toBitVec.slt a.toBitVec = false := by
      simp [Int32.le_iff_toBitVec_sle] at h
      simp [BitVec.slt, BitVec.sle] at h ⊢
      omega
    simp [h, this]
  · have : b.toBitVec.slt a.toBitVec = true := by
      simp [Int32.le_iff_toBitVec_sle] at h
      simp [BitVec.slt, BitVec.sle] at h ⊢
      omega
    simp [h, this]

section Constructor

variable {rp : String → Option (List JvmInstr)} {d sf k : Nat} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
  {hp : AlgHeap} {l t r b : Int32}

private theorem run_constructorImpl_valid
    (hl : locs 0 = .ext (.intRect l.toUInt32 t.toUInt32 r.toUInt32 b.toUInt32)) (htb : t ≤ b) (hlr : l ≤ r) :
    ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 23) CellWindow_constructor_impl_prog ⟨0, [], locs, jh, hp⟩ = some p ∧
      p.1 = .ext (.intRect l.toUInt32 t.toUInt32 r.toUInt32 b.toUInt32) ∧ p.2.jvmHeap = jh ∧ p.2.heap = hp := by
  cases d <;>
  · cw_step [hl]; cw_step; cw_step; cw_step [hl]; cw_step; cw_step [hl]; cw_step; cw_step [hl]; cw_step
    rw [run_if_icmpgt rfl rfl, slt_toUInt32_eq]
    simp only [htb, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cw_step; cw_goto; cw_ifne
    cw_step [hl]; cw_step; cw_step [hl]; cw_step
    rw [run_if_icmpgt rfl rfl, slt_toUInt32_eq]
    simp only [hlr, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cw_step; cw_goto; cw_ifne; cw_step [hl]
    exact run_ret rfl rfl rfl ⟨rfl, rfl, rfl⟩

private theorem run_constructorImpl_invalid
    (hl : locs 0 = .ext (.intRect l.toUInt32 t.toUInt32 r.toUInt32 b.toUInt32)) (h : ¬ (t ≤ b ∧ l ≤ r)) :
    Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 28) CellWindow_constructor_impl_prog ⟨0, [], locs, jh, hp⟩ = none := by
  by_cases htb : t ≤ b
  · have hlr : ¬ l ≤ r := fun h' => h ⟨htb, h'⟩
    cases d <;>
    · cw_stepn [hl]; cw_stepn; cw_stepn; cw_stepn [hl]; cw_stepn; cw_stepn [hl]; cw_stepn; cw_stepn [hl]
      cw_stepn
      rw [run_if_icmpgt rfl rfl, slt_toUInt32_eq]
      simp only [htb, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cw_stepn; cw_goto; cw_ifne
      cw_stepn [hl]; cw_stepn; cw_stepn [hl]; cw_stepn
      rw [run_if_icmpgt rfl rfl, slt_toUInt32_eq]
      simp only [hlr, decide_false, Bool.not_false, ↓reduceIte]
      cw_stepn; cw_ifne
      cw_stepn; cw_stepn; cw_stepn; cw_stepn; cw_stepn; cw_stepn; cw_stepn
      exact run_fail rfl rfl rfl
  · cases d <;>
    · cw_stepn [hl]; cw_stepn; cw_stepn; cw_stepn [hl]; cw_stepn; cw_stepn [hl]; cw_stepn; cw_stepn [hl]
      cw_stepn
      rw [run_if_icmpgt rfl rfl, slt_toUInt32_eq]
      simp only [htb, decide_false, Bool.not_false, ↓reduceIte]
      cw_stepn; cw_ifne
      cw_stepn; cw_stepn; cw_stepn; cw_stepn; cw_stepn; cw_stepn; cw_stepn
      exact run_fail rfl rfl rfl

end Constructor

theorem cellWindow_constructorImpl_equiv (rp : String → Option (List JvmInstr)) (d sf k : Nat) (l t r b : Int32)
    (jh : Jvm.JvmHeap AlgExt) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 28) CellWindow_constructor_impl_prog
        (initKotlinJvmState [(0, .ext (.intRect l.toUInt32 t.toUInt32 r.toUInt32 b.toUInt32))] jh)).map
          cellWindowRunOut =
      (mkCellWindowModel l t r b).map fun w => (cellWindowIntRect w, jh) := by
  rw [initKotlinJvmState_eq]
  by_cases h : t ≤ b ∧ l ≤ r
  · have hm : mkCellWindowModel l t r b = some ⟨l, t, r, b⟩ := by
      simp [mkCellWindowModel, isValidCellWindow, h.1, h.2]
    rw [hm]
    exact map_out_of_ex (run_constructorImpl_valid (k := k + 5) rfl h.1 h.2)
  · have hm : mkCellWindowModel l t r b = none := by
      simp only [mkCellWindowModel, isValidCellWindow, Bool.and_eq_true, decide_eq_true_eq]
      simp [h]
    rw [hm, run_constructorImpl_invalid rfl h]
    rfl

/-! ## Boxing: the private constructor, `box-impl`, `unbox-impl`, `getIntRect`, `hashCode` -/

private theorem cw_alloc_set (jh : Jvm.JvmHeap AlgExt) (o1 o2 : Jvm.HeapObj AlgExt) :
    (jh.alloc o1).2.set jh.objects.size o2 = (jh.alloc o2).2 := by
  simp [Jvm.JvmHeap.alloc, Jvm.JvmHeap.set, Array.set_push]

private theorem cw_nonvoid_I : "(Landroidx/compose/ui/unit/IntRect;)I".endsWith ")V" = false :=
  cw_endsWith_V_false (by simp; decide)

private theorem cw_nonvoid_rect :
    "(Landroidx/compose/ui/unit/IntRect;)Landroidx/compose/ui/unit/IntRect;".endsWith ")V" = false :=
  cw_endsWith_V_false (by simp; decide)

private theorem cw_nonvoid_unbox : "()Landroidx/compose/ui/unit/IntRect;".endsWith ")V" = false :=
  cw_endsWith_V_false (by simp; decide)

set_option maxRecDepth 4000 in
private theorem cw_tags_equals :
    Jvm.parseMethodParamTags "(Landroidx/compose/ui/unit/IntRect;Ljava/lang/Object;)Z" = ['L', 'L'] := by
  decide

private theorem hooks_beqExt {rp : String → Option (List JvmInstr)} {d sf : Nat} :
    (mkAlgKotlinHooks rp d sf).beqExt = algKotlinBeqExt := by
  cases d <;> rfl

private theorem cw_nonvoid_equals :
    "(Landroidx/compose/ui/unit/IntRect;Ljava/lang/Object;)Z".endsWith ")V" = false :=
  cw_endsWith_V_false (by simp; decide)

section Boxing

variable {rp : String → Option (List JvmInstr)} {d sf k : Nat} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
  {hp : AlgHeap}

private theorem run_init {a : Nat} {fs : List (String × JvmVal)} {v : JvmVal}
    (h0 : locs 0 = .heapRef a) (h1 : locs 1 = v) (ha : jh.get? a = some (.instance cellWindowClass fs)) :
    ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 6) CellWindow_init_prog
        ⟨0, [], locs, jh, hp⟩ = some p ∧
      p.1 = .unit ∧
      p.2.jvmHeap = jh.set a (.instance cellWindowClass (("intRect", v) :: fs.filter (fun (f, _) => f != "intRect"))) ∧
      p.2.heap = hp := by
  cases d <;>
  · cw_step [h0]; cw_step; cw_step [h0]; cw_step [h1]
    refine run_step rfl rfl (stepInstr_putfield_cw ha) ?_
    exact run_ret rfl rfl rfl ⟨rfl, rfl, rfl⟩

private theorem run_unbox {a : Nat} {w : CellWindowModel}
    (h0 : locs 0 = .heapRef a) (ha : jh.get? a = some (boxedCellWindowObj w)) :
    ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_unbox_impl_prog ⟨0, [], locs, jh, hp⟩ = some p ∧
      p.1 = cellWindowIntRect w ∧ p.2.jvmHeap = jh ∧ p.2.heap = hp := by
  cw_step [h0]
  refine run_step rfl rfl (stepInstr_getfield_cw ha) ?_
  exact run_ret rfl rfl rfl ⟨rfl, rfl, rfl⟩

private theorem run_getIntRect {a : Nat} {w : CellWindowModel}
    (h0 : locs 0 = .heapRef a) (ha : jh.get? a = some (boxedCellWindowObj w)) :
    ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getIntRect_prog ⟨0, [], locs, jh, hp⟩ = some p ∧
      p.1 = cellWindowIntRect w ∧ p.2.jvmHeap = jh ∧ p.2.heap = hp := by
  cw_step [h0]
  refine run_step rfl rfl (stepInstr_getfield_cw ha) ?_
  exact run_ret rfl rfl rfl ⟨rfl, rfl, rfl⟩

end Boxing

/-- The private constructor `CellWindow(intRect)` stores `intRect` in the instance it is called on. -/
theorem cellWindow_init_equiv (rp : String → Option (List JvmInstr)) (d sf k : Nat) (w : CellWindowModel)
    (jh : Jvm.JvmHeap AlgExt) (a : Nat) (fs : List (String × JvmVal))
    (ha : jh.get? a = some (.instance cellWindowClass fs)) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 6) CellWindow_init_prog
        (initKotlinJvmState [(0, .heapRef a), (1, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (.unit, jh.set a (.instance cellWindowClass
        (("intRect", cellWindowIntRect w) :: fs.filter (fun (f, _) => f != "intRect")))) := by
  rw [initKotlinJvmState_eq]
  exact map_out_of_ex (run_init rfl rfl ha)

/-- `box-impl` allocates a fresh boxed `CellWindow` holding the window's `IntRect`. -/
theorem cellWindow_boxImpl_equiv (rp : String → Option (List JvmInstr)) (hR : ResolvesCellWindowProgs rp)
    (d sf k : Nat) (w : CellWindowModel) (jh : Jvm.JvmHeap AlgExt) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 6)) (k + 5) CellWindow_box_impl_prog
        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
      some (.heapRef jh.objects.size, (jh.alloc (boxedCellWindowObj w)).2) := by
  rw [initKotlinJvmState_eq]
  have hrp := hR (algKotlinTag "CellWindow" "<init>" "(Landroidx/compose/ui/unit/IntRect;)V")
    CellWindow_init_prog rfl
  obtain ⟨⟨res, endSt⟩, hrun, -, hjh, hhp⟩ := run_init (rp := rp) (d := d) (k := sf)
    (locs := Jvm.setLocal (Jvm.setLocal (fun _ => .i32 0) 0 (.heapRef jh.objects.size)) 1 (cellWindowIntRect w))
    (hp := {}) rfl rfl (Jvm.jvmHeap_get?_alloc_self jh (.instance cellWindowClass []))
  simp only at hjh hhp
  apply map_out_of_ex (hp := {})
  cw_step; cw_step; cw_step
  refine run_step rfl rfl (stepInstr_init_cellWindow hrp hrun) ?_
  refine run_ret rfl rfl rfl ⟨rfl, ?_, ?_⟩
  · simp only [hjh, List.filter_nil]
    exact cw_alloc_set jh _ _
  · exact hhp

/-- `unbox-impl` of a boxed `CellWindow` returns its `IntRect`. -/
theorem cellWindow_unboxImpl_equiv (rp : String → Option (List JvmInstr)) (d sf k : Nat) (w : CellWindowModel)
    (jh : Jvm.JvmHeap AlgExt) (a : Nat) (ha : jh.get? a = some (boxedCellWindowObj w)) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_unbox_impl_prog
        (initKotlinJvmState [(0, .heapRef a)] jh)).map cellWindowRunOut =
      some (cellWindowIntRect w, jh) := by
  rw [initKotlinJvmState_eq]
  exact map_out_of_ex (run_unbox rfl ha)

/-- `getIntRect` of a boxed `CellWindow` returns its `IntRect`. -/
theorem cellWindow_getIntRect_equiv (rp : String → Option (List JvmInstr)) (d sf k : Nat) (w : CellWindowModel)
    (jh : Jvm.JvmHeap AlgExt) (a : Nat) (ha : jh.get? a = some (boxedCellWindowObj w)) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) CellWindow_getIntRect_prog
        (initKotlinJvmState [(0, .heapRef a)] jh)).map cellWindowRunOut =
      some (cellWindowIntRect w, jh) := by
  rw [initKotlinJvmState_eq]
  exact map_out_of_ex (run_getIntRect rfl ha)

private theorem cw_hashCode_toUInt32 (w : CellWindowModel) :
    intRectHashCode w.left.toUInt32 w.top.toUInt32 w.right.toUInt32 w.bottom.toUInt32 =
      (cellWindowHashCode w).toUInt32 := by
  simp [intRectHashCode, cellWindowHashCode, Int32.toUInt32_add, Int32.toUInt32_mul]
  rfl

/-- `hashCode` of a boxed `CellWindow` is its `IntRect`'s hash code (through `hashCode-impl`). -/
theorem cellWindow_hashCode_equiv (rp : String → Option (List JvmInstr)) (hR : ResolvesCellWindowProgs rp)
    (d sf k : Nat) (w : CellWindowModel) (jh : Jvm.JvmHeap AlgExt) (a : Nat)
    (ha : jh.get? a = some (boxedCellWindowObj w)) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 3)) (k + 4) CellWindow_hashCode_prog
        (initKotlinJvmState [(0, .heapRef a)] jh)).map cellWindowRunOut =
      some (.i32 (cellWindowHashCode w).toUInt32, jh) := by
  rw [initKotlinJvmState_eq]
  have hrp := hR (algKotlinTag "CellWindow" "hashCode-impl" "(Landroidx/compose/ui/unit/IntRect;)I")
    CellWindow_hashCode_impl_prog rfl
  obtain ⟨⟨res, endSt⟩, hrun, hres, hjh, hhp⟩ := run_hashCodeImpl (rp := rp) (d := d) (k := sf)
    (locs := Jvm.setLocal (fun _ => .i32 0) 0 (cellWindowIntRect w)) (jh := jh) (hp := {}) rfl
  simp only at hres hjh hhp
  apply map_out_of_ex (hp := {})
  cw_step
  refine run_step rfl rfl (stepInstr_getfield_cw ha) ?_
  refine run_step rfl rfl (stepInstr_static1_cellWindow hrp rfl cw_nonvoid_I hrun) ?_
  refine run_ret rfl rfl rfl ⟨?_, hjh, hhp⟩
  simp only [hres, cw_hashCode_toUInt32]
  rfl

/-! ## Equality: `equals-impl0`, `equals-impl`, `equals` -/

private theorem cw_int32_toUInt32_inj {a b : Int32} : a.toUInt32 = b.toUInt32 ↔ a = b :=
  ⟨fun h => by cases a; cases b; cases h; rfl, fun h => h ▸ rfl⟩

private theorem cw_beq_intRect (w1 w2 : CellWindowModel) :
    Jvm.JvmVal.beqVal algKotlinBeqExt (cellWindowIntRect w1) (cellWindowIntRect w2) = decide (w1 = w2) := by
  rcases w1 with ⟨l1, t1, r1, b1⟩
  rcases w2 with ⟨l2, t2, r2, b2⟩
  simp [cellWindowIntRect, Jvm.JvmVal.beqVal, algKotlinBeqExt, cw_int32_toUInt32_inj, Bool.and_assoc,
    Bool.beq_eq_decide_eq]

/-- `equals-impl0` compares two windows' `IntRect`s structurally. -/
theorem cellWindow_equalsImpl0_equiv (rp : String → Option (List JvmInstr)) (d sf k : Nat)
    (w1 w2 : CellWindowModel) (jh : Jvm.JvmHeap AlgExt) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 4) CellWindow_equals_impl0_prog
        (initKotlinJvmState [(0, cellWindowIntRect w1), (1, cellWindowIntRect w2)] jh)).map cellWindowRunOut =
      some (.bool (decide (w1 = w2)), jh) := by
  rw [← cw_beq_intRect]
  apply map_out_of_ex (hp := {})
  cases d <;> (cw_step; cw_step; cw_step; cw_ret)

section Equals

variable {rp : String → Option (List JvmInstr)} {d sf k : Nat} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt}
  {hp : AlgHeap}

/-- `equals-impl` with a boxed `CellWindow` as the other object. -/
private theorem run_equalsImpl_boxed (hR : ResolvesCellWindowProgs rp) {w w' : CellWindowModel} {a : Nat}
    (h0 : locs 0 = cellWindowIntRect w) (h1 : locs 1 = .heapRef a)
    (ha : jh.get? a = some (boxedCellWindowObj w')) :
    ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 3)) (k + 12) CellWindow_equals_impl_prog ⟨0, [], locs, jh, hp⟩ =
        some p ∧
      p.1 = .i32 (if w = w' then 1 else 0) ∧ p.2.jvmHeap = jh ∧ p.2.heap = hp := by
  have hrp := hR (algKotlinTag "CellWindow" "unbox-impl" "()Landroidx/compose/ui/unit/IntRect;")
    CellWindow_unbox_impl_prog rfl
  obtain ⟨⟨res, endSt⟩, hrun, hres, hjh, hhp⟩ := run_unbox (rp := rp) (d := d) (k := sf)
    (locs := Jvm.setLocal (fun _ => .i32 0) 0 (.heapRef a)) (jh := jh) (hp := hp) rfl ha
  simp only at hres hjh hhp
  subst hres
  cw_step [h1]
  refine run_step rfl rfl (stepInstr_instanceof_cw ha) ?_
  cw_ifne
  cw_step [h1]
  refine run_step rfl rfl (stepInstr_checkcast_inst (c := cellWindowClass) ha rfl) ?_
  refine run_step rfl rfl (stepInstr_virtual0_cellWindow hrp rfl cw_nonvoid_unbox rfl hrun) ?_
  simp only [hjh, hhp]
  cw_step [h0]; cw_step; cw_step
  rw [run_ifne rfl rfl rfl, hooks_beqExt, cw_beq_intRect]
  dsimp only
  by_cases hw : w = w'
  · simp only [hw, decide_true, ↓reduceIte, show ((1 : UInt32) == 0) = false from rfl, Bool.false_eq_true]
    cw_step
    exact run_ret rfl rfl rfl ⟨rfl, rfl, rfl⟩
  · simp only [hw, decide_false, Bool.false_eq_true, ↓reduceIte, show ((0 : UInt32) == 0) = true from rfl]
    cw_step
    exact run_ret rfl rfl rfl ⟨rfl, rfl, rfl⟩

/-- `equals-impl` with an object that is not a `CellWindow`. -/
private theorem run_equalsImpl_other {other : JvmVal} (h1 : locs 1 = other)
    (hni : Jvm.evalInstanceOf (mkAlgKotlinHooks rp d sf) jh cellWindowClass other = false) :
    ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 5) CellWindow_equals_impl_prog ⟨0, [], locs, jh, hp⟩ = some p ∧
      p.1 = .i32 0 ∧ p.2.jvmHeap = jh ∧ p.2.heap = hp := by
  simp only [cellWindowClass] at hni
  cw_step [h1]; cw_step
  simp only [hni, Bool.false_eq_true, ↓reduceIte]
  cw_ifne
  cases d <;> (cw_step; exact run_ret rfl rfl rfl ⟨rfl, rfl, rfl⟩)

end Equals

/-- `equals-impl` with a boxed `CellWindow`: whether the two windows are equal. -/
theorem cellWindow_equalsImpl_boxed_equiv (rp : String → Option (List JvmInstr)) (hR : ResolvesCellWindowProgs rp)
    (d sf k : Nat) (w w' : CellWindowModel) (jh : Jvm.JvmHeap AlgExt) (a : Nat)
    (ha : jh.get? a = some (boxedCellWindowObj w')) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 3)) (k + 12) CellWindow_equals_impl_prog
        (initKotlinJvmState [(0, cellWindowIntRect w), (1, .heapRef a)] jh)).map cellWindowRunOut =
      some (.i32 (if w = w' then 1 else 0), jh) := by
  rw [initKotlinJvmState_eq]
  exact map_out_of_ex (run_equalsImpl_boxed hR rfl rfl ha)

/-- `equals-impl` with an object that is not a `CellWindow` (for example `null` or another class): `false`. -/
theorem cellWindow_equalsImpl_other_equiv (rp : String → Option (List JvmInstr)) (d sf k : Nat)
    (w : CellWindowModel) (jh : Jvm.JvmHeap AlgExt) (other : JvmVal)
    (hni : Jvm.evalInstanceOf (mkAlgKotlinHooks rp d sf) jh cellWindowClass other = false) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 5) CellWindow_equals_impl_prog
        (initKotlinJvmState [(0, cellWindowIntRect w), (1, other)] jh)).map cellWindowRunOut =
      some (.i32 0, jh) := by
  rw [initKotlinJvmState_eq]
  exact map_out_of_ex (run_equalsImpl_other rfl hni)

/-- `equals` of a boxed `CellWindow` with another boxed `CellWindow`: whether the two windows are equal. -/
theorem cellWindow_equals_boxed_equiv (rp : String → Option (List JvmInstr)) (hR : ResolvesCellWindowProgs rp)
    (d sf k : Nat) (w w' : CellWindowModel) (jh : Jvm.JvmHeap AlgExt) (a a' : Nat)
    (ha : jh.get? a = some (boxedCellWindowObj w)) (ha' : jh.get? a' = some (boxedCellWindowObj w')) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 2) (sf + 12)) (k + 5) CellWindow_equals_prog
        (initKotlinJvmState [(0, .heapRef a), (1, .heapRef a')] jh)).map cellWindowRunOut =
      some (.i32 (if w = w' then 1 else 0), jh) := by
  rw [initKotlinJvmState_eq]
  have hrp := hR (algKotlinTag "CellWindow" "equals-impl" "(Landroidx/compose/ui/unit/IntRect;Ljava/lang/Object;)Z")
    CellWindow_equals_impl_prog rfl
  obtain ⟨⟨res, endSt⟩, hrun, hres, hjh, hhp⟩ := run_equalsImpl_boxed (rp := rp) (d := d) (sf := sf + 9) (k := sf)
    (locs := Jvm.setLocal (Jvm.setLocal (fun _ => .i32 0) 0 (cellWindowIntRect w)) 1 (.heapRef a')) (jh := jh)
    (hp := {}) hR rfl rfl ha'
  simp only at hres hjh hhp
  apply map_out_of_ex (hp := {})
  cw_step
  refine run_step rfl rfl (stepInstr_getfield_cw ha) ?_
  cw_step
  refine run_step rfl rfl (stepInstr_static2_cellWindow hrp cw_tags_equals cw_nonvoid_equals hrun) ?_
  exact run_ret rfl rfl rfl ⟨hres, hjh, hhp⟩

/-- `equals` of a boxed `CellWindow` with an object that is not a `CellWindow`: `false`. -/
theorem cellWindow_equals_other_equiv (rp : String → Option (List JvmInstr)) (hR : ResolvesCellWindowProgs rp)
    (d sf k : Nat) (w : CellWindowModel) (jh : Jvm.JvmHeap AlgExt) (a : Nat) (other : JvmVal)
    (ha : jh.get? a = some (boxedCellWindowObj w))
    (hni : Jvm.evalInstanceOf (mkAlgKotlinHooks rp d (sf + 5)) jh cellWindowClass other = false) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 5)) (k + 5) CellWindow_equals_prog
        (initKotlinJvmState [(0, .heapRef a), (1, other)] jh)).map cellWindowRunOut =
      some (.i32 0, jh) := by
  rw [initKotlinJvmState_eq]
  have hrp := hR (algKotlinTag "CellWindow" "equals-impl" "(Landroidx/compose/ui/unit/IntRect;Ljava/lang/Object;)Z")
    CellWindow_equals_impl_prog rfl
  obtain ⟨⟨res, endSt⟩, hrun, hres, hjh, hhp⟩ := run_equalsImpl_other (rp := rp) (d := d) (sf := sf + 5) (k := sf)
    (locs := Jvm.setLocal (Jvm.setLocal (fun _ => .i32 0) 0 (cellWindowIntRect w)) 1 other) (jh := jh)
    (hp := {}) rfl hni
  simp only at hres hjh hhp
  apply map_out_of_ex (hp := {})
  cw_step
  refine run_step rfl rfl (stepInstr_getfield_cw ha) ?_
  cw_step
  refine run_step rfl rfl (stepInstr_static2_cellWindow hrp cw_tags_equals cw_nonvoid_equals hrun) ?_
  exact run_ret rfl rfl rfl ⟨hres, hjh, hhp⟩

/-! ## `translate` -/

private theorem cw_offsetX (x y : Int32) : intOffsetX (geomPackOffset x y) = x.toUInt32 := by
  show intOffsetX (packIntOffset x.toUInt32 y.toUInt32) = x.toUInt32
  simp only [intOffsetX, packIntOffset]
  apply UInt32.toBitVec_inj.mp
  ext i hi
  have h1 : 32 + i < 64 := by omega
  have h2 : ¬ 32 + i < 32 := by omega
  have h3 : i < 64 := by omega
  simp [h1, h2, h3, BitVec.getLsbD_eq_getElem hi]

private theorem cw_offsetY (x y : Int32) : intOffsetY (geomPackOffset x y) = y.toUInt32 := by
  show intOffsetY (packIntOffset x.toUInt32 y.toUInt32) = y.toUInt32
  simp only [intOffsetY, packIntOffset]
  apply UInt32.toBitVec_inj.mp
  ext i hi
  simp

/-- `translate` moves the window's `IntRect` by the offset, then checks it with `constructor-impl`: the model's
`CellWindowModel.translate`, which fails (an `IllegalArgumentException`) when the moved window is not valid. -/
theorem cellWindow_translate_equiv (rp : String → Option (List JvmInstr)) (hR : ResolvesCellWindowProgs rp)
    (d sf k : Nat) (w : CellWindowModel) (dx dy : Int32) (jh : Jvm.JvmHeap AlgExt) :
    (Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 28)) (k + 5) CellWindow_translate_prog
        (initKotlinJvmState [(0, cellWindowIntRect w), (1, cellWindowOffset dx dy)] jh)).map cellWindowRunOut =
      (w.translate dx dy).map fun w' => (cellWindowIntRect w', jh) := by
  rw [initKotlinJvmState_eq]
  have hrp := hR (algKotlinTag "CellWindow" "constructor-impl"
    "(Landroidx/compose/ui/unit/IntRect;)Landroidx/compose/ui/unit/IntRect;") CellWindow_constructor_impl_prog rfl
  have hx := cw_offsetX dx dy
  have hy := cw_offsetY dx dy
  by_cases h : w.top + dy ≤ w.bottom + dy ∧ w.left + dx ≤ w.right + dx
  · have hm : w.translate dx dy = some ⟨w.left + dx, w.top + dy, w.right + dx, w.bottom + dy⟩ := by
      simp [CellWindowModel.translate, mkCellWindowModel, isValidCellWindow, h.1, h.2]
    rw [hm]
    obtain ⟨⟨res, endSt⟩, hrun, hres, hjh, hhp⟩ := run_constructorImpl_valid (rp := rp) (d := d) (k := sf + 5)
      (locs := Jvm.setLocal (fun _ => .i32 0) 0 (.ext (.intRect (w.left + dx).toUInt32 (w.top + dy).toUInt32
        (w.right + dx).toUInt32 (w.bottom + dy).toUInt32))) (jh := jh) (hp := {}) rfl h.1 h.2
    simp only at hres hjh hhp
    apply map_out_of_ex (hp := {})
    cw_step; cw_step; cw_step
    simp only [hx, hy, Jvm.int32_toUInt32_add]
    refine run_step rfl rfl (stepInstr_static1_cellWindow hrp rfl cw_nonvoid_rect hrun) ?_
    exact run_ret rfl rfl rfl ⟨hres, hjh, hhp⟩
  · have hm : w.translate dx dy = none := by
      simp only [CellWindowModel.translate, mkCellWindowModel, isValidCellWindow, Bool.and_eq_true,
        decide_eq_true_eq]
      simp [h]
    rw [hm]
    have hrun := run_constructorImpl_invalid (rp := rp) (d := d) (sf := sf + 28) (k := sf)
      (locs := Jvm.setLocal (fun _ => .i32 0) 0 (.ext (.intRect (w.left + dx).toUInt32 (w.top + dy).toUInt32
        (w.right + dx).toUInt32 (w.bottom + dy).toUInt32))) (jh := jh) (hp := {}) rfl h
    suffices hn : Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 28)) (k + 5) CellWindow_translate_prog
        ⟨0, [], [(0, cellWindowIntRect w), (1, cellWindowOffset dx dy)].foldl
          (fun loc (i, v) => Jvm.setLocal loc i v) (fun _ => .i32 0), jh, {}⟩ = none by
      rw [hn]; rfl
    cw_stepn; cw_stepn; cw_stepn
    simp only [hx, hy, Jvm.int32_toUInt32_add]
    exact run_fail rfl rfl (stepInstr_static1_cellWindow_fail hrp rfl hrun)

/-! ## `containedPoints-impl`

The bytecode of `(top until bottom).flatMap { row -> (left until right).map { column -> IntOffset(column, row) } }`
iterates two `IntProgressionIterator`s, collects each row into a fresh `ArrayList` and appends it to the result
`ArrayList` with `CollectionsKt.addAll`. -/

/-- An `IntProgressionIterator` (step 1) with final element `fin`, `hasNext` flag `has` and next value `cur`. -/
def cwIt (fin cur has : UInt32) : Jvm.HeapObj AlgExt :=
  .instance "kotlin/ranges/IntProgressionIterator"
    [("step", .i32 1), ("finalElement", .i32 fin), ("hasNext", .i32 has), ("next", .i32 cur)]

/-- An iterator that still returns the `n` values `cur, cur + 1, …` (the last one being `fin`). -/
def cwItRem (fin cur : UInt32) (n : Nat) : Jvm.HeapObj AlgExt :=
  if n = 0 then cwIt fin fin 0 else cwIt fin cur 1

/-- The `n` values `cur, cur + 1, …` such an iterator returns. -/
def cwRange (cur : UInt32) (n : Nat) : List UInt32 := (List.range n).map fun j => cur + UInt32.ofNat j

/-- A boxed `IntOffset(x, y)`. -/
def cwPt (x y : UInt32) : JvmVal := .ext (.intOffset (packIntOffset x y))

/-- The boxed points `IntOffset(x, y)` of row `y`, for the columns `xs`. -/
def cwRow (xs : List UInt32) (y : UInt32) : List JvmVal := xs.map fun x => cwPt x y

/-- An `ArrayList` backed by the object array at `arr`. -/
def cwList (arr : Nat) : Jvm.HeapObj AlgExt := .instance "java/util/ArrayList" [("arr", .heapRef arr)]

/-- The backing object array of an `ArrayList` holding `es`. -/
def cwArr (es : List JvmVal) : Jvm.HeapObj AlgExt := .objArray "java/lang/Object" es.toArray

/-- `jh` extends `jh0`: it keeps every object of `jh0` and its static fields, and may hold new objects. -/
def CwFrame (jh0 jh : Jvm.JvmHeap AlgExt) : Prop :=
  jh0.objects.size ≤ jh.objects.size ∧ jh.statics = jh0.statics ∧ ∀ x < jh0.objects.size, jh.get? x = jh0.get? x

private theorem cw_alloc_size (jh : Jvm.JvmHeap AlgExt) (o : Jvm.HeapObj AlgExt) :
    (jh.alloc o).2.objects.size = jh.objects.size + 1 := by
  simp [Jvm.JvmHeap.alloc]

private theorem cw_set_size (jh : Jvm.JvmHeap AlgExt) (a : Nat) (o : Jvm.HeapObj AlgExt) :
    (jh.set a o).objects.size = jh.objects.size := by
  unfold Jvm.JvmHeap.set; split <;> simp

private theorem cw_alloc_statics (jh : Jvm.JvmHeap AlgExt) (o : Jvm.HeapObj AlgExt) :
    (jh.alloc o).2.statics = jh.statics := rfl

private theorem cw_set_statics (jh : Jvm.JvmHeap AlgExt) (a : Nat) (o : Jvm.HeapObj AlgExt) :
    (jh.set a o).statics = jh.statics := by
  unfold Jvm.JvmHeap.set; split <;> rfl

section ContainedPointsSteps

variable {rp : String → Option (List JvmInstr)} {d sf : Nat} {pc : Nat} {stk : List JvmVal}
  {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}

private theorem stepInstr_aload_of {n : Nat} {v : JvmVal} (h : locs n = v) :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf) (.aload n) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, v :: stk, locs, jh, hp⟩) := by
  subst h; cases d <;> rfl

private theorem stepInstr_iload_of {n : Nat} {v : JvmVal} (h : locs n = v) :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf) (.iload n) ⟨pc, stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, v :: stk, locs, jh, hp⟩) := by
  subst h; cases d <;> rfl

private theorem stepInstr_hasNext_cw {a : Nat} {fin cur has : UInt32} (ha : jh.get? a = some (cwIt fin cur has)) :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf) (.invokeinterface "java/util/Iterator" "hasNext" "()Z")
        ⟨pc, .heapRef a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 has :: stk, locs, jh, hp⟩) := by
  have ht : Jvm.parseMethodParamTags "()Z" = [] := rfl
  cases d <;>
  · unfold Jvm.stepInstr
    simp [Jvm.stepInvokeInterfaceGeneric, ha, cwIt, mkAlgKotlinHooks, algKotlinHooksWith,
      algKotlinStepInterfaceLeaf, algKotlinFieldI32?, ht]

private theorem stepInstr_nextInt_cw {a : Nat} {fin cur : UInt32} (ha : jh.get? a = some (cwIt fin cur 1)) :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf) (.invokevirtual "kotlin/collections/IntIterator" "nextInt" "()I")
        ⟨pc, .heapRef a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 cur :: stk, locs,
        jh.set a (if cur = fin then cwIt fin fin 0 else cwIt fin (cur + 1) 1), hp⟩) := by
  have hl : isAlgKotlinLiftedClass "kotlin/collections/IntIterator" = false := rfl
  cases d <;>
  · unfold Jvm.stepInstr
    by_cases h : cur = fin
    · subst h
      simp [Jvm.stepInvokeVirtualGeneric, mkAlgKotlinHooks, algKotlinHooksWith, algKotlinStepVirtualLeaf, ha,
        cwIt, intProgressionNextInt?, algKotlinFieldI32?, hl]
    · simp [Jvm.stepInvokeVirtualGeneric, mkAlgKotlinHooks, algKotlinHooksWith, algKotlinStepVirtualLeaf, ha,
        cwIt, intProgressionNextInt?, algKotlinFieldI32?, hl, h]

private theorem stepInstr_iterRange_cw {f l : UInt32} :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf) (.invokeinterface "java/lang/Iterable" "iterator" "()Ljava/util/Iterator;")
        ⟨pc, .ext (.intRange f l) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef jh.objects.size :: stk, locs, (jh.alloc (mkIntProgressionIterator f l)).2, hp⟩) := by
  cases d <;> rfl

private theorem stepInstr_until_cw {a b f l : UInt32} (hU : kotlinUntil a b = .intRange f l) :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf)
        (.invokestatic "kotlin/ranges/RangesKt" "until" "(II)Lkotlin/ranges/IntRange;")
        ⟨pc, .i32 b :: .i32 a :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .ext (.intRange f l) :: stk, locs, jh, hp⟩) := by
  rw [← hU]; cases d <;> rfl

/-- A fresh empty `ArrayList` (its backing array at `jh.objects.size`, the list right after it). -/
def cwNewList (jh : Jvm.JvmHeap AlgExt) : Jvm.JvmHeap AlgExt :=
  ((jh.alloc (cwArr [])).2.alloc (cwList jh.objects.size)).2

private theorem stepInstr_newList0_cw :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf) (.invokespecial "java/util/ArrayList" "<init>" "()V")
        ⟨pc, .allocRef "java/util/ArrayList" :: .allocRef "java/util/ArrayList" :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef (jh.objects.size + 1) :: stk, locs, cwNewList jh, hp⟩) := by
  unfold Jvm.stepInstr
  simp [Jvm.stepInvokeSpecialGeneric, cwNewList, Jvm.JvmHeap.alloc, cwArr, cwList]

private theorem stepInstr_newList10_cw :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf) (.invokespecial "java/util/ArrayList" "<init>" "(I)V")
        ⟨pc, .i32 10 :: .allocRef "java/util/ArrayList" :: .allocRef "java/util/ArrayList" :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .heapRef (jh.objects.size + 1) :: stk, locs, cwNewList jh, hp⟩) := by
  unfold Jvm.stepInstr
  simp [Jvm.stepInvokeSpecialGeneric, cwNewList, Jvm.JvmHeap.alloc, cwArr, cwList]

private theorem stepInstr_sizeOrDefault_cw {f l : UInt32} :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf)
        (.invokestatic "kotlin/collections/CollectionsKt" "collectionSizeOrDefault" "(Ljava/lang/Iterable;I)I")
        ⟨pc, .i32 10 :: .ext (.intRange f l) :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 10 :: stk, locs, jh, hp⟩) := by
  cases d <;> rfl

private theorem stepInstr_add_cw {lst arr : Nat} {es : List JvmVal} {p : UInt64}
    (hl : jh.get? lst = some (cwList arr)) (ha : jh.get? arr = some (cwArr es)) :
    Jvm.stepInstr (mkAlgKotlinHooks rp d sf) (.invokeinterface "java/util/Collection" "add" "(Ljava/lang/Object;)Z")
        ⟨pc, .ext (.intOffset p) :: .heapRef lst :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, .i32 1 :: stk, locs, jh.set arr (cwArr (es ++ [.ext (.intOffset p)])), hp⟩) := by
  unfold Jvm.stepInstr
  simp [Jvm.stepInvokeInterfaceGeneric, hl, ha, cwList, cwArr, Jvm.isArrayElemCompat, Jvm.JvmVal.isRef]

end ContainedPointsSteps

private theorem cw_coll_list {h : Jvm.JvmHeap AlgExt} {lst arr : Nat} {es : List JvmVal}
    (hl : h.get? lst = some (cwList arr)) (ha : h.get? arr = some (cwArr es)) :
    algKotlinColl? h lst = some ("java/util/ArrayList", arr, "java/lang/Object", es.toArray) := by
  simp [algKotlinColl?, hl, ha, cwList, cwArr, isAlgKotlinCollClass]

private theorem cw_list_ne_arr {h : Jvm.JvmHeap AlgExt} {lst arr : Nat} {es : List JvmVal}
    (hl : h.get? lst = some (cwList arr)) (ha : h.get? arr = some (cwArr es)) : lst ≠ arr := by
  rintro rfl
  rw [hl] at ha
  simp [cwList, cwArr] at ha

private theorem cw_collAddAll {lst arr : Nat} :
    ∀ (xs acc : List JvmVal) (h : Jvm.JvmHeap AlgExt), h.get? lst = some (cwList arr) →
      h.get? arr = some (cwArr acc) →
      ∃ c h', algKotlinCollAddAll h lst xs = some (c, h') ∧ h'.get? arr = some (cwArr (acc ++ xs)) ∧
        (∀ y, y ≠ arr → h'.get? y = h.get? y) ∧ h'.objects.size = h.objects.size ∧ h'.statics = h.statics
  | [], acc, h, _, ha => ⟨false, h, rfl, by simpa using ha, fun _ _ => rfl, rfl, rfl⟩
  | x :: xs, acc, h, hl, ha => by
    have hne := cw_list_ne_arr hl ha
    have hadd : algKotlinCollAdd h lst x = some (true, h.set arr (cwArr (acc ++ [x]))) := by
      simp [algKotlinCollAdd, cw_coll_list hl ha, cwArr]
    have hl1 : (h.set arr (cwArr (acc ++ [x]))).get? lst = some (cwList arr) := by
      rw [Jvm.jvmHeap_get?_set_ne _ _ hne]; exact hl
    have ha1 : (h.set arr (cwArr (acc ++ [x]))).get? arr = some (cwArr (acc ++ [x])) :=
      Jvm.jvmHeap_get?_set_self ha
    obtain ⟨c, h', hrun, ha', hy, hs, hst⟩ := cw_collAddAll xs (acc ++ [x]) _ hl1 ha1
    refine ⟨true || c, h', ?_, by simpa using ha', ?_, ?_, ?_⟩
    · simp [algKotlinCollAddAll, hadd, hrun]
    · intro y hy'
      rw [hy y hy', Jvm.jvmHeap_get?_set_ne _ _ hy']
    · rw [hs, cw_set_size]
    · rw [hst, cw_set_statics]

section AddAll

variable {rp : String → Option (List JvmInstr)} {d sf : Nat} {pc : Nat} {stk : List JvmVal}
  {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap}

private theorem stepInstr_addAll_cw {src srcArr dst dstArr : Nat} {es acc : List JvmVal}
    (hs : jh.get? src = some (cwList srcArr)) (hsa : jh.get? srcArr = some (cwArr es))
    (hd : jh.get? dst = some (cwList dstArr)) (hda : jh.get? dstArr = some (cwArr acc)) :
    ∃ c jh', Jvm.stepInstr (mkAlgKotlinHooks rp d sf)
        (.invokestatic "kotlin/collections/CollectionsKt" "addAll" "(Ljava/util/Collection;Ljava/lang/Iterable;)Z")
        ⟨pc, .heapRef src :: .heapRef dst :: stk, locs, jh, hp⟩ = .inl (some ⟨pc + 1, .i32 c :: stk, locs, jh', hp⟩) ∧
      jh'.get? dstArr = some (cwArr (acc ++ es)) ∧ (∀ y, y ≠ dstArr → jh'.get? y = jh.get? y) ∧
      jh'.objects.size = jh.objects.size ∧ jh'.statics = jh.statics := by
  obtain ⟨c, h', hrun, h1, h2, h3, h4⟩ := cw_collAddAll es acc jh hd hda
  have hl : isAlgKotlinLiftedClass "kotlin/collections/CollectionsKt" = false := rfl
  refine ⟨if c then 1 else 0, h', ?_, h1, h2, h3, h4⟩
  cases d <;>
  · unfold Jvm.stepInstr
    simp [Jvm.stepInvokeStaticGeneric, mkAlgKotlinHooks, algKotlinHooksWith, algKotlinStepStaticLeaf, hl,
      cw_coll_list hs hsa, hrun]

end AddAll

/-! ### Packing and iterator arithmetic -/

private theorem cw_u64_eq_of_toBitVec {a b : UInt64} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a; cases b; cases h; rfl

private theorem cw_signExtend_shl32 (x : UInt32) :
    UInt64.ofBitVec (BitVec.signExtend 64 x.toBitVec) <<< (((32 : UInt32) &&& (63 : UInt32)).toUInt64) =
      x.toUInt64 <<< 32 := by
  apply cw_u64_eq_of_toBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hL :
      (UInt64.ofBitVec (BitVec.signExtend 64 x.toBitVec) <<<
          (((32 : UInt32) &&& (63 : UInt32)).toUInt64)).toBitVec.getLsbD i =
        (BitVec.signExtend 64 x.toBitVec <<< 32#64).getLsbD i := rfl
  have hR : (x.toUInt64 <<< 32).toBitVec.getLsbD i =
      (BitVec.zeroExtend 64 x.toBitVec <<< 32#64).getLsbD i := rfl
  rw [hL, hR]
  by_cases hi64 : i < 64
  · by_cases hi : i < 32
    · simp [BitVec.getLsbD_shiftLeft, hi]
    · have hlt32 : i - 32 < 32 := by omega
      simp [BitVec.getElem_signExtend, BitVec.getElem_setWidth, hi, hi64, hlt32]
  · simp [BitVec.getLsbD_shiftLeft, hi64]

private theorem cw_signExtend_andMask (y : UInt32) :
    UInt64.ofBitVec (BitVec.signExtend 64 y.toBitVec) &&& (4294967295 : UInt64) = y.toUInt64 := by
  apply cw_u64_eq_of_toBitVec
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hL :
      (UInt64.ofBitVec (BitVec.signExtend 64 y.toBitVec) &&& (4294967295 : UInt64)).toBitVec.getLsbD i =
        ((BitVec.signExtend 64 y.toBitVec) &&& 4294967295#64).getLsbD i := rfl
  have hR : y.toUInt64.toBitVec.getLsbD i = (BitVec.zeroExtend 64 y.toBitVec).getLsbD i := rfl
  rw [hL, hR]
  by_cases hi64 : i < 64
  · have hm : (4294967295#64).getLsbD i = decide (i < 32) := by
      rw [BitVec.getLsbD_ofNat, show (4294967295 : Nat) = 2 ^ 32 - 1 by rfl,
        Nat.testBit_two_pow_sub_one]
      simp [hi64]
    by_cases hi : i < 32
    · have hm' : (4294967295#64).getLsbD i = true := by rw [hm]; exact decide_eq_true hi
      rw [BitVec.getLsbD_and, hm', Bool.and_true]
      simp [hi, hi64, BitVec.getElem_signExtend, BitVec.getElem_setWidth]
    · have hm' : (4294967295#64).getLsbD i = false := by rw [hm]; simp [hi]
      rw [BitVec.getLsbD_and, hm', Bool.and_false]
      have hlt : y.toNat < 2 ^ i := by
        have hy : y.toNat < 2 ^ 32 := y.toBitVec.isLt
        have hp : 2 ^ 32 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      simp [BitVec.getLsbD, hi64, Nat.testBit_lt_two_pow hlt]
  · simp [hi64]

/-- The bytecode's inlined `IntOffset(x, y)`: `(x.toLong() shl 32) or (y.toLong() and 0xFFFFFFFF)`. -/
private theorem cw_pack_eq (x y : UInt32) :
    (UInt64.ofBitVec (x.toBitVec.signExtend 64) <<< ((32 : UInt32) &&& 63).toUInt64) |||
      (UInt64.ofBitVec (y.toBitVec.signExtend 64) &&& 4294967295) = packIntOffset x y := by
  rw [cw_signExtend_shl32, cw_signExtend_andMask]
  rfl

private theorem cw_ofNat_succ (n : Nat) : UInt32.ofNat (n + 1) = UInt32.ofNat n + 1 := by
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_ofNat, UInt32.toNat_add]

private theorem cw_nextInt_rem {fin cur : UInt32} {n : Nat} (hfin : cur + UInt32.ofNat (n + 1) = fin + 1)
    (hn : n + 1 < 2 ^ 32) :
    (if cur = fin then cwIt fin fin 0 else cwIt fin (cur + 1) 1) = cwItRem fin (cur + 1) n := by
  rw [cw_ofNat_succ, ← UInt32.add_assoc] at hfin
  have hf : cur + UInt32.ofNat n = fin := (UInt32.add_left_inj 1).mp hfin
  cases n with
  | zero => simp at hf; simp [hf, cwItRem]
  | succ m =>
    have hne : cur ≠ fin := by
      rintro rfl
      have h0 : cur + UInt32.ofNat (m + 1) = cur + 0 := by simpa using hf
      have : UInt32.ofNat (m + 1) = 0 := (UInt32.add_right_inj cur).mp h0
      have h2 := congrArg UInt32.toNat this
      simp [UInt32.toNat_ofNat] at h2
      omega
    simp [hne, cwItRem]

private theorem cw_fin_succ {fin cur : UInt32} {n : Nat} (hfin : cur + UInt32.ofNat (n + 1) = fin + 1) :
    cur + 1 + UInt32.ofNat n = fin + 1 := by
  rw [cw_ofNat_succ] at hfin
  rw [← hfin, UInt32.add_assoc, UInt32.add_comm 1]

private theorem cw_range_succ (cur : UInt32) (n : Nat) : cwRange cur (n + 1) = cur :: cwRange (cur + 1) n := by
  simp only [cwRange, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · refine List.map_congr_left fun j _ => ?_
    simp [cw_ofNat_succ, UInt32.add_assoc, UInt32.add_comm 1]

private theorem cw_slt (x y : Int32) :
    x.toUInt32.toBitVec.slt y.toUInt32.toBitVec = decide (x.toInt < y.toInt) := by
  simp [BitVec.slt, Int32.toInt_toBitVec]

private theorem cw_slt_pred (a b : Int32) :
    (b.toUInt32 - 1).toBitVec.slt a.toUInt32.toBitVec = decide ((b - 1).toInt < a.toInt) := by
  rw [← cw_slt]; simp

private theorem cw_ofInt_add (a : Int32) (k : Nat) :
    (Int32.ofInt (a.toInt + k)).toUInt32 = a.toUInt32 + UInt32.ofNat k := by
  apply UInt32.toBitVec_inj.mp
  simp
  rfl

private theorem cw_min_toInt {b : Int32} (h : b.toUInt32 = 0x80000000) : b.toInt = -2 ^ 31 := by
  have : b.toBitVec = Int32.minValue.toBitVec := by rw [← Jvm.int32_toUInt32_toBitVec, h]; rfl
  rw [Int32.toBitVec_inj.mp this]; rfl

/-- `a until b` is an `IntRange` whose iterator returns exactly the model's `int32RangeUntil a b`. -/
private theorem cw_until_spec (a b : Int32) :
    ∃ f l fin cur, kotlinUntil a.toUInt32 b.toUInt32 = .intRange f l ∧
      mkIntProgressionIterator f l = cwItRem fin cur (int32RangeUntil a b).length ∧
      ((int32RangeUntil a b).length ≠ 0 → cur + UInt32.ofNat (int32RangeUntil a b).length = fin + 1) ∧
      (int32RangeUntil a b).length < 2 ^ 32 ∧
      cwRange cur (int32RangeUntil a b).length = (int32RangeUntil a b).map Int32.toUInt32 := by
  have ha1 := Int32.le_toInt a
  have ha2 := Int32.toInt_lt a
  have hb1 := Int32.le_toInt b
  have hb2 := Int32.toInt_lt b
  have hsub : (b - 1).toInt = (b.toInt - 1).bmod (2 ^ 32) := by simp [Int32.toInt_sub]
  rw [Int.bmod_def] at hsub
  by_cases hba : b ≤ a
  · have hn : int32RangeUntil a b = [] := by simp [int32RangeUntil, hba]
    rw [hn]
    by_cases hmin : b.toUInt32 = 0x80000000
    · refine ⟨1, 0, 0, 0, by simp [kotlinUntil, hmin], ?_, by simp, by simp, rfl⟩
      simp [mkIntProgressionIterator, intRangeIsEmpty, cwItRem, cwIt]
    · have hbm : b.toInt ≠ -2 ^ 31 := fun h' => hmin (by
        have : b = Int32.minValue := Int32.toInt_inj.mp (by rw [h']; rfl)
        subst this; rfl)
      refine ⟨a.toUInt32, b.toUInt32 - 1, b.toUInt32 - 1, 0, by simp [kotlinUntil, hmin], ?_, by simp, by simp,
        rfl⟩
      have hle := Int32.le_iff_toInt_le.mp hba
      have hlt : (b - 1).toInt < a.toInt := by rw [hsub]; split <;> omega
      simp only [mkIntProgressionIterator, intRangeIsEmpty, cw_slt_pred, hlt, decide_true]
      simp [cwItRem, cwIt]
  · have hlt : ¬ b.toInt ≤ a.toInt := fun h => hba (Int32.le_iff_toInt_le.mpr h)
    have hbm : b.toUInt32 ≠ 0x80000000 := fun h' => by have := cw_min_toInt h'; omega
    have hn : (int32RangeUntil a b).length = (b.toInt - a.toInt).toNat := by
      simp [int32RangeUntil, hba]
    rw [hn]
    have hge : ¬ (b - 1).toInt < a.toInt := by rw [hsub]; split <;> omega
    refine ⟨a.toUInt32, b.toUInt32 - 1, b.toUInt32 - 1, a.toUInt32, by simp [kotlinUntil, hbm], ?_, ?_, by omega,
      ?_⟩
    · have hne : (b.toInt - a.toInt).toNat ≠ 0 := by omega
      simp only [mkIntProgressionIterator, intRangeIsEmpty, cw_slt_pred, hge, decide_false]
      simp [cwItRem, cwIt, hne]
    · intro _
      rw [← cw_ofInt_add, show a.toInt + ((b.toInt - a.toInt).toNat : Int) = b.toInt by omega, Int32.ofInt_toInt]
      simp
    · simp only [cwRange, int32RangeUntil, hba, ite_false, List.map_map]
      refine List.map_congr_left fun k _ => ?_
      exact (cw_ofInt_add a k).symm

/-! ### Heap bookkeeping -/

private theorem cwNewList_size (jh : Jvm.JvmHeap AlgExt) : (cwNewList jh).objects.size = jh.objects.size + 2 := by
  simp [cwNewList, Jvm.JvmHeap.alloc]

private theorem cwNewList_get_arr (jh : Jvm.JvmHeap AlgExt) :
    (cwNewList jh).get? jh.objects.size = some (cwArr []) := by
  simp [cwNewList, Jvm.JvmHeap.alloc, Jvm.JvmHeap.get?, Array.getElem?_push]

private theorem cwNewList_get_list (jh : Jvm.JvmHeap AlgExt) :
    (cwNewList jh).get? (jh.objects.size + 1) = some (cwList jh.objects.size) := by
  have := Jvm.jvmHeap_get?_alloc_self (jh.alloc (cwArr [])).2 (cwList jh.objects.size)
  rw [cw_alloc_size] at this
  exact this

private theorem cwNewList_get_old {jh : Jvm.JvmHeap AlgExt} {a : Nat} (h : a < jh.objects.size) :
    (cwNewList jh).get? a = jh.get? a := by
  simp only [cwNewList]
  rw [Jvm.jvmHeap_get?_alloc_old _ _ (by rw [cw_alloc_size]; omega), Jvm.jvmHeap_get?_alloc_old _ _ h]

private theorem cwFrame_refl (jh : Jvm.JvmHeap AlgExt) : CwFrame jh jh := ⟨Nat.le_refl _, rfl, fun _ _ => rfl⟩

private theorem cwFrame_set {jh0 jh : Jvm.JvmHeap AlgExt} {x : Nat} (o : Jvm.HeapObj AlgExt) (hF : CwFrame jh0 jh)
    (hx : jh0.objects.size ≤ x) : CwFrame jh0 (jh.set x o) := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨by rw [cw_set_size]; exact h1, by rw [cw_set_statics]; exact h2, fun y hy => ?_⟩
  rw [Jvm.jvmHeap_get?_set_ne _ _ (by omega)]; exact h3 y hy

private theorem cwFrame_alloc {jh0 jh : Jvm.JvmHeap AlgExt} (o : Jvm.HeapObj AlgExt) (hF : CwFrame jh0 jh) :
    CwFrame jh0 (jh.alloc o).2 := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨by rw [cw_alloc_size]; omega, by rw [cw_alloc_statics]; exact h2, fun y hy => ?_⟩
  rw [Jvm.jvmHeap_get?_alloc_old _ _ (by omega)]; exact h3 y hy

private theorem cwFrame_newList {jh0 jh : Jvm.JvmHeap AlgExt} (hF : CwFrame jh0 jh) : CwFrame jh0 (cwNewList jh) :=
  cwFrame_alloc _ (cwFrame_alloc _ hF)

private theorem cwFrame_agree {jh0 jh jh' : Jvm.JvmHeap AlgExt} {x : Nat} (hF : CwFrame jh0 jh)
    (hx : jh0.objects.size ≤ x) (hy : ∀ y, y ≠ x → jh'.get? y = jh.get? y)
    (hs : jh'.objects.size = jh.objects.size) (hst : jh'.statics = jh.statics) : CwFrame jh0 jh' := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨by omega, by rw [hst]; exact h2, fun y hy' => ?_⟩
  rw [hy y (by omega)]; exact h3 y hy'

/-! ### Calls and continuation-style steps -/

section ContainedPointsCalls

variable {rp : String → Option (List JvmInstr)} {d sf : Nat} {pc : Nat} {stk : List JvmVal}
  {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {l t r b : UInt32}

private theorem stepInstr_cwGetter {method : String} {callee : List JvmInstr} {v res : JvmVal}
    (hrp : rp (algKotlinTag "CellWindow" method "(Landroidx/compose/ui/unit/IntRect;)I") = some callee)
    (hrun : ∀ (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap), ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) sf callee
      ⟨0, [], Jvm.setLocal (fun _ => .i32 0) 0 v, jh, hp⟩ = some p ∧ p.1 = res ∧ p.2.jvmHeap = jh ∧ p.2.heap = hp) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) sf)
        (.invokestatic "com/alexvanyo/composelife/model/CellWindow" method "(Landroidx/compose/ui/unit/IntRect;)I") ⟨pc, v :: stk, locs, jh, hp⟩ =
      .inl (some ⟨pc + 1, res :: stk, locs, jh, hp⟩) := by
  obtain ⟨⟨r', e⟩, h, hr, hj, hh⟩ := hrun jh hp
  simp only at hr hj hh
  rw [stepInstr_static1_cellWindow hrp rfl cw_nonvoid_I h, hr, hj, hh]

private theorem stepInstr_getTop_cw (hR : ResolvesCellWindowProgs rp) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) (sf + 3))
        (.invokestatic "com/alexvanyo/composelife/model/CellWindow" "getTop-impl" "(Landroidx/compose/ui/unit/IntRect;)I")
        ⟨pc, .ext (.intRect l t r b) :: stk, locs, jh, hp⟩ = .inl (some ⟨pc + 1, .i32 t :: stk, locs, jh, hp⟩) :=
  stepInstr_cwGetter (hR _ CellWindow_getTop_impl_prog rfl) fun _ _ => run_getTopImpl (k := sf) rfl

private theorem stepInstr_getBottom_cw (hR : ResolvesCellWindowProgs rp) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) (sf + 3))
        (.invokestatic "com/alexvanyo/composelife/model/CellWindow" "getBottom-impl" "(Landroidx/compose/ui/unit/IntRect;)I")
        ⟨pc, .ext (.intRect l t r b) :: stk, locs, jh, hp⟩ = .inl (some ⟨pc + 1, .i32 b :: stk, locs, jh, hp⟩) :=
  stepInstr_cwGetter (hR _ CellWindow_getBottom_impl_prog rfl) fun _ _ => run_getBottomImpl (k := sf) rfl

private theorem stepInstr_getLeft_cw (hR : ResolvesCellWindowProgs rp) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) (sf + 3))
        (.invokestatic "com/alexvanyo/composelife/model/CellWindow" "getLeft-impl" "(Landroidx/compose/ui/unit/IntRect;)I")
        ⟨pc, .ext (.intRect l t r b) :: stk, locs, jh, hp⟩ = .inl (some ⟨pc + 1, .i32 l :: stk, locs, jh, hp⟩) :=
  stepInstr_cwGetter (hR _ CellWindow_getLeft_impl_prog rfl) fun _ _ => run_getLeftImpl (k := sf) rfl

private theorem stepInstr_getRight_cw (hR : ResolvesCellWindowProgs rp) :
    Jvm.stepInstr (mkAlgKotlinHooks rp (d + 1) (sf + 3))
        (.invokestatic "com/alexvanyo/composelife/model/CellWindow" "getRight-impl" "(Landroidx/compose/ui/unit/IntRect;)I")
        ⟨pc, .ext (.intRect l t r b) :: stk, locs, jh, hp⟩ = .inl (some ⟨pc + 1, .i32 r :: stk, locs, jh, hp⟩) :=
  stepInstr_cwGetter (hR _ CellWindow_getRight_impl_prog rfl) fun _ _ => run_getRightImpl (k := sf) rfl

end ContainedPointsCalls

/-- Loads a local slot whose value is known from a hypothesis. -/
macro "cw_load" h:term : tactic =>
  `(tactic| (refine run_step rfl rfl (stepInstr_aload_of (by exact $h)) ?_; try dsimp only))
macro "cw_iload" h:term : tactic =>
  `(tactic| (refine run_step rfl rfl (stepInstr_iload_of (by exact $h)) ?_; try dsimp only))

/-- `CollectionsKt.addAll(dst, src)` between two `ArrayList`s, in continuation style. -/
private theorem run_addAll_cw {rp : String → Option (List JvmInstr)} {d sf fuel pc : Nat} {prog : List JvmInstr}
    {stk : List JvmVal} {locs : Nat → JvmVal} {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {P : JvmVal × JvmState → Prop}
    {src srcArr dst dstArr : Nat} {es acc : List JvmVal}
    (hs : jh.get? src = some (cwList srcArr)) (hsa : jh.get? srcArr = some (cwArr es))
    (hd : jh.get? dst = some (cwList dstArr)) (hda : jh.get? dstArr = some (cwArr acc))
    (hget : prog[pc]? = some
      (.invokestatic "kotlin/collections/CollectionsKt" "addAll" "(Ljava/util/Collection;Ljava/lang/Iterable;)Z"))
    (h : ∀ (c : UInt32) (jh' : Jvm.JvmHeap AlgExt), jh'.get? dstArr = some (cwArr (acc ++ es)) →
      (∀ y, y ≠ dstArr → jh'.get? y = jh.get? y) → jh'.objects.size = jh.objects.size → jh'.statics = jh.statics →
      ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel prog ⟨pc + 1, .i32 c :: stk, locs, jh', hp⟩ = some p ∧ P p) :
    ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (fuel + 1) prog
      ⟨pc, .heapRef src :: .heapRef dst :: stk, locs, jh, hp⟩ = some p ∧ P p := by
  obtain ⟨c, jh', hstep, h1, h2, h3, h4⟩ := stepInstr_addAll_cw (rp := rp) (d := d) (sf := sf) (pc := pc) (stk := stk)
    (locs := locs) (hp := hp) hs hsa hd hda
  exact run_step hget rfl hstep (h c jh' h1 h2 h3 h4)

section ContainedPointsLoops

variable {rp : String → Option (List JvmInstr)} {d sf : Nat}

/-- The inner loop (`(left until right).map { column -> IntOffset(column, row) }`, pc 56–97) followed by
`addAll` of the row into the result (pc 98–108), back at the outer loop head (pc 21). -/
private theorem cw_inner_loop {P : JvmVal × JvmState → Prop} {K : Nat} {jh0 : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {rect : JvmVal} {aO aI : Nat} {itObj : Jvm.HeapObj AlgExt} {acc rowAll : List JvmVal} {y fin : UInt32}
    (hO : jh0.objects.size ≤ aO) (hOI : aO + 3 ≤ aI)
    (hk : ∀ (jh' : Jvm.JvmHeap AlgExt) (locs' : Nat → JvmVal), locs' 0 = rect → locs' 4 = .heapRef (aO + 1) →
      locs' 6 = .heapRef (aO + 2) → CwFrame jh0 jh' → jh'.get? (aO + 1) = some (cwList aO) →
      jh'.get? (aO + 2) = some itObj → jh'.get? aO = some (cwArr (acc ++ rowAll)) →
      ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 3)) K CellWindow_containedPoints_impl_prog
        ⟨21, [], locs', jh', hp⟩ = some p ∧ P p) :
    ∀ (n : Nat) (cur : UInt32) (rowAcc : List JvmVal) (jh : Jvm.JvmHeap AlgExt) (locs : Nat → JvmVal),
      n < 2 ^ 32 → (n ≠ 0 → cur + UInt32.ofNat n = fin + 1) → rowAcc ++ cwRow (cwRange cur n) y = rowAll →
      locs 0 = rect → locs 4 = .heapRef (aO + 1) → locs 6 = .heapRef (aO + 2) → locs 8 = .i32 y →
      locs 13 = .heapRef (aI + 1) → locs 15 = .heapRef (aI + 2) → CwFrame jh0 jh →
      jh.get? (aO + 1) = some (cwList aO) → jh.get? (aO + 2) = some itObj → jh.get? aO = some (cwArr acc) →
      jh.get? (aI + 1) = some (cwList aI) → jh.get? aI = some (cwArr rowAcc) →
      jh.get? (aI + 2) = some (cwItRem fin cur n) →
      ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 3)) (K + n * 42 + 14) CellWindow_containedPoints_impl_prog
        ⟨56, [], locs, jh, hp⟩ = some p ∧ P p := by
  intro n
  induction n with
  | zero =>
    intro cur rowAcc jh locs _ _ hrow h0 h4 h6 _ h13 h15 hF hlO hitO haO hlI haI hitI
    simp only [cwRange, List.range_zero, List.map_nil, cwRow, List.append_nil] at hrow
    subst hrow
    rw [show cwItRem fin cur 0 = cwIt fin fin 0 from rfl] at hitI
    rw [show K + 0 * 42 + 14 = K + 13 + 1 by omega]
    cw_load h15
    refine run_step rfl rfl (stepInstr_hasNext_cw hitI) ?_
    cw_ifeq
    cw_load h13
    refine run_step rfl rfl (stepInstr_checkcast_inst hlI rfl) ?_
    cw_step
    refine run_step rfl rfl (stepInstr_checkcast_inst hlI rfl) ?_
    cw_step; cw_step
    cw_load h4
    cw_step
    refine run_addAll_cw hlI haI hlO haO rfl ?_
    intro c jh' ha' hy hs hst
    cw_step
    cw_goto
    refine hk jh' _ h0 h4 h6 (cwFrame_agree hF hO hy hs hst) ?_ ?_ ha'
    · rw [hy _ (by omega)]; exact hlO
    · rw [hy _ (by omega)]; exact hitO
  | succ n ih =>
    intro cur rowAcc jh locs hn hfin hrow h0 h4 h6 h8 h13 h15 hF hlO hitO haO hlI haI hitI
    have hfin' := hfin (Nat.succ_ne_zero n)
    rw [show cwItRem fin cur (n + 1) = cwIt fin cur 1 by simp [cwItRem]] at hitI
    rw [show K + (n + 1) * 42 + 14 = (K + n * 42 + 14) + 42 by omega]
    cw_load h15
    refine run_step rfl rfl (stepInstr_hasNext_cw hitI) ?_
    cw_ifeq
    cw_load h15
    refine run_step rfl rfl (stepInstr_checkcast_inst hitI rfl) ?_
    refine run_step rfl rfl (stepInstr_nextInt_cw hitI) ?_
    rw [cw_nextInt_rem hfin' hn]
    cw_step
    cw_load h13
    cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step
    cw_iload h8
    cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step
    cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step
    rw [cw_pack_eq]
    cw_step; cw_step; cw_step; cw_step; cw_step
    have hlI' : (jh.set (aI + 2) (cwItRem fin (cur + 1) n)).get? (aI + 1) = some (cwList aI) := by
      rw [Jvm.jvmHeap_get?_set_ne _ _ (by omega)]; exact hlI
    have haI' : (jh.set (aI + 2) (cwItRem fin (cur + 1) n)).get? aI = some (cwArr rowAcc) := by
      rw [Jvm.jvmHeap_get?_set_ne _ _ (by omega)]; exact haI
    refine run_step rfl rfl (stepInstr_add_cw hlI' haI') ?_
    cw_step
    cw_goto
    have hne : ∀ z, z < aI → ((jh.set (aI + 2) (cwItRem fin (cur + 1) n)).set aI
        (cwArr (rowAcc ++ [.ext (.intOffset (packIntOffset cur y))]))).get? z = jh.get? z := by
      intro z hz
      rw [Jvm.jvmHeap_get?_set_ne _ _ (by omega), Jvm.jvmHeap_get?_set_ne _ _ (by omega)]
    refine ih (cur + 1) (rowAcc ++ [cwPt cur y]) _ _ (by omega) (fun _ => cw_fin_succ hfin') ?_ (by exact h0)
      (by exact h4) (by exact h6) (by exact h8) (by exact h13) (by exact h15)
      (cwFrame_set _ (cwFrame_set _ hF (by omega)) (by omega)) (by rw [hne _ (by omega)]; exact hlO)
      (by rw [hne _ (by omega)]; exact hitO) (by rw [hne _ (by omega)]; exact haO) ?_ ?_ ?_
    · rw [← hrow, cw_range_succ]; simp [cwRow]
    · rw [Jvm.jvmHeap_get?_set_ne _ _ (by omega)]; exact hlI'
    · exact Jvm.jvmHeap_get?_set_self haI'
    · rw [Jvm.jvmHeap_get?_set_ne _ _ (by omega)]
      exact Jvm.jvmHeap_get?_set_self hitI

/-- What the outer loop ends with: the result list at `aO + 1`, backed by the array at `aO` holding `es`. -/
def CwOuterOut (jh0 : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (aO : Nat) (es : List JvmVal) (p : JvmVal × JvmState) :
    Prop :=
  p.1 = .heapRef (aO + 1) ∧ CwFrame jh0 p.2.jvmHeap ∧ p.2.jvmHeap.get? (aO + 1) = some (cwList aO) ∧
    p.2.jvmHeap.get? aO = some (cwArr es) ∧ p.2.heap = hp

/-- The outer loop (`(top until bottom).flatMap { … }`, pc 21–108) and the return (pc 109–112). -/
private theorem cw_outer_loop (hR : ResolvesCellWindowProgs rp) {K : Nat} {jh0 : Jvm.JvmHeap AlgExt} {hp : AlgHeap}
    {l t r b fC lC finC curC finR : UInt32} {nC aO : Nat}
    (hU : kotlinUntil l r = .intRange fC lC) (hItC : mkIntProgressionIterator fC lC = cwItRem finC curC nC)
    (hfinC : nC ≠ 0 → curC + UInt32.ofNat nC = finC + 1) (hnC : nC < 2 ^ 32) (hO : jh0.objects.size ≤ aO) :
    ∀ (nR : Nat) (curR : UInt32) (acc : List JvmVal) (jh : Jvm.JvmHeap AlgExt) (locs : Nat → JvmVal),
      nR < 2 ^ 32 → (nR ≠ 0 → curR + UInt32.ofNat nR = finR + 1) →
      locs 0 = .ext (.intRect l t r b) → locs 4 = .heapRef (aO + 1) → locs 6 = .heapRef (aO + 2) →
      CwFrame jh0 jh → jh.get? (aO + 1) = some (cwList aO) → jh.get? aO = some (cwArr acc) →
      jh.get? (aO + 2) = some (cwItRem finR curR nR) →
      ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 3)) (K + nR * (49 + 42 * nC) + 7)
        CellWindow_containedPoints_impl_prog ⟨21, [], locs, jh, hp⟩ = some p ∧
        CwOuterOut jh0 hp aO (acc ++ (cwRange curR nR).flatMap fun y => cwRow (cwRange curC nC) y) p := by
  intro nR
  induction nR with
  | zero =>
    intro curR acc jh locs _ _ _ h4 h6 hF hlO haO hitO
    rw [show cwItRem finR curR 0 = cwIt finR finR 0 from rfl] at hitO
    rw [show K + 0 * (49 + 42 * nC) + 7 = K + 6 + 1 by omega]
    cw_load h6
    refine run_step rfl rfl (stepInstr_hasNext_cw hitO) ?_
    cw_ifeq
    cw_load h4
    refine run_step rfl rfl (stepInstr_checkcast_inst hlO rfl) ?_
    cw_step
    exact run_ret rfl rfl rfl ⟨rfl, hF, hlO, by simpa [cwRange] using haO, rfl⟩
  | succ nR ih =>
    intro curR acc jh locs hn hfin h0 h4 h6 hF hlO haO hitO
    have hfin' := hfin (Nat.succ_ne_zero nR)
    rw [show cwItRem finR curR (nR + 1) = cwIt finR curR 1 by simp [cwItRem]] at hitO
    have hsz := Jvm.jvmHeap_get?_some_lt hitO
    rw [show K + (nR + 1) * (49 + 42 * nC) + 7 = (K + nR * (49 + 42 * nC) + 7 + nC * 42 + 14) + 35 by
      rw [Nat.succ_mul]; omega]
    cw_load h6
    refine run_step rfl rfl (stepInstr_hasNext_cw hitO) ?_
    cw_ifeq
    cw_load h6
    refine run_step rfl rfl (stepInstr_checkcast_inst hitO rfl) ?_
    refine run_step rfl rfl (stepInstr_nextInt_cw hitO) ?_
    rw [cw_nextInt_rem hfin' hn]
    cw_step; cw_step; cw_step; cw_step; cw_step
    cw_load h0
    refine run_step rfl rfl (stepInstr_getLeft_cw hR) ?_
    cw_load h0
    refine run_step rfl rfl (stepInstr_getRight_cw hR) ?_
    refine run_step rfl rfl (stepInstr_until_cw hU) ?_
    cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step
    refine run_step rfl rfl stepInstr_sizeOrDefault_cw ?_
    refine run_step rfl rfl stepInstr_newList10_cw ?_
    refine run_step rfl rfl (stepInstr_checkcast_inst (cwNewList_get_list _) rfl) ?_
    cw_step; cw_step; cw_step; cw_step
    refine run_step rfl rfl stepInstr_iterRange_cw ?_
    cw_step
    rw [hItC]
    generalize hj1 : jh.set (aO + 2) (cwItRem finR (curR + 1) nR) = jh1
    have hs1 : jh1.objects.size = jh.objects.size := by rw [← hj1, cw_set_size]
    have hF1 : CwFrame jh0 jh1 := hj1 ▸ cwFrame_set _ hF (by omega)
    have hg1 : ∀ z, z ≠ aO + 2 → jh1.get? z = jh.get? z := fun z hz => by
      rw [← hj1, Jvm.jvmHeap_get?_set_ne _ _ hz]
    have hit1 : jh1.get? (aO + 2) = some (cwItRem finR (curR + 1) nR) := by
      rw [← hj1]; exact Jvm.jvmHeap_get?_set_self hitO
    have hn2 := cwNewList_size jh1
    have hg3 : ∀ z, z < jh1.objects.size + 2 →
        ((cwNewList jh1).alloc (cwItRem finC curC nC)).2.get? z = (cwNewList jh1).get? z := fun z hz => by
      rw [Jvm.jvmHeap_get?_alloc_old _ _ (by omega)]
    have hg3o : ∀ z, z < jh1.objects.size →
        ((cwNewList jh1).alloc (cwItRem finC curC nC)).2.get? z = jh1.get? z := fun z hz => by
      rw [hg3 z (by omega), cwNewList_get_old hz]
    refine cw_inner_loop (aI := jh1.objects.size) (itObj := cwItRem finR (curR + 1) nR) (acc := acc)
      (rowAll := cwRow (cwRange curC nC) curR) (y := curR) hO (by omega) ?_ nC curC [] _ _ hnC hfinC (by simp)
      (by exact h0) (by exact h4) (by exact h6) (by exact rfl) (by exact rfl)
      (by exact congrArg Jvm.JvmVal.heapRef hn2)
      (cwFrame_alloc _ (cwFrame_newList hF1))
      (by rw [hg3o _ (by omega), hg1 _ (by omega)]; exact hlO)
      (by rw [hg3o _ (by omega)]; exact hit1)
      (by rw [hg3o _ (by omega), hg1 _ (by omega)]; exact haO)
      (by rw [hg3 _ (by omega)]; exact cwNewList_get_list _)
      (by rw [hg3 _ (by omega)]; exact cwNewList_get_arr _)
      (by rw [← hn2]; exact Jvm.jvmHeap_get?_alloc_self _ _)
    intro jh' locs' h0' h4' h6' hF' hlO' hitO' haO'
    obtain ⟨p, hrun, hout⟩ := ih (curR + 1) (acc ++ cwRow (cwRange curC nC) curR) jh' locs' (by omega)
      (fun _ => cw_fin_succ hfin') h0' h4' h6' hF' hlO' haO' hitO'
    refine ⟨p, hrun, ?_⟩
    rw [cw_range_succ, List.flatMap_cons, ← List.append_assoc]
    exact hout

end ContainedPointsLoops

/-- Fuel for `containedPoints-impl`: 28 steps outside the loops, `49 + 42 · columns` steps per row. -/
def cellWindowContainedPointsFuel (w : CellWindowModel) : Nat :=
  28 + (int32RangeUntil w.top w.bottom).length * (49 + 42 * (int32RangeUntil w.left w.right).length)

private theorem cw_points_eq (rows cols : List Int32) :
    (rows.map Int32.toUInt32).flatMap (fun y => cwRow (cols.map Int32.toUInt32) y) =
      ((rows.flatMap fun y => cols.map fun x => (x, y)).map fun (x, y) => geomPackOffset x y).map
        fun p => JvmVal.ext (.intOffset p) := by
  simp [List.flatMap_map, List.map_flatMap, cwRow, cwPt, geomPackOffset, packIntOffset, Function.comp_def]

/--
`containedPoints-impl` returns a fresh `ArrayList` (at `jh.objects.size + 1`, backed by the object array at
`jh.objects.size`) holding the boxed `IntOffset`s of the model's `containedPoints`, in the same (row-major) order,
and leaves every object and static field of the initial heap unchanged. It holds for every window, with any fuel
from `cellWindowContainedPointsFuel w` on, given call depth and callee fuel for the `CellWindow` getters it calls.
-/
theorem cellWindow_containedPointsImpl_equiv (rp : String → Option (List JvmInstr))
    (hR : ResolvesCellWindowProgs rp) (d sf k : Nat) (w : CellWindowModel) (jh : Jvm.JvmHeap AlgExt) :
    ∃ jh', (Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 3)) (k + cellWindowContainedPointsFuel w)
        CellWindow_containedPoints_impl_prog (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
        some (.heapRef (jh.objects.size + 1), jh') ∧
      algKotlinColl? jh' (jh.objects.size + 1) = some ("java/util/ArrayList", jh.objects.size, "java/lang/Object",
        encodeIntOffsets (w.containedPoints.map fun (x, y) => geomPackOffset x y)) ∧
      CwFrame jh jh' := by
  obtain ⟨fR, lR, finR, curR, hUR, hItR, hfinR, hnR, hrR⟩ := cw_until_spec w.top w.bottom
  obtain ⟨fC, lC, finC, curC, hUC, hItC, hfinC, hnC, hrC⟩ := cw_until_spec w.left w.right
  have hrun : ∃ p, Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 3)) (k + cellWindowContainedPointsFuel w)
      CellWindow_containedPoints_impl_prog (initKotlinJvmState [(0, cellWindowIntRect w)] jh) = some p ∧
      CwOuterOut jh {} jh.objects.size
        ([] ++ (cwRange curR (int32RangeUntil w.top w.bottom).length).flatMap
          fun y => cwRow (cwRange curC (int32RangeUntil w.left w.right).length) y) p := by
    rw [initKotlinJvmState_eq, cellWindowContainedPointsFuel,
      show k + (28 + (int32RangeUntil w.top w.bottom).length * (49 + 42 * (int32RangeUntil w.left w.right).length)) =
        (k + (int32RangeUntil w.top w.bottom).length * (49 + 42 * (int32RangeUntil w.left w.right).length) + 7) + 21
        by omega]
    cw_load (show _ = cellWindowIntRect w from rfl)
    refine run_step rfl rfl (stepInstr_getTop_cw hR) ?_
    cw_load (show _ = cellWindowIntRect w from rfl)
    refine run_step rfl rfl (stepInstr_getBottom_cw hR) ?_
    refine run_step rfl rfl (stepInstr_until_cw hUR) ?_
    cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step; cw_step
    refine run_step rfl rfl stepInstr_newList0_cw ?_
    refine run_step rfl rfl (stepInstr_checkcast_inst (cwNewList_get_list _) rfl) ?_
    cw_step; cw_step; cw_step; cw_step
    refine run_step rfl rfl stepInstr_iterRange_cw ?_
    cw_step
    rw [hItR]
    have hn2 := cwNewList_size jh
    have hg3 : ∀ z, z < jh.objects.size + 2 →
        ((cwNewList jh).alloc (cwItRem finR curR (int32RangeUntil w.top w.bottom).length)).2.get? z =
          (cwNewList jh).get? z := fun z hz => by
      rw [Jvm.jvmHeap_get?_alloc_old _ _ (by omega)]
    exact cw_outer_loop hR hUC hItC hfinC hnC (Nat.le_refl _) _ curR [] _ _ hnR hfinR (by exact rfl) (by exact rfl)
      (by exact congrArg Jvm.JvmVal.heapRef hn2) (cwFrame_alloc _ (cwFrame_newList (cwFrame_refl jh)))
      (by rw [hg3 _ (by omega)]; exact cwNewList_get_list _)
      (by rw [hg3 _ (by omega)]; exact cwNewList_get_arr _)
      (by rw [← hn2]; exact Jvm.jvmHeap_get?_alloc_self _ _)
  obtain ⟨p, hp, h1, hF, hl, ha, -⟩ := hrun
  refine ⟨p.2.jvmHeap, ?_, ?_, hF⟩
  · rw [hp]; simp [cellWindowRunOut, h1]
  · rw [cw_coll_list hl ha, List.nil_append, hrR, hrC, cw_points_eq]
    rfl

/-! ## `toString-impl` and `toString`: not modeled

Both build the string with `invokedynamic makeConcatWithConstants` on an `IntRect` argument. `jvm-lean`'s string
concatenation formats only primitives, strings, `null` and boxed primitives (`Jvm.formatConcatArg`), so the step
fails closed: these theorems state that the runs halt with no result, for every fuel. They do not relate the
programs to a model string. -/

private theorem run_toStringImpl_none {rp : String → Option (List JvmInstr)} {d sf : Nat} {locs : Nat → JvmVal}
    {jh : Jvm.JvmHeap AlgExt} {hp : AlgHeap} {w : CellWindowModel} (h0 : locs 0 = cellWindowIntRect w) :
    ∀ fuel, Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel CellWindow_toString_impl_prog ⟨0, [], locs, jh, hp⟩ = none
  | 0 => rfl
  | 1 => run_step_none rfl rfl (stepInstr_aload_of h0) rfl
  | _ + 2 => run_step_none rfl rfl (stepInstr_aload_of h0) (run_fail rfl rfl rfl)

/-- `toString-impl` fails closed (`jvm-lean` cannot format the `IntRect` argument of the string concatenation). -/
theorem cellWindow_toStringImpl_halts (rp : String → Option (List JvmInstr)) (d sf fuel : Nat) (w : CellWindowModel)
    (jh : Jvm.JvmHeap AlgExt) :
    Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel CellWindow_toString_impl_prog
      (initKotlinJvmState [(0, cellWindowIntRect w)] jh) = none := by
  rw [initKotlinJvmState_eq]
  exact run_toStringImpl_none rfl fuel

/-- `toString` of a boxed `CellWindow` fails closed: it calls `toString-impl`, which does. -/
theorem cellWindow_toString_halts (rp : String → Option (List JvmInstr)) (hR : ResolvesCellWindowProgs rp)
    (d sf fuel : Nat) (w : CellWindowModel) (jh : Jvm.JvmHeap AlgExt) (a : Nat)
    (ha : jh.get? a = some (boxedCellWindowObj w)) :
    Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel CellWindow_toString_prog (initKotlinJvmState [(0, .heapRef a)] jh) = none := by
  rw [initKotlinJvmState_eq]
  have hrp := hR (algKotlinTag "CellWindow" "toString-impl" "(Landroidx/compose/ui/unit/IntRect;)Ljava/lang/String;")
    CellWindow_toString_impl_prog rfl
  rcases fuel with _ | _ | _ | fuel
  · rfl
  · exact run_step_none rfl rfl (stepInstr_aload_of rfl) rfl
  · exact run_step_none rfl rfl (stepInstr_aload_of rfl) (run_step_none rfl rfl (stepInstr_getfield_cw ha) rfl)
  · refine run_step_none rfl rfl (stepInstr_aload_of rfl) (run_step_none rfl rfl (stepInstr_getfield_cw ha) ?_)
    cases d with
    | zero =>
      refine run_fail rfl rfl ?_
      have ht : Jvm.parseMethodParamTags "(Landroidx/compose/ui/unit/IntRect;)Ljava/lang/String;" = ['L'] := rfl
      have hlt : ¬ ([cellWindowIntRect w] : List JvmVal).length <
          (Jvm.parseMethodParamTags "(Landroidx/compose/ui/unit/IntRect;)Ljava/lang/String;").length := by
        rw [ht]; simp
      rw [show Jvm.stepInstr (mkAlgKotlinHooks rp 0 sf)
          (.invokestatic "com/alexvanyo/composelife/model/CellWindow" "toString-impl" "(Landroidx/compose/ui/unit/IntRect;)Ljava/lang/String;")
          ⟨0 + 1 + 1, [cellWindowIntRect w], _, jh, {}⟩ =
        (mkAlgKotlinHooks rp 0 sf).stepInvokeStatic ⟨0 + 1 + 1, [cellWindowIntRect w], _, jh, {}⟩ "CellWindow"
          "toString-impl" "(Landroidx/compose/ui/unit/IntRect;)Ljava/lang/String;" from rfl]
      simp only [mkAlgKotlinHooks, algKotlinHooksWith, show isAlgKotlinLiftedClass "CellWindow" = true from rfl,
        ↓reduceIte, hlt, hrp, Option.map_some]
    | succ d =>
      exact run_fail rfl rfl (stepInstr_static1_cellWindow_fail hrp rfl (run_toStringImpl_none rfl sf))

end Algorithm.KotlinJvmVerification
