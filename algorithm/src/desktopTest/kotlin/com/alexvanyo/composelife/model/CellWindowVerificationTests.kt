/*
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
 */

package com.alexvanyo.composelife.model

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

/**
 * Standard `@Test` suite verifying the hand-written `CellWindow` value class by lifting the actual compiled
 * `CellWindow.class` JVM bytecode from the test runtime classpath into Lean 4 and proving theorems about that real
 * bytecode with `lake env lean`.
 *
 * `toString` is not covered: `jvm-lean` does not model string concatenation of an `IntRect` argument.
 */
class CellWindowVerificationTests {
    @Test
    fun constructor_bytecode_enforces_the_window_invariant() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_cellWindow_constructor_enforces_invariant",
            leanBody = """
                |theorem real_cellWindow_constructor_enforces_invariant
                |    (rp : String → Option (List JvmInstr)) (d sf k : Nat) (l t r b : Int32)
                |    (jh : Jvm.JvmHeap AlgExt) :
                |    (t ≤ b ∧ l ≤ r →
                |      (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 28)
                |          Algorithm.RealJvmBytecode.CellWindow_constructor_impl_prog
                |          (initKotlinJvmState [(0, .ext (.intRect l.toUInt32 t.toUInt32 r.toUInt32 b.toUInt32))]
                |            jh)).map
                |          cellWindowRunOut =
                |        some (.ext (.intRect l.toUInt32 t.toUInt32 r.toUInt32 b.toUInt32), jh)) ∧
                |    (¬(t ≤ b ∧ l ≤ r) →
                |      Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 28) Algorithm.RealJvmBytecode.CellWindow_constructor_impl_prog
                |          (initKotlinJvmState [(0, .ext (.intRect l.toUInt32 t.toUInt32 r.toUInt32 b.toUInt32))] jh) =
                |        none) := by
                |  have hprog : Algorithm.RealJvmBytecode.CellWindow_constructor_impl_prog =
                |      Algorithm.KotlinJvmBytecode.CellWindow_constructor_impl_prog := rfl
                |  rw [hprog]
                |  have h := cellWindow_constructorImpl_equiv rp d sf k l t r b jh
                |  constructor
                |  · intro hv
                |    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((mkCellWindowModel_some_iff l t r b).mpr hv)
                |    have hw' : w = ⟨l, t, r, b⟩ := by
                |      simp only [mkCellWindowModel] at hw
                |      split at hw <;> simp_all
                |    rw [hw, hw'] at h
                |    exact h
                |  · intro hv
                |    have hn : mkCellWindowModel l t r b = none := by
                |      cases hc : mkCellWindowModel l t r b with
                |      | none => rfl
                |      | some w => exact absurd ((mkCellWindowModel_some_iff l t r b).mp (by simp [hc])) hv
                |    rw [hn] at h
                |    simpa using h
            """.trimMargin(),
        )
    }

    @Test
    fun containedPoints_bytecode_lists_the_window_in_row_major_order() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_cellWindow_containedPoints_row_major",
            leanBody = """
                |theorem real_cellWindow_containedPoints_row_major
                |    (rp : String → Option (List JvmInstr)) (hR : ResolvesCellWindowProgs rp) (d sf k : Nat)
                |    (w : CellWindowModel) (jh : Jvm.JvmHeap AlgExt) :
                |    ∃ jh', ∃ pts : List (Int32 × Int32),
                |      (Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 3)) (k + cellWindowContainedPointsFuel w)
                |          Algorithm.RealJvmBytecode.CellWindow_containedPoints_impl_prog
                |          (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
                |        some (.heapRef (jh.objects.size + 1), jh') ∧
                |      algKotlinColl? jh' (jh.objects.size + 1) = some ("java/util/ArrayList", jh.objects.size,
                |        "java/lang/Object", encodeIntOffsets (pts.map fun (x, y) => geomPackOffset x y)) ∧
                |      CwFrame jh jh' ∧
                |      pts.Nodup ∧
                |      (∀ x y : Int32, (x, y) ∈ pts ↔
                |        w.left.toInt ≤ x.toInt ∧ x.toInt < w.right.toInt ∧
                |          w.top.toInt ≤ y.toInt ∧ y.toInt < w.bottom.toInt) ∧
                |      (∀ i j : Nat, i < (w.right.toInt - w.left.toInt).toNat →
                |        j < (w.bottom.toInt - w.top.toInt).toNat →
                |        pts[j * (w.right.toInt - w.left.toInt).toNat + i]? =
                |          some (Int32.ofInt (w.left.toInt + i), Int32.ofInt (w.top.toInt + j))) := by
                |  have hprog : Algorithm.RealJvmBytecode.CellWindow_containedPoints_impl_prog =
                |      Algorithm.KotlinJvmBytecode.CellWindow_containedPoints_impl_prog := rfl
                |  rw [hprog]
                |  obtain ⟨jh', h1, h2, h3⟩ := cellWindow_containedPointsImpl_equiv rp hR d sf k w jh
                |  exact ⟨jh', w.containedPoints, h1, h2, h3, CellWindowModel_containedPoints_nodup w,
                |    CellWindowModel_mem_containedPoints_iff w,
                |    fun i j hi hj => CellWindowModel_containedPoints_getElem? w i j hi hj⟩
            """.trimMargin(),
        )
    }

    @Test
    fun getters_translate_and_equality_bytecode_implement_model() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_cellWindow_getters_translate_equals",
            leanBody = """
                |theorem real_cellWindow_getters_translate_equals
                |    (rp : String → Option (List JvmInstr)) (hR : ResolvesCellWindowProgs rp) (d sf k : Nat)
                |    (w w' : CellWindowModel) (dx dy : Int32) (jh : Jvm.JvmHeap AlgExt) (a a' : Nat)
                |    (ha : jh.get? a = some (boxedCellWindowObj w)) (ha' : jh.get? a' = some (boxedCellWindowObj w')) :
                |    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) Algorithm.RealJvmBytecode.CellWindow_getTopLeft_prog
                |        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
                |      some (cellWindowOffset w.left w.top, jh) ∧
                |    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) Algorithm.RealJvmBytecode.CellWindow_getBottomRight_prog
                |        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
                |      some (cellWindowOffset w.right w.bottom, jh) ∧
                |    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) Algorithm.RealJvmBytecode.CellWindow_getWidth_impl_prog
                |        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
                |      some (.i32 w.width.toUInt32, jh) ∧
                |    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 3) Algorithm.RealJvmBytecode.CellWindow_getHeight_impl_prog
                |        (initKotlinJvmState [(0, cellWindowIntRect w)] jh)).map cellWindowRunOut =
                |      some (.i32 w.height.toUInt32, jh) ∧
                |    (Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 1) (sf + 28)) (k + 5)
                |        Algorithm.RealJvmBytecode.CellWindow_translate_prog
                |        (initKotlinJvmState [(0, cellWindowIntRect w), (1, cellWindowOffset dx dy)] jh)).map
                |        cellWindowRunOut =
                |      (w.translate dx dy).map (fun w2 => (cellWindowIntRect w2, jh)) ∧
                |    (Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) (k + 4) Algorithm.RealJvmBytecode.CellWindow_equals_impl0_prog
                |        (initKotlinJvmState [(0, cellWindowIntRect w), (1, cellWindowIntRect w')] jh)).map
                |        cellWindowRunOut =
                |      some (.bool (decide (w = w')), jh) ∧
                |    (Jvm.runJvmRes (mkAlgKotlinHooks rp (d + 2) (sf + 12)) (k + 5)
                |        Algorithm.RealJvmBytecode.CellWindow_equals_prog
                |        (initKotlinJvmState [(0, .heapRef a), (1, .heapRef a')] jh)).map cellWindowRunOut =
                |      some (.i32 (if w = w' then 1 else 0), jh) := by
                |  have h1 : Algorithm.RealJvmBytecode.CellWindow_getTopLeft_prog =
                |      Algorithm.KotlinJvmBytecode.CellWindow_getTopLeft_prog := rfl
                |  have h2 : Algorithm.RealJvmBytecode.CellWindow_getBottomRight_prog =
                |      Algorithm.KotlinJvmBytecode.CellWindow_getBottomRight_prog := rfl
                |  have h3 : Algorithm.RealJvmBytecode.CellWindow_getWidth_impl_prog =
                |      Algorithm.KotlinJvmBytecode.CellWindow_getWidth_impl_prog := rfl
                |  have h4 : Algorithm.RealJvmBytecode.CellWindow_getHeight_impl_prog =
                |      Algorithm.KotlinJvmBytecode.CellWindow_getHeight_impl_prog := rfl
                |  have h5 : Algorithm.RealJvmBytecode.CellWindow_translate_prog =
                |      Algorithm.KotlinJvmBytecode.CellWindow_translate_prog := rfl
                |  have h6 : Algorithm.RealJvmBytecode.CellWindow_equals_impl0_prog =
                |      Algorithm.KotlinJvmBytecode.CellWindow_equals_impl0_prog := rfl
                |  have h7 : Algorithm.RealJvmBytecode.CellWindow_equals_prog = Algorithm.KotlinJvmBytecode.CellWindow_equals_prog := rfl
                |  rw [h1, h2, h3, h4, h5, h6, h7]
                |  exact ⟨cellWindow_getTopLeft_equiv rp d sf k w jh, cellWindow_getBottomRight_equiv rp d sf k w jh,
                |    cellWindow_getWidth_equiv rp d sf k w jh, cellWindow_getHeight_equiv rp d sf k w jh,
                |    cellWindow_translate_equiv rp hR d sf k w dx dy jh, cellWindow_equalsImpl0_equiv rp d sf k w w' jh,
                |    cellWindow_equals_boxed_equiv rp hR d sf k w w' jh a a' ha ha'⟩
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "algorithm",
            classResourcePath = "com/alexvanyo/composelife/model/CellWindow.class",
            realBytecodeNamespace = "Algorithm.RealJvmBytecode",
            instrType = "Algorithm.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "CellWindow_getIntRect_prog",
                "CellWindow_getTopLeft_prog",
                "CellWindow_getTopRight_prog",
                "CellWindow_getBottomRight_prog",
                "CellWindow_getBottomLeft_prog",
                "CellWindow_getCenter_prog",
                "CellWindow_getTop_impl_prog",
                "CellWindow_getLeft_impl_prog",
                "CellWindow_getBottom_impl_prog",
                "CellWindow_getRight_impl_prog",
                "CellWindow_getWidth_impl_prog",
                "CellWindow_getHeight_impl_prog",
                "CellWindow_getSize_prog",
                "CellWindow_translate_prog",
                "CellWindow_containedPoints_impl_prog",
                "CellWindow_hashCode_impl_prog",
                "CellWindow_hashCode_prog",
                "CellWindow_equals_impl_prog",
                "CellWindow_equals_prog",
                "CellWindow_init_prog",
                "CellWindow_constructor_impl_prog",
                "CellWindow_box_impl_prog",
                "CellWindow_unbox_impl_prog",
                "CellWindow_equals_impl0_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.CellWindowModel",
                "theorems.CellWindowModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.CellWindow",
            ),
            defaultOpens = listOf(
                "Algorithm.JvmVerification",
                "Algorithm.KotlinModel",
                "Algorithm.KotlinJvmVerification",
            ),
        )
    }
}
