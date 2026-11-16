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

package com.alexvanyo.composelife.algorithm

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

/**
 * Standard `@Test` suite verifying hand-written Kotlin code in `MacroCellCoordinates.kt` by lifting the actual
 * compiled `MacroCellCoordinatesKt.class` JVM bytecode from the test runtime classpath into Lean 4 and proving
 * theorems about that real bytecode with `lake env lean`.
 */
class MacroCellCoordinatesVerificationTests {
    @Test
    fun cellToLeafBit_bytecode_returns_morton_index_or_throws() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_cellToLeafBit_morton_or_require",
            leanBody = """
                |theorem real_cellToLeafBit_morton_or_require
                |    (rp : String → Option (List JvmInstr)) (d sf fuel : Nat) (hf : 45 ≤ fuel) (x y : Int32)
                |    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
                |    ((0 ≤ x.toInt ∧ x.toInt < 8 ∧ 0 ≤ y.toInt ∧ y.toInt < 8) →
                |      ∃ b : UInt32, ∃ endSt,
                |        Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel Algorithm.RealJvmBytecode.MacroCellCoordinatesKt_cellToLeafBit_prog
                |            (Jvm.initJvmState [(0, .i32 x.toUInt32), (1, .i32 y.toUInt32)] (.i32 0) hp jh) =
                |          some (.i32 b, endSt) ∧
                |        endSt.jvmHeap = jh ∧ endSt.heap = hp ∧
                |        b.toNat = Algorithm.mortonIndex x.toInt.toNat y.toInt.toNat) ∧
                |    (¬(0 ≤ x.toInt ∧ x.toInt < 8 ∧ 0 ≤ y.toInt ∧ y.toInt < 8) →
                |      Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel Algorithm.RealJvmBytecode.MacroCellCoordinatesKt_cellToLeafBit_prog
                |          (Jvm.initJvmState [(0, .i32 x.toUInt32), (1, .i32 y.toUInt32)] (.i32 0) hp jh) = none) := by
                |  have hprog : Algorithm.RealJvmBytecode.MacroCellCoordinatesKt_cellToLeafBit_prog =
                |      Algorithm.KotlinJvmBytecode.MacroCellCoordinatesKt_cellToLeafBit_prog := rfl
                |  rw [hprog]
                |  have h := MacroCellCoordinates.cellToLeafBit_equiv rp d sf fuel hf x y jh hp
                |  constructor
                |  · intro hr
                |    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((cellToLeafBitModel_some_iff x y).mpr hr)
                |    rw [hb] at h
                |    obtain ⟨⟨v, st⟩, hrun, hv⟩ := Option.map_eq_some_iff.mp h
                |    simp only [Prod.mk.injEq] at hv
                |    obtain ⟨rfl, h1, h2⟩ := hv
                |    exact ⟨b, st, hrun, h1, h2, cellToLeafBitModel_eq_morton x y b hb⟩
                |  · intro hr
                |    have hn : cellToLeafBitModel x y = none := by
                |      cases hc : cellToLeafBitModel x y with
                |      | none => rfl
                |      | some b => exact absurd ((cellToLeafBitModel_some_iff x y).mp (by simp [hc])) hr
                |    rw [hn] at h
                |    simpa using h
            """.trimMargin(),
        )
    }

    @Test
    fun coordinatesToLeaf_bytecode_encodes_the_window() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_coordinatesToLeaf_encodes_window",
            leanBody = """
                |theorem real_coordinatesToLeaf_encodes_window
                |    (rp : String → Option (List JvmInstr)) (hres : MacroCellCoordinates.ResolvesMccProgs rp)
                |    (d sf fuel : Nat) (hd : 1 ≤ d) (hsf : 45 ≤ sf) (coords : List (Int32 × Int32))
                |    (h32 : coords.length < 2 ^ 32) (hf : 60 * coords.length + 14 ≤ fuel) (ox oy : Int32)
                |    (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (setAddr arrAddr : Nat) (cls ec : String)
                |    (hcoll : algKotlinColl? jh setAddr =
                |      some (cls, arrAddr, ec, MacroCellCoordinates.encodeCoords coords)) :
                |    ∃ leaf : UInt64, ∃ endSt,
                |      Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel Algorithm.RealJvmBytecode.MacroCellCoordinatesKt_coordinatesToLeaf_prog
                |          (Jvm.initJvmState [(0, .heapRef setAddr), (1, .i32 ox.toUInt32), (2, .i32 oy.toUInt32)]
                |            (.i32 0) hp jh) = some (.i64 leaf, endSt) ∧
                |      endSt.jvmHeap = (jh.alloc (MacroCellCoordinates.iterObj arrAddr coords.length)).2 ∧
                |      endSt.heap = hp ∧
                |      leaf = coordinatesToLeafModel coords ox oy ∧
                |      (∀ x y : Int, 0 ≤ x ∧ x < 8 → 0 ≤ y ∧ y < 8 →
                |        Algorithm.leafAt leaf x y = decide ((ox + Int32.ofInt x, oy + Int32.ofInt y) ∈ coords)) ∧
                |      (∀ p, p ∈ leafToCoordinatesModel leaf ox oy ↔
                |        p ∈ coords ∧ (cellToLeafBitModel (p.1 - ox) (p.2 - oy)).isSome) := by
                |  have hprog : Algorithm.RealJvmBytecode.MacroCellCoordinatesKt_coordinatesToLeaf_prog =
                |      Algorithm.KotlinJvmBytecode.MacroCellCoordinatesKt_coordinatesToLeaf_prog := rfl
                |  rw [hprog]
                |  have h := MacroCellCoordinates.coordinatesToLeaf_equiv rp hres d sf fuel hd hsf coords h32 hf ox oy
                |    jh hp setAddr arrAddr cls ec hcoll
                |  obtain ⟨⟨v, st⟩, hrun, hv⟩ := Option.map_eq_some_iff.mp h
                |  simp only [Prod.mk.injEq] at hv
                |  obtain ⟨rfl, h1, h2⟩ := hv
                |  exact ⟨_, st, hrun, h1, h2, rfl,
                |    fun x y hx hy => leafAt_coordinatesToLeafModel coords ox oy x y hx hy,
                |    leafToCoordinates_coordinatesToLeaf coords ox oy⟩
            """.trimMargin(),
        )
    }

    @Test
    fun leafToCoordinates_bytecode_decodes_the_leaf() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_leafToCoordinates_decodes_leaf",
            leanBody = """
                |theorem real_leafToCoordinates_decodes_leaf
                |    (rp : String → Option (List JvmInstr)) (hres : MacroCellCoordinates.ResolvesMccProgs rp)
                |    (d sf fuel : Nat) (hd : 1 ≤ d) (hsf : 45 ≤ sf) (hf : 1888 ≤ fuel) (leaf : UInt64)
                |    (ox oy : Int32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) :
                |    ∃ a endSt, ∃ cells : List (Int32 × Int32), ∃ cls : String,
                |      Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel Algorithm.RealJvmBytecode.MacroCellCoordinatesKt_leafToCoordinates_prog
                |          (Jvm.initJvmState [(0, .i64 leaf), (2, .i32 ox.toUInt32), (3, .i32 oy.toUInt32)]
                |            (.i32 0) hp jh) = some (.heapRef a, endSt) ∧
                |      endSt.heap = hp ∧
                |      algKotlinColl? endSt.jvmHeap a =
                |        some (cls, jh.objects.size, "java/lang/Object", MacroCellCoordinates.encodeCoords cells) ∧
                |      (∀ b < jh.objects.size, endSt.jvmHeap.get? b = jh.get? b) ∧
                |      cls = (if leaf = 0 then "kotlin/collections/EmptySet" else "java/util/LinkedHashSet") ∧
                |      coordinatesToLeafModel cells ox oy = leaf ∧
                |      (∀ p, p ∈ cells ↔ ∃ nx < 8, ∃ ny < 8,
                |        leaf.toBitVec.getLsbD (Algorithm.mortonIndex nx ny) = true ∧
                |          p = (Int32.ofInt (nx : Int) + ox, Int32.ofInt (ny : Int) + oy)) := by
                |  have hprog : Algorithm.RealJvmBytecode.MacroCellCoordinatesKt_leafToCoordinates_prog =
                |      Algorithm.KotlinJvmBytecode.MacroCellCoordinatesKt_leafToCoordinates_prog := rfl
                |  rw [hprog]
                |  have hcoll : ∀ (cls : String) (elems : Array JvmVal), isAlgKotlinCollClass cls = true →
                |      algKotlinColl? (allocAlgKotlinColl jh cls elems).2 (allocAlgKotlinColl jh cls elems).1 =
                |        some (cls, jh.objects.size, "java/lang/Object", elems) ∧
                |      ∀ b < jh.objects.size, (allocAlgKotlinColl jh cls elems).2.get? b = jh.get? b := by
                |    intro cls elems hc
                |    have g1 : (allocAlgKotlinColl jh cls elems).2.get? (allocAlgKotlinColl jh cls elems).1 =
                |        some (.instance cls [("arr", .heapRef jh.objects.size)]) := by
                |      show ((jh.objects.push _).push _)[(jh.objects.push _).size]? = _
                |      rw [Array.getElem?_push_size]
                |    have g2 : (allocAlgKotlinColl jh cls elems).2.get? jh.objects.size =
                |        some (.objArray "java/lang/Object" elems) := by
                |      show ((jh.objects.push _).push _)[jh.objects.size]? = _
                |      rw [Array.getElem?_push_lt (by simp)]
                |      simp
                |    refine ⟨?_, fun b hb => ?_⟩
                |    · unfold algKotlinColl?
                |      rw [g1]
                |      simp only [hc, ↓reduceIte, List.find?, beq_self_eq_true, Option.map_some]
                |      rw [g2]
                |    · show ((jh.objects.push _).push _)[b]? = jh.objects[b]?
                |      rw [Array.getElem?_push_lt (by simp; omega)]
                |      simp [Array.getElem_push_lt hb, hb]
                |  have h := MacroCellCoordinates.leafToCoordinates_equiv rp hres d sf fuel hd hsf hf leaf ox oy jh hp
                |  obtain ⟨⟨v, st⟩, hrun, hv⟩ := Option.map_eq_some_iff.mp h
                |  simp only [Prod.mk.injEq] at hv
                |  obtain ⟨rfl, h1, h2⟩ := hv
                |  have hc : isAlgKotlinCollClass
                |      (if leaf = 0 then "kotlin/collections/EmptySet" else "java/util/LinkedHashSet") = true := by
                |    split <;> rfl
                |  obtain ⟨hk1, hk2⟩ :=
                |    hcoll _ (MacroCellCoordinates.encodeCoords (leafToCoordinatesModel leaf ox oy)) hc
                |  rw [← h1] at hk1 hk2
                |  exact ⟨_, st, leafToCoordinatesModel leaf ox oy, _, hrun, h2, hk1, hk2, rfl,
                |    coordinatesToLeaf_leafToCoordinates leaf ox oy, mem_leafToCoordinatesModel_iff leaf ox oy⟩
            """.trimMargin(),
        )
    }

    @Test
    fun coordinatesToLevel4_bytecode_encodes_the_16x16_window() {
        spec.verifyTheorem(
            ownerClass = javaClass,
            theoremName = "real_coordinatesToLevel4_encodes_window",
            leanBody = """
                |theorem real_coordinatesToLevel4_encodes_window
                |    (rp : String → Option (List JvmInstr)) (hres : MacroCellCoordinates.ResolvesMccProgs rp)
                |    (d sf fuel : Nat) (hd : 2 ≤ d) (hsf : 45 ≤ sf) (coords : List (Int32 × Int32))
                |    (h32 : coords.length < 2 ^ 32) (hsf2 : 60 * coords.length + 14 ≤ sf) (hf : 34 ≤ fuel)
                |    (ox oy : Int32) (jh : Jvm.JvmHeap AlgExt) (hp : AlgHeap) (setAddr arrAddr : Nat) (cls ec : String)
                |    (hcoll : algKotlinColl? jh setAddr =
                |      some (cls, arrAddr, ec, MacroCellCoordinates.encodeCoords coords))
                |    (hcomp : jh.getStatic? MacroCellCoordinates.level4Node "Companion" = none ∨
                |      jh.getStatic? MacroCellCoordinates.level4Node "Companion" =
                |        some (.allocRef MacroCellCoordinates.level4Companion)) :
                |    ∃ nw ne sw se : UInt64, ∃ endSt,
                |      Jvm.runJvmRes (mkAlgKotlinHooks rp d sf) fuel Algorithm.RealJvmBytecode.MacroCellCoordinatesKt_coordinatesToLevel4_prog
                |          (Jvm.initJvmState [(0, .heapRef setAddr), (1, .i32 ox.toUInt32), (2, .i32 oy.toUInt32)]
                |            (.i32 0) hp jh) = some (.ext (.mc (Algorithm.makeLevel4Node nw ne sw se)), endSt) ∧
                |      endSt.jvmHeap = MacroCellCoordinates.iter4 jh arrAddr coords.length ∧ endSt.heap = hp ∧
                |      (∀ x y : Int, 0 ≤ x ∧ x < 16 → 0 ≤ y ∧ y < 16 →
                |        level4CellAt nw ne sw se x y =
                |          decide ((ox + Int32.ofInt x, oy + Int32.ofInt y) ∈ coords)) := by
                |  have hprog : Algorithm.RealJvmBytecode.MacroCellCoordinatesKt_coordinatesToLevel4_prog =
                |      Algorithm.KotlinJvmBytecode.MacroCellCoordinatesKt_coordinatesToLevel4_prog := rfl
                |  rw [hprog]
                |  have h := MacroCellCoordinates.coordinatesToLevel4_equiv rp hres d sf fuel hd hsf coords h32 hsf2 hf
                |    ox oy jh hp setAddr arrAddr cls ec hcoll hcomp
                |  obtain ⟨⟨v, st⟩, hrun, hv⟩ := Option.map_eq_some_iff.mp h
                |  simp only [Prod.mk.injEq] at hv
                |  obtain ⟨rfl, h1, h2⟩ := hv
                |  exact ⟨_, _, _, _, st, hrun, h1, h2,
                |    fun x y hx hy => level4CellAt_coordinatesToLevel4Model coords ox oy x y hx hy⟩
            """.trimMargin(),
        )
    }

    companion object {
        private val spec = JvmBytecodeVerificationSpec(
            moduleDirName = "algorithm",
            classResourcePath = "com/alexvanyo/composelife/algorithm/MacroCellCoordinatesKt.class",
            realBytecodeNamespace = "Algorithm.RealJvmBytecode",
            instrType = "Algorithm.JvmVerification.JvmInstr",
            requiredProgs = listOf(
                "MacroCellCoordinatesKt_cellToLeafBit_prog",
                "MacroCellCoordinatesKt_coordinatesToLeaf_prog",
                "MacroCellCoordinatesKt_coordinatesToLeaf_default_prog",
                "MacroCellCoordinatesKt_leafToCoordinates_prog",
                "MacroCellCoordinatesKt_leafToCoordinates_default_prog",
                "MacroCellCoordinatesKt_coordinatesToLevel4_prog",
                "MacroCellCoordinatesKt_coordinatesToLevel4_default_prog",
            ),
            defaultImports = listOf(
                "JvmSemantics",
                "models.MacroCellCoordinatesModel",
                "theorems.MacroCellCoordinatesModelTheorems",
                "KotlinJvmBytecode",
                "proofs.KotlinJvmEquiv.MacroCellCoordinates",
            ),
            defaultOpens = listOf(
                "Algorithm.JvmVerification",
                "Algorithm.KotlinModel",
                "Algorithm.KotlinJvmVerification",
            ),
        )
    }
}
