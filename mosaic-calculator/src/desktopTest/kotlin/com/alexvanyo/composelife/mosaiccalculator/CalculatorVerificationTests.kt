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

package com.alexvanyo.composelife.mosaiccalculator

import com.alexvanyo.composelife.lean.JvmBytecodeVerificationSpec
import com.alexvanyo.composelife.lean.verifyTheorem
import kotlin.test.Test

class CalculatorVerificationTests {
    private val verificationSpec = JvmBytecodeVerificationSpec(
        moduleDirName = "mosaic-calculator",
        classResourcePath = "com/alexvanyo/composelife/mosaiccalculator/CalculatorScreenKt.class",
        semanticsImport = "JvmSemantics",
        realBytecodeNamespace = "MosaicCalculator.RealJvmBytecode",
        instrType = "MosaicCalculator.JvmVerification.JvmInstr",
        requiredProgs = listOf(
            "CalculatorApp_prog",
            "CalculatorScreen_prog",
            "reduceCalculatorState_prog",
            "mapTerminalKey_prog",
            "formatDisplayLine_prog",
        ),
        defaultImports = listOf(
            "models.CalculatorModel",
            "ComposeSemantics",
            "MosaicSemantics",
            "proofs.KotlinJvmEquiv.CalculatorComposeUi",
        ),
        defaultOpens = listOf(
            "MosaicCalculator",
            "MosaicCalculator.Model",
            "MosaicCalculator.JvmVerification",
            "MosaicCalculator.KotlinJvmVerification",
        ),
        extraClassResourcePaths = listOf(
            "com/alexvanyo/composelife/mosaiccalculator/CalculatorEngineKt.class",
            "com/alexvanyo/composelife/mosaiccalculator/ComposableSingletons\$CalculatorScreenKt.class",
        ),
    )

    @Test
    fun engine_bytecode_evaluates_key_sequence_and_div_by_zero() {
        verificationSpec.verifyTheorem(
            ownerClass = CalculatorVerificationTests::class.java,
            theoremName = "live_engine_bytecode_equiv",
            leanBody = """
              theorem live_engine_bytecode_equiv :
                  (MosaicCalculator.RealJvmBytecode.mapTerminalKey_prog =
                      MosaicCalculator.KotlinJvmBytecode.mapTerminalKey_prog) ∧
                  (MosaicCalculator.RealJvmBytecode.reduceCalculatorState_prog =
                      MosaicCalculator.KotlinJvmBytecode.reduceCalculatorState_prog) ∧
                  (MosaicCalculator.RealJvmBytecode.formatDisplayLine_prog =
                      MosaicCalculator.KotlinJvmBytecode.formatDisplayLine_prog) ∧
                  (∃ s1,
                    Jvm.runJvmRes (mkCalcHooks calcProgLookup 1 0) 25
                        MosaicCalculator.RealJvmBytecode.mapTerminalKey_prog
                        (initCalcJvmState
                          [(0, .str "invalid")] { closures := calcUiInitClosures } calcUiInitJvmHeap) =
                      some (.null, s1)) ∧
                  (∃ endSt,
                    let divZeroSt :=
                      ["1", "/", "0", "="].foldl (fun s k =>
                        match mapTerminalKeyModel k with
                        | some ck => reduceCalculatorStateModel s ck
                        | none => s) .initial
                    Jvm.runJvmRes (mkCalcHooks calcProgLookup 1 0) 35
                        MosaicCalculator.RealJvmBytecode.formatDisplayLine_prog
                        (initCalcJvmState [(0, .ext (.calcState divZeroSt))] {} calcUiInitJvmHeap) =
                      some (.str "ERR: DIV BY ZERO", endSt)) ∧
                  (∃ endSt,
                    let addedSt :=
                      ["1", "+", "2", "="].foldl (fun s k =>
                        match mapTerminalKeyModel k with
                        | some ck => reduceCalculatorStateModel s ck
                        | none => s) .initial
                    Jvm.runJvmRes (mkCalcHooks calcProgLookup 3 60) 80
                        MosaicCalculator.RealJvmBytecode.reduceCalculatorState_prog
                        (initCalcJvmState
                          [(0, .ext (.calcState addedSt)), (1, .ext (.calcKey .clear))]
                          {} calcUiInitJvmHeap) =
                      some (.ext (.calcState .initial), endSt)) := by
                have hMapProg :
                    MosaicCalculator.RealJvmBytecode.mapTerminalKey_prog =
                      MosaicCalculator.KotlinJvmBytecode.mapTerminalKey_prog := by rfl
                have hRedProg :
                    MosaicCalculator.RealJvmBytecode.reduceCalculatorState_prog =
                      MosaicCalculator.KotlinJvmBytecode.reduceCalculatorState_prog := by rfl
                have hFmtProg :
                    MosaicCalculator.RealJvmBytecode.formatDisplayLine_prog =
                      MosaicCalculator.KotlinJvmBytecode.formatDisplayLine_prog := by rfl
                refine ⟨hMapProg, hRedProg, hFmtProg, ?_, ?_, ?_⟩
                · rw [hMapProg]
                  obtain ⟨s1, h1, _, _⟩ := mapTerminalKey_equiv calcProgLookup 1 0 25
                    (by omega) (by omega) "invalid"
                    { closures := calcUiInitClosures } calcUiInitJvmHeap
                    calcUiInitJvmHeap_hasWhenMappings.staticsClean
                  exact ⟨s1, h1⟩
                · rw [hFmtProg]
                  dsimp only
                  let divZeroSt :=
                    ["1", "/", "0", "="].foldl (fun s k =>
                      match mapTerminalKeyModel k with
                      | some ck => reduceCalculatorStateModel s ck
                      | none => s) .initial
                  have hfmtStr : formatDisplayLineModel divZeroSt = "ERR: DIV BY ZERO" := by decide
                  obtain ⟨endSt, hfmt, _, _⟩ := formatDisplayLine_equiv calcProgLookup 1 0 35
                    (by omega) (by omega) divZeroSt
                    {} calcUiInitJvmHeap calcUiInitJvmHeap_hasWhenMappings.errSwitch
                  rw [hfmtStr] at hfmt
                  exact ⟨endSt, hfmt⟩
                · rw [hRedProg]
                  dsimp only
                  let addedSt :=
                    ["1", "+", "2", "="].foldl (fun s k =>
                      match mapTerminalKeyModel k with
                      | some ck => reduceCalculatorStateModel s ck
                      | none => s) .initial
                  have hclr : reduceCalculatorStateModel addedSt .clear = .initial := by decide
                  obtain ⟨endSt, hred, _, _⟩ := reduceCalculatorState_equiv calcProgLookup
                    calcProgLookup_extends 3 60 80 (by omega) (by omega) (by omega)
                    addedSt .clear {} calcUiInitJvmHeap calcUiInitJvmHeap_hasWhenMappings
                  rw [hclr] at hred
                  exact ⟨endSt, hred⟩
            """.trimIndent(),
        )
    }

    @Test
    fun calculator_screen_bytecode_skips_when_state_unchanged() {
        verificationSpec.verifyTheorem(
            ownerClass = CalculatorVerificationTests::class.java,
            theoremName = "live_calculator_screen_skip_equiv",
            leanBody = """
              theorem live_calculator_screen_skip_equiv :
                  (MosaicCalculator.RealJvmBytecode.CalculatorScreen_prog =
                      MosaicCalculator.KotlinJvmBytecode.CalculatorScreen_prog) ∧
                  (let cSt : CalculatorState :=
                    ["1", "2"].foldl (fun s k =>
                      match mapTerminalKeyModel k with
                      | some ck => reduceCalculatorStateModel s ck
                      | none => s) .initial
                  let gScr : Compose.GroupEntry (Jvm.JvmVal CalcExt) := {
                    key := (2094116101 : Int32)
                    slots := [.ext (.calcState cSt), .ext (.closureRef 4)]
                    dirty := false
                  }
                  let hp : CalcHeap := {
                    composer := { inserting := false, groups := [gScr] }
                    closures := calcUiInitClosures
                    emittedRoot? := some (calculatorScreenMosaicNode cSt 4)
                  }
                  ∃ endSt,
                    Jvm.runJvmRes (mkCalcHooks calcProgLookup 1 110) 80
                        MosaicCalculator.RealJvmBytecode.CalculatorScreen_prog
                        (initCalcJvmState
                          [(0, .ext (.calcState cSt)), (1, .ext (.closureRef 0)),
                           (2, .ext (.modifier none)), (3, .ext .composer),
                           (4, .i32 176), (5, .i32 0)]
                          hp calcUiInitJvmHeap) =
                      some (.unit, endSt) ∧
                    endSt.heap.nodeStack = [] ∧
                    endSt.heap.emittedRoot? = some (calculatorScreenMosaicNode cSt 4)) := by
                have hScrProg :
                    MosaicCalculator.RealJvmBytecode.CalculatorScreen_prog =
                      MosaicCalculator.KotlinJvmBytecode.CalculatorScreen_prog := by rfl
                refine ⟨hScrProg, ?_⟩
                dsimp only
                rw [hScrProg]
                let cSt : CalculatorState :=
                  ["1", "2"].foldl (fun s k =>
                    match mapTerminalKeyModel k with
                    | some ck => reduceCalculatorStateModel s ck
                    | none => s) .initial
                let gScr : Compose.GroupEntry (Jvm.JvmVal CalcExt) := {
                  key := (2094116101 : Int32)
                  slots := [.ext (.calcState cSt), .ext (.closureRef 4)]
                  dirty := false
                }
                let hp : CalcHeap := {
                  composer := { inserting := false, groups := [gScr] }
                  closures := calcUiInitClosures
                  emittedRoot? := some (calculatorScreenMosaicNode cSt 4)
                }
                obtain ⟨endSt, hrun, _, hhp⟩ := CalculatorScreen_skip_equiv 1 110 80
                  (by omega) (by omega) cSt (.ext (.closureRef 0)) rfl 4
                  hp calcUiInitJvmHeap rfl gScr rfl rfl rfl (Or.inl rfl)
                refine ⟨endSt, hrun, ?_, ?_⟩ <;> rw [hhp] <;> rfl
            """.trimIndent(),
        )
    }

    @Test
    fun calculator_app_live_bytecode_processes_keys_and_renders_terminal_display() {
        verificationSpec.verifyTheorem(
            ownerClass = CalculatorVerificationTests::class.java,
            theoremName = "live_calculator_app_end_to_end_render",
            leanBody = """
              theorem live_calculator_app_end_to_end_render :
                  (MosaicCalculator.RealJvmBytecode.CalculatorApp_prog =
                      MosaicCalculator.KotlinJvmBytecode.CalculatorApp_prog) ∧
                  (MosaicCalculator.RealJvmBytecode.CalculatorScreen_prog =
                      MosaicCalculator.KotlinJvmBytecode.CalculatorScreen_prog) ∧
                  (∃ initSt initTree,
                    Jvm.runJvmRes (mkCalcHooks calcProgLookup 6 200) 200
                        MosaicCalculator.RealJvmBytecode.CalculatorApp_prog
                        (initCalcJvmState
                          [(0, .null), (1, .null), (2, .ext .composer), (3, .i32 0), (4, .i32 3)]
                          { closures := calcUiInitClosures } calcUiInitJvmHeap) =
                      some (.unit, initSt) ∧
                    initSt.heap.emittedRoot? = some initTree ∧
                    Mosaic.renderMosaic initTree =
                      "=== Calculator ===\n> 0\n[7] [8] [9] [/]\n" ++
                        "[4] [5] [6] [*]\n[1] [2] [3] [-]\n[0] [C] [=] [+]") ∧
                  (∃ initSt finalSt finalTree,
                    Jvm.runJvmRes (mkCalcHooks calcProgLookup 6 200) 200
                        MosaicCalculator.RealJvmBytecode.CalculatorApp_prog
                        (initCalcJvmState
                          [(0, .null), (1, .null), (2, .ext .composer), (3, .i32 0), (4, .i32 3)]
                          { closures := calcUiInitClosures } calcUiInitJvmHeap) =
                      some (.unit, initSt) ∧
                    runUiKeysJvm 6 200 initSt ["1", "2", "+", "3", "=", "x"] = some finalSt ∧
                    finalSt.heap.emittedRoot? = some finalTree ∧
                    Mosaic.renderMosaic finalTree =
                      "=== Calculator ===\n> 15\n[7] [8] [9] [/]\n" ++
                        "[4] [5] [6] [*]\n[1] [2] [3] [-]\n[0] [C] [=] [+]") ∧
                  (∃ initSt divSt divTree,
                    Jvm.runJvmRes (mkCalcHooks calcProgLookup 6 200) 200
                        MosaicCalculator.RealJvmBytecode.CalculatorApp_prog
                        (initCalcJvmState
                          [(0, .null), (1, .null), (2, .ext .composer), (3, .i32 0), (4, .i32 3)]
                          { closures := calcUiInitClosures } calcUiInitJvmHeap) =
                      some (.unit, initSt) ∧
                    runUiKeysJvm 6 200 initSt ["9", "/", "0", "="] = some divSt ∧
                    divSt.heap.emittedRoot? = some divTree ∧
                    Mosaic.renderMosaic divTree =
                      "=== Calculator ===\n> ERR: DIV BY ZERO\n[7] [8] [9] [/]\n" ++
                        "[4] [5] [6] [*]\n[1] [2] [3] [-]\n[0] [C] [=] [+]") := by
                have hAppProg :
                    MosaicCalculator.RealJvmBytecode.CalculatorApp_prog =
                      MosaicCalculator.KotlinJvmBytecode.CalculatorApp_prog := by rfl
                have hScrProg :
                    MosaicCalculator.RealJvmBytecode.CalculatorScreen_prog =
                      MosaicCalculator.KotlinJvmBytecode.CalculatorScreen_prog := by rfl
                refine ⟨hAppProg, hScrProg, ?_, ?_, ?_⟩
                · obtain ⟨initSt, initTree, hrun, _, hroot, hrend⟩ :=
                    CalculatorApp_initial_renders_expected 6 200 200 (by omega) (by omega) (by omega)
                  have hexp :
                      expectedCalculatorScreen .initial =
                        "=== Calculator ===\n> 0\n[7] [8] [9] [/]\n" ++
                          "[4] [5] [6] [*]\n[1] [2] [3] [-]\n[0] [C] [=] [+]" := by decide
                  rw [hAppProg]
                  exact ⟨initSt, initTree, hrun, hroot, hrend.trans hexp⟩
                · obtain ⟨initSt, finalSt, finalTree, hinit, hkeys, _, hroot, hrend⟩ :=
                    CalculatorApp_runKeys_renders_expected 6 200 (by omega) (by omega)
                      ["1", "2", "+", "3", "=", "x"]
                  have hexp :
                      expectedCalculatorScreen
                          (["1", "2", "+", "3", "=", "x"].foldl (fun s k =>
                            match mapTerminalKeyModel k with
                            | some ck => reduceCalculatorStateModel s ck
                            | none => s) .initial) =
                        "=== Calculator ===\n> 15\n[7] [8] [9] [/]\n" ++
                          "[4] [5] [6] [*]\n[1] [2] [3] [-]\n[0] [C] [=] [+]" := by decide
                  rw [hAppProg]
                  exact ⟨initSt, finalSt, finalTree, hinit, hkeys, hroot, hrend.trans hexp⟩
                · obtain ⟨initSt, divSt, divTree, hinit, hkeys, _, hroot, hrend⟩ :=
                    CalculatorApp_runKeys_renders_expected 6 200 (by omega) (by omega)
                      ["9", "/", "0", "="]
                  have hexp :
                      expectedCalculatorScreen
                          (["9", "/", "0", "="].foldl (fun s k =>
                            match mapTerminalKeyModel k with
                            | some ck => reduceCalculatorStateModel s ck
                            | none => s) .initial) =
                        "=== Calculator ===\n> ERR: DIV BY ZERO\n[7] [8] [9] [/]\n" ++
                          "[4] [5] [6] [*]\n[1] [2] [3] [-]\n[0] [C] [=] [+]" := by decide
                  rw [hAppProg]
                  exact ⟨initSt, divSt, divTree, hinit, hkeys, hroot, hrend.trans hexp⟩
            """.trimIndent(),
        )
    }
}
