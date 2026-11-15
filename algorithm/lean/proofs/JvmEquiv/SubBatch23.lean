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

namespace Algorithm.JvmVerification
open Algorithm.JvmBytecode

theorem getRemapCell_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    runJvm 30 f_Algorithm_getRemapCell_prog (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena]) =
      some (.i32 (Algorithm.getRemapCell arena nodeId)) := by
  apply runJvm_of_runJvmValFast0 30 _ _ _ rfl
  step_flat_tree f_Algorithm_getRemapCell_prog
  all_goals (simp only [Algorithm.getRemapCell]; close_flat_leaf)

theorem getCellStepRes_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    runJvm 30 f_Algorithm_getCellStepRes_prog (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena]) =
      some (.i32 (Algorithm.getCellStepRes arena nodeId)) := by
  apply runJvm_of_runJvmValFast0 30 _ _ _ rfl
  step_flat_tree f_Algorithm_getCellStepRes_prog
  all_goals (simp only [Algorithm.getCellStepRes]; close_flat_leaf)

theorem flatHashLifeArena_expandFrameIfNeeded_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId base : UInt32) :
    (runJvmRes 30 f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId), (2, .i32 base)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.unit, [arena.expandFrameIfNeeded nodeId base]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 30 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_expandFrameIfNeeded_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.expandFrameIfNeeded]; close_flat_leaf)

theorem flatHashLifeArena_needToExpandCell_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    runJvm 40 f_Algorithm_FlatHashLifeArena_needToExpandCell_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena]) =
      some (.i32 (if arena.needToExpandCell nodeId then 1 else 0)) := by
  apply runJvm_of_runJvmValFast0 40 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_needToExpandCell_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.needToExpandCell]; close_flat_leaf)

theorem flatHashLifeArena_combineQuadrants_equiv (arena : Algorithm.FlatHashLifeArena)
    (nodeId : UInt32) (lvl : UInt8) (r_nw r_ne r_sw r_se : UInt32) :
    (runJvmRes 60 f_Algorithm_FlatHashLifeArena_combineQuadrants_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId), (2, .i32 lvl.toUInt32),
        (3, .i32 r_nw), (4, .i32 r_ne), (5, .i32 r_sw), (6, .i32 r_se)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.combineQuadrants nodeId lvl r_nw r_ne r_sw r_se).1,
        [(arena.combineQuadrants nodeId lvl r_nw r_ne r_sw r_se).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 60 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_combineQuadrants_prog
  all_goals
    try rw [u8_sub1_u32_jvm]
    simp only [Algorithm.FlatHashLifeArena.combineQuadrants]
    close_flat_leaf

theorem copySubgraphInto_equiv (dst src : Algorithm.FlatHashLifeArena) (rootId : UInt32) (copyMemos : Bool) :
    (runJvmRes 80 f_Algorithm_copySubgraphInto_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, (.ext (.arenaRef 1))), (2, .i32 rootId),
        (3, .i32 (if copyMemos then 1 else 0))] [dst, src])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.unit, [Algorithm.copySubgraphInto dst src rootId copyMemos, src]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 80 _ _ _ rfl
  step_flat_tree f_Algorithm_copySubgraphInto_prog
  all_goals (simp only [Algorithm.copySubgraphInto]; close_flat_leaf)

theorem flatHashLifeArena_stepLevel4_equiv (arena : Algorithm.FlatHashLifeArena) (l4Id : UInt32) :
    (runJvmRes 80 f_Algorithm_FlatHashLifeArena_stepLevel4_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 l4Id)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i64 (arena.stepLevel4 l4Id).1, [(arena.stepLevel4 l4Id).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 80 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_stepLevel4_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.stepLevel4]; close_flat_leaf)

theorem flatHashLifeArena_stepCellSerial_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 80 f_Algorithm_FlatHashLifeArena_stepCellSerial_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.stepCellSerial nodeId).1, [(arena.stepCellSerial nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 80 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_stepCellSerial_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.stepCellSerial]; close_flat_leaf)

theorem flatHashLifeArena_stepLevel5_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 110 f_Algorithm_FlatHashLifeArena_stepLevel5_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.stepLevel5 nodeId).1, [(arena.stepLevel5 nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 110 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_stepLevel5_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.stepLevel5]; close_flat_leaf)

theorem flatHashLifeArena_copyL4From_equiv (dst src : Algorithm.FlatHashLifeArena)
    (l4Id : UInt32) (copyMemos : Bool) :
    (runJvmRes 120 f_Algorithm_FlatHashLifeArena_copyL4From_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, (.ext (.arenaRef 1))), (2, .i32 l4Id),
        (3, .i32 (if copyMemos then 1 else 0))] [dst, src])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (dst.copyL4From src l4Id copyMemos).1,
        [(dst.copyL4From src l4Id copyMemos).2, src]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 120 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_copyL4From_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.copyL4From]; close_flat_leaf)

theorem flatHashLifeArena_expandLevel4Centered_equiv (arena : Algorithm.FlatHashLifeArena) (l4Id : UInt32) :
    (runJvmRes 200 f_Algorithm_FlatHashLifeArena_expandLevel4Centered_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 l4Id)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.expandLevel4Centered l4Id).1, [(arena.expandLevel4Centered l4Id).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 200 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_expandLevel4Centered_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.expandLevel4Centered]; close_flat_leaf)

theorem flatHashLifeArena_centeredSubnode_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 200 f_Algorithm_FlatHashLifeArena_centeredSubnode_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.centeredSubnode nodeId).1, [(arena.centeredSubnode nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 200 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_centeredSubnode_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.centeredSubnode]; close_flat_leaf)

theorem flatHashLifeArena_centeredHorizontal_equiv (arena : Algorithm.FlatHashLifeArena) (wId eId : UInt32) :
    (runJvmRes 200 f_Algorithm_FlatHashLifeArena_centeredHorizontal_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 wId), (2, .i32 eId)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.centeredHorizontal wId eId).1, [(arena.centeredHorizontal wId eId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 200 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_centeredHorizontal_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.centeredHorizontal]; close_flat_leaf)

theorem flatHashLifeArena_centeredVertical_equiv (arena : Algorithm.FlatHashLifeArena) (nId sId : UInt32) :
    (runJvmRes 200 f_Algorithm_FlatHashLifeArena_centeredVertical_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nId), (2, .i32 sId)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.centeredVertical nId sId).1, [(arena.centeredVertical nId sId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 200 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_centeredVertical_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.centeredVertical]; close_flat_leaf)

theorem flatHashLifeArena_centeredSubSubnode_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 200 f_Algorithm_FlatHashLifeArena_centeredSubSubnode_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.centeredSubSubnode nodeId).1, [(arena.centeredSubSubnode nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 200 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_centeredSubSubnode_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.centeredSubSubnode]; close_flat_leaf)

theorem flatHashLifeArena_expandCentered_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 300 f_Algorithm_FlatHashLifeArena_expandCentered_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.expandCentered nodeId).1, [(arena.expandCentered nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 300 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_expandCentered_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.expandCentered, Algorithm.emptyNodeForLevel]; close_flat_leaf)

theorem flatHashLifeArena_expandFrame_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId base : UInt32) :
    (runJvmRes 300 f_Algorithm_FlatHashLifeArena_expandFrame_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId), (2, .i32 base)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.unit, [arena.expandFrame nodeId base]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 300 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_expandFrame_prog
  all_goals (simp only [Algorithm.FlatHashLifeArena.expandFrame]; close_flat_leaf)

private theorem shift_and_63_1 : ((1 : UInt32) &&& 63).toUInt64 = 1 := rfl
private theorem shift_and_63_2 : ((2 : UInt32) &&& 63).toUInt64 = 2 := rfl
private theorem shift_and_63_4 : ((4 : UInt32) &&& 63).toUInt64 = 4 := rfl
private theorem shift_and_63_56 : ((56 : UInt32) &&& 63).toUInt64 = 56 := rfl
private theorem shift_and_63_16_f : (((16 : UInt32) &&& 63).toUInt64) = 16 := rfl
private theorem shift_and_63_32_f : (((32 : UInt32) &&& 63).toUInt64) = 32 := rfl
private theorem shift_and_63_48_f : (((48 : UInt32) &&& 63).toUInt64) = 48 := rfl
private theorem ui64_add_zero (x : UInt64) : x + 0 = x := by bv_normalize
private theorem ui64_zero_add (x : UInt64) : 0 + x = x := by bv_normalize
private theorem u8_toUInt32_beq_five (b : UInt8) : (b.toUInt32 == 5) = (b == 5) := by
  revert b; decide
private theorem u8_6_eq_5 : ((6 : UInt8) = 5) = False := by decide
private theorem u8_7_eq_5 : ((7 : UInt8) = 5) = False := by decide
private theorem u8_7_eq_6 : ((7 : UInt8) = 6) = False := by decide

private theorem centeredSubnodeLevel4_jvm_fold (a b c d : UInt64) :
    (((a >>> ((48 : UInt32) &&& 63).toUInt64).toUInt32 &&& 65535).toUInt64 |||
      ((b >>> ((32 : UInt32) &&& 63).toUInt64).toUInt32 &&& 65535).toUInt64 <<< ((16 : UInt32) &&& 63).toUInt64 |||
      ((c >>> ((16 : UInt32) &&& 63).toUInt64).toUInt32 &&& 65535).toUInt64 <<< ((32 : UInt32) &&& 63).toUInt64 |||
      (d.toUInt32 &&& 65535).toUInt64 <<< ((48 : UInt32) &&& 63).toUInt64) =
    Algorithm.centeredSubnodeLevel4 a b c d := by
  simp only [Algorithm.centeredSubnodeLevel4, shift_and_63_16_f, shift_and_63_32_f, shift_and_63_48_f]

set_option maxHeartbeats 400000 in
theorem copyCellTryStep_equiv (dst src : Algorithm.FlatHashLifeArena) (cellId : UInt32) (copyMemos : Bool) :
    (runJvmRes 350 f_Algorithm_copyCellTryStep_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, (.ext (.arenaRef 1))), (2, .i32 cellId),
        (3, .i32 (if copyMemos then 1 else 0))] [dst, src])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (Algorithm.copyCellTryStep dst src cellId copyMemos).1,
        [(Algorithm.copyCellTryStep dst src cellId copyMemos).2, src]) := by
  cases copyMemos
  · simp only [Bool.false_eq_true, ite_false]
    apply runJvmRes_map_of_runJvmResFast0 _ 350 _ _ _ rfl
    step_flat_tree f_Algorithm_copyCellTryStep_prog
    all_goals (simp only [Algorithm.copyCellTryStep]; close_flat_leaf)
  · simp only [ite_true]
    apply runJvmRes_map_of_runJvmResFast0 _ 350 _ _ _ rfl
    step_flat_tree f_Algorithm_copyCellTryStep_prog
    all_goals (simp only [Algorithm.copyCellTryStep]; close_flat_leaf)

theorem flatHashLifeArena_quadrantNW_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 500 f_Algorithm_FlatHashLifeArena_quadrantNW_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.quadrantNW nodeId).1, [(arena.quadrantNW nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 500 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_quadrantNW_prog
  all_goals (try (repeat rw [centeredSubnodeLevel4_jvm_fold]); simp only [Algorithm.FlatHashLifeArena.quadrantNW]; close_flat_leaf)

theorem flatHashLifeArena_quadrantNE_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 500 f_Algorithm_FlatHashLifeArena_quadrantNE_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.quadrantNE nodeId).1, [(arena.quadrantNE nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 500 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_quadrantNE_prog
  all_goals (try (repeat rw [centeredSubnodeLevel4_jvm_fold]); simp only [Algorithm.FlatHashLifeArena.quadrantNE]; close_flat_leaf)

theorem flatHashLifeArena_quadrantSW_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 500 f_Algorithm_FlatHashLifeArena_quadrantSW_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.quadrantSW nodeId).1, [(arena.quadrantSW nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 500 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_quadrantSW_prog
  all_goals (try (repeat rw [centeredSubnodeLevel4_jvm_fold]); simp only [Algorithm.FlatHashLifeArena.quadrantSW]; close_flat_leaf)

theorem flatHashLifeArena_quadrantSE_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    (runJvmRes 500 f_Algorithm_FlatHashLifeArena_quadrantSE_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena])).map
        (fun p => (p.1, p.2.heap.arenas)) =
      some (.i32 (arena.quadrantSE nodeId).1, [(arena.quadrantSE nodeId).2]) := by
  apply runJvmRes_map_of_runJvmResFast0 _ 500 _ _ _ rfl
  step_flat_tree f_Algorithm_FlatHashLifeArena_quadrantSE_prog
  all_goals (try (repeat rw [centeredSubnodeLevel4_jvm_fold]); simp only [Algorithm.FlatHashLifeArena.quadrantSE]; close_flat_leaf)

theorem computePopulation_equiv (arena : Algorithm.FlatHashLifeArena) (lvl : UInt8) (nw ne sw se : UInt32) :
    runJvm 1500 f_Algorithm_computePopulation_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 lvl.toUInt32),
        (2, .i32 nw), (3, .i32 ne), (4, .i32 sw), (5, .i32 se)] [arena]) =
      some (.i64 (Algorithm.computePopulation arena lvl nw ne sw se)) := by
  apply runJvm_of_runJvmValFast0 1500 _ _ _ rfl
  step_flat_tree f_Algorithm_computePopulation_prog
  all_goals (
    try simp only [getArenaU64, decide_eq_true_eq, u8_toUInt32_beq_five, beq_iff_eq] at *
    try simp only [Algorithm.computePopulation, Algorithm.popLevel4Id, Algorithm.popCellId,
      Algorithm.popcount64, shift_and_63_1, shift_and_63_2, shift_and_63_4, shift_and_63_56,
      beq_self_eq_true, beq_iff_eq, ite_true, ite_false, ui64_add_zero, ui64_zero_add, UInt64.add_assoc, *])

theorem centeredSubSubnodeSizeCell_equiv (arena : Algorithm.FlatHashLifeArena) (nodeId : UInt32) :
    runJvm 2000 f_Algorithm_centeredSubSubnodeSizeCell_prog
      (initJvmState [(0, (.ext (.arenaRef 0))), (1, .i32 nodeId)] [arena]) =
      some (.i64 (Algorithm.centeredSubSubnodeSizeCell arena nodeId)) := by
  apply runJvm_of_runJvmValFast0 2000 _ _ _ rfl
  step_flat_tree f_Algorithm_centeredSubSubnodeSizeCell_prog
  all_goals (
    try simp only [decide_eq_true_eq] at *
    try simp only [getArenaU64, getArenaU32, getArenaU8,
      u8_sext_beq_five, u8_sext_beq_six, u8_sext_beq_seven, beq_iff_eq] at *
    try simp only [decide_eq_true_eq] at *
    try simp only [Algorithm.centeredSubSubnodeSizeCell, Algorithm.popLevel4Id, Algorithm.popcount64,
      centeredSubnodeLevel4_jvm_fold, shift_and_63_1, shift_and_63_2, shift_and_63_4, shift_and_63_56,
      u8_6_eq_5, u8_7_eq_5, u8_7_eq_6,
      beq_self_eq_true, beq_iff_eq, ite_true, ite_false, ui64_add_zero, ui64_zero_add, UInt64.add_assoc, *])


end Algorithm.JvmVerification
