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

import Algorithm.Basic
import Algorithm.BitComputation
import Algorithm.MacroCell
import Algorithm.HashLife
import Algorithm.FlatHashLife
import Algorithm.HashLifeEquivalence
import AlgorithmDefs
import proofs.FlatHashLifeProofs

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

theorem flat_sentinels_eq :
    EMPTY_BUCKET = 0xFFFFFFFF ∧ UNCOMPUTED = 0xFFFFFFFF :=
  flat_sentinels_eq_Impl

theorem emptyNodeForLevel_four :
    emptyNodeForLevel 4 = 0 :=
  emptyNodeForLevel_four_Impl

theorem emptyNodeForLevel_ge_five (lvl : UInt32) (h : ¬ (lvl <= 4)) :
    emptyNodeForLevel lvl = lvl - 5 :=
  emptyNodeForLevel_ge_five_Impl lvl h

theorem initEmptyNodesLoop_zero_fuel (arena : FlatHashLifeArena) (i : UInt32) :
    arena.initEmptyNodesLoop 0 i = arena :=
  initEmptyNodesLoop_zero_fuel_Impl arena i

theorem initEmptyNodes_overflow_zero (arena : FlatHashLifeArena) :
    (arena.initEmptyNodes).overflow = 0 :=
  initEmptyNodes_overflow_zero_Impl arena

theorem initEmptyNodes_l4Count (arena : FlatHashLifeArena) :
    (arena.initEmptyNodes).l4Count = 1 :=
  initEmptyNodes_l4Count_Impl arena

theorem initEmptyNodes_cellCount (arena : FlatHashLifeArena) :
    (arena.initEmptyNodes).cellCount = 56 :=
  initEmptyNodes_cellCount_Impl arena

theorem initEmptyNodes_l4Nw (arena : FlatHashLifeArena) :
    (arena.initEmptyNodes).l4Nw = arena.l4Nw.set! 0 0 :=
  initEmptyNodes_l4Nw_Impl arena

theorem initEmptyNodes_l4Ne (arena : FlatHashLifeArena) :
    (arena.initEmptyNodes).l4Ne = arena.l4Ne.set! 0 0 :=
  initEmptyNodes_l4Ne_Impl arena

theorem initEmptyNodes_l4Sw (arena : FlatHashLifeArena) :
    (arena.initEmptyNodes).l4Sw = arena.l4Sw.set! 0 0 :=
  initEmptyNodes_l4Sw_Impl arena

theorem initEmptyNodes_l4Se (arena : FlatHashLifeArena) :
    (arena.initEmptyNodes).l4Se = arena.l4Se.set! 0 0 :=
  initEmptyNodes_l4Se_Impl arena

theorem initEmptyNodes_l4StepRes (arena : FlatHashLifeArena) :
    (arena.initEmptyNodes).l4StepRes = arena.l4StepRes.set! 0 0 :=
  initEmptyNodes_l4StepRes_Impl arena

theorem initEmptyNodes_l4HasRes (arena : FlatHashLifeArena) :
    (arena.initEmptyNodes).l4HasRes = arena.l4HasRes.set! 0 1 :=
  initEmptyNodes_l4HasRes_Impl arena

theorem clearL4Loop_zero_fuel (arena : FlatHashLifeArena) (i cap : UInt32) :
    arena.clearL4Loop 0 i cap = arena :=
  clearL4Loop_zero_fuel_Impl arena i cap

theorem clearCellLoop_zero_fuel (arena : FlatHashLifeArena) (i cap : UInt32) :
    arena.clearCellLoop 0 i cap = arena :=
  clearCellLoop_zero_fuel_Impl arena i cap

theorem clear_overflow_zero (arena : FlatHashLifeArena) :
    (arena.clear).overflow = 0 :=
  clear_overflow_zero_Impl arena

theorem probeLevel4_zero_fuel
    (arena : FlatHashLifeArena) (head : UInt32) (nw ne sw se : UInt64) :
    probeLevel4 arena head nw ne sw se 0 = none :=
  probeLevel4_zero_fuel_Impl arena head nw ne sw se

theorem probeLevel4_empty_bucket
    (arena : FlatHashLifeArena) (nw ne sw se : UInt64) (fuel : UInt32) :
    probeLevel4 arena EMPTY_BUCKET nw ne sw se fuel = none :=
  probeLevel4_empty_bucket_Impl arena nw ne sw se fuel

theorem internLevel4_empty_fastpath
    (arena : FlatHashLifeArena) (h : (arena.l4Count > 0) = true) :
    arena.internLevel4 0 0 0 0 = (0, arena) :=
  internLevel4_empty_fastpath_Impl arena h

theorem probeCellNode_zero_fuel
    (arena : FlatHashLifeArena) (head : UInt32) (lvl : UInt8) (nw ne sw se : UInt32) :
    probeCellNode arena head lvl nw ne sw se 0 = none :=
  probeCellNode_zero_fuel_Impl arena head lvl nw ne sw se

theorem probeCellNode_empty_bucket
    (arena : FlatHashLifeArena) (lvl : UInt8) (nw ne sw se : UInt32) (fuel : UInt32) :
    probeCellNode arena EMPTY_BUCKET lvl nw ne sw se fuel = none :=
  probeCellNode_empty_bucket_Impl arena lvl nw ne sw se fuel

theorem computePopulation_out_of_bounds
    (arena : FlatHashLifeArena) (lvl : UInt8) (h_lvl : (lvl == 5) = false)
    (nw ne sw se : UInt32)
    (h_nw : ¬ (nw < arena.cellCount))
    (h_ne : ¬ (ne < arena.cellCount))
    (h_sw : ¬ (sw < arena.cellCount))
    (h_se : ¬ (se < arena.cellCount)) :
    computePopulation arena lvl nw ne sw se = 0 :=
  computePopulation_out_of_bounds_Impl arena lvl h_lvl nw ne sw se h_nw h_ne h_sw h_se

theorem popLevel4Id_zero (arena : FlatHashLifeArena)
    (h_cnt : (0 < arena.l4Count) = true)
    (h_nw : arena.l4Nw[0]! = 0)
    (h_ne : arena.l4Ne[0]! = 0)
    (h_sw : arena.l4Sw[0]! = 0)
    (h_se : arena.l4Se[0]! = 0) :
    popLevel4Id arena 0 = 0 :=
  popLevel4Id_zero_Impl arena h_cnt h_nw h_ne h_sw h_se

theorem popCellId_zero_pop (arena : FlatHashLifeArena) (id : UInt32)
    (h_lt : (id < arena.cellCount) = true)
    (h_pop : arena.cellPop[id.toNat]! = 0) :
    popCellId arena id = 0 :=
  popCellId_zero_pop_Impl arena id h_lt h_pop

theorem computePopulation_level5_all_zero (arena : FlatHashLifeArena)
    (nw ne sw se : UInt32)
    (h_nw : popLevel4Id arena nw = 0)
    (h_ne : popLevel4Id arena ne = 0)
    (h_sw : popLevel4Id arena sw = 0)
    (h_se : popLevel4Id arena se = 0) :
    computePopulation arena 5 nw ne sw se = 0 :=
  computePopulation_level5_all_zero_Impl arena nw ne sw se h_nw h_ne h_sw h_se

theorem computePopulation_cell_all_zero (arena : FlatHashLifeArena) (lvl : UInt8)
    (h_lvl : (lvl == 5) = false)
    (nw ne sw se : UInt32)
    (h_nw : popCellId arena nw = 0)
    (h_ne : popCellId arena ne = 0)
    (h_sw : popCellId arena sw = 0)
    (h_se : popCellId arena se = 0) :
    computePopulation arena lvl nw ne sw se = 0 :=
  computePopulation_cell_all_zero_Impl arena lvl h_lvl nw ne sw se h_nw h_ne h_sw h_se

theorem internCellNode_empty_fastpath
    (arena : FlatHashLifeArena) (lvl : UInt8)
    (h1 : (lvl >= 5) = true) (h2 : (lvl <= 60) = true) (h3 : (arena.cellCount >= 56) = true) :
    let e := emptyNodeForLevel (lvl.toUInt32 - 1)
    arena.internCellNode lvl e e e e = (emptyNodeForLevel lvl.toUInt32, arena) :=
  internCellNode_empty_fastpath_Impl arena lvl h1 h2 h3

theorem stepLevel4_out_of_bounds
    (arena : FlatHashLifeArena) (l4Id : UInt32)
    (h : l4Id >= arena.l4Count) :
    arena.stepLevel4 l4Id = (0, arena) :=
  stepLevel4_out_of_bounds_Impl arena l4Id h

theorem stepLevel4_cached
    (arena : FlatHashLifeArena) (l4Id : UInt32)
    (h_not_ge : (l4Id >= arena.l4Count) = false)
    (h_has : (arena.l4HasRes[l4Id.toNat]! == 1) = true) :
    arena.stepLevel4 l4Id = (arena.l4StepRes[l4Id.toNat]!, arena) :=
  stepLevel4_cached_Impl arena l4Id h_not_ge h_has

theorem stepLevel4_zero_cached
    (arena : FlatHashLifeArena)
    (h_cnt : (0 >= arena.l4Count) = false)
    (h_has : (arena.l4HasRes[0]! == 1) = true)
    (h_res : arena.l4StepRes[0]! = 0) :
    arena.stepLevel4 0 = (0, arena) :=
  stepLevel4_zero_cached_Impl arena h_cnt h_has h_res

theorem flat_centeredSubnode_out_of_bounds
    (arena : FlatHashLifeArena) (id : UInt32)
    (h : id >= arena.cellCount) :
    arena.centeredSubnode id = (0, arena) :=
  flat_centeredSubnode_out_of_bounds_Impl arena id h

theorem flat_centeredHorizontal_out_of_bounds
    (arena : FlatHashLifeArena) (wId eId : UInt32)
    (h : wId >= arena.cellCount) :
    arena.centeredHorizontal wId eId = (0, arena) :=
  flat_centeredHorizontal_out_of_bounds_Impl arena wId eId h

theorem flat_centeredVertical_out_of_bounds
    (arena : FlatHashLifeArena) (nId sId : UInt32)
    (h : nId >= arena.cellCount) :
    arena.centeredVertical nId sId = (0, arena) :=
  flat_centeredVertical_out_of_bounds_Impl arena nId sId h

theorem flat_centeredSubSubnode_out_of_bounds
    (arena : FlatHashLifeArena) (id : UInt32)
    (h : id >= arena.cellCount) :
    arena.centeredSubSubnode id = (0, arena) :=
  flat_centeredSubSubnode_out_of_bounds_Impl arena id h

theorem centeredSubSubnodeSizeCell_out_of_bounds
    (arena : FlatHashLifeArena) (id : UInt32)
    (h : id >= arena.cellCount) :
    centeredSubSubnodeSizeCell arena id = 0 :=
  centeredSubSubnodeSizeCell_out_of_bounds_Impl arena id h

theorem needToExpandCell_out_of_bounds
    (arena : FlatHashLifeArena) (id : UInt32)
    (h : id >= arena.cellCount) :
    arena.needToExpandCell id = true :=
  needToExpandCell_out_of_bounds_Impl arena id h

theorem needToExpandCell_eq_pop
    (arena : FlatHashLifeArena) (id : UInt32)
    (h_not_ge : (id >= arena.cellCount) = false)
    (h_eq : centeredSubSubnodeSizeCell arena id = arena.cellPop[id.toNat]!) :
    arena.needToExpandCell id = false :=
  needToExpandCell_eq_pop_Impl arena id h_not_ge h_eq

theorem needToExpandCell_ne_pop
    (arena : FlatHashLifeArena) (id : UInt32)
    (h_not_ge : (id >= arena.cellCount) = false)
    (h_ne : centeredSubSubnodeSizeCell arena id ≠ arena.cellPop[id.toNat]!) :
    arena.needToExpandCell id = true :=
  needToExpandCell_ne_pop_Impl arena id h_not_ge h_ne

theorem expandLevel4Centered_out_of_bounds
    (arena : FlatHashLifeArena) (l4Id : UInt32)
    (h : l4Id >= arena.l4Count) :
    arena.expandLevel4Centered l4Id = (UNCOMPUTED, arena) :=
  expandLevel4Centered_out_of_bounds_Impl arena l4Id h

theorem expandCentered_out_of_bounds
    (arena : FlatHashLifeArena) (id : UInt32)
    (h : id >= arena.cellCount) :
    arena.expandCentered id = (UNCOMPUTED, arena) :=
  expandCentered_out_of_bounds_Impl arena id h

theorem flat_quadrantNW_out_of_bounds
    (arena : FlatHashLifeArena) (id : UInt32)
    (h : id >= arena.cellCount) :
    arena.quadrantNW id = (0, arena) :=
  flat_quadrantNW_out_of_bounds_Impl arena id h

theorem flat_quadrantNE_out_of_bounds
    (arena : FlatHashLifeArena) (id : UInt32)
    (h : id >= arena.cellCount) :
    arena.quadrantNE id = (0, arena) :=
  flat_quadrantNE_out_of_bounds_Impl arena id h

theorem flat_quadrantSW_out_of_bounds
    (arena : FlatHashLifeArena) (id : UInt32)
    (h : id >= arena.cellCount) :
    arena.quadrantSW id = (0, arena) :=
  flat_quadrantSW_out_of_bounds_Impl arena id h

theorem flat_quadrantSE_out_of_bounds
    (arena : FlatHashLifeArena) (id : UInt32)
    (h : id >= arena.cellCount) :
    arena.quadrantSE id = (0, arena) :=
  flat_quadrantSE_out_of_bounds_Impl arena id h

theorem stepLevel5_out_of_bounds
    (arena : FlatHashLifeArena) (id : UInt32)
    (h : id >= arena.cellCount) :
    arena.stepLevel5 id = (UNCOMPUTED, arena) :=
  stepLevel5_out_of_bounds_Impl arena id h

theorem stepLevel5_cached
    (arena : FlatHashLifeArena) (id : UInt32)
    (h_not_ge : (id >= arena.cellCount) = false)
    (h_res : (arena.cellStepRes[id.toNat]! != UNCOMPUTED) = true) :
    arena.stepLevel5 id = (arena.cellStepRes[id.toNat]!, arena) :=
  stepLevel5_cached_Impl arena id h_not_ge h_res

theorem stepLevel5_zero_cached
    (arena : FlatHashLifeArena)
    (h_cnt : (0 >= arena.cellCount) = false)
    (h_res : arena.cellStepRes[0]! = 0) :
    arena.stepLevel5 0 = (0, arena) :=
  stepLevel5_zero_cached_Impl arena h_cnt h_res

theorem isNearCapacity_eq
    (arena : FlatHashLifeArena) :
    arena.isNearCapacity =
      ((arena.l4Count * 4 >= (arena.l4Mask + 1) * 3) ||
       (arena.cellCount * 4 >= (arena.cellMask + 1) * 3)) :=
  isNearCapacity_eq_Impl arena

theorem isOver60Percent_eq
    (arena : FlatHashLifeArena) :
    arena.isOver60Percent =
      ((arena.l4Count * 5 >= (arena.l4Mask + 1) * 3) ||
       (arena.cellCount * 5 >= (arena.cellMask + 1) * 3)) :=
  isOver60Percent_eq_Impl arena

theorem combineQuadrants_overflow
    (arena : FlatHashLifeArena) (nodeId : UInt32) (lvl : UInt8) (r_nw r_ne r_sw r_se : UInt32)
    (h : ((arena.internCellNode (lvl - 1) r_nw r_ne r_sw r_se).2.overflow == 0) = false) :
    (arena.combineQuadrants nodeId lvl r_nw r_ne r_sw r_se).1 = UNCOMPUTED :=
  combineQuadrants_overflow_Impl arena nodeId lvl r_nw r_ne r_sw r_se h

theorem setRemapL4_overflow_eq
    (arena : FlatHashLifeArena) (idx val : UInt32) :
    (arena.setRemapL4 idx val).overflow = arena.overflow :=
  setRemapL4_overflow_eq_Impl arena idx val

theorem setRemapCell_overflow_eq
    (arena : FlatHashLifeArena) (idx val : UInt32) :
    (arena.setRemapCell idx val).overflow = arena.overflow :=
  setRemapCell_overflow_eq_Impl arena idx val

theorem setCellStepRes_overflow_eq
    (arena : FlatHashLifeArena) (idx val : UInt32) :
    (arena.setCellStepRes idx val).overflow = arena.overflow :=
  setCellStepRes_overflow_eq_Impl arena idx val

theorem setL4StepRes_overflow_eq
    (arena : FlatHashLifeArena) (idx : UInt32) (val : UInt64) :
    (arena.setL4StepRes idx val).overflow = arena.overflow :=
  setL4StepRes_overflow_eq_Impl arena idx val

theorem getCellStepRes_out_of_bounds
    (arena : FlatHashLifeArena) (nodeId : UInt32)
    (h : ¬ (nodeId < arena.cellCount)) :
    getCellStepRes arena nodeId = UNCOMPUTED :=
  getCellStepRes_out_of_bounds_Impl arena nodeId h

theorem getRemapCell_out_of_bounds
    (arena : FlatHashLifeArena) (nodeId : UInt32)
    (h : ¬ (nodeId < arena.remapCell.size.toUInt32)) :
    getRemapCell arena nodeId = UNCOMPUTED :=
  getRemapCell_out_of_bounds_Impl arena nodeId h

theorem getCellLevel_out_of_bounds
    (arena : FlatHashLifeArena) (nodeId : UInt32)
    (h : ¬ (nodeId < arena.cellCount)) :
    getCellLevel arena nodeId = 0 :=
  getCellLevel_out_of_bounds_Impl arena nodeId h

theorem getOverflow_eq
    (arena : FlatHashLifeArena) :
    getOverflow arena = arena.overflow :=
  getOverflow_eq_Impl arena

theorem getCellCount_eq
    (arena : FlatHashLifeArena) :
    getCellCount arena = arena.cellCount :=
  getCellCount_eq_Impl arena

theorem getL4Count_eq
    (arena : FlatHashLifeArena) :
    getL4Count arena = arena.l4Count :=
  getL4Count_eq_Impl arena

theorem stepCellSerialLoop_zero_fuel
    (arena : FlatHashLifeArena) (sp : UInt32) :
    arena.stepCellSerialLoop sp 0 = arena :=
  stepCellSerialLoop_zero_fuel_Impl arena sp

theorem stepCellSerial_snd_eq
    (arena : FlatHashLifeArena) (nodeId : UInt32) :
    (arena.stepCellSerial nodeId).2 =
      (arena.setRemapL4 0 nodeId).stepCellSerialLoop 1 ((arena.cellMask + 1) * 8 + 1024) :=
  stepCellSerial_snd_eq_Impl arena nodeId

theorem prepareRootForStep_out_of_bounds
    (arena : FlatHashLifeArena) (rootId : UInt32)
    (h : rootId >= arena.cellCount) :
    arena.prepareRootForStep rootId = (UNCOMPUTED, arena) :=
  prepareRootForStep_out_of_bounds_Impl arena rootId h

theorem prepareRootForStep_no_expand
    (arena : FlatHashLifeArena) (rootId : UInt32)
    (h_lt : ¬ (rootId >= arena.cellCount))
    (h_lvl : ¬ (getCellLevel arena rootId <= 5))
    (h_need : arena.needToExpandCell rootId = false) :
    arena.prepareRootForStep rootId = (rootId, arena) :=
  prepareRootForStep_no_expand_Impl arena rootId h_lt h_lvl h_need

theorem stepOneGeneration_out_of_bounds
    (arena : FlatHashLifeArena) (ox oy : Int32) (rootNodeId : UInt32)
    (h : rootNodeId >= arena.cellCount) :
    arena.stepOneGeneration ox oy rootNodeId = ((ox, oy, UNCOMPUTED), arena) :=
  stepOneGeneration_out_of_bounds_Impl arena ox oy rootNodeId h


theorem initRemapL4Loop_zero_fuel
    (arena : FlatHashLifeArena) (i limit : UInt32) :
    arena.initRemapL4Loop 0 i limit = arena :=
  initRemapL4Loop_zero_fuel_Impl arena i limit

theorem initRemapCellLoop_zero_fuel
    (arena : FlatHashLifeArena) (i limit : UInt32) :
    arena.initRemapCellLoop 0 i limit = arena :=
  initRemapCellLoop_zero_fuel_Impl arena i limit

theorem copyL4From_zero_id
    (dst src : FlatHashLifeArena) (copyMemos : Bool) :
    dst.copyL4From src 0 copyMemos = (0, dst) :=
  copyL4From_zero_id_Impl dst src copyMemos

theorem copyCellTryStep_empty_fastpath
    (dst src : FlatHashLifeArena) (cellId : UInt32) (copyMemos : Bool)
    (h_pop : (src.cellPop[cellId.toNat]! == 0) = true)
    (h_min : (src.cellLevel[cellId.toNat]! >= 5) = true)
    (h_max : (src.cellLevel[cellId.toNat]! <= 60) = true) :
    copyCellTryStep dst src cellId copyMemos =
      (UNCOMPUTED, dst.setRemapCell cellId (src.cellLevel[cellId.toNat]!.toUInt32 - 5)) :=
  copyCellTryStep_empty_fastpath_Impl dst src cellId copyMemos h_pop h_min h_max

theorem copyCellFromLoop_zero_fuel
    (dst src : FlatHashLifeArena) (copyMemos : Bool) (stackBase sp : UInt32) :
    dst.copyCellFromLoop src copyMemos stackBase sp 0 = dst :=
  copyCellFromLoop_zero_fuel_Impl dst src copyMemos stackBase sp

theorem copySubgraphInto_out_of_bounds
    (dst src : FlatHashLifeArena) (rootId : UInt32) (copyMemos : Bool)
    (h : rootId >= src.cellCount) :
    copySubgraphInto dst src rootId copyMemos =
      (dst.initRemapL4Loop (getL4Count src + 1) 0 (getL4Count src)).initRemapCellLoop
        (getCellCount src + 1) 0 (getCellCount src) :=
  copySubgraphInto_out_of_bounds_Impl dst src rootId copyMemos h

theorem copySubgraphFrom_out_of_bounds
    (dst src : FlatHashLifeArena) (rootId : UInt32) (copyMemos : Bool)
    (h : rootId >= src.cellCount) :
    (dst.copySubgraphFrom src rootId copyMemos).1 = 0 :=
  copySubgraphFrom_out_of_bounds_Impl dst src rootId copyMemos h

theorem compactRootFrom_out_of_bounds
    (dst src : FlatHashLifeArena) (rootId : UInt32)
    (h : (rootId >= src.cellCount) = true) :
    dst.compactRootFrom src rootId = ((0, 0), dst) :=
  compactRootFrom_out_of_bounds_Impl dst src rootId h

theorem compactRootFrom_overflow
    (dst src : FlatHashLifeArena) (rootId : UInt32)
    (h : (src.overflow != 0) = true) :
    dst.compactRootFrom src rootId = ((0, 0), dst) :=
  compactRootFrom_overflow_Impl dst src rootId h

theorem internMacroCellLoop_zero_fuel
    (arena : FlatHashLifeArena) (todo : List (Sum MacroCell UInt8)) (sp : UInt32) :
    arena.internMacroCellLoop todo sp 0 = arena :=
  internMacroCellLoop_zero_fuel_Impl arena todo sp

theorem internMacroCellAsRoot_overflow
    (arena : FlatHashLifeArena) (m : MacroCell)
    (h : (getOverflow (arena.internMacroCellLoop [.inl m] 0 ((arena.cellMask + 1) * 8 + 4096)) != 0) = true) :
    (arena.internMacroCellAsRoot m).1 = UNCOMPUTED :=
  internMacroCellAsRoot_overflow_Impl arena m h

theorem internMacroCellWithOffset_overflow
    (arena : FlatHashLifeArena) (ox oy : Int32) (m : MacroCell)
    (h : (arena.internMacroCellAsRoot m).1 = UNCOMPUTED) :
    (arena.internMacroCellWithOffset ox oy m).1.2.2 = UNCOMPUTED :=
  internMacroCellWithOffset_overflow_Impl arena ox oy m h

theorem containsCell_zero_fuel
    (arena : FlatHashLifeArena) (nodeId : UInt32) (rx ry : Int32) :
    arena.containsCell nodeId rx ry 0 = false :=
  containsCell_zero_fuel_Impl arena nodeId rx ry

theorem containsCell_zero_pop
    (arena : FlatHashLifeArena) (nodeId : UInt32)
    (rx ry : Int32) (fuel : UInt32)
    (h_not_ge : (nodeId >= arena.cellCount) = false)
    (h_pop : (arena.cellPop[nodeId.toNat]! == 0) = true) :
    arena.containsCell nodeId rx ry fuel = false :=
  containsCell_zero_pop_Impl arena nodeId rx ry fuel h_not_ge h_pop

theorem containsCell_emptyNode
    (arena : FlatHashLifeArena) (lvl : UInt8)
    (rx ry : Int32) (fuel : UInt32)
    (h_not_ge : (emptyNodeForLevel lvl.toUInt32 >= arena.cellCount) = false)
    (h_pop : (arena.cellPop[(emptyNodeForLevel lvl.toUInt32).toNat]! == 0) = true) :
    arena.containsCell (emptyNodeForLevel lvl.toUInt32) rx ry fuel = false :=
  containsCell_emptyNode_Impl arena lvl rx ry fuel h_not_ge h_pop

theorem denoteLevel4_out_of_bounds
    (arena : FlatHashLifeArena) (id : UInt32)
    (h : ¬ (id.toUSize < arena.l4Count.toUSize)) :
    denoteLevel4 arena id = emptyLevel4 :=
  denoteLevel4_out_of_bounds_Impl arena id h

theorem denoteLevel4_empty
    (arena : FlatHashLifeArena)
    (h_cnt : (0 : USize) < arena.l4Count.toUSize)
    (h_nw : arena.l4Nw[0]! = 0)
    (h_ne : arena.l4Ne[0]! = 0)
    (h_sw : arena.l4Sw[0]! = 0)
    (h_se : arena.l4Se[0]! = 0) :
    denoteLevel4 arena 0 = emptyLevel4 :=
  denoteLevel4_empty_Impl arena h_cnt h_nw h_ne h_sw h_se

theorem denoteCellNode_zero_fuel
    (arena : FlatHashLifeArena) (lvl : UInt8) (id : UInt32) :
    denoteCellNode 0 arena lvl id = emptyLevel4 :=
  denoteCellNode_zero_fuel_Impl arena lvl id

theorem denoteCellNode_out_of_bounds
    (arena : FlatHashLifeArena) (fuel : ℕ) (lvl : UInt8) (id : UInt32)
    (h_not_le : ¬ (lvl <= 4))
    (h_id : ¬ (id.toUSize < arena.cellCount.toUSize)) :
    denoteCellNode (fuel + 1) arena lvl id = emptyNode lvl.toNat :=
  denoteCellNode_out_of_bounds_Impl arena fuel lvl id h_not_le h_id

theorem emptyNode_five_eq :
    emptyNode 5 = makeCellNode emptyLevel4 emptyLevel4 emptyLevel4 emptyLevel4 :=
  emptyNode_five_eq_Impl

theorem denoteCellNode_five_empty
    (arena : FlatHashLifeArena) (fuel : ℕ)
    (h_cnt : (0 : USize) < arena.cellCount.toUSize)
    (h_nw : arena.cellNw[0]! = 0)
    (h_ne : arena.cellNe[0]! = 0)
    (h_sw : arena.cellSw[0]! = 0)
    (h_se : arena.cellSe[0]! = 0)
    (h_l4 : denoteLevel4 arena 0 = emptyLevel4) :
    denoteCellNode (fuel + 1) arena 5 0 = emptyNode 5 :=
  denoteCellNode_five_empty_Impl arena fuel h_cnt h_nw h_ne h_sw h_se h_l4

theorem flat_single_step_equivalence
    (arena : FlatHashLifeArena)
    (st : FlatCellState)
    (h_wf : isWellFormed (flatToMacroCell arena st))
    (h_bounds : isInInt32Bounds { offset := st.offset, macroCell := flatToMacroCell arena st }) :
    cellsEqual
      (hashLifeToGrid (hashLifeNextGeneration { offset := st.offset, macroCell := flatToMacroCell arena st }))
      (stepGrid (flatToGrid arena st)) = true :=
  flat_single_step_equivalence_Impl arena st h_wf h_bounds

theorem flat_n_step_equivalence
    (n : ℕ)
    (arena : FlatHashLifeArena)
    (st : FlatCellState)
    (h_wf : isWellFormed (flatToMacroCell arena st))
    (h_bounds : isInInt32BoundsN n { offset := st.offset, macroCell := flatToMacroCell arena st }) :
    cellsEqual
      (hashLifeToGrid (hashLifeStepN n { offset := st.offset, macroCell := flatToMacroCell arena st }))
      (stepN n (flatToGrid arena st)) = true :=
  flat_n_step_equivalence_Impl n arena st h_wf h_bounds

end Algorithm
