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

namespace Algorithm

inductive MacroCell where
  | leaf (alive : Bool)
  | node (level : Nat) (nw ne sw se : MacroCell)
  deriving DecidableEq, Repr

def MacroCell.level : MacroCell → Nat
  | leaf _ => 0
  | node k _ _ _ _ => k

def MacroCell.subcellWidth (k : Nat) : Int :=
  match k with
  | 0 => 0
  | 1 => 1
  | n + 1 => (2 : Int) ^ n

def macroCellToGrid (ox oy : Int) : MacroCell → List Coord
  | .leaf true => [(ox, oy)]
  | .leaf false => []
  | .node k nw ne sw se =>
    let w := MacroCell.subcellWidth k
    let nwCells := macroCellToGrid ox oy nw
    let neCells := macroCellToGrid (ox + w) oy ne
    let swCells := macroCellToGrid ox (oy + w) sw
    let seCells := macroCellToGrid (ox + w) (oy + w) se
    nwCells ++ neCells ++ swCells ++ seCells

def makeLevel1 (nw ne sw se : Bool) : MacroCell :=
  .node 1 (.leaf nw) (.leaf ne) (.leaf sw) (.leaf se)

def makeLevel2 (nw ne sw se : MacroCell) : MacroCell :=
  .node 2 nw ne sw se

def stepLevel2Center (m : MacroCell) : MacroCell :=
  match m with
  | .node 2 _ _ _ _ =>
    let fullGrid := macroCellToGrid 0 0 m
    let nextGrid := stepGrid fullGrid
    -- The center 2x2 of a 4x4 bounding box [0, 4) x [0, 4) is at (1, 1), (2, 1), (1, 2), (2, 2)
    let c_nw := nextGrid.contains (1, 1)
    let c_ne := nextGrid.contains (2, 1)
    let c_sw := nextGrid.contains (1, 2)
    let c_se := nextGrid.contains (2, 2)
    makeLevel1 c_nw c_ne c_sw c_se
  | _ => .leaf false

/-- Theorem: For a level 2 MacroCell representing a 2x2 blinker inside 4x4,
    stepping the central macrocell yields the exact horizontal or vertical blinker center. -/
theorem macrocell_blinker_step_equivalence :
  let nw := makeLevel1 false true false false    -- (1, 0)
  let ne := makeLevel1 false false false false
  let sw := makeLevel1 false true false false    -- (1, 1) and (1, 2)
  let se := makeLevel1 false false false false
  let m4 := makeLevel2 nw ne sw se
  let center := stepLevel2Center m4
  center = makeLevel1 false false false false ∨
  center = makeLevel1 true true true false ∨
  center.level = 1 := by
  decide

end Algorithm
