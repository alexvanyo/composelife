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

import AlgorithmDefs
import proofs.SemanticModelProofs
import proofs.GridEquivalenceProofs
import proofs.HashLifeEquivalenceProofs

/-!
# Symmetries of Conway's rule

`stepGrid` commutes with every translation and with the symmetries of the square (reflections and rotations),
for every grid.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

namespace Algorithm

/--
Conway's rule is invariant under any map of the plane that permutes the Moore neighborhood: if `f` around `p`
agrees with `g` around `q` along a permutation `σ` of the neighbor offsets, the next generations agree.
-/
theorem nextGenAt_of_perm (σ : ℤ × ℤ → ℤ × ℤ) (hσ : (mooreOffsets.map σ).Perm mooreOffsets)
    (f g : ℤ → ℤ → Bool) (x y x' y' : ℤ) (hc : f x y = g x' y')
    (hn : ∀ d ∈ mooreOffsets, f (x + d.1) (y + d.2) = g (x' + (σ d).1) (y' + (σ d).2)) :
    nextGenAt f x y = nextGenAt g x' y' := by
  unfold nextGenAt neighborCountAt
  rw [hc]
  congr 1
  have h1 : mooreOffsets.filter (fun d => f (x + d.1) (y + d.2)) =
      mooreOffsets.filter ((fun d => g (x' + d.1) (y' + d.2)) ∘ σ) :=
    List.filter_congr (fun d hd => by simp only [Function.comp, hn d hd])
  rw [h1, ← List.length_map (f := σ), ← List.filter_map]
  exact (hσ.filter _).length_eq

theorem mem_map_iff_of_inv {T Ti : Coord → Coord} (h1 : ∀ c, Ti (T c) = c) (h2 : ∀ c, T (Ti c) = c)
    (s : List Coord) (c : Coord) : c ∈ s.map T ↔ Ti c ∈ s := by
  constructor
  · intro hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    rwa [h1]
  · intro hc
    exact List.mem_map.mpr ⟨Ti c, hc, h2 c⟩

/--
`stepGrid` commutes with a bijection `T` of the plane (with inverse `Ti`) that maps the Moore neighborhood of
every cell to the Moore neighborhood of its image, along an offset permutation `σ`.
-/
theorem stepGrid_map_comm {T Ti : Coord → Coord} (h1 : ∀ c, Ti (T c) = c) (h2 : ∀ c, T (Ti c) = c)
    (σ : ℤ × ℤ → ℤ × ℤ) (hσ : (mooreOffsets.map σ).Perm mooreOffsets)
    (hT : ∀ (c : Coord) (d : ℤ × ℤ), Ti (c.1 + d.1, c.2 + d.2) = ((Ti c).1 + (σ d).1, (Ti c).2 + (σ d).2))
    (s : List Coord) :
    cellsEqual (stepGrid (s.map T)) ((stepGrid s).map T) = true := by
  apply cellsEqual_of_same_elements
  intro c
  have hs : ∀ c, c ∈ s ↔ (fun x y => s.contains (x, y)) c.1 c.2 = true := fun c => by simp
  have hs' : ∀ c, c ∈ s.map T ↔ (fun x y => s.contains (Ti (x, y))) c.1 c.2 = true := fun c => by
    rw [mem_map_iff_of_inv h1 h2]; simp
  rw [mem_stepGrid_iff_nextGenAt _ (fun x y => s.contains (Ti (x, y))) hs', mem_map_iff_of_inv h1 h2,
    mem_stepGrid_iff_nextGenAt _ (fun x y => s.contains (x, y)) hs]
  rw [nextGenAt_of_perm σ hσ (fun x y => s.contains (Ti (x, y))) (fun x y => s.contains (x, y)) c.1 c.2 (Ti c).1
    (Ti c).2 rfl (fun d _ => by show s.contains (Ti _) = _; rw [hT c d])]

theorem stepGrid_translate_Impl (dx dy : ℤ) (s : List Coord) :
    cellsEqual (stepGrid (translateGrid dx dy s)) (translateGrid dx dy (stepGrid s)) = true :=
  stepGrid_map_comm (T := fun c => (c.1 + dx, c.2 + dy)) (Ti := fun c => (c.1 - dx, c.2 - dy))
    (fun c => by simp) (fun c => by simp) id (by simp) (fun c d => by simp only [id]; congr 1 <;> omega) s

theorem stepGrid_flipX_Impl (s : List Coord) :
    cellsEqual (stepGrid (flipXGrid s)) (flipXGrid (stepGrid s)) = true :=
  stepGrid_map_comm (T := fun c => (c.1, -c.2)) (Ti := fun c => (c.1, -c.2))
    (fun c => by simp) (fun c => by simp) (fun d => (d.1, -d.2)) (by decide)
    (fun c d => by simp only; congr 1; omega) s

theorem stepGrid_flipY_Impl (s : List Coord) :
    cellsEqual (stepGrid (flipYGrid s)) (flipYGrid (stepGrid s)) = true :=
  stepGrid_map_comm (T := fun c => (-c.1, c.2)) (Ti := fun c => (-c.1, c.2))
    (fun c => by simp) (fun c => by simp) (fun d => (-d.1, d.2)) (by decide)
    (fun c d => by simp only; congr 1; omega) s

theorem stepGrid_flipDiag_Impl (s : List Coord) :
    cellsEqual (stepGrid (flipDiagGrid s)) (flipDiagGrid (stepGrid s)) = true :=
  stepGrid_map_comm (T := fun c => (c.2, c.1)) (Ti := fun c => (c.2, c.1))
    (fun c => by simp) (fun c => by simp) (fun d => (d.2, d.1)) (by decide) (fun c d => by simp) s

theorem stepGrid_rotate90_Impl (s : List Coord) :
    cellsEqual (stepGrid (rotate90Grid s)) (rotate90Grid (stepGrid s)) = true :=
  stepGrid_map_comm (T := fun c => (-c.2, c.1)) (Ti := fun c => (c.2, -c.1))
    (fun c => by simp) (fun c => by simp) (fun d => (d.2, -d.1)) (by decide)
    (fun c d => by simp only; congr 1; omega) s

end Algorithm
