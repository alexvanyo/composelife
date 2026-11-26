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

namespace UiCommon.Model

/--
Exact model of `java.lang.Float.compare(a, b)`:
- `< 0` if `a < b` (or `-0.0f` vs `+0.0f`),
- `0` if `a` and `b` have the same canonical IEEE-754 bits (including `NaN` with `NaN`),
- `> 0` if `a > b` (or `NaN` vs non-`NaN`, `+0.0f` vs `-0.0f`).
-/
def floatCompare (a b : Float32) : Int32 :=
  if a < b then -1
  else if b < a then 1
  else
    let ab : Int32 := (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits).toInt32
    let bb : Int32 := (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits).toInt32
    if ab < bb then -1 else if bb < ab then 1 else 0

/-- Total preorder `≤` induced by `java.lang.Float.compare`. -/
def floatCompareLe (a b : Float32) : Bool :=
  floatCompare a b ≤ 0

/-- Strict order `<` induced by `java.lang.Float.compare`. -/
def floatCompareLt (a b : Float32) : Bool :=
  floatCompare a b < 0

/-- Map-key equality matching `java.lang.Float.equals` (`Float.floatToIntBits` equality). -/
def floatKeyEq (a b : Float32) : Bool :=
  (if a.isNaN then (0x7fc00000 : UInt32) else a.toBits) ==
    (if b.isNaN then (0x7fc00000 : UInt32) else b.toBits)

/--
Bounded-fuel binary search loop matching `List<T>.floorBinarySearch` in `EasingPiecewise.kt`:
```kotlin
while (low + 1 < high) {
    val mid = (low + high) / 2
    if (this[mid] <= value) low = mid else high = mid
}
return low
```
-/
def floorBinarySearchLoop (keys : List Float32) (value : Float32) (low high : Nat) : Nat → Nat
  | 0 => low
  | fuel + 1 =>
    if low + 1 < high then
      let mid := (low + high) / 2
      if floatCompare keys[mid]! value ≤ 0 then
        floorBinarySearchLoop keys value mid high fuel
      else
        floorBinarySearchLoop keys value low mid fuel
    else
      low

/-- Logarithmic fuel bound `Nat.log2 n + 1` sufficient for `floorBinarySearchLoop` on length `n`. -/
def floorBinarySearchFuel (n : Nat) : Nat :=
  Nat.log2 n + 1

/--
Pure Lean 4 model of `List<Float>.floorBinarySearch(value)` returning `-1` when `value < keys[0]`,
and the greatest floor index otherwise. Returns `-1` on empty `keys`.
-/
def floorBinarySearch (keys : List Float32) (value : Float32) : Int :=
  if h : keys.length = 0 then -1
  else
    if floatCompare keys[0] value > 0 then -1
    else (floorBinarySearchLoop keys value 0 keys.length (floorBinarySearchFuel keys.length) : Int)

/-- Predicate asserting every list read in `floorBinarySearchLoop` is strictly within `0 ..< keys.length`. -/
def FloorSearchReadsInBounds (keys : List Float32) (value : Float32) (low high : Nat) : Nat → Prop
  | 0 => True
  | fuel + 1 =>
    if low + 1 < high then
      let mid := (low + high) / 2
      mid < keys.length ∧
        (if floatCompare keys[mid]! value ≤ 0 then
          FloorSearchReadsInBounds keys value mid high fuel
        else
          FloorSearchReadsInBounds keys value low mid fuel)
    else
      True

/-- Non-decreasing adjacency predicate for `Float32` keyframe lists under `floatCompareLe`. -/
def KeysNonDecreasing : List Float32 → Prop
  | [] | [_] => True
  | a :: b :: rest => floatCompareLe a b = true ∧ KeysNonDecreasing (b :: rest)

/-- Strict adjacency predicate for `Float32` keyframe lists under `floatCompareLt`. -/
def KeysStrictlyIncreasing : List Float32 → Prop
  | [] | [_] => True
  | a :: b :: rest => floatCompareLt a b = true ∧ KeysStrictlyIncreasing (b :: rest)

/-- Check whether `easings` is sorted non-decreasingly by keyframe (`sortedBy { it.first } == easings`). -/
def isSortedByKeyframe {E : Type} : List (Float32 × E) → Bool
  | [] | [_] => true
  | (k1, _) :: rest@((k2, _) :: _) => floatCompareLe k1 k2 && isSortedByKeyframe rest

/--
Insert `(k, e)` into an insertion-ordered association list matching Java `LinkedHashMap.put`:
if `k` is already present (by `floatKeyEq`), replace its value in place preserving key order;
otherwise append `(k, e)` at the end.
-/
def putKeyMap {E : Type} (m : List (Float32 × E)) (k : Float32) (e : E) : List (Float32 × E) :=
  match m with
  | [] => [(k, e)]
  | (k0, e0) :: rest =>
    if floatKeyEq k0 k then (k0, e) :: rest
    else (k0, e0) :: putKeyMap rest k e

/-- Build the `LinkedHashMap` constructed by `buildMap { put(0f, easing); putAll(easings) }`. -/
def buildKeyframeMap {E : Type} (easing : E) (easings : List (Float32 × E)) : List (Float32 × E) :=
  easings.foldl (fun acc p => putKeyMap acc p.1 p.2) [((0.0 : Float32), easing)]

/--
Keyframe validation matching `Easing(easing, vararg easings)`:
1. `isSortedByKeyframe easings` (`require(easings.sortedBy { it.first } == easings.toList())`),
2. `allEasings.length == easings.length + 1` (`require(allEasings.size == easings.size + 1)`).
Returns `some (keyList, easingsList)` when valid, `none` when a `require` traps.
-/
def validateEasingKeyframes {E : Type} (easing : E) (easings : List (Float32 × E)) :
    Option (List Float32 × List E) :=
  if isSortedByKeyframe easings then
    let allEasings := buildKeyframeMap easing easings
    if allEasings.length == easings.length + 1 then
      some (allEasings.map Prod.fst, allEasings.map Prod.snd)
    else
      none
  else
    none

/--
Piecewise segment lookup matching the body of the `Easing` lambda in `EasingPiecewise.kt`:
returns `none` if `floorBinarySearch` returns `-1` (which traps on `keyList[-1]`),
otherwise returns `some (piecewiseEasing, piecewiseStart, piecewiseEnd)`.
-/
def piecewiseSegment {E : Type} (keys : List Float32) (easings : List E) (t : Float32) :
    Option (E × Float32 × Float32) :=
  let idx := floorBinarySearch keys t
  if idx < 0 then none
  else
    let i := idx.toNat
    match keys[i]?, easings[i]? with
    | some pStart, some pEasing =>
      let pEnd := keys[i + 1]?.getD (1.0 : Float32)
      some (pEasing, pStart, pEnd)
    | _, _ => none

/-- Full piecewise `Easing` evaluation parameterized by `transform : E → Float32 → Float32`. -/
def evalPiecewiseEasing {E : Type} (transform : E → Float32 → Float32)
    (keys : List Float32) (easings : List E) (t : Float32) : Option Float32 :=
  (piecewiseSegment keys easings t).map fun (e, pStart, pEnd) =>
    transform e ((t - pStart) / (pEnd - pStart))

end UiCommon.Model
