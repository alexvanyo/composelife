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

namespace Algorithm.KotlinModel

/-- Standalone model of `DeserializationResult`. -/
inductive DeserResultModel where
  | successful (warningsEmpty : Bool) (id : Nat)
  | unsuccessful (id : Nat)
  deriving DecidableEq, Repr

/-- Standalone model of `DeserializationResult.isSuccessful()`. -/
def DeserResultModel.isSuccessful : DeserResultModel → Bool
  | .successful _ _ => true
  | .unsuccessful _ => false

/-- Whether `reduceToSuccessfulStep a b` picks `a` (true) or `b` (false). -/
def reduceToSuccessfulPicksFirst (a b : DeserResultModel) : Bool :=
  match a with
  | .unsuccessful _ => false
  | .successful aClean _ =>
    match b with
    | .successful _ _ => aClean
    | .unsuccessful _ => true

/-- Binary reduction step of `Iterable<DeserializationResult>.reduceToSuccessful()`. -/
def reduceToSuccessfulStep (a b : DeserResultModel) : DeserResultModel :=
  if reduceToSuccessfulPicksFirst a b then a else b

/-- List reduction model of `Iterable<DeserializationResult>.reduceToSuccessful()`. -/
def reduceToSuccessfulModel : List DeserResultModel → Option DeserResultModel
  | [] => none
  | x :: xs => some (xs.foldl reduceToSuccessfulStep x)

/-- Standalone model of `CellStateFormat`. -/
inductive CellStateFormatModel where
  | plaintext
  | life
  | runLengthEncoding
  | macrocell
  | unknown
  deriving DecidableEq, Repr

/-- Standalone model of `CellStateFormat.Companion.fromFileExtension(String?)`. -/
def fromFileExtensionModel : Option String → CellStateFormatModel
  | some "cells" => .plaintext
  | some "lif" => .life
  | some "life" => .life
  | some "rle" => .runLengthEncoding
  | some "mc" => .macrocell
  | _ => .unknown

end Algorithm.KotlinModel
