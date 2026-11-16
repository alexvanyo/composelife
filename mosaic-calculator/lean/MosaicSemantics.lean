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

namespace MosaicCalculator.Mosaic

/-- Simplified Mosaic layout node tree matching Column / Row / Text / onKeyEvent. -/
inductive MosaicNode where
  | text (value : String)
  | row (children : List MosaicNode) (onKeyHandler? : Option Nat := none)
  | column (children : List MosaicNode) (onKeyHandler? : Option Nat := none)
  deriving Repr, Inhabited

/-- Open container kind pushed while composing `Column` or `Row` children. -/
inductive ContainerKind where
  | column
  | row
  deriving DecidableEq, Repr, Inhabited

private def splitNewlineCharsAux (acc : List Char) : List Char → List String
  | [] => [String.ofList acc.reverse]
  | c :: cs =>
    if c = '\n' then String.ofList acc.reverse :: splitNewlineCharsAux [] cs
    else splitNewlineCharsAux (c :: acc) cs

/-- Split a text node string on `'\n'` cleanly for kernel-reducible UI rendering. -/
def splitLines (s : String) : List String :=
  splitNewlineCharsAux [] s.toList

private theorem splitNewlineCharsAux_no_newline (acc cs : List Char) (h : '\n' ∉ cs) :
    splitNewlineCharsAux acc cs = [String.ofList (acc.reverse ++ cs)] := by
  induction cs generalizing acc with
  | nil => simp [splitNewlineCharsAux]
  | cons c cs ih =>
    have hc : c ≠ '\n' := fun heq => h (by simp [heq])
    have hcs : '\n' ∉ cs := fun hmem => h (List.mem_cons_of_mem c hmem)
    dsimp only [splitNewlineCharsAux]
    rw [ite_eq_right (fun hEq => False.elim (hc hEq)), ih (c :: acc) hcs]
    simp

/-- A string without `'\n'` splits into a singleton line. -/
theorem splitLines_eq_singleton (s : String) (h : '\n' ∉ s.toList) :
    splitLines s = [s] := by
  dsimp only [splitLines]
  rw [splitNewlineCharsAux_no_newline [] s.toList h]
  simp [String.ofList_toList]

mutual
  /-- Render a `MosaicNode` tree into terminal text lines matching Mosaic's text applier semantics. -/
  def renderMosaicLines : MosaicNode → List String
    | .text value => splitLines value
    | .column children _ => (renderMosaicListLines children).flatten
    | .row children _ =>
      match children with
      | [] => []
      | _ =>
        let rendered := renderMosaicListLines children
        let maxH := rendered.foldl (fun acc ls => max acc ls.length) 0
        (List.range maxH).map fun rowIdx =>
          String.join (rendered.map fun ls => ls.getD rowIdx "")

  /-- Helper rendering each child `MosaicNode` into its list of lines. -/
  def renderMosaicListLines : List MosaicNode → List (List String)
    | [] => []
    | c :: cs => renderMosaicLines c :: renderMosaicListLines cs
end

/-- Render a `MosaicNode` tree to the terminal string awaited in `runMosaicTest`. -/
def renderMosaic (node : MosaicNode) : String :=
  String.intercalate "\n" (renderMosaicLines node)

mutual
  /-- Extract the outermost attached `onKeyEvent` handler id from a `MosaicNode` tree. -/
  def findKeyHandler? : MosaicNode → Option Nat
    | .text _ => none
    | .row children h? => h? <|> findKeyHandlerList? children
    | .column children h? => h? <|> findKeyHandlerList? children

  def findKeyHandlerList? : List MosaicNode → Option Nat
    | [] => none
    | c :: cs => findKeyHandler? c <|> findKeyHandlerList? cs
end

end MosaicCalculator.Mosaic
