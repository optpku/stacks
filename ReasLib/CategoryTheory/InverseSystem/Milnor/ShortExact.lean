/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Milnor.ShortExact.Rows
public import ReasLib.CategoryTheory.InverseSystem.Milnor.ShortExact.Universal
public import ReasLib.CategoryTheory.InverseSystem.Milnor.ShortExact.Snake

/-!
# Milnor Exact Rows for Sequential Inverse Systems

@stack 0H31

This compatibility aggregator reexports the row constructions, their explicit kernel and
cokernel universal properties, and the snake-lemma exact sequence. Existing consumers may keep
importing `ReasLib.CategoryTheory.InverseSystem.Milnor.ShortExact`.
-/
