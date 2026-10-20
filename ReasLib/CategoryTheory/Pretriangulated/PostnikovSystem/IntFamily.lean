/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ComposableArrows.IntFamily.Vanishing
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Stages.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Integer-Indexed Views of Finite Rows

Finite rows and finite Postnikov systems are viewed here as integer-indexed
families in reverse order, extended by the zero object outside their support.
This is the bridge used by generic shifted-Hom vanishing APIs.
-/

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

namespace PostnikovSystem

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]
variable {n : ℕ} {X : ComposableArrows D n}

/-- Stacks 0DW1: the reversed integer-indexed extension by zero of the auxiliary objects of a
finite Postnikov system. -/
@[stacks 0DW1]
noncomputable def intFamily (P : PostnikovSystem X) : ℤ → D :=
  IntFamily.reverseOfFin P.Y

/-- The integer-indexed view recovers every auxiliary object on its supported indices. -/
@[simp, stacks 0DW1]
theorem intFamily_reverse (P : PostnikovSystem X) (a : Fin (n + 1)) :
    P.intFamily (((n - a.1 : ℕ) : ℤ)) = P a := sorry

/-- A successor-diagonal vanishing hypothesis on a row and auxiliary family specializes to the
corresponding finite-row shifted-Hom group. -/
@[stacks 0DW1]
theorem subsingleton_of_vanishesAboveSuccessor
    {X' : ComposableArrows D n} (P : PostnikovSystem X')
    {X : ComposableArrows D n}
    (h : ShiftedHom.vanishesAboveSuccessor X.intFamily P.intFamily)
    {a b : Fin (n + 1)} (hab : a.1 + 1 < b.1) :
    Subsingleton (ShiftedHom (X.obj a) (P b) ((a.1 : ℤ) + 1 - b.1)) := sorry

end

end PostnikovSystem

end CategoryTheory
