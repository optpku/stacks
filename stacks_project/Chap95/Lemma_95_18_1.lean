/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Stack
import StacksCheckRecall

/-!
# Lemma 95.18.1

The category of positive-degree finite Hilbert lifts, with its projection to
the test scheme, is a stack in groupoids over the big fppf site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 95.18.1: the finite Hilbert category of positive degree, with its
canonical projection, is a stack in groupoids over `(Sch/S)_fppf`. -/
@[stacks 05WB] #check (AlgebraicGeometry.FiniteHilbertStack.isStackInGroupoids_of_pos :
  {S : Scheme.{u}} → {X Y : GroupoidsOver S} →
  [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p] →
  [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p] →
  (F : X ⟶ Y) → (d : ℕ) → 1 ≤ d →
  IsStack.InGroupoids (Scheme.fppfTopology.over S) (FiniteHilbertStack.p F d))
