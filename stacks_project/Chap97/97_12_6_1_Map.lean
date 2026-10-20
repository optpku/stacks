/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Map

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

/- The induced map of finite Hilbert categories preserves the underlying test schemes. -/
#check (AlgebraicGeometry.FiniteHilbertStack.map :
  ∀ {S : Scheme.{u}} {X' X Y : GroupoidsOver S}
    (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ),
    FiniteHilbertStack.toGroupoids (G ≫ F) d ⟶ FiniteHilbertStack.toGroupoids F d)
