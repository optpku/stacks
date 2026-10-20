/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo
import StacksCheckRecall

open CategoryTheory

universe u

/- 81.12.0.1: the canonical functor Spaces/X ⟶ Spaces(U ← U' → X') sending
Y to (U ×_X Y, U' ×_X Y, X' ×_X Y) by base change along the Spec square of
(R → R', f). -/
@[stacks 0F9N] #check (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.functor :
  ∀ {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R),
    CategoryTheory.Over (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.space R) ⥤
      AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.category R' f)
