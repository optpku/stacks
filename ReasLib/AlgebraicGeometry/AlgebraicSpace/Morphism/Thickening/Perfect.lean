/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FiniteOrder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening

/-- In a cartesian square of algebraic spaces with flat, locally finitely presented
right vertical morphism and a finite-order thickening as bottom morphism, a derived
module on the upper right space is relatively perfect if its derived pullback is
pseudo-coherent and has locally finite Tor dimension over the lower left space. -/
theorem isPerfectRelativeTo_of_pullback {S : Scheme.{u}}
    {X X' Y Y' : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) (f' : X' ⟶ Y') (j : Y ⟶ Y')
    (sq : IsPullback i f f' j) [Flat f'] [LocallyOfFinitePresentation f']
    [IsFiniteOrderThickening j] (E' : ModuleDerived X')
    (hE : IsPseudoCoherent X ((modulePullbackDerived i).obj E') ∧
      ModuleDerived.locallyFiniteTorDimensionOver f ((modulePullbackDerived i).obj E')) :
    ModuleDerived.IsPerfectRelativeTo f' E' := sorry

end AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening
