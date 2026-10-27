/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Hilbert
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Proper

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

/-- For a proper morphism of finite presentation of algebraic spaces and a relatively
ample invertible module, the Hilbert-polynomial locus is proper over the base. -/
theorem hilbertPolynomial_isProperOver {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [Proper f] [FinitePresentation f] (L : X.Modules)
    [CategoryTheory.MonoidalCategory.isInvertibleObject L]
    [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L] (P : ℤ → ℤ) :
    IsProperOver
      (Quot.quotHilbert f (SheafOfModules.unit (structureSheaf X)) L P).toFunctor := sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
