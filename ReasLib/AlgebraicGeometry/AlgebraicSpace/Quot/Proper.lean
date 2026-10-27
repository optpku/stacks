/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Hilbert
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- For a proper finitely presented morphism of algebraic spaces, a finitely
presented module, and a relatively ample invertible module, the Quot functor
with fixed numerical Hilbert polynomial is represented by an algebraic space
proper over the base. -/
theorem quotHilbert_isProperOver {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [Proper f] [FinitePresentation f] (F L : X.Modules)
    [F.IsFinitePresentation] [isInvertibleObject L]
    [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L]
    (P : ℤ → ℤ) (hP : IsNumericalPolynomial P) :
    IsProperOver (quotHilbert f F L P).toFunctor := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
