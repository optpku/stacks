/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 37.34.1: an affine finitely presented morphism `f : X ⟶ S` is obtained from
a finite-type morphism `D.toSi : D.W ⟶ S₀` between affine schemes by the cartesian square
whose other maps are `D.toW : X ⟶ D.W` and `π : S ⟶ S₀`, with `S₀` of finite type over
`Spec ℤ`. -/
@[stacks 05FB] #check
  (AlgebraicGeometry.FiniteTypeApproximationDiagram.exists_isPullback_of_finitePresentation :
    ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
      (f : X ⟶ S) [Scheme.Hom.FinitePresentation f],
      ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
        (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
        (D : AlgebraicGeometry.FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
        (_ : Scheme.Hom.FiniteType D.toSi),
        IsPullback D.toW f D.toSi π)
