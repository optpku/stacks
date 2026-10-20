/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/- Lemma 37.34.4: a flat finitely presented morphism `f : X ⟶ S` between affine
schemes is obtained from a flat finite-type morphism `D.toSi : D.W ⟶ S₀` between
affine schemes by a cartesian square, where `S₀` is of finite type over `Spec ℤ`. -/
@[stacks 05FE] #check
  (AlgebraicGeometry.FiniteTypeApproximationDiagram.exists_isPullback_of_flat :
    ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
      (f : X ⟶ S) [Scheme.Hom.FinitePresentation f] [Flat f],
      ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
        (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
        (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
        (_ : Scheme.Hom.FiniteType D.toSi) (_ : Flat D.toSi),
        IsPullback D.toW f D.toSi π)

end AlgebraicGeometry.FiniteTypeApproximationDiagram
