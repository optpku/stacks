/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FinitePresentation
import ReasLib.AlgebraicGeometry.Scheme.Limit.Constructible

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/-- An affine finitely presented morphism with fibres of constant dimension `d` admits a
finite-type approximation whose comparison square is cartesian and whose fibres also all have
dimension `d`. -/
@[stacks 05FJ]
theorem exists_isPullback_of_fiberDimension_eq
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (d : ℕ) (hfdim : ∀ s : S, f.fiberDimension s = (d : WithBot ℕ∞)) :
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
      (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
      (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
      (_ : Scheme.Hom.FiniteType D.toSi),
      IsPullback D.toW f D.toSi π ∧
        ∀ s₀ : S₀, D.toSi.fiberDimension s₀ = (d : WithBot ℕ∞) := sorry

end AlgebraicGeometry.FiniteTypeApproximationDiagram
