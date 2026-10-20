/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Standard
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Descent

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/-- A standard syntomic morphism between affine schemes is obtained by base change from a
standard syntomic finite-type morphism between affine schemes over `Spec ℤ`. -/
@[stacks 05FK]
theorem exists_isPullback_of_standardSyntomic
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (hf : StandardSyntomic f) :
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
      (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
      (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
      (_ : Scheme.Hom.FiniteType D.toSi),
      IsPullback D.toW f D.toSi π ∧ StandardSyntomic D.toSi := sorry

end AlgebraicGeometry.FiniteTypeApproximationDiagram
