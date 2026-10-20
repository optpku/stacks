module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local

/-!
# Unramified Noether normalization coordinates

This file provides a relative affine-space factorization that is unramified at
a prescribed point.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

noncomputable section

/-- An affine finite type morphism factors through relative affine space of dimension equal to
the rank of its relative tangent space at a prescribed point, with the factorization morphism
unramified at that point. -/
theorem exists_affineSpace_factorization_unramifiedAt
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S] [FiniteType f] (x : X) :
    let r := Module.finrank (X.residueField x) (tangentSpaceAt f x)
    let A := AffineSpace (ULift.{u} (Fin r)) S
    ∃ π : X ⟶ A, π ≫ (A ↘ S) = f ∧ π.UnramifiedAt x := sorry

end

end AlgebraicGeometry.Scheme.Hom
