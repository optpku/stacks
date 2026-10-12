/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.DottedArrow
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Cotangent

/-!
# Dotted tangent arrows and fibre cotangent duals

This file composes the canonical dotted-arrow and relative tangent/cotangent
equivalences.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Under a bijective residue-field map, dotted tangent arrows are equivalent
to the residue-field-linear dual of the cotangent space of the fibre stalk. -/
noncomputable def dottedTangentArrowEquivCotangentLinearDual
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : Function.Bijective (f.residueFieldMap x).hom) :
    DottedTangentArrow f x ≃
      (IsLocalRing.CotangentSpace (fiberStalkAt f x) →ₗ[X.residueField x]
        X.residueField x) :=
  (dottedTangentArrowEquiv f x).trans
    (relativeTangentSpaceToCotangentLinearDual f x h).toEquiv

/-- The dotted-arrow/cotangent equivalence sends an arrow to the corresponding
linear form obtained from its relative tangent vector. -/
theorem dottedTangentArrowEquivCotangentLinearDual_apply
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : Function.Bijective (f.residueFieldMap x).hom)
    (θ : DottedTangentArrow f x) :
    dottedTangentArrowEquivCotangentLinearDual f x h θ =
      relativeTangentSpaceToCotangentLinearDual f x h
        (dottedTangentArrowEquiv f x θ) := sorry

/-- The inverse dotted-arrow/cotangent equivalence sends a cotangent linear
form to the dotted tangent arrow corresponding to its relative tangent vector. -/
theorem dottedTangentArrowEquivCotangentLinearDual_symm_apply
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : Function.Bijective (f.residueFieldMap x).hom)
    (φ : IsLocalRing.CotangentSpace (fiberStalkAt f x) →ₗ[X.residueField x]
      X.residueField x) :
    (dottedTangentArrowEquivCotangentLinearDual f x h).symm φ =
      (dottedTangentArrowEquiv f x).symm
        ((relativeTangentSpaceToCotangentLinearDual f x h).symm φ) := sorry

/-- Under a separable residue-field extension, dotted tangent arrows are
equivalent to the residue-field-linear dual of the fibre cotangent space. -/
noncomputable def dottedTangentArrowEquivCotangentLinearDualOfIsSeparable
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h_sep : Algebra.IsSeparable
      (S.residueField (f x)) (X.residueField x)) :
    DottedTangentArrow f x ≃
      (IsLocalRing.CotangentSpace (fiberStalkAt f x) →ₗ[X.residueField x]
        X.residueField x) :=
  (dottedTangentArrowEquiv f x).trans
    (relativeTangentSpaceLinearDualOfIsSeparable f x h_sep).toEquiv

end AlgebraicGeometry.Scheme.Hom
