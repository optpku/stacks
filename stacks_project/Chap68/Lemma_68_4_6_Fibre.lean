module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_8_4_Coproduct
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap68.Definition_68_3_1_FiberDegree

/-!
# Universally bounded fibres of étale morphisms of algebraic spaces

This module records the existence of an étale scheme covering with universally
bounded fibres, and the corresponding affine étale test.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- There is a family of étale morphisms from schemes covering `X` with
universally bounded fibres. -/
def existsEtaleCoverUniversallyBoundedFibres {S : Scheme.{u}}
    (X : AlgebraicSpace S) : Prop :=
  ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
    (∀ i, Etale (φ i)) ∧
      (∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i))) ∧
        ∀ i, universallyBoundedFibres (φ i)

namespace existsEtaleCoverUniversallyBoundedFibres

/-- An étale family of schemes whose images cover the points of `X` and whose
fibres are universally bounded witnesses `existsEtaleCoverUniversallyBoundedFibres`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type u}
    {U : I → Over S} (φ : (i : I) → ofOver (U i) ⟶ X) [∀ i, Etale (φ i)]
    (hcover : ∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i)))
    (hbound : ∀ i, universallyBoundedFibres (φ i)) :
    existsEtaleCoverUniversallyBoundedFibres X :=
  sorry

/-- `existsEtaleCoverUniversallyBoundedFibres X` supplies an étale family of
schemes covering the points of `X` with universally bounded fibres. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsEtaleCoverUniversallyBoundedFibres X) :
    ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
      (∀ i, Etale (φ i)) ∧
        (∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i))) ∧
          ∀ i, universallyBoundedFibres (φ i) :=
  sorry

end existsEtaleCoverUniversallyBoundedFibres

/-- The covering clause of `existsEtaleCoverUniversallyBoundedFibres` is
equivalent to surjectivity of the induced coproduct morphism `∐ φ i`. -/
theorem existsEtaleCoverUniversallyBoundedFibres_iff_coproductDesc
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    existsEtaleCoverUniversallyBoundedFibres X ↔
      ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
        (∀ i, Etale (φ i)) ∧ Surjective (coproductDesc φ) ∧
          ∀ i, universallyBoundedFibres (φ i) :=
  sorry

/-- Every étale morphism from an affine scheme to `X` has universally bounded
fibres. -/
def forallAffineEtaleUniversallyBoundedFibres {S : Scheme.{u}}
    (X : AlgebraicSpace S) : Prop :=
  ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
    universallyBoundedFibres φ

/-- `forallAffineEtaleUniversallyBoundedFibres X` means every étale morphism
from an affine scheme to `X` has universally bounded fibres. -/
theorem forallAffineEtaleUniversallyBoundedFibres_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    forallAffineEtaleUniversallyBoundedFibres X ↔
      ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
        universallyBoundedFibres φ :=
  sorry

namespace forallAffineEtaleUniversallyBoundedFibres

/-- A universal fibre-boundedness condition on affine étale morphisms to `X`
witnesses `forallAffineEtaleUniversallyBoundedFibres`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
      universallyBoundedFibres φ) :
    forallAffineEtaleUniversallyBoundedFibres X :=
  sorry

/-- Under `forallAffineEtaleUniversallyBoundedFibres X`, every étale morphism
from an affine scheme to `X` has universally bounded fibres. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : forallAffineEtaleUniversallyBoundedFibres X) (U : Over S)
    [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ] :
    universallyBoundedFibres φ :=
  sorry

end forallAffineEtaleUniversallyBoundedFibres

end AlgebraicGeometry.AlgebraicSpace
