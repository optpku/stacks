/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap67.Lemma_67_25_1
public import stacks_project.Chap67.Lemma_67_25_4_FiniteTypePoint

/-!
# Identification of finite-type points of an algebraic space

The finite-type points of an algebraic space are the images of closed points of
schemes under étale morphisms, and the same description holds if those schemes
are required to be affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.25.3 (1): Let `S` be a scheme. Let `X` be an algebraic space over
`S`. The finite-type points of `X` are the union of the images
`Points.mapOfOver φ '' closedPoints U.left` as `U` ranges over schemes over `S`
and `φ : ofOver U ⟶ X` ranges over étale morphisms. -/
@[stacks 06EH]
theorem finiteTypePoints_eq_iUnion_image_closedPoints_etale {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    finiteTypePoints X =
      ⋃ (U : Over S) (φ : ofOver U ⟶ X) (_ : Etale φ),
        Points.mapOfOver φ '' closedPoints U.left :=
  sorry

/-- Lemma 67.25.3 (2): Let `S` be a scheme. Let `X` be an algebraic space over
`S`. The same identification of `finiteTypePoints X` holds if `U` ranges only
over affine schemes étale over `X`. -/
@[stacks 06EH]
theorem finiteTypePoints_eq_iUnion_image_closedPoints_affine_etale
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    finiteTypePoints X =
      ⋃ (U : Over S) (_ : AlgebraicGeometry.IsAffine U.left)
        (φ : ofOver U ⟶ X) (_ : Etale φ),
        Points.mapOfOver φ '' closedPoints U.left :=
  sorry

/-- Membership in `finiteTypePoints X` is equivalent to being the image of a
closed point under an étale morphism from a scheme over `S`. -/
theorem mem_finiteTypePoints_iff_existsEtaleClosedPoint {S : Scheme.{u}}
    {X : AlgebraicSpace S} {x : Points X} :
    x ∈ finiteTypePoints X ↔ existsEtaleClosedPoint x :=
  sorry

/-- Membership in `finiteTypePoints X` is equivalent to being the image of a
closed point under an étale morphism from an affine scheme over `S`. -/
theorem mem_finiteTypePoints_iff_exists_affine_etale_closedPoint
    {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} :
    x ∈ finiteTypePoints X ↔
      ∃ (U : Over S) (u : U.left) (φ : ofOver U ⟶ X),
        AlgebraicGeometry.IsAffine U.left ∧ u ∈ closedPoints U.left ∧
          Etale φ ∧ Points.mapOfOver φ u = x :=
  sorry

/-- The image of the closed points of a scheme under an étale morphism to `X`
consists of finite-type points of `X`. -/
theorem mapOfOver_image_closedPoints_subset_finiteTypePoints {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    Points.mapOfOver φ '' closedPoints U.left ⊆ finiteTypePoints X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
