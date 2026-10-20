module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Finite-type points and étale morphisms

A point of an algebraic space is of finite type if and only if it is the image
of a closed point of a scheme under an étale morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X)

/-- There exists a scheme `U` over `S`, a closed point of `U`, and an étale
morphism from `ofOver U` to `X` sending that point to `x`. -/
def existsEtaleClosedPoint : Prop :=
  ∃ (U : Over S) (u : U.left) (φ : ofOver U ⟶ X),
    u ∈ closedPoints U.left ∧ Etale φ ∧ Points.mapOfOver φ u = x

/-- A point is the image of a closed point under an étale morphism from a scheme
if and only if there exist such a scheme, closed point, and morphism over the base. -/
theorem existsEtaleClosedPoint_iff :
    existsEtaleClosedPoint x ↔
      ∃ (U : Over S) (u : U.left) (φ : ofOver U ⟶ X),
        u ∈ closedPoints U.left ∧ Etale φ ∧ Points.mapOfOver φ u = x :=
  Iff.rfl

/-- A point of an algebraic space is of finite type if and only if it is the
image of a closed point of a scheme under an étale morphism. -/
theorem isFiniteTypePoint_iff_existsEtaleClosedPoint :
    IsFiniteTypePoint x ↔ existsEtaleClosedPoint x :=
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

/-- The finite-type points of an algebraic space are the union of the images
of closed points of schemes under étale morphisms to that space. -/
theorem finiteTypePoints_eq_iUnion_image_closedPoints_etale {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    finiteTypePoints X =
      ⋃ (U : Over S) (φ : ofOver U ⟶ X) (_ : Etale φ),
        Points.mapOfOver φ '' closedPoints U.left :=
  sorry

/-- The finite-type points of an algebraic space are the union of the images
of closed points of affine schemes under étale morphisms to that space. -/
theorem finiteTypePoints_eq_iUnion_image_closedPoints_affine_etale
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    finiteTypePoints X =
      ⋃ (U : Over S) (_ : AlgebraicGeometry.IsAffine U.left)
        (φ : ofOver U ⟶ X) (_ : Etale φ),
        Points.mapOfOver φ '' closedPoints U.left :=
  sorry

/-- The image of the closed points of a scheme under an étale morphism to `X`
consists of finite-type points of `X`. -/
theorem mapOfOver_image_closedPoints_subset_finiteTypePoints {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] :
    Points.mapOfOver φ '' closedPoints U.left ⊆ finiteTypePoints X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
