module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap94.Definition_94_12_3_AlgebraicStacks
public import stacks_project.Chap100.Definition_100_5_1_Surjective
public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact

/-!
# Atlas and cover tests for quasi-compact algebraic stacks

An algebraic stack is quasi-compact precisely when it admits a surjective
smooth atlas from an affine scheme, from a quasi-compact scheme, or from a
quasi-compact algebraic space, or a merely surjective morphism from a
quasi-compact algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists an affine scheme `U` over `S` and a surjective smooth morphism
`GroupoidsOver.slice U ⟶ X`. -/
def existsAffineSmoothCover {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop :=
  ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
    Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ IsAffine U.left

namespace existsAffineSmoothCover

/-- `existsAffineSmoothCover X` unpacks to a surjective smooth atlas from an
affine scheme over `S`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    existsAffineSmoothCover X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ IsAffine U.left :=
  sorry

/-- A surjective smooth atlas from an affine scheme witnesses
`existsAffineSmoothCover`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [IsAffine U.left] :
    existsAffineSmoothCover X :=
  sorry

/-- `existsAffineSmoothCover X` supplies a surjective smooth atlas from an
affine scheme over `S`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : existsAffineSmoothCover X) :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ IsAffine U.left :=
  sorry

end existsAffineSmoothCover

/-- There exists a quasi-compact scheme `U` over `S` and a surjective smooth
morphism `GroupoidsOver.slice U ⟶ X`. -/
def existsQuasiCompactSchemeSmoothCover {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop :=
  ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
    Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ CompactSpace U.left

namespace existsQuasiCompactSchemeSmoothCover

/-- `existsQuasiCompactSchemeSmoothCover X` unpacks to a surjective smooth
atlas from a quasi-compact scheme over `S`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    existsQuasiCompactSchemeSmoothCover X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          CompactSpace U.left :=
  sorry

/-- A surjective smooth atlas from a quasi-compact scheme witnesses
`existsQuasiCompactSchemeSmoothCover`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [CompactSpace U.left] :
    existsQuasiCompactSchemeSmoothCover X :=
  sorry

/-- `existsQuasiCompactSchemeSmoothCover X` supplies a surjective smooth atlas
from a quasi-compact scheme over `S`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : existsQuasiCompactSchemeSmoothCover X) :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ CompactSpace U.left :=
  sorry

end existsQuasiCompactSchemeSmoothCover

/-- There exists a quasi-compact algebraic space `U` over `S` and a surjective
smooth morphism `U.toGroupoids ⟶ X`. -/
def existsQuasiCompactSpaceSmoothCover {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop :=
  ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
    Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
      AlgebraicSpace.IsQuasiCompact U

namespace existsQuasiCompactSpaceSmoothCover

/-- `existsQuasiCompactSpaceSmoothCover X` unpacks to a surjective smooth atlas
from a quasi-compact algebraic space over `S`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    existsQuasiCompactSpaceSmoothCover X ↔
      ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          AlgebraicSpace.IsQuasiCompact U :=
  sorry

/-- A surjective smooth atlas from a quasi-compact algebraic space witnesses
`existsQuasiCompactSpaceSmoothCover`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : AlgebraicSpace S} (p : U.toGroupoids ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicSpace.IsQuasiCompact U] :
    existsQuasiCompactSpaceSmoothCover X :=
  sorry

/-- `existsQuasiCompactSpaceSmoothCover X` supplies a surjective smooth atlas
from a quasi-compact algebraic space over `S`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : existsQuasiCompactSpaceSmoothCover X) :
    ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicSpace.IsQuasiCompact U :=
  sorry

end existsQuasiCompactSpaceSmoothCover

/-- There exists a quasi-compact algebraic stack `U` over `S` and a surjective
morphism `AlgebraicStacks.toGroupoids U ⟶ X`. -/
def existsQuasiCompactSurjection {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop :=
  ∃ (U : AlgebraicStacks S) (p : AlgebraicStacks.toGroupoids U ⟶ X),
    Surjective p ∧ IsQuasiCompact (AlgebraicStacks.toGroupoids U)

namespace existsQuasiCompactSurjection

/-- `existsQuasiCompactSurjection X` unpacks to a surjective morphism from a
quasi-compact algebraic stack over `S`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    existsQuasiCompactSurjection X ↔
      ∃ (U : AlgebraicStacks S) (p : AlgebraicStacks.toGroupoids U ⟶ X),
        Surjective p ∧ IsQuasiCompact (AlgebraicStacks.toGroupoids U) :=
  sorry

/-- A surjective morphism of algebraic stacks from a quasi-compact algebraic
stack witnesses `existsQuasiCompactSurjection`. -/
theorem of {S : Scheme.{u}} {U X : GroupoidsOver S} [AlgebraicStack U]
    [AlgebraicStack X] (p : U ⟶ X) [Surjective p] [IsQuasiCompact U] :
    existsQuasiCompactSurjection X :=
  sorry

/-- `existsQuasiCompactSurjection X` supplies a surjective morphism from a
quasi-compact algebraic stack over `S`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : existsQuasiCompactSurjection X) :
    ∃ (U : AlgebraicStacks S) (p : AlgebraicStacks.toGroupoids U ⟶ X),
      Surjective p ∧ IsQuasiCompact (AlgebraicStacks.toGroupoids U) :=
  sorry

end existsQuasiCompactSurjection

/-- Viewing a quasi-compact algebraic space as an algebraic stack yields a
quasi-compact algebraic stack. -/
instance instIsQuasiCompact_toGroupoids {S : Scheme.{u}} (U : AlgebraicSpace S)
    [AlgebraicSpace.IsQuasiCompact U] : IsQuasiCompact U.toGroupoids :=
  sorry

end AlgebraicGeometry.AlgebraicStack
