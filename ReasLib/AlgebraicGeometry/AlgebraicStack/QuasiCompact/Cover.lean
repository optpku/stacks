module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Bicategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Quasi-compact covers of algebraic stacks

Quasi-compactness of an algebraic stack is characterized by smooth surjective
covers from affine schemes, quasi-compact schemes, or quasi-compact algebraic
spaces, and by surjections from quasi-compact algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Viewing a quasi-compact algebraic space as an algebraic stack yields a
quasi-compact algebraic stack. -/
instance instIsQuasiCompact_toGroupoids {S : Scheme.{u}} (U : AlgebraicSpace S)
    [AlgebraicSpace.IsQuasiCompact U] : IsQuasiCompact U.toGroupoids :=
  sorry

/-- An algebraic stack is quasi-compact exactly when it admits a smooth
surjective cover by an affine scheme, a quasi-compact scheme, or a
quasi-compact algebraic space, and exactly when it is the surjective image
of a quasi-compact algebraic stack. -/
theorem isQuasiCompact_tfae {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    List.TFAE
      [ IsQuasiCompact X
      , ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
          Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ IsAffine U.left
      , ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
          Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ CompactSpace U.left
      , ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
          Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
            AlgebraicSpace.IsQuasiCompact U
      , ∃ (U : AlgebraicStacks S) (p : AlgebraicStacks.toGroupoids U ⟶ X),
          Surjective p ∧ IsQuasiCompact (AlgebraicStacks.toGroupoids U) ] :=
  sorry

/-- An algebraic stack is quasi-compact if and only if it admits a surjective
smooth atlas from an affine scheme. -/
theorem isQuasiCompact_iff_existsAffineSmoothCover {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] :
    IsQuasiCompact X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ IsAffine U.left :=
  (isQuasiCompact_tfae X).out 0 1

/-- An algebraic stack is quasi-compact if and only if it admits a surjective
smooth atlas from a quasi-compact algebraic space. -/
theorem isQuasiCompact_iff_existsQuasiCompactSpaceSmoothCover {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] :
    IsQuasiCompact X ↔
      ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          AlgebraicSpace.IsQuasiCompact U :=
  (isQuasiCompact_tfae X).out 0 3

/-- An algebraic stack is quasi-compact if and only if it admits a surjective
morphism from a quasi-compact algebraic stack. -/
theorem isQuasiCompact_iff_existsQuasiCompactSurjection {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] :
    IsQuasiCompact X ↔
      ∃ (U : AlgebraicStacks S) (p : AlgebraicStacks.toGroupoids U ⟶ X),
        Surjective p ∧ IsQuasiCompact (AlgebraicStacks.toGroupoids U) :=
  (isQuasiCompact_tfae X).out 0 4

end AlgebraicGeometry.AlgebraicStack
