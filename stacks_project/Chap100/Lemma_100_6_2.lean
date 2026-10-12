/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap100.Lemma_100_6_2_Cover

/-!
# Characterizations of quasi-compact algebraic stacks

An algebraic stack is quasi-compact if and only if it admits a surjective
smooth atlas from an affine scheme, from a quasi-compact scheme, or from a
quasi-compact algebraic space, and if and only if it admits a surjective
morphism from a quasi-compact algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.6.2: Let `X` be an algebraic stack. The following are equivalent:
`X` is quasi-compact; there exists a surjective smooth morphism `U ⟶ X` with
`U` an affine scheme; there exists a surjective smooth morphism `U ⟶ X` with
`U` a quasi-compact scheme; there exists a surjective smooth morphism `U ⟶ X`
with `U` a quasi-compact algebraic space; and there exists a surjective
morphism `𝒰 ⟶ X` of algebraic stacks such that `𝒰` is quasi-compact.

Source (1) (`|X|` is quasi-compact) is represented by `IsQuasiCompact`, because
Definition 100.6.1 took a surjective smooth atlas from a quasi-compact scheme
as the owner. -/
@[stacks 04YC]
theorem isQuasiCompact_tfae {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    List.TFAE
      [ IsQuasiCompact X
      , existsAffineSmoothCover X
      , existsQuasiCompactSchemeSmoothCover X
      , existsQuasiCompactSpaceSmoothCover X
      , existsQuasiCompactSurjection X ] :=
  sorry

/-- An algebraic stack is quasi-compact if and only if it admits a surjective
smooth atlas from an affine scheme. -/
theorem isQuasiCompact_iff_existsAffineSmoothCover {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] :
    IsQuasiCompact X ↔ existsAffineSmoothCover X :=
  sorry

/-- An algebraic stack is quasi-compact if and only if it admits a surjective
smooth atlas from a quasi-compact scheme. -/
theorem isQuasiCompact_iff_existsQuasiCompactSchemeSmoothCover {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] :
    IsQuasiCompact X ↔ existsQuasiCompactSchemeSmoothCover X :=
  sorry

/-- An algebraic stack is quasi-compact if and only if it admits a surjective
smooth atlas from a quasi-compact algebraic space. -/
theorem isQuasiCompact_iff_existsQuasiCompactSpaceSmoothCover {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] :
    IsQuasiCompact X ↔ existsQuasiCompactSpaceSmoothCover X :=
  sorry

/-- An algebraic stack is quasi-compact if and only if it admits a surjective
morphism from a quasi-compact algebraic stack. -/
theorem isQuasiCompact_iff_existsQuasiCompactSurjection {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] :
    IsQuasiCompact X ↔ existsQuasiCompactSurjection X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
