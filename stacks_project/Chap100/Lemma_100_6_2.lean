/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact.Cover
import StacksCheckRecall

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

/- Lemma 100.6.2: Let `X` be an algebraic stack. The following are equivalent:
`X` is quasi-compact; there exists a surjective smooth morphism `U ⟶ X` with
`U` an affine scheme; there exists a surjective smooth morphism `U ⟶ X` with
`U` a quasi-compact scheme; there exists a surjective smooth morphism `U ⟶ X`
with `U` a quasi-compact algebraic space; and there exists a surjective
morphism `𝒰 ⟶ X` of algebraic stacks such that `𝒰` is quasi-compact.

Source (1) (`|X|` is quasi-compact) is represented by `IsQuasiCompact`, because
Definition 100.6.1 took a surjective smooth atlas from a quasi-compact scheme
as the owner. -/
@[stacks 04YC] #check (AlgebraicGeometry.AlgebraicStack.isQuasiCompact_tfae :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
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
          Surjective p ∧ IsQuasiCompact (AlgebraicStacks.toGroupoids U) ])

end AlgebraicGeometry.AlgebraicStack
