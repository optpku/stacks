/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap87.Lemma_87_38_6_Comparison
public import stacks_project.Chap87.Lemma_87_38_6_Counterexample

/-!
# When the canonical comparison of completions is an isomorphism

For a closed subspace `Z ⊂ X` with `T = |Z|`, the comparison
`toCompletionAlong Z : completionAlongSubspace Z.ι ⟶ completionAlong X Z.pointsCloseds`
is an isomorphism when `Z.ι` is of finite presentation, but not in general.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.completionAlongSubspace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 87.38.6 (1): Let `S` be a scheme, let `X` be an algebraic space over
`S`, and let `Z ⊂ X` be a closed subspace with `T = |Z|`. If `Z.ι` is of finite
presentation, then the canonical morphism
`toCompletionAlong Z : completionAlongSubspace Z.ι ⟶ completionAlong X Z.pointsCloseds`
is an isomorphism. -/
@[stacks 0H8N, instance]
instance isIso_toCompletionAlong {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [FinitePresentation Z.ι] :
    IsIso (toCompletionAlong Z) :=
  sorry

/-- Lemma 87.38.6 (2): The comparison `toCompletionAlong` is not an isomorphism
in general. For a nontrivial coefficient ring `R` (the Stacks witness is
`R = ℤ`, `A = MvPolynomial ℕ+ ℤ`, and `I = MvPolynomial.idealOfVars ℕ+ ℤ`),
the closed subspace of `Spec A` cut out by `I` has
`¬ IsIso (toCompletionAlong (counterexample.closedSubspace R))`. -/
@[stacks 0H8N]
theorem not_isIso_toCompletionAlong_counterexample {R : Type u} [CommRing R]
    [Nontrivial R] :
    ¬ IsIso (toCompletionAlong (counterexample.closedSubspace R)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
