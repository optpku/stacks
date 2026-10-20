/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver
public import stacks_project.Chap77.Theorem_77_9_1_IsomorphismFunctor

/-!
# Isomorphism functor under proper support

In Situation 77.7.1, if `f` is locally of finite presentation, `ℱ` is of finite
presentation and flat over `B`, the support of `ℱ` is proper over `B`, and `u` is
surjective, then `F_iso` is an algebraic space and `F_iso ⟶ B` is a closed
immersion. If `𝒢` is of finite presentation, that morphism is of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

namespace isomorphismOverSFunctor

/-- Lemma 77.9.2 (1): In Situation 77.7.1, if `f` is locally of finite presentation,
`ℱ` is of finite presentation and flat over `B`, the support of `ℱ` is proper over
`B`, and `u` is surjective, then the functor `F_iso` is an algebraic space. -/
@[stacks 083N]
theorem isAlgebraicSpace_of_properSupport [LocallyOfFinitePresentation f]
    [ℱ.IsFinitePresentation] [Proper ((schemeTheoreticSupport ℱ).ι ≫ f)]
    (h_flat : ∀ x : Points X, flatOverAt ℱ f x) (u : ℱ ⟶ 𝒢) [Epi u] :
    IsAlgebraicSpace (isomorphismOverSFunctor f u) :=
  sorry

/-- Lemma 77.9.2 (2): In Situation 77.7.1, if `f` is locally of finite presentation,
`ℱ` is of finite presentation and flat over `B`, the support of `ℱ` is proper over
`B`, and `u` is surjective, then `F_iso ⟶ B` is a closed immersion. -/
@[stacks 083N]
theorem isClosedImmersion_toB_of_properSupport [LocallyOfFinitePresentation f]
    [ℱ.IsFinitePresentation] [Proper ((schemeTheoreticSupport ℱ).ι ≫ f)]
    (h_flat : ∀ x : Points X, flatOverAt ℱ f x) (u : ℱ ⟶ 𝒢) [Epi u]
    [IsAlgebraicSpace (isomorphismOverSFunctor f u)] :
    IsClosedImmersion (toB f u) :=
  sorry

/-- Lemma 77.9.2 (3): In Situation 77.7.1, if in addition `𝒢` is of finite presentation,
then `F_iso ⟶ B` is of finite presentation. -/
@[stacks 083N]
theorem finitePresentation_toB_of_properSupport [LocallyOfFinitePresentation f]
    [ℱ.IsFinitePresentation] [Proper ((schemeTheoreticSupport ℱ).ι ≫ f)]
    (h_flat : ∀ x : Points X, flatOverAt ℱ f x) (u : ℱ ⟶ 𝒢) [Epi u]
    [𝒢.IsFinitePresentation] [IsAlgebraicSpace (isomorphismOverSFunctor f u)] :
    FinitePresentation (toB f u) :=
  sorry

end isomorphismOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Modules
