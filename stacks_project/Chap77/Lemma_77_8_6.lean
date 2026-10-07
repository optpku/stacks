module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap77.Lemma_77_8_5_ZeroFunctor
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Vanishing functor under proper support

In Situation 77.7.1, if `f` is locally of finite presentation, `𝒢` is of finite
presentation and flat over `B`, and the support of `𝒢` is proper over `B`, then
`F_zero` is an algebraic space and `F_zero ⟶ B` is a closed immersion. If `ℱ` is
of finite type, that morphism is of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

namespace zeroOverSFunctor

/-- Lemma 77.8.6 (1): In Situation 77.7.1, if `f` is locally of finite presentation,
`𝒢` is of finite presentation and flat over `B`, and the support of `𝒢` is proper
over `B`, then the functor `F_zero` is an algebraic space. -/
@[stacks 083M]
theorem isAlgebraicSpace_of_properSupport [LocallyOfFinitePresentation f]
    [𝒢.IsFinitePresentation] [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (u : ℱ ⟶ 𝒢) :
    IsAlgebraicSpace (zeroOverSFunctor f u) :=
  sorry

/-- Lemma 77.8.6 (2): In Situation 77.7.1, if `f` is locally of finite presentation,
`𝒢` is of finite presentation and flat over `B`, and the support of `𝒢` is proper
over `B`, then `F_zero ⟶ B` is a closed immersion. -/
@[stacks 083M]
theorem isClosedImmersion_toB_of_properSupport [LocallyOfFinitePresentation f]
    [𝒢.IsFinitePresentation] [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (u : ℱ ⟶ 𝒢)
    [IsAlgebraicSpace (zeroOverSFunctor f u)] :
    IsClosedImmersion (toB f u) :=
  sorry

/-- Lemma 77.8.6 (3): In Situation 77.7.1, if in addition `ℱ` is of finite type, then
`F_zero ⟶ B` is of finite presentation. -/
@[stacks 083M]
theorem finitePresentation_toB_of_properSupport [LocallyOfFinitePresentation f]
    [𝒢.IsFinitePresentation] [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (u : ℱ ⟶ 𝒢)
    [ℱ.IsFiniteType] [IsAlgebraicSpace (zeroOverSFunctor f u)] :
    FinitePresentation (toB f u) :=
  sorry

end zeroOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Modules
