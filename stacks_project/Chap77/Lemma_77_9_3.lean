/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap77.Lemma_77_9_3_Surjectivity

/-!
# Lemma 77.9.3

In Situation 77.7.1, if `f` is locally of finite presentation, `𝒢` is of finite
type, and the support of `𝒢` is proper over `B`, then `F_surj` is the algebraic
space `surjectivityOpenSubspace f u`, and `F_surj ⟶ B` is an open immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢)

/-- Lemma 77.9.3 (1): In Situation 77.7.1, if `f` is locally of finite presentation,
`𝒢` is of finite type, and the support of `𝒢` is proper over `B`, then a test
morphism `a : ofOver T ⟶ B` factors through `surjectivityOpenSubspace f u` if and
only if `baseChangeMap f a u` is an epimorphism. Thus `F_surj` is the algebraic
space `(surjectivityOpenSubspace f u).X`. -/
@[stacks 09TP]
theorem factors_surjectivityOpenSubspace_iff [𝒢.IsFiniteType]
    [LocallyOfFinitePresentation f] [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
    {T : Over S} (a : ofOver T ⟶ B) :
    (∃ ℓ : ofOver T ⟶ (surjectivityOpenSubspace f u).X,
        ℓ ≫ (surjectivityOpenSubspace f u).ι = a) ↔
      Epi (baseChangeMap f a u) :=
  sorry

/-- Lemma 77.9.3 (2): In Situation 77.7.1, if `f` is locally of finite presentation,
`𝒢` is of finite type, and the support of `𝒢` is proper over `B`, then
`(surjectivityOpenSubspace f u).ι` is an open immersion. -/
@[stacks 09TP]
theorem isOpenImmersion_surjectivityOpenSubspace_ι [𝒢.IsFiniteType]
    [LocallyOfFinitePresentation f] [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)] :
    IsOpenImmersion (surjectivityOpenSubspace f u).ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
