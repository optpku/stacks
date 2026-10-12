/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_3_8_Functor
public import stacks_project.Chap99.Lemma_99_3_8_Yoneda

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- Lemma 99.3.8 (1): if `K` is pseudo-coherent in `D(𝒪_B)` and
`H^{-1}(Lg^* K)` vanishes for every scheme `g : T ⟶ B` over `B`, then
`T ↦ H^0(T, H^0(Lg^* K))` is an algebraic space affine of finite presentation
over `B`. -/
@[stacks 08JX]
theorem cohomologyZeroFunctor_isAffineFinitePresentation (K : ModuleDerived B)
    (hK : IsPseudoCoherent B K)
    (hvan : ∀ σ : SchemeOver B,
      IsZero (cohomologySheaf (pullbackOver K σ) (-1))) :
    IsAffineFinitePresentationOver (cohomologyZeroFunctor K) :=
  sorry

/-- Lemma 99.3.8 (2): if `K` is pseudo-coherent in `D(𝒪_B)` and
`H^i(Lg^* K)` vanishes for all `i < 0` and every scheme over `B`, then `K`
is perfect. -/
@[stacks 08JX]
theorem isPerfect_of_negativePullbackCohomology (K : ModuleDerived B)
    (hK : IsPseudoCoherent B K)
    (hvan : ∀ (σ : SchemeOver B) (i : ℤ), i < 0 →
      IsZero (cohomologySheaf (pullbackOver K σ) i)) :
    IsPerfect K :=
  sorry

/-- Lemma 99.3.8 (3): if `K` is pseudo-coherent in `D(𝒪_B)` and
`H^i(Lg^* K)` vanishes for all `i < 0` and every scheme over `B`, then on
every affine étale scheme `σ : T ⟶ B` over `B` there exists `b ≥ 0` such
that `pullbackOver K σ` has tor amplitude in `[0, b]`. -/
@[stacks 08JX]
theorem exists_hasTorAmplitudeIn_of_negativePullbackCohomology
    (K : ModuleDerived B) (hK : IsPseudoCoherent B K)
    (hvan : ∀ (σ : SchemeOver B) (i : ℤ), i < 0 →
      IsZero (cohomologySheaf (pullbackOver K σ) i)) :
    ∀ (σ : SchemeOver B) [Etale σ.hom] [AlgebraicGeometry.IsAffine σ.left.left],
      ∃ b : ℤ, 0 ≤ b ∧ HasTorAmplitudeIn (pullbackOver K σ) 0 b :=
  sorry

/-- Lemma 99.3.8 (4): if `K` is pseudo-coherent in `D(𝒪_B)` and
`H^i(Lg^* K)` vanishes for all `i < 0` and every scheme over `B`, then
`T ↦ H^0(T, Lg^* K)` is an algebraic space affine of finite presentation
over `B`. -/
@[stacks 08JX]
theorem derivedZeroFunctor_isAffineFinitePresentation (K : ModuleDerived B)
    (hK : IsPseudoCoherent B K)
    (hvan : ∀ (σ : SchemeOver B) (i : ℤ), i < 0 →
      IsZero (cohomologySheaf (pullbackOver K σ) i)) :
    IsAffineFinitePresentationOver (derivedZeroFunctor K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
