/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_10_3_TargetLocus

/-!
# Largest open of the target for a local morphism property
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 74.10.3 (1): if `P` is τ-local on the target for
τ ∈ {fppf, syntomic, smooth, étale}, then the restriction of `f` along
`targetLocus P f` has `P`, and every open subspace of `Y` along which the
restriction has `P` factors through `targetLocus P f`. -/
@[stacks 06R2]
theorem targetLocus_isLargest {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P (pullback.snd f (targetLocus P f).ι) ∧
      ∀ V : OpenSubspace Y, P (pullback.snd f V.ι) →
        ∃ χ : V.X ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = V.ι :=
  sorry

/-- Lemma 74.10.3 (2): if `g : Y' ⟶ Y` is flat and locally of finite
presentation, syntomic, smooth, or étale, and the base change
`pullback.snd f g` has `P`, then `g` factors through `targetLocus P f`. -/
@[stacks 06R2]
theorem factorsThrough_targetLocus {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : isFppfToEtale g)
    (hf : P (pullback.snd f g)) :
    ∃ χ : Y' ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = g :=
  sorry

/-- Lemma 74.10.3 (3): if `g : Y' ⟶ Y` is flat and locally of finite
presentation, syntomic, smooth, or étale, then the point-set of
`targetLocus P (pullback.snd f g)` is the preimage of the point-set of
`targetLocus P f`. -/
@[stacks 06R2]
theorem targetLocus_inverseImage {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : isFppfToEtale g) :
    (targetLocus P (pullback.snd f g)).pointsSet =
      Points.map g ⁻¹' (targetLocus P f).pointsSet :=
  sorry

/-- Lemma 74.10.3 (4): if `𝒰` is a τ-covering of `Y`, then the point-set of
`targetLocus P (pullback.snd f (𝒰.f i))` is the preimage of the point-set of
`targetLocus P f` along `𝒰.f i`. -/
@[stacks 06R2]
theorem targetLocus_inverseImage_cover {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒰 : Precoverage.ZeroHypercover.{u} K Y) (i : 𝒰.I₀) :
    (targetLocus P (pullback.snd f (𝒰.f i))).pointsSet =
      Points.map (𝒰.f i) ⁻¹' (targetLocus P f).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
