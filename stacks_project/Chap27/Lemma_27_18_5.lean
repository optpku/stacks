/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.DegreeOneGenerated

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Scheme.Hom

noncomputable section

universe u

/- Lemma 27.18.5 (1): eventual epimorphy of the nonnegative graded pieces makes the natural
domain of an affine-compatible relative projective-spectrum map equal to the full source. -/
@[stacks 07ZK] #check
  (AlgebraicGeometry.RelativeProjMap.domain_eq_top_of_eventually_surjective :
    ∀ {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S}
      (P𝒜 : RelativeProjPresentation pX) (Pℬ : RelativeProjPresentation pY)
      (φ : P𝒜.algebra ⟶ Pℬ.algebra) (rφ : RelativeProjMap P𝒜 Pℬ φ)
      (hcompat : ∀ W : S.affineOpens,
        Nonempty (RelativeProjMap.AffineChartCompatibility P𝒜 Pℬ φ rφ W))
      (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d))),
      rφ.domain = ⊤)

/- Lemma 27.18.5 (2): under the same hypotheses, the canonical full-source morphism is a closed
immersion. -/
@[stacks 07ZK] #check
  (AlgebraicGeometry.RelativeProjMap.mapOnTarget_isClosedImmersion_of_eventually_surjective :
    ∀ {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S}
      (P𝒜 : RelativeProjPresentation pX) (Pℬ : RelativeProjPresentation pY)
      (φ : P𝒜.algebra ⟶ Pℬ.algebra) (rφ : RelativeProjMap P𝒜 Pℬ φ)
      (hcompat : ∀ W : S.affineOpens,
        Nonempty (RelativeProjMap.AffineChartCompatibility P𝒜 Pℬ φ rφ W))
      (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d))),
      let hTop : rφ.domain = ⊤ :=
        RelativeProjMap.domain_eq_top_of_eventually_surjective
          P𝒜 Pℬ φ rφ hcompat hφsurj
      IsClosedImmersion (RelativeProjMap.mapOnTarget P𝒜 Pℬ φ rφ hTop))

/- Lemma 27.18.5 (3): if the compatible affine source models are generated in degree one over
degree zero, every canonical full-source integral-twist comparison is an isomorphism. -/
@[stacks 07ZK] #check
  (AlgebraicGeometry.RelativeProjMap.thetaOnTarget_isIso_of_degreeOneGenerated :
    ∀ {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S}
      (P𝒜 : RelativeProjPresentation pX) (Pℬ : RelativeProjPresentation pY)
      (φ : P𝒜.algebra ⟶ Pℬ.algebra) (rφ : RelativeProjMap P𝒜 Pℬ φ)
      (hgenerated : RelativeProjMap.HasDegreeOneGeneratedAffineModels P𝒜 Pℬ φ rφ)
      (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d))) (n : ℤ),
      let hTop : rφ.domain = ⊤ :=
        RelativeProjMap.domain_eq_top_of_eventually_surjective P𝒜 Pℬ φ rφ
          (RelativeProjMap.HasDegreeOneGeneratedAffineModels.affineCompatible
            P𝒜 Pℬ φ hgenerated) hφsurj
      let hι : RelativeProjMap.domainTopInclusion P𝒜 Pℬ φ rφ hTop ≫
          rφ.domain.ι = 𝟙 Y :=
        RelativeProjMap.domainTopInclusion_comp_ι P𝒜 Pℬ φ rφ hTop
      IsIso (RelativeProjMap.thetaOnTarget P𝒜 Pℬ φ rφ hTop hι n))
