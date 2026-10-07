module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.Isomorphism

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Scheme.Hom

noncomputable section

universe u

/- Lemma 27.18.4: with two relative projective-spectrum presentations over the same base and a
compatible relative projective-spectrum map, if the maps on nonnegative graded pieces are
isomorphisms in all sufficiently large degrees, then its natural domain is all of the source,
its full-source morphism is an isomorphism, and every full-source integral-twist comparison is
an isomorphism. -/
@[stacks 07ZJ] #check
  (AlgebraicGeometry.RelativeProjMap.domain_eq_top_of_eventually_isIso :
    ∀ {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S}
      (P𝒜 : RelativeProjPresentation pX) (Pℬ : RelativeProjPresentation pY)
      (φ : P𝒜.algebra ⟶ Pℬ.algebra) (rφ : RelativeProjMap P𝒜 Pℬ φ)
      (hcompat : ∀ W : S.affineOpens,
        Nonempty (RelativeProjMap.AffineChartCompatibility P𝒜 Pℬ φ rφ W))
      (hφIso : ∃ N : ℕ, ∀ d ≥ N, IsIso (φ.hom (Int.ofNat d))),
      rφ.domain = ⊤)

#check
  (AlgebraicGeometry.RelativeProjMap.mapOnTarget_isIso_of_eventually_isIso :
    ∀ {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S}
      (P𝒜 : RelativeProjPresentation pX) (Pℬ : RelativeProjPresentation pY)
      (φ : P𝒜.algebra ⟶ Pℬ.algebra) (rφ : RelativeProjMap P𝒜 Pℬ φ)
      (hcompat : ∀ W : S.affineOpens,
        Nonempty (RelativeProjMap.AffineChartCompatibility P𝒜 Pℬ φ rφ W))
      (hφIso : ∃ N : ℕ, ∀ d ≥ N, IsIso (φ.hom (Int.ofNat d))),
      let hTop : rφ.domain = ⊤ :=
        RelativeProjMap.domain_eq_top_of_eventually_isIso
          P𝒜 Pℬ φ rφ hcompat hφIso
      IsIso (RelativeProjMap.mapOnTarget P𝒜 Pℬ φ rφ hTop))

#check
  (AlgebraicGeometry.RelativeProjMap.thetaOnTarget_isIso_of_eventually_isIso :
    ∀ {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S}
      (P𝒜 : RelativeProjPresentation pX) (Pℬ : RelativeProjPresentation pY)
      (φ : P𝒜.algebra ⟶ Pℬ.algebra) (rφ : RelativeProjMap P𝒜 Pℬ φ)
      (hcompat : ∀ W : S.affineOpens,
        Nonempty (RelativeProjMap.AffineChartCompatibility P𝒜 Pℬ φ rφ W))
      (hφIso : ∃ N : ℕ, ∀ d ≥ N, IsIso (φ.hom (Int.ofNat d))) (n : ℤ),
      let hTop : rφ.domain = ⊤ :=
        RelativeProjMap.domain_eq_top_of_eventually_isIso
          P𝒜 Pℬ φ rφ hcompat hφIso
      let hι : RelativeProjMap.domainTopInclusion P𝒜 Pℬ φ rφ hTop ≫
          rφ.domain.ι = 𝟙 Y :=
        RelativeProjMap.domainTopInclusion_comp_ι P𝒜 Pℬ φ rφ hTop
      IsIso (RelativeProjMap.thetaOnTarget P𝒜 Pℬ φ rφ hTop hι n))
