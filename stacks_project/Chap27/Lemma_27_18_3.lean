module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Map.ClosedImmersion
public import stacks_project.Chap27.Lemma_27_18_1

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Scheme.Hom

noncomputable section

universe u

/- Lemma 27.18.3: with two relative projective-spectrum presentations over the same base and a
compatible relative projective-spectrum map, if the maps on nonnegative graded pieces are
epimorphisms in all sufficiently large degrees, then its natural domain is all of the source,
its full-source morphism is a closed immersion, and every full-source integral-twist comparison
is an epimorphism. These twist comparisons need not be isomorphisms in general, even when the
graded-algebra morphism is surjective. -/
@[stacks 07ZI] #check
  (AlgebraicGeometry.RelativeProjMap.domain_eq_top_of_eventually_surjective :
    ∀ {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S}
      (P𝒜 : RelativeProjPresentation pX) (Pℬ : RelativeProjPresentation pY)
      (φ : P𝒜.algebra ⟶ Pℬ.algebra) (rφ : RelativeProjMap P𝒜 Pℬ φ)
      (hcompat : ∀ W : S.affineOpens,
        Nonempty (RelativeProjMap.AffineChartCompatibility P𝒜 Pℬ φ rφ W))
      (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d))),
      rφ.domain = ⊤)

#check
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

#check
  (AlgebraicGeometry.RelativeProjMap.thetaOnTarget_epi_of_eventually_surjective :
    ∀ {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S}
      (P𝒜 : RelativeProjPresentation pX) (Pℬ : RelativeProjPresentation pY)
      (φ : P𝒜.algebra ⟶ Pℬ.algebra) (rφ : RelativeProjMap P𝒜 Pℬ φ)
      (hcompat : ∀ W : S.affineOpens,
        Nonempty (RelativeProjMap.AffineChartCompatibility P𝒜 Pℬ φ rφ W))
      (hφsurj : ∃ N : ℕ, ∀ d ≥ N, Epi (φ.hom (Int.ofNat d))) (n : ℤ),
      let hTop : rφ.domain = ⊤ :=
        RelativeProjMap.domain_eq_top_of_eventually_surjective
          P𝒜 Pℬ φ rφ hcompat hφsurj
      let hι : RelativeProjMap.domainTopInclusion P𝒜 Pℬ φ rφ hTop ≫
          rφ.domain.ι = 𝟙 Y :=
        RelativeProjMap.domainTopInclusion_comp_ι P𝒜 Pℬ φ rφ hTop
      Epi (RelativeProjMap.thetaOnTarget P𝒜 Pℬ φ rφ hTop hι n))
