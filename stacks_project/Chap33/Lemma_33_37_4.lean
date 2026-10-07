module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Spec.FractionRing.DimensionOne

@[expose] public section

open AlgebraicGeometry

universe u

namespace FractionRing.SubringPair

variable {K : Type u} [Field K]

variable (P : FractionRing.SubringPair K)
variable [IsNoetherianRing P.left] [Finite (MaximalSpectrum P.left)]
variable [IsDiscreteValuationRing P.right]

/- Lemma 33.37.4 (1): if some unit of the left component is outside the
intersection, the two affine spectrum maps are open immersions whose open
ranges cover the spectrum of the intersection. -/
@[stacks 09N1]
#check (FractionRing.SubringPair.specMaps_openCover_of_unit_not_mem_intersection P :
  (hdim : ringKrullDim P.left = 1) →
  (hunit : ∃ u : P.leftˣ, ((u : P.left) : K) ∉ P.intersection) →
  ∃ hleft : IsOpenImmersion P.specLeft,
    ∃ hright : IsOpenImmersion P.specRight,
      @Scheme.Hom.opensRange _ _ P.specLeft hleft ⊔
        @Scheme.Hom.opensRange _ _ P.specRight hright = ⊤)

/- Lemma 33.37.4 (2): if some unit of the left component is outside the
intersection, the canonical tensor comparison to the ambient field is
bijective. -/
@[stacks 09N1]
#check (FractionRing.SubringPair.tensorToAmbient_bijective_of_unit_not_mem_intersection P :
  (hdim : ringKrullDim P.left = 1) →
  (hunit : ∃ u : P.leftˣ, ((u : P.left) : K) ∉ P.intersection) →
  Function.Bijective P.tensorToAmbient)

/- Lemma 33.37.4 (3): if every unit of the left component belongs to the
intersection, the right valuation subring dominates the localization of the
left component at some maximal ideal. -/
@[stacks 09N1]
#check (FractionRing.SubringPair.exists_dominated_localization_of_units_mem_intersection P :
  (hdim : ringKrullDim P.left = 1) →
  (hunit : ∀ u : P.leftˣ, ((u : P.left) : K) ∈ P.intersection) →
  ∃ m : MaximalSpectrum P.left,
    LocalSubring.ofPrime P.left m.asIdeal ≤ LocalSubring.range P.right.subtype)

/- Lemma 33.37.4 (4): if every unit of the left component belongs to the
intersection, the canonical tensor comparison to the ambient field is not
surjective. -/
@[stacks 09N1]
#check (FractionRing.SubringPair.tensorToAmbient_not_surjective_of_units_mem_intersection P :
  (hdim : ringKrullDim P.left = 1) →
  (hunit : ∀ u : P.leftˣ, ((u : P.left) : K) ∈ P.intersection) →
  ¬ Function.Surjective P.tensorToAmbient)

/- The first case admits localization-away presentations whose defining
elements generate the unit ideal in the intersection. -/
#check (FractionRing.SubringPair.exists_awayCover_of_unit_not_mem_intersection P :
  (hdim : ringKrullDim P.left = 1) →
  (hunit : ∃ u : P.leftˣ, ((u : P.left) : K) ∉ P.intersection) →
  ∃ u x : P.intersection,
    ∃ _ : IsLocalization.Away u P.left,
      ∃ _ : IsLocalization.Away x P.right,
        Ideal.span ({u, x} : Set P.intersection) = ⊤)

end FractionRing.SubringPair
