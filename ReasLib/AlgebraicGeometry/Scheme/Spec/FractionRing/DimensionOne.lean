/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Spec.FractionRing
public import ReasLib.RingTheory.Localization.FractionRing.SubringPair.DimensionOne

/-!
# Spectra of one-dimensional fraction-subring pairs

This file records the open-cover consequence of the dimension-one dichotomy
for two subrings of a common fraction field.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace FractionRing.SubringPair

variable {K : Type u} [Field K]

variable (P : FractionRing.SubringPair K)
variable [IsNoetherianRing P.left] [Finite (MaximalSpectrum P.left)]

section discreteValuation

variable [IsDiscreteValuationRing P.right]

/-- If some unit of the left component is outside the intersection, the affine
spectrum maps of the two components are open immersions whose open ranges
cover the spectrum of the intersection. -/
theorem specMaps_openCover_of_unit_not_mem_intersection
    (hdim : ringKrullDim P.left = 1)
    (hunit : ∃ u : P.leftˣ, ((u : P.left) : K) ∉ P.intersection) :
    ∃ hleft : IsOpenImmersion P.specLeft,
      ∃ hright : IsOpenImmersion P.specRight,
        @Scheme.Hom.opensRange _ _ P.specLeft hleft ⊔
          @Scheme.Hom.opensRange _ _ P.specRight hright = ⊤ := sorry

end discreteValuation

variable [IsNoetherianRing P.right] [Finite (MaximalSpectrum P.right)]

/-- If two Noetherian semilocal components of a fraction-subring pair have
Krull dimension one and their tensor comparison is surjective, their affine
spectrum maps are open immersions whose open ranges cover the spectrum of the
intersection. -/
theorem specMaps_openCover_of_dim_one
    (hleft : ringKrullDim P.left = 1) (hright : ringKrullDim P.right = 1)
    (hsurj : Function.Surjective P.tensorToAmbient) :
    ∃ hleftOpen : IsOpenImmersion P.specLeft,
      ∃ hrightOpen : IsOpenImmersion P.specRight,
        @Scheme.Hom.opensRange _ _ P.specLeft hleftOpen ⊔
          @Scheme.Hom.opensRange _ _ P.specRight hrightOpen = ⊤ := sorry

end FractionRing.SubringPair
