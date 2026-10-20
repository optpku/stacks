/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
variable [IsNoetherianRing P.right] [Finite (MaximalSpectrum P.right)]

/- Lemma 33.37.6 (1): if both components of a fraction-subring pair are
Noetherian semilocal domains of dimension one and the tensor comparison is
surjective, the two affine spectrum maps are open immersions whose ranges
cover the intersection spectrum. -/
@[stacks 09N3]
#check (FractionRing.SubringPair.specMaps_openCover_of_dim_one P :
  (hleft : ringKrullDim P.left = 1) → (hright : ringKrullDim P.right = 1) →
  (hsurj : Function.Surjective P.tensorToAmbient) →
  ∃ hleftOpen : IsOpenImmersion P.specLeft,
      ∃ hrightOpen : IsOpenImmersion P.specRight,
        @Scheme.Hom.opensRange _ _ P.specLeft hleftOpen ⊔
          @Scheme.Hom.opensRange _ _ P.specRight hrightOpen = ⊤)

/- The same hypotheses yield two localization-away charts
whose defining elements generate the unit ideal in the intersection. -/
#check (FractionRing.SubringPair.exists_awayCover_of_dim_one P :
  (hleft : ringKrullDim P.left = 1) → (hright : ringKrullDim P.right = 1) →
  (hsurj : Function.Surjective P.tensorToAmbient) →
  ∃ x y : P.intersection,
    IsLocalization.Away x P.left ∧ IsLocalization.Away y P.right ∧
      Ideal.span ({x, y} : Set P.intersection) = ⊤)

/- Lemma 33.37.6 (2): under the same hypotheses, surjectivity of the tensor
comparison upgrades to bijectivity. -/
@[stacks 09N3]
#check (FractionRing.SubringPair.tensorToAmbient_bijective_of_dim_one P :
  (hleft : ringKrullDim P.left = 1) → (hright : ringKrullDim P.right = 1) →
  (hsurj : Function.Surjective P.tensorToAmbient) →
  Function.Bijective P.tensorToAmbient)

end FractionRing.SubringPair
