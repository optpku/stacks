/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.OpenImmersion

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

section

variable {A B sigma tau : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
  {calA : Nat → sigma} {calB : Nat → tau} [GradedRing calA] [GradedRing calB]
variable (PcalA : AlgebraicGeometry.ProjTwistPresentation calA)
  (PcalB : AlgebraicGeometry.ProjTwistPresentation calB)
  (psi : calA →+*ᵍ calB) (g : calA 0) (hpsig : IsUnit (psi g))
  [IsIso (CommRingCat.ofHom
    (Localization.awayLift psi.toRingHom (g : A) hpsig))]
variable (n : Int)

/- Lemma 27.11.7 (1): the natural domain of the induced `Proj` map is the whole target. -/
@[stacks 01N3] #check
  (AlgebraicGeometry.projMapDomain_eq_top_of_isIso_awayMap psi g hpsig :
    AlgebraicGeometry.projMapDomain psi = ⊤)

/- Lemma 27.11.7 (2): the induced map on projective spectra is an open immersion. -/
@[stacks 01N3] #check
  (AlgebraicGeometry.projMapMap_isOpenImmersion_of_isIso_awayMap psi g hpsig :
    AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.projMap PcalA PcalB psi).map))

/- Lemma 27.11.7 (3): the range is the inverse image of the degree-zero basic open. -/
@[stacks 01N3] #check
  (AlgebraicGeometry.projMapMap_range_eq_preimage_basicOpen_toSpecZero_of_isIso_awayMap
      psi g hpsig :
    Set.range ((AlgebraicGeometry.projMap PcalA PcalB psi).map) =
      ((Proj.toSpecZero calA) ⁻¹ᵁ PrimeSpectrum.basicOpen g : Set (Proj calA)))

/- Lemma 27.11.7 (4): every degreewise twist comparison is an isomorphism. -/
@[stacks 01N3] #check
  (AlgebraicGeometry.projMapTheta_isIso_of_isIso_awayMap PcalA PcalB psi g hpsig n :
    IsIso ((AlgebraicGeometry.projMap PcalA PcalB psi).theta n))

end
