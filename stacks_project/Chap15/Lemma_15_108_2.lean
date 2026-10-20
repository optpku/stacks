/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Etale.Neighborhood.GeometricallyUnibranch

/-!
@stack 0GSC
-/

@[expose] public section

universe u v

/- Lemma 15.108.2: if `q` is a prime of `B`,
`A` is a domain, the localization at the contracted prime is geometrically unibranch, `A → B`
is unramified at `q`, and the induced map of local rings is injective, then some `B_g` with
`g ∉ q` is etale over `A`.  The historical snapshot maps to current Stacks
15.109.2, tag `0GSC`. -/
@[stacks 0GSC "Lemma 15.108.2"]
#check fun (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]
    (q : PrimeSpectrum B)
    [IsGeometricallyUnibranch (Localization.AtPrime (q.asIdeal.under A))]
    (h_unramified : Algebra.UnramifiedAt A B q)
    (h_injective : Function.Injective ((algebraMap A B).localRingHomAt q)) ↦
  (Algebra.UnramifiedAt.exists_etale_away_of_geometricallyUnibranch_of_injective
    (A := A) (B := B) q h_unramified h_injective :
    ∃ g : B, g ∉ q.asIdeal ∧ Algebra.Etale A (Localization.Away g))

end
