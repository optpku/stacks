/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.WContractible.Characterization
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.11.2: for a commutative ring `A`, the following are equivalent:
`A` is w-contractible, every faithfully flat ind-étale ring map `A →+* B` has
a retraction, and `PrimeSpectrum A` is w-local with
`ConnectedComponents (PrimeSpectrum A)` extremally disconnected and
`Localization.AtPrime m` strictly henselian at every maximal ideal `m`. -/
@[stacks 0982] #check (IsWContractibleRing.tfae :
  ∀ (A : Type u) [CommRing A],
    List.TFAE
      [IsWContractibleRing.{u, u} A,
        Algebra.HasFaithfullyFlatIndEtaleRetraction A,
        WLocalSpace (PrimeSpectrum A) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) ∧
            ∀ (m : Ideal A) [m.IsMaximal],
              StrictHenselianLocalRing (Localization.AtPrime m)])

#check (IsWContractibleRing.iff_hasFaithfullyFlatIndEtaleRetraction :
  ∀ {A : Type u} [CommRing A],
    IsWContractibleRing.{u, u} A ↔
      Algebra.HasFaithfullyFlatIndEtaleRetraction A)
#check (IsWContractibleRing.iff_wLocal_extremallyDisconnected_strictlyHenselian :
  ∀ {A : Type u} [CommRing A],
    IsWContractibleRing.{u, u} A ↔
      WLocalSpace (PrimeSpectrum A) ∧
        ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) ∧
          ∀ (m : Ideal A) [m.IsMaximal],
            StrictHenselianLocalRing (Localization.AtPrime m))
