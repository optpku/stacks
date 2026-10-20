/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski.Retraction
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.6.7: for a commutative ring `A`, the following are equivalent:
every faithfully flat ring map `A →+* B` identifying local rings has a
retraction, every faithfully flat ind-Zariski ring map `A →+* B` has a
retraction, and `PrimeSpectrum A` is w-local with
`ConnectedComponents (PrimeSpectrum A)` extremally disconnected. -/
@[stacks 09AZ] #check (Algebra.hasFaithfullyFlatIndZariskiRetraction_tfae :
    ∀ (A : Type u) [CommRing A],
    List.TFAE
      [Algebra.HasFaithfullyFlatIsIsoOnLocalRingsRetraction A,
        Algebra.HasFaithfullyFlatIndZariskiRetraction A,
        WLocalSpace (PrimeSpectrum A) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A))])
