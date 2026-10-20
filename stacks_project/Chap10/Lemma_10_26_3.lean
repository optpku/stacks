/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Localization.Irreducible
import StacksCheckRecall

@[expose] public section

/-!
@stack 00ET

# Irreducible closed subsets through a prime

The two source correspondences are recalled directly from their reusable
order-isomorphism owners.
-/

/- Lemma 10.26.3 (1): irreducible closed subsets containing `p` correspond to
primes of `R_p`. -/
@[stacks 00ET "(1) irreducible closed subsets"]
#check @PrimeSpectrum.localizationAtPrimeIrreducibleCloseds

/- Lemma 10.26.3 (2): irreducible components containing `p` correspond to
minimal primes of `R_p`. -/
@[stacks 00ET "(2) irreducible components"]
#check @PrimeSpectrum.localizationAtPrimeIrreducibleComponents

@[stacks 00ES "minimal primes and irreducible components"]
#check @minimalPrimes.equivIrreducibleComponents

#check @PrimeSpectrum.pointsEquivIrreducibleCloseds
