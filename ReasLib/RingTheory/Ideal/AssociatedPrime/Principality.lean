/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.UFD
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable [IsNoetherianRing R]

/-- An ideal in a Noetherian unique factorization domain is principal if its quotient has no
embedded primes and every prime minimal over it has height one. -/
@[stacks 0BXI]
theorem isPrincipal_of_noEmbedded_of_minimalPrimes_height_eq_one
    (I : Ideal R)
    (hembedded : embeddedPrimes (R ⧸ I) = ∅)
    (hheight : ∀ p ∈ I.minimalPrimes, p.height = 1) :
    I.IsPrincipal := sorry

end Ideal
