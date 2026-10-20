/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Reduced rings and their minimal primes

@stack 00EW

The canonical map to the product of minimal-prime localizations simultaneously realizes the
two embedding clauses. The zero-divisor clause is exposed independently in the same owner.
-/

universe u

section

variable {R : Type u} [CommRing R] [IsReduced R]

/- Lemma 10.25.2 (1) and (2): `R` embeds through the canonical map into the product of the fields
`Localization.AtPrime p.1`, indexed by the minimal primes of `R`. -/
@[stacks 00EW "(1), (2), canonical embedding"]
#check @minimalPrimes.algebraMap_injective

@[stacks 00EW "(1), (2), field factors"]
#check @minimalPrimes.isField_localizationAtPrime

/- Lemma 10.25.2 (3): the union of the minimal prime ideals is the set of zero divisors. -/
@[stacks 00EW "(3), zero divisors"]
#check @minimalPrimes.iUnion_eq_setOf_exists_mul_eq_zero

end
