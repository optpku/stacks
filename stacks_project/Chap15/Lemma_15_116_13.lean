/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RootsOfUnity.KummerArtinSchreier
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.116.13

The reusable owner is the concrete Kummer--Artin--Schreier polynomial in
`KummerArtinSchreier`.  Its cyclotomic-root API is stable under arbitrary base change.  The
domain-specialized recalls below bridge Mathlib's `IsPrimitiveRoot` predicate to the source
statement; this avoids the false zero-divisor generalization admitted by that predicate alone.

@stack 09F2
-/

namespace Lemma_15_116_13

/- Lemma 15.116.13 (1): the base-change-stable owner uses the prime cyclotomic relation and the
explicit canonical polynomial. -/
@[stacks 09F2 "Lemma 15.116.13 (1): canonical quotient polynomial"]
#check (@KummerArtinSchreier.polynomial_spec)

/- Lemma 15.116.13 (2): the canonical polynomial satisfies the exact addition formula over every
commutative algebra when `ζ` satisfies the prime cyclotomic relation. -/
@[stacks 09F2 "Lemma 15.116.13 (2): canonical addition formula"]
#check (@KummerArtinSchreier.addFormula)

/- Domain companion for Lemma 15.116.13 (1): Mathlib's `IsPrimitiveRoot` supplies the cyclotomic
relation when the coefficient ring is a domain. -/
#check (@KummerArtinSchreier.exists_of_isPrimitiveRoot)

/- Lemma 15.116.13 (2): in a domain, a primitive root supplies the cyclotomic relation. -/
#check (@KummerArtinSchreier.addFormula_of_isPrimitiveRoot)

#check @KummerArtinSchreier.IsQuotient.exists_coefficients
#check @KummerArtinSchreier.IsQuotient.quotient_eq
#check @KummerArtinSchreier.IsQuotient.hasQuotientIdentity
#check @KummerArtinSchreier.HasQuotientIdentity.addFormula_mul
#check @KummerArtinSchreier.IsQuotient.map

end Lemma_15_116_13
