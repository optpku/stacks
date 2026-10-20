/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.RingTheory.PrincipalIdealDomainOfPrime
public import ReasLib.RingTheory.Ideal.Principal

@[expose] public section

/-!
# Principal Ideals from Prime Ideals

The two source clauses are exposed through the Oka and principal-ideal-ring
owners; no chapter theorem wrapper is needed.

@stack 05KH
-/

universe u

section

variable {R : Type u} [CommSemiring R]

/- Lemma 10.28.11 (1): an ideal of `R` maximal among the non-principal ideals is prime. This is
the exact canonical specialization of the owner theorem `Ideal.IsOka.isPrime_of_maximal_not` to
the Oka predicate `Ideal.isOka_isPrincipal` recalled in Example 10.28.5. -/
@[stacks 05KH "maximal nonprincipal ideals are prime"]
#check Ideal.isOka_isPrincipal.isPrime_of_maximal_not

/- Lemma 10.28.11 (2): if every prime ideal of `R` is principal, then every ideal of `R` is
principal. This is the canonical theorem `IsPrincipalIdealRing.of_prime`, already stated in the
stronger generality of commutative semirings; the source phrasing follows by specializing the
resulting `IsPrincipalIdealRing R` instance to an ideal `I`. -/
@[stacks 05KH "all ideals are principal when all prime ideals are principal"]
#check @IsPrincipalIdealRing.of_prime

/- The source-shaped companion returns the result for a chosen ideal without
installing a local `IsPrincipalIdealRing` instance. -/
#check @Ideal.isPrincipal_of_prime

end
