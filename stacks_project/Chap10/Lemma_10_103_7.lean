/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.AssociatedPrime
import StacksCheckRecall

@[expose] public section

/-!
# Associated primes of Cohen--Macaulay modules

@stack 0BUS

Associated primes of a Cohen--Macaulay module have the full support dimension and are minimal in
the support. In particular, a Cohen--Macaulay module has no embedded associated primes.
-/

open PrimeSpectrum

universe u v

namespace Module.CohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]

/- Lemma 10.103.7 (1): the quotient by an associated prime has the full
support dimension of a Cohen--Macaulay module. -/
@[stacks 0BUS "(1)"]
#check @Module.CohenMacaulay.quotientDim_eq_supportDim_of_associatedPrime

/- Lemma 10.103.7 (2): an associated prime of a Cohen--Macaulay module is a
minimal point of its support. -/
@[stacks 0BUS "(2)"]
#check @Module.CohenMacaulay.minimal_support_of_associatedPrime

/- Lemma 10.103.7 (3): a Cohen--Macaulay module has no embedded associated
primes. -/
@[stacks 0BUS "(3)"]
#check @Module.CohenMacaulay.embeddedAssociatedPrimes_eq_empty

end Module.CohenMacaulay
