module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Empty sets of associated primes

This file owns the Noetherian criterion saying that associated primes detect the
zero module.  It keeps Mathlib's radical-based `associatedPrimes` as the canonical
general interface and gives `associatedPrimesOfModule` the corresponding
exact-annihilator criteria.

## API design

The canonical theorem is stated at the `CommSemiring`/`AddCommMonoid` level supported
by Mathlib.  The exact-annihilator companions stay at `CommRing`/`AddCommGroup`, which
is the minimal layer of `associatedPrimesOfModule`.  The iff is oriented set-first as
`eq_empty_iff_subsingleton`, following the `Set.eq_empty_iff_*` family; its explicit
`Subsingleton M` right-hand side lets callers use a proof without installing a local
instance.  Separate class-driven empty and nonempty lemmas remain convenient when
those structures are already ambient.
-/

@[expose] public section

universe u v

namespace associatedPrimes

variable {R : Type u} [CommSemiring R] [IsNoetherianRing R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Over a Noetherian commutative semiring, the associated-prime set is empty exactly when the
module is subsingleton. -/
@[stacks 0587 "associated primes detect the zero module"]
theorem eq_empty_iff_subsingleton :
    associatedPrimes R M = ∅ ↔ Subsingleton M := sorry

end associatedPrimes

namespace associatedPrimesOfModule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A subsingleton module has no exact-annihilator associated primes.  No Noetherian hypothesis
is needed in this direction. -/
@[stacks 0587 "exact associated primes of the zero module"]
theorem eq_empty_of_subsingleton [Subsingleton M] :
    associatedPrimesOfModule R M = ∅ := sorry

variable [IsNoetherianRing R]

/-- A nontrivial module over a Noetherian ring has an exact-annihilator associated prime. -/
@[stacks 0587 "existence of an exact associated prime"]
theorem nonempty [Nontrivial M] :
    (associatedPrimesOfModule R M).Nonempty := sorry

/-- The exact-annihilator associated-prime set of a module over a Noetherian ring is empty
exactly when the module is subsingleton. -/
@[stacks 0587 "exact associated primes detect the zero module"]
theorem eq_empty_iff_subsingleton :
    associatedPrimesOfModule R M = ∅ ↔ Subsingleton M := sorry

end associatedPrimesOfModule
