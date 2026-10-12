/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

@[expose] public section

/-!
# Embedded Associated Primes

The embedded associated primes of a module are its associated primes that are
not minimal among the associated primes. The corresponding notion for a ring
uses the ring as a module over itself.
-/

universe u v

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- The embedded associated primes of the `R`-module `M` are its associated
primes that are not minimal among its associated primes. -/
@[stacks 02M5]
def embeddedAssociatedPrimes : Set (Ideal R) :=
  { p |
    p ∈ associatedPrimesOfModule R M ∧
      ¬ Minimal (· ∈ associatedPrimesOfModule R M) p }

/-- Membership in `embeddedAssociatedPrimes R M` is association together with
nonminimality among the associated primes of `M`. -/
@[simp]
theorem mem_embeddedAssociatedPrimes_iff (p : Ideal R) :
    p ∈ embeddedAssociatedPrimes R M ↔
      p ∈ associatedPrimesOfModule R M ∧
        ¬ Minimal (· ∈ associatedPrimesOfModule R M) p := sorry

/-- Over a Noetherian ring, embedded associated primes can be read using
mathlib's radical-based `associatedPrimes R M`. -/
theorem mem_embeddedAssociatedPrimes_iff_mem_associatedPrimes [IsNoetherianRing R]
    (p : Ideal R) :
    p ∈ embeddedAssociatedPrimes R M ↔
      p ∈ associatedPrimes R M ∧ ¬ Minimal (· ∈ associatedPrimes R M) p := sorry

/-- Over a Noetherian ring, a module has no embedded associated primes exactly
when all of its associated primes are minimal among its associated primes. -/
theorem embeddedAssociatedPrimes_eq_empty_iff [IsNoetherianRing R] :
    embeddedAssociatedPrimes R M = ∅ ↔
      ∀ p ∈ associatedPrimes R M, Minimal (· ∈ associatedPrimes R M) p := sorry

end

section

variable (R : Type u) [CommRing R]

/-- The embedded primes of `R` are the embedded associated primes of `R`
viewed as a module over itself. -/
@[stacks 02M5]
abbrev embeddedPrimes : Set (Ideal R) :=
  embeddedAssociatedPrimes R R

/-- Membership in `embeddedPrimes R` is membership in the corresponding
module-level embedded-associated-prime set. -/
@[simp]
theorem mem_embeddedPrimes_iff (p : Ideal R) :
    p ∈ embeddedPrimes R ↔ p ∈ embeddedAssociatedPrimes R R := sorry

/-- Over a Noetherian ring, an embedded prime is an associated prime that is
not minimal among the associated primes of the ring. -/
@[simp]
theorem mem_embeddedPrimes_iff_mem_associatedPrimes [IsNoetherianRing R]
    (p : Ideal R) :
    p ∈ embeddedPrimes R ↔
      p ∈ associatedPrimes R R ∧ ¬ Minimal (· ∈ associatedPrimes R R) p := sorry

/-- Over a Noetherian ring, a ring has no embedded primes exactly when all of
its associated primes are minimal among its associated primes. -/
theorem embeddedPrimes_eq_empty_iff [IsNoetherianRing R] :
    embeddedPrimes R = ∅ ↔
      ∀ p ∈ associatedPrimes R R, Minimal (· ∈ associatedPrimes R R) p := sorry

end

namespace embeddedAssociatedPrimes

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- If the finite `R`-module `M` has no embedded associated primes, then
`R ⧸ Module.annihilator R M` has no embedded primes. -/
@[stacks 02M8]
theorem quotient_annihilator_eq_empty
    (hM : embeddedAssociatedPrimes R M = ∅) :
    embeddedPrimes (R ⧸ Module.annihilator R M) = ∅ := sorry

end embeddedAssociatedPrimes
