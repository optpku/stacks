module

public import Mathlib.Algebra.Module.Torsion.Basic
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated primes of torsion-free modules over domains

For a torsion-free module over a domain, every nonzero element has zero
annihilator.  Thus the exact-annihilator and radical-associated-prime sets both
collapse to the singleton `{⊥}`.  The field case follows from the canonical
torsion-free instance.
-/

@[expose] public section

universe u v

namespace associatedPrimesOfModule

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.IsTorsionFree R M] [Nontrivial M]

/-- The exact-annihilator associated primes of a nontrivial torsion-free module over a domain are
the singleton `{⊥}`. -/
@[stacks 05BX "torsion-free domain exact-associated-prime specialization"]
theorem eq_singleton_bot : associatedPrimesOfModule R M = {⊥} := sorry

end associatedPrimesOfModule

namespace associatedPrimes

variable {R : Type u} [CommSemiring R] [IsDomain R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable [Module.IsTorsionFree R M] [Nontrivial M]

/-- Mathlib's radical-associated primes of a nontrivial torsion-free module over a domain are the
singleton `{⊥}`. -/
@[stacks 05BX "torsion-free domain radical-associated-prime specialization"]
theorem eq_singleton_bot : associatedPrimes R M = {⊥} := sorry

end associatedPrimes
