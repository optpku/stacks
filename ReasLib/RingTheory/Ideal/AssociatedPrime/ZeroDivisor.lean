module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Zero divisors and exact associated primes

This leaf gives the zero-divisor characterization at the exact-annihilator
owner.  The radical-associated version remains Mathlib's canonical theorem;
the comparison isomorphism is hidden behind this symmetric companion.
-/

universe u v

namespace associatedPrimesOfModule

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The union of exact associated primes is the set of elements that act as zero divisors on
the module. -/
@[stacks 00LD]
theorem biUnion_eq_zero_divisors :
    ⋃ p ∈ associatedPrimesOfModule R M, p =
      {r : R | ∃ x : M, x ≠ 0 ∧ r • x = 0} := sorry

/-- The same union is the complement of the elements acting regularly on the module.  This
companion mirrors the weak-association API and is convenient when the downstream statement is
formulated with `IsSMulRegular`. -/
@[stacks 00LD "regular-element form"]
theorem biUnion_eq_compl_regular :
    ⋃ p ∈ associatedPrimesOfModule R M, p =
      {r : R | IsSMulRegular M r}ᶜ := sorry

end associatedPrimesOfModule
