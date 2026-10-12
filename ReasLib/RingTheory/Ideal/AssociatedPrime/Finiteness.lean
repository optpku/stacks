/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finiteness of exact associated primes

The exact-annihilator associated primes of a finite module over a Noetherian ring form a finite
set. A Noetherian ring with infinite maximal spectrum also has a non-zero-divisor that is not a
unit.
-/

universe u v

namespace associatedPrimesOfModule

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The exact-annihilator associated-prime set of a finite module over a Noetherian ring is
finite. -/
@[stacks 00LC]
theorem finite : (associatedPrimesOfModule R M).Finite := sorry

end associatedPrimesOfModule

namespace nonZeroDivisors

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A Noetherian ring with infinitely many maximal ideals has a non-zero-divisor that is not a
unit.  The infinite maximal spectrum is the precise reusable hypothesis behind the finite-type
application; no dimension or base field is needed here. -/
@[stacks 0GEC "infinite maximal spectrum form"]
theorem exists_nonunit_of_infinite_maximalSpectrum [Infinite (MaximalSpectrum R)] :
    ∃ f : R, f ∈ nonZeroDivisors R ∧ ¬ IsUnit f := sorry

end nonZeroDivisors
