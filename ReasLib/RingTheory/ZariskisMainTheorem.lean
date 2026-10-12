/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.ZariskisMainTheorem

@[expose] public section

universe u v

namespace Algebra.QuasiFiniteAt

/-- A finite-type algebra that is quasi-finite at a prime contains an integral
element outside that prime whose powers make every element integral. -/
theorem exists_integral_notMem_forall_isIntegral_pow_mul
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (prime : Ideal S) [prime.IsPrime]
    [Algebra.QuasiFiniteAt R prime] :
    ∃ element : S, element ∉ prime ∧ IsIntegral R element ∧
      ∀ value : S, ∃ exponent : ℕ, IsIntegral R (element ^ exponent * value) := sorry

end Algebra.QuasiFiniteAt
