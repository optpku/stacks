/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

universe u

namespace Ideal

/-- An ideal not contained in either of two prime ideals is not contained in their union. -/
theorem not_subset_union {A : Type u} [CommRing A] (I q1 q2 : Ideal A) [q1.IsPrime] [q2.IsPrime]
    (h1 : ¬ I ≤ q1) (h2 : ¬ I ≤ q2) :
    ¬ ((I : Set A) ⊆ (q1 : Set A) ∪ (q2 : Set A)) := sorry

/-- An ideal avoiding two prime ideals contains an element outside both primes. -/
theorem exists_mem_notMem {A : Type u} [CommRing A] (I q1 q2 : Ideal A) [q1.IsPrime] [q2.IsPrime]
    (h1 : ¬ I ≤ q1) (h2 : ¬ I ≤ q2) :
    ∃ x ∈ I, x ∉ q1 ∧ x ∉ q2 := sorry

end Ideal
