/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideals Maximal Among Those Disjoint From a Submonoid

Mathlib owns the prime-ideal criterion with disjointness and strict-maximality as separate
hypotheses. This leaf provides the bundled `Maximal` form used by source statements and later
specializations.

@stack 05KF
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- Lemma 10.28.9: an ideal maximal among the ideals disjoint from a submonoid is prime. -/
@[stacks 05KF]
theorem isPrime_of_maximal_disjoint (S : Submonoid R) {I : Ideal R}
    (hI : Maximal (fun J : Ideal R => Disjoint (J : Set R) (S : Set R)) I) :
    I.IsPrime := sorry

end Ideal
