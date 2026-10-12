/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Smooth.AtPrime

@[expose] public section

/-!
# Locality of Smoothness at a Prime

This leaf relates the Stacks-style principal-open predicate
`Algebra.SmoothAtPrime` to global smoothness without imposing finite
presentation as an ambient assumption.

@stack 00TC
-/

universe u v

namespace Algebra.Smooth

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.137.12, tag `00TC`: an `R`-algebra is smooth precisely when it
is smooth on a principal-open neighbourhood of every target prime. -/
@[stacks 00TC "smoothness is local at target primes"]
theorem iff_forall_smoothAtPrime :
    Algebra.Smooth R S ↔ ∀ q : PrimeSpectrum S, Algebra.SmoothAtPrime R S q := sorry

end Algebra.Smooth
