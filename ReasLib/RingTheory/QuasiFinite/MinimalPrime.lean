/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finiteness near a minimal prime

This leaf records the finite-type criterion that turns a finite set of primes
over a minimal base prime into a finite morphism on a standard open
neighborhood.

@stack 02ML
-/

universe u v

namespace Algebra.FiniteType

/-- Lemma 10.122.11 (02ML): if `R -> S` is of finite type, `p` is a minimal
prime of `R`, and only finitely many primes of `S` lie over `p`, then the map is
finite after localizing away from an element outside `p`. -/
@[stacks 02ML]
theorem exists_away_finite_of_finite_primesOver_minimalPrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    (hfinite : Finite (p.asIdeal.primesOver S)) :
    ∃ g : R, g ∉ p.asIdeal ∧
      (Localization.awayMapₐ (Algebra.ofId R S) g).Finite := sorry

end Algebra.FiniteType
