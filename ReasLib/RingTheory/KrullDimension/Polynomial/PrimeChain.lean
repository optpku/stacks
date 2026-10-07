module

public import ReasLib.RingTheory.Catenary.PrimeSpectrum
public import ReasLib.RingTheory.KrullDimension.Polynomial
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Maximal prime chains in polynomial algebras

@stack 00OR

This leaf identifies the common length of maximal prime chains in an interval
of the spectrum of a finite polynomial algebra over a field.
-/

universe u

namespace MvPolynomial

/-- Lemma 10.114.3 (00OR): if `p <= q` are primes in a polynomial algebra in
finitely many variables over a field, then a maximal chain in `[p, q]` has one
more element than the difference of the two prime heights. -/
@[stacks 00OR]
theorem maximalPrimeChain_encard_eq_height_sub_add_one
    {k : Type u} [Field k] {n : ℕ}
    (p q : PrimeSpectrum (MvPolynomial (Fin n) k)) (hpq : p ≤ q)
    {s : Set (Set.Icc p q)} (hs : IsMaxChain (· ≤ ·) s) :
    s.encard = ENat.toNat (q.asIdeal.height - p.asIdeal.height) + 1 := sorry

end MvPolynomial
