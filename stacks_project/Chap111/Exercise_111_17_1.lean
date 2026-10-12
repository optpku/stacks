/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.HahnSeries.LexProd
import StacksCheckRecall

/-!
# Exercise 111.17.1

A commutative ring with finitely many prime ideals and Krull dimension strictly
greater than one. The constructed example is the rank-two lexicographic Hahn
valuation ring `lexProdInteger k`.
-/

universe u

/- Exercise 111.17.1: the rank-two lexicographic Hahn valuation integer ring
over any field has finitely many prime ideals and dimension strictly greater
than one. -/
@[stacks 076H] #check
  (HahnSeries.instFinitePrimeSpectrum_lexProdInteger :
    ∀ (k : Type u) [Field k], Finite (PrimeSpectrum (HahnSeries.lexProdInteger k)))

#check (HahnSeries.one_lt_ringKrullDim_lexProdInteger :
  ∀ (k : Type u) [Field k], 1 < ringKrullDim (HahnSeries.lexProdInteger k))

#check (HahnSeries.not_isNoetherianRing_lexProdInteger :
  ∀ (k : Type u) [Field k], ¬ IsNoetherianRing (HahnSeries.lexProdInteger k))

/- Companion: the valuation integer of a valued field is a valuation ring. -/
#check ValuationRing.instValuationRingInteger

/- Companion: a Noetherian ring with finite prime spectrum has Krull dimension at most one. -/
#check Ring.krullDim_le_one_of_finitePrimeSpectrum
