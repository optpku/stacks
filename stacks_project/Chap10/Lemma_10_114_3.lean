/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.Polynomial.PrimeChain
import StacksCheckRecall

/-!
# Maximal Prime Chains in Polynomial Algebras

@stack 00OR
-/

/- Lemma 10.114.3: maximal prime chains between `p <= q` in a finite
polynomial algebra over a field have height-difference length. -/
@[stacks 00OR]
#check @MvPolynomial.maximalPrimeChain_encard_eq_height_sub_add_one

/- The reusable catenary owner gives equality of maximal chain lengths; the
statement above specializes that owner and identifies the common length with
the prime-height difference. -/
#check @IsCatenaryRing.maximalPrimeChainsHaveSameLength
