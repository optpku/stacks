/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType.HeightOne
import StacksCheckRecall

/-!
# Height-One Primes in a Finite Fraction-Field Extension

@stack 02MA
-/

/- Lemma 10.113.2 (1): finiteness of primes over a height-one prime. -/
@[stacks 02MA "(1)"]
#check @Ideal.finite_primesOver_of_fractionRing_finite

/- Lemma 10.113.2 (2): primes above the source prime have height one. -/
@[stacks 02MA "(2)"]
#check @Ideal.height_eq_one_of_primesOver_of_fractionRing_finite
