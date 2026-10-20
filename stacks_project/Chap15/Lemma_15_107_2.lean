/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.Unibranch.Henselization.Normalization
import StacksCheckRecall

/-!
# Normalization and Henselization

This file records Lemma 15.107.2, Stacks `0C24`, through the shared prime-geometry API of the
normalization base change to a Henselization.

@stack 0C24
-/

@[expose] public section

-- The source ring `(A')^h = A' ⊗[A] A^h` and its two canonical maps.
@[stacks 0C24 "Lemma 15.107.2, normalization base change"]
#check @Unibranch.Henselization.normalizationBaseChange

#check @Unibranch.Henselization.normalizationMap
#check @Unibranch.Henselization.henselizationMap

-- Lemma 15.107.2 (1): the left map is bijective on maximal ideals.
@[stacks 0C24 "Lemma 15.107.2 (1)"]
#check @Unibranch.Henselization.maximalIdeals_bijOn

-- Lemma 15.107.2 (2): the right map is bijective on minimal primes.
@[stacks 0C24 "Lemma 15.107.2 (2)"]
#check @Unibranch.Henselization.minimalPrimes_bijOn

-- Lemma 15.107.2 (3): every minimal prime lies in a unique maximal ideal.
@[stacks 0C24 "Lemma 15.107.2 (3)"]
#check @Unibranch.Henselization.minimalPrime_existsUnique_maximalIdeal

-- Lemma 15.107.2 (4): every maximal ideal contains a unique minimal prime.
@[stacks 0C24 "Lemma 15.107.2 (4)"]
#check @Unibranch.Henselization.maximalIdeal_existsUnique_minimalPrime
