/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.Unibranch.StrictHenselization.Normalization
import StacksCheckRecall

/-!
# Normalization after strict Henselization

This file recalls Lemma 15.107.4 from the reusable normalization and strict-Henselization API.

@stack 0C25
-/

@[expose] public section

-- Lemma 15.107.4 (1): normalization residue fields are algebraic over the closed-point field.
@[stacks 0C25 "Lemma 15.107.4 (1)"]
#check @Unibranch.StrictHenselization.residueField_isAlgebraic

-- Lemma 15.107.4 (2): embeddings into an algebraic closure classify the maximal-point fiber.
@[stacks 0C25 "Lemma 15.107.4 (2), classifier"]
#check @Unibranch.StrictHenselization.fiberPoint

@[stacks 0C25 "Lemma 15.107.4 (2), equivalence"]
#check @Unibranch.StrictHenselization.fiberEquiv

-- Lemma 15.107.4 (3): the right structural map is bijective on minimal primes.
@[stacks 0C25 "Lemma 15.107.4 (3)"]
#check @Unibranch.StrictHenselization.minimalPrimes_bijOn

-- Lemma 15.107.4 (4): each minimal prime lies in a unique maximal ideal.
@[stacks 0C25 "Lemma 15.107.4 (4)"]
#check @Unibranch.StrictHenselization.minimalPrime_existsUnique_maximalIdeal

-- Lemma 15.107.4 (5): each maximal ideal contains a unique minimal prime.
@[stacks 0C25 "Lemma 15.107.4 (5)"]
#check @Unibranch.StrictHenselization.maximalIdeal_existsUnique_minimalPrime
