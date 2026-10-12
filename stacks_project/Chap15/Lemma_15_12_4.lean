/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Pair.Completion
import StacksCheckRecall

/-!
# Henselization and adic completion of a Noetherian pair

This file recalls the clauses of Lemma 15.12.4 from the reusable pair-Henselization completion
API.

@stack 0AGV
-/

@[expose] public section

-- Lemma 15.12.4 (1): `A^∧ → (A^h)^∧` is an isomorphism.
@[stacks 0AGV "Lemma 15.12.4 (1)"]
#check @RingPairCat.adicCompletion_map_toHenselization_bijective

-- Lemma 15.12.4 (2): `A^h` is Noetherian.
@[stacks 0AGV "Lemma 15.12.4 (2)"]
#check @RingPairCat.henselizationRing_isNoetherian

-- Lemma 15.12.4 (3): `A → A^h` is flat.
@[stacks 0AGV "Lemma 15.12.4 (3)"]
#check @RingPairCat.toHenselization_flat

-- Lemma 15.12.4 (4): `A^h → A^∧` is flat.
@[stacks 0AGV "Lemma 15.12.4 (4)"]
#check @RingPairCat.henselizationToAdicCompletion_flat

-- Lemma 15.12.4 (5): `A^h → A^∧` is faithfully flat.
@[stacks 0AGV "Lemma 15.12.4 (5)"]
#check @RingPairCat.henselizationToAdicCompletion_faithfullyFlat

-- The shared owner exposes the concrete comparison maps used by all five clauses.
@[stacks 0AGV "map from pair Henselization to adic completion"]
#check @RingPairCat.henselizationToAdicCompletion

#check @RingPairCat.adicCompletionMapToHenselization
