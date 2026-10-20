module

public import ReasLib.RingTheory.Henselian.Pair.Basic
import StacksCheckRecall

/-!
# Basic properties of pair Henselization

This file recalls the three clauses of Lemma 15.12.2 from the reusable pair-Henselization API.

@stack 0AGU
-/

@[expose] public section

-- Lemma 15.12.2 (1): `A → A^h` is flat.
@[stacks 0AGU "Lemma 15.12.2 (1)"]
#check @RingPairCat.toHenselization_flat

-- Lemma 15.12.2 (2): `I^h = I A^h`.
@[stacks 0AGU "Lemma 15.12.2 (2)"]
#check @RingPairCat.henselizationIdeal_eq_map

-- Lemma 15.12.2 (3): `A / I^n → A^h / (I^h)^n` is bijective for every `n`.
@[stacks 0AGU "Lemma 15.12.2 (3)"]
#check @RingPairCat.quotientPowToHenselization_bijective
