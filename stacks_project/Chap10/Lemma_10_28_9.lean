/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.Maximal.Disjoint
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.28.9: an ideal maximal among the ideals disjoint from a multiplicative subset is prime.
The ReasLib companion uses the source's bundled `Maximal` hypothesis; Mathlib owns the lower-level
form with disjointness and strict maximality split apart.

@stack 05KF
-/

@[stacks 05KF "maximal-disjoint packaging"]
#check @Ideal.isPrime_of_maximal_disjoint

@[stacks 05KF "canonical split-hypothesis form"]
#check @Ideal.isPrime_of_maximally_disjoint
