/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Restriction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.63.11

@stack 05BW
-/

/- Lemma 10.63.11 (Stacks 05BW): contraction of exact associated primes along
a ring map preserves exact association after restriction of scalars. -/
@[stacks 05BW] #check @associatedPrimesOfModule.Restriction.image_comap_subset
