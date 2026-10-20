/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Reflexive
import StacksCheckRecall

/-!
# Lemma 15.23.13

This file recalls the local depth and associated-prime criterion for a module map to be an
isomorphism.

@stack 0AV8
-/

@[expose] public section

/- Lemma 15.23.13: a map from a finite module is an isomorphism when it is locally an isomorphism
or the localized source has depth at least two away from the target's associated primes. -/
@[stacks 0AV8 "Lemma 15.23.13"]
#check @LinearMap.bijective_of_localized_bijective_or_depth_ge_two_and_not_mem_associatedPrimes
