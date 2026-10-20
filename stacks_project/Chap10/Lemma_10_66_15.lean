/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Weakly associated primes and localization

@stack 05C9

Lemma 10.66.15 records the two set-level consequences of the canonical
localization map on weakly associated primes.  The reusable statements live in
the ReasLib localization owner; this chapter file is a source-facing recall.
-/

/- Lemma 10.66.15, tag 05C9: weakly associated primes under localization. -/
@[stacks 05C9 "(1)"]
#check @weaklyAssociatedPrimes.Localization.localizedModule_eq_image_comap

@[stacks 05C9 "(2)"]
#check @weaklyAssociatedPrimes.Localization.inter_localization_range_eq
