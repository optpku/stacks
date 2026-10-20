/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.66.6
@stack 0589

The three comparison inclusions are neutral associated-prime infrastructure
owned by `ReasLib.RingTheory.Ideal.AssociatedPrime.Weak`.
-/

/- Lemma 10.66.6 (Stacks 0589): exact-annihilator associated primes and
mathlib associated primes are weakly associated, and weakly associated primes
belong to module support. -/
@[stacks 0589]
#check @associatedPrimesOfModule.subset_weaklyAssociatedPrimes
@[stacks 0589]
#check @associatedPrimes.subset_weaklyAssociatedPrimes
@[stacks 0589]
#check @weaklyAssociatedPrimes.subset_support

/- Pointwise comparison and support views. -/
#check @IsAssociatedPrime.isWeaklyAssociatedToModule
#check @Ideal.IsAssociatedToModule.isWeaklyAssociatedToModule
#check @Ideal.IsWeaklyAssociatedToModule.mem_support
