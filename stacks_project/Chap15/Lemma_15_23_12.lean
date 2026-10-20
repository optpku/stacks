/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.ProductInjective
import StacksCheckRecall

/-!
# Lemma 15.23.12

@stack 0AV7

The associated-prime localization criterion is owned by the shared associated-prime leaf.
-/

@[expose] public section

/- Lemma 15.23.12: a module map is injective if it is injective after localization at every prime
or the prime is not associated to the source. -/
@[stacks 0AV7 "Lemma 15.23.12"]
#check @associatedPrimes.injective_of_localized_injective_or_not_mem_associatedPrimes

/- The stronger bundled-index form is also available for consumers that already have associated
prime hypotheses. -/
@[stacks 0AV7 "associated-prime bundled criterion"]
#check @associatedPrimes.injective_of_localized_injective
