/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.67.3

@stack 02M7
-/

@[stacks 02M7 "localization of the canonical nowhere-dense submodule"]
#check @Module.embeddedPrimeFreeSubmodule.localized_away_eq

@[stacks 02M7 "localization of the embedded-prime-free quotient"]
#check @Module.embeddedPrimeFreeSubmodule.awayQuotientEquiv
