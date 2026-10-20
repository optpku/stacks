/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded.Quotient
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.67.2

@stack 02M6

The source existence statement is represented by a canonical submodule and four independent
properties, so downstream users need not unpack a conjunction.
-/

@[stacks 02M6 "canonical nowhere-dense submodule"]
#check @Module.embeddedPrimeFreeSubmodule

@[stacks 02M6 "maximal nowhere-dense submodule"]
#check @Module.embeddedPrimeFreeSubmodule.isMaximal_nowhereDense

@[stacks 02M6 "support of the embedded-prime-free quotient"]
#check @Module.embeddedPrimeFreeSubmodule.support_quotient

@[stacks 02M6 "embedded associated primes of the quotient"]
#check @Module.embeddedPrimeFreeSubmodule.embeddedAssociatedPrimes_quotient

@[stacks 02M6 "localized quotient map"]
#check @Module.embeddedPrimeFreeSubmodule.localized_quotientMap_bijective
