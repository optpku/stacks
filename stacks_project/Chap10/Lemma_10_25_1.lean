/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Minimal-prime localizations
@stack 00EU

Lemma 10.25.1 (Tag 00EU) is a canonical recall of the reusable
minimal-prime-localization API in `ReasLib.RingTheory.Ideal.MinimalPrime.Localization`.
-/

/- (1) -/
@[stacks 00EU]
#check @IsMinimalPrime.krullDimLE_zero_localizationAtPrime
#check @IsMinimalPrime.isNilpotent_iff_mem_maximalIdeal_localizationAtPrime
#check @minimalPrimes.isNilpotent_of_mem_maximalIdeal_localizationAtPrime

/- (2) -/
@[stacks 00EU]
#check @IsMinimalPrime.isField_localizationAtPrime
#check @minimalPrimes.isField_localizationAtPrime
