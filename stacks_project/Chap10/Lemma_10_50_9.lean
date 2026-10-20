/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Valuation.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.50.9

@stack 088Y
-/

/- Lemma 10.50.9 [stacks 088Y]: canonical recall of localization preserving
the valuation-ring structure. -/
@[stacks 088Y "localization"]
#check @ValuationRing.localization
@[stacks 088Y "localization instance"]
#check @ValuationRing.instLocalization
@[stacks 088Y "localization at a prime"]
#check @ValuationRing.localizationAtPrime
@[stacks 088Y "quotient by a prime ideal"]
#check @ValuationRing.quotient
