/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Valuation.Noetherian
import StacksCheckRecall

/-!
# Lemma 10.50.18

@stack 00II
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

/- Lemma 10.50.18 (Tag 00II): canonical recall of the shared valuation-ring classification. -/
@[stacks 00II]
#check @ValuationRing.isNoetherianRing_iff_isDiscreteValuationRing_or_isField

end
