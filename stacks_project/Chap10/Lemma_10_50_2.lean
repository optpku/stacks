/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Valuation.LocalSubring
import StacksCheckRecall

/-!
# Dominating local subrings by valuation subrings

@stack 00IA
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (K : Type u) [Field K]

/- Lemma 10.50.2: let `K` be a field and let `A ⊂ K` be a local subring. Then there exists a
valuation ring with fraction field `K` dominating `A`. The primary domain is valuation theory for
local subrings of a field. This file is a `bridge/view` recall of the core owner theorem
`LocalSubring.exists_le_valuationSubring`: the primitive data are `K` and `A : LocalSubring K`,
while the domination relation `A ≤ B.toLocalSubring` is derived from the owner abstractions
`LocalSubring K` and `ValuationSubring K`. -/
@[stacks 00IA]
#check @LocalSubring.exists_le_valuationSubring

end
