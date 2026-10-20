/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Lean.Parser.Command
public import ReasLib.FieldTheory.PurelyInseparable.PerfectClosure
import StacksCheckRecall

/-!
# Definition 10.45.5

@stack 046X
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped PerfectClosure

section

variable (k : Type u) [Field k]

/-
Definition 10.45.5: the perfect closure `k^{perf}` of `k` is the canonical intermediate field
`perfectClosure k (AlgebraicClosure k)` inside a chosen algebraic closure.
-/
@[stacks 046X]
#check kᵖᵉʳᶠ

end

/- Companion recall: `perfectClosure k E` is the owner-level relative perfect closure attached to
any field extension `E/k`, and `k^{perf}` is its specialization to `E = AlgebraicClosure k`.
-/
@[stacks 046X "relative perfect closure companion"]
#check @perfectClosure
