/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.5.5

@stack 0560
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.5.5: let `R → S` be a ring map and let `M` be an `S`-module. If `M` is finite as an
`R`-module via restriction of scalars, then `M` is finite as an `S`-module. This is exactly the
canonical theorem `Module.Finite.of_restrictScalars_finite`. -/
@[stacks 0560]
#check @Module.Finite.of_restrictScalars_finite
