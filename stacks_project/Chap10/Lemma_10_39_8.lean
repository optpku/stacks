/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.39.8

@stack 00HJ
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.39.8 (Stacks tag `00HJ`): for a faithfully flat ring map `R → R'`, an `R`-module `M`
is flat over `R` if and only if its canonical base change `R' ⊗[R] M` is flat over `R'`. This is
exactly the canonical faithfully flat descent theorem `Module.Flat.iff_flat_tensorProduct`; the
textbook notation `M' = R' ⊗[R] M` is just the usual name for this base-changed module. -/
@[stacks 00HJ]
#check @Module.Flat.iff_flat_tensorProduct
