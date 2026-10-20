/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Kaehler.TensorProduct
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.131.12

@stack 00RV
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.131.12: for ring maps `R → R'` and `R → S`, with `S' = R' ⊗[R] S`, the canonical map
identifies the base change `R' ⊗[R] Ω[S⁄R]` with `Ω[S'⁄R']`. This is exactly the standard
base-change isomorphism for Kähler differentials. -/
@[stacks 00RV "tensor-product base change for Kähler differentials"]
#check @KaehlerDifferential.tensorKaehlerEquivBase
