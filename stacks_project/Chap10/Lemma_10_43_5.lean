/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.Reduced
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.43.5 (Tag 034N) is a canonical recall of
`Algebra.TensorProduct.isReduced_of_isGeometricallyReduced_right`: if `S` is geometrically
reduced over a field `k` and `R` is a reduced `k`-algebra, then `R ⊗[k] S` is reduced.

The reusable tensor-product theorem belongs to `ReasLib`, rather than to this chapter-specific
presentation.

@stack 034N
-/

@[stacks 034N]
#check @Algebra.TensorProduct.isReduced_of_isGeometricallyReduced_right

@[stacks 034N "tensor-product reducedness companion"]
#check @Algebra.TensorProduct.isReduced_of_isGeometricallyReduced_right_of
