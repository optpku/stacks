/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.LinearAlgebra.Matrix.MulVecOrder
import StacksCheckRecall

open scoped BigOperators

universe u

namespace Matrix

/- 55.2.2.1: the displayed equation is a hypothesis in the surrounding lemma; this
check records the equivalence that rewrites that condition, rather than proving it
unconditionally. -/
@[stacks 0C5W]
#check (Matrix.neg_diag_dominates_iff_mulVec_nonpos :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (m : ι → ℝ),
    (∀ i, -A i i * m i ≥ ∑ j ∈ Finset.univ.erase i, A i j * m j) ↔
      A *ᵥ m ≤ 0)

#check (Matrix.neg_diag_eq_sum_erase_iff_mulVec_eq_zero :
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (m : ι → ℝ) (i : ι),
    (-A i i * m i = ∑ j ∈ Finset.univ.erase i, A i j * m j) ↔
      (A *ᵥ m) i = 0)

end Matrix
