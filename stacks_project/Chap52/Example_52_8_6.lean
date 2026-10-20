/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPowerSeries.PadicNode
import StacksCheckRecall

/- Example 52.8.6: for the p-adic node `M = A/(xy - p)`, the image of
`H⁰_(p,x)(M/pⁿM) ⟶ H⁰_(p,x)(M/pM)` in `M/pM = A/(p,xy)` is the ideal `(yⁿ)`. -/
@[stacks 0EFM] #check (PadicNode.image_h0Transition_eq_yPow :
  ∀ (p n : ℕ) [Fact p.Prime] (hn : 1 ≤ n),
    Set.range (PadicNode.h0TransitionAmbient p n hn) =
      (Ideal.span ({PadicNode.yClass p ^ n} : Set (PadicNode.Stage p 1)) :
        Set (PadicNode.Stage p 1)))
