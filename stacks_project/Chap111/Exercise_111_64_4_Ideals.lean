/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DualNumberPair.Ideals
public import ReasLib.RingTheory.DualNumberPair.Presentation
import StacksCheckRecall

@[expose] public section

noncomputable section

/- Exercise 111.64.4 (Ideals): the ideals of `DualNumberPair (ZMod 2)` are
exactly `⊥`, `Ideal.span {ε₁}`, `Ideal.span {ε₂}`, `Ideal.span {ε₁ + ε₂}`,
`Ideal.span {ε₁, ε₂}`, and `⊤`. -/
@[stacks 0GRW] #check
  (DualNumberPair.ideals_eq :
    (Set.univ : Set (Ideal (DualNumberPair (ZMod 2)))) =
      {⊥, Ideal.span {(DualNumberPair.eps1 : DualNumberPair (ZMod 2))},
        Ideal.span {DualNumberPair.eps2},
        Ideal.span {DualNumberPair.eps1 + DualNumberPair.eps2},
        Ideal.span {DualNumberPair.eps1, DualNumberPair.eps2}, ⊤})
