/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DualNumbers
public import ReasLib.RingTheory.Kaehler.CrossingFamily
public import ReasLib.RingTheory.Kaehler.NodeFamily
import StacksCheckRecall

/-!
# Exercise 111.50.1

Fitting ideals of `Ω[A⁄R]` for three affine families over a field.
-/

@[expose] public section

noncomputable section

open scoped DualNumber FittingIdeal

universe u

/- Exercise 111.50.1 (1): the dual-number Fitting ideal computation. -/
@[stacks 02FC]
#check (DualNumbersOmega.fittingIdeal :
  ∀ (k : Type u) [Field k] (n : ℕ),
    Fit[DualNumbersOmega.coordRing k]_(n)(Ω[DualNumbersOmega.coordRing k⁄ k[ε]]) =
      if n = 0 then Ideal.span {DualNumbersOmega.eps k} else ⊤)

/- Exercise 111.50.1 (2): the crossing-family Fitting ideal computation. -/
@[stacks 02FC]
#check (CrossingFamily.fittingIdeal :
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ),
    Fit[CrossingFamily.coordRing k]_(n)(Ω[CrossingFamily.coordRing k⁄ Polynomial k]) =
      if n = 0 then Ideal.span {CrossingFamily.fittingZeroGenerator k}
      else if n = 1 then
        CrossingFamily.originIdeal k ⊓ CrossingFamily.otherPointIdeal k
      else ⊤)

/- Exercise 111.50.1 (3): the node-family Fitting ideal computation. -/
@[stacks 02FC]
#check (NodeFamily.fittingIdeal :
  ∀ (k : Type u) [Field k] (m n : ℕ),
    Fit[NodeFamily.coordRing k m]_(n)(Ω[NodeFamily.coordRing k m⁄ Polynomial k]) =
      if n = 0 then ⊥
      else if n = 1 then
        (Ideal.span {NodeFamily.x k, NodeFamily.y k}).map
          (Ideal.Quotient.mk (NodeFamily.relationIdeal k m))
      else ⊤)
