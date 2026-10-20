/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.DividedPowers.CrystallineBase
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A : Type u) [CommRing A]
variable (I : Ideal A) (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (C : Type v) [CommRing C]
variable (f : A →+* C)

/- Situation 60.5.1: `p` is prime, `(A, I, γ)` is a divided-power ring with `A` a
`ℤ` localized at `(p)`-algebra, and `f : A →+* C` annihilates `I` while `p` is
nilpotent in `C`. -/
@[stacks 07MD] #check (DividedPowers.IsCrystallineBase p γ f : Prop)
