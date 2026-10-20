/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap60.Definition_60_5_2
import ReasLib.RingTheory.DividedPowers.Thickening.Algebra

@[expose] public section

universe u v

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))

/- 60.5.2.1: the affine crystalline object assignment sends
`T : CRIS(C/A)` to the `C`-algebra structure on the quotient `T.B ⧸ T.B.ideal`.
-/
@[stacks 07KF] #check
  (DividedPowerThickening.quotientAlgebra γ f hIC h_pC :
    ∀ T : DividedPowerThickening.CRIS γ f hIC h_pC,
      Algebra C (T.B ⧸ T.B.ideal))
