/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Thickening

@[expose] public section

universe u v w

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))

/-! Compatibility surface for the affine divided-power thickening owner. -/

variable {X Y : DividedPowerThickening p A I γ C f hIC h_pC}

#check (DividedPowerThickening p A I γ C f hIC h_pC : Type _)
#check (DividedPowerThickening.of γ f hIC h_pC :
  ∀ (B : DividedPowerRing.{w})
    (base : DividedPowers.DPMorphism γ B.dividedPowers)
    (p_nilpotent : IsNilpotent (p : B))
    (quotient : C →+* (B ⧸ B.ideal)),
    (Ideal.Quotient.mk B.ideal).comp base.toRingHom = quotient.comp f →
      DividedPowerThickening p A I γ C f hIC h_pC)
#check (DividedPowerThickening.spec γ f hIC h_pC :
  ∀ T : DividedPowerThickening p A I γ C f hIC h_pC,
    IsNilpotent (p : T.B) ∧
      (Ideal.Quotient.mk T.B.ideal).comp T.base.toRingHom = T.quotient.comp f)
