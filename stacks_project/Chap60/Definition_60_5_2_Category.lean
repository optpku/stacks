module

public import ReasLib.RingTheory.DividedPowers.Thickening.Category

@[expose] public section

universe u v w

open CategoryTheory

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))

/-! Compatibility surface for the affine divided-power thickening category owner. -/

variable {X Y : DividedPowerThickening p A I γ C f hIC h_pC}

#check (DividedPowerThickening.Hom γ f X Y : Type _)
#check (DividedPowerThickening.CRIS γ f hIC h_pC : Type _)
#check (DividedPowerThickening.Cris γ f hIC h_pC : Type _)
#check (DividedPowerThickening.crisCategory γ f hIC h_pC :
  Category (DividedPowerThickening.CRIS γ f hIC h_pC))
