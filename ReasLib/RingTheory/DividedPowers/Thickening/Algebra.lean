/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Thickening.Category

@[expose] public section

universe u v

namespace DividedPowerThickening

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))

/-- The `C`-algebra structure on the quotient of a divided-power thickening. -/
@[reducible]
noncomputable def quotientAlgebra
    (T : DividedPowerThickening.CRIS γ f hIC h_pC) :
    Algebra C (T.B ⧸ T.B.ideal) :=
  T.quotient.toAlgebra

/-- The scalar map of the quotient algebra is the thickening quotient map. -/
theorem quotientAlgebra_algebraMap
    (T : DividedPowerThickening.CRIS γ f hIC h_pC) :
    @algebraMap C (T.B ⧸ T.B.ideal) _ _ (quotientAlgebra γ f hIC h_pC T) =
      T.quotient := sorry

end DividedPowerThickening
