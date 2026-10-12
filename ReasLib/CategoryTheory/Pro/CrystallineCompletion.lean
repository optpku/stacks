/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.CrystallineCompletion
public import ReasLib.CategoryTheory.Pro.Presentation

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open DividedPowers

universe u v

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))

/-- The pro-object functor realized by the prime-power quotients of completed crystalline objects. -/
noncomputable def toProCris :
    CompletedCrisObject p A I γ C f hIC h_pC ⥤
      Pro (DividedPowerThickening.Cris γ f hIC h_pC) where
  obj X := (Pro.lim.{_, v} ℕᵒᵖ).obj (pAdicQuotientSystem γ f hIC h_pC X)
  map u := (Pro.lim.{_, v} ℕᵒᵖ).map (pAdicQuotientSystemMap γ f hIC h_pC u)
  map_id := sorry
  map_comp := sorry

/-- The object mapping of `toProCris` is the pro-object of the `p`-adic inverse system. -/
theorem toProCris_obj (X : CompletedCrisObject p A I γ C f hIC h_pC) :
    (toProCris γ f hIC h_pC).obj X =
      (Pro.lim.{_, v} ℕᵒᵖ).obj (pAdicQuotientSystem γ f hIC h_pC X) := sorry

/-- The prime-power pro-object functor on completed crystalline objects is full. -/
instance toProCris.full : (toProCris γ f hIC h_pC).Full := sorry

/-- The prime-power pro-object functor on completed crystalline objects is faithful. -/
instance toProCris.faithful : (toProCris γ f hIC h_pC).Faithful := sorry
