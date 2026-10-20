/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.CrystallineCompletion
public import ReasLib.CategoryTheory.Pro.CrystallineCompletion
import StacksCheckRecall

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

/- Remark 60.5.4 (1): the completed crystalline category consists of complete
 divided-power rings over A with a surjection to C whose kernel is the divided-power ideal. -/
@[stacks 07KH] #check (CompletedCrisObject p A I γ C f hIC h_pC : Type (max u (v + 1)))

/- Remark 60.5.4 (2): the full subcategory on objects with nilpotent p is equivalent to Cris. -/
@[stacks 07KH] #check (CompletedCris.equivalenceCris γ f hIC h_pC :
  (CompletedCris.toCrisFunctor γ f hIC h_pC).IsEquivalence)

/- Remark 60.5.4 (3): stable prime-power quotients form an inverse system in Cris. -/
@[stacks 07KH] #check (pAdicQuotientSystem γ f hIC h_pC :
  ∀ _ : CompletedCrisObject p A I γ C f hIC h_pC,
    ℕᵒᵖ ⥤ DividedPowerThickening.Cris γ f hIC h_pC)

/- Remark 60.5.4 (4): each completed crystalline object is the limit of its prime-power quotients. -/
@[stacks 07KH] #check (isLimit_pAdicQuotientCone γ f hIC h_pC :
  ∀ X : CompletedCrisObject p A I γ C f hIC h_pC,
    IsLimit (pAdicQuotientCone γ f hIC h_pC X))

/- Remark 60.5.4 (5): the prime-power quotient system realizes a functor to pro-objects of Cris. -/
@[stacks 07KH] #check (toProCris γ f hIC h_pC :
  CompletedCrisObject p A I γ C f hIC h_pC ⥤ Pro (DividedPowerThickening.Cris γ f hIC h_pC))

/- Remark 60.5.4 (6): the functor to pro-objects of Cris is full. -/
@[stacks 07KH] #check (toProCris.full γ f hIC h_pC : (toProCris γ f hIC h_pC).Full)

/- Remark 60.5.4 (7): the functor to pro-objects of Cris is faithful. -/
@[stacks 07KH] #check (toProCris.faithful γ f hIC h_pC : (toProCris γ f hIC h_pC).Faithful)
