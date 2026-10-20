/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.DividedPowers.Thickening.FiniteColimits

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))

/- Lemma 60.5.3 (1): in Situation 60.5.1, `CRIS(C/A)` has finite products. -/
@[stacks 07HN] #check
  (DividedPowerThickening.cris_hasFiniteProducts γ f hIC h_pC :
    HasFiniteProducts (DividedPowerThickening.CRIS γ f hIC h_pC))

/- Lemma 60.5.3 (2): `CRIS(C/A)` has all finite nonempty colimits. -/
@[stacks 07HN] #check
  (DividedPowerThickening.cris_hasFiniteNonemptyColimits γ f hIC h_pC :
    HasFiniteNonemptyColimits (DividedPowerThickening.CRIS γ f hIC h_pC))

/- Lemma 60.5.3 (3): the affine crystalline assignment (60.5.2.1) commutes
with finite nonempty colimits. -/
@[stacks 07HN] #check
  (DividedPowerThickening.crystallineCAlgebraFunctor_preservesFiniteNonemptyColimits
    γ f hIC h_pC :
    PreservesFiniteNonemptyColimits
      (DividedPowerThickening.crystallineCAlgebraFunctor γ f hIC h_pC))

/- Lemma 60.5.3 (4): `Cris(C/A)` has all finite nonempty colimits. -/
@[stacks 07HN] #check
  (DividedPowerThickening.cris_hasFiniteNonemptyColimits_subcategory γ f hIC h_pC :
    HasFiniteNonemptyColimits (DividedPowerThickening.Cris γ f hIC h_pC))

/- Lemma 60.5.3 (5): the inclusion `Cris(C/A) ⥤ CRIS(C/A)` commutes with
finite nonempty colimits. -/
@[stacks 07HN] #check
  (DividedPowerThickening.cris_inclusion_preservesFiniteNonemptyColimits
    γ f hIC h_pC :
    PreservesFiniteNonemptyColimits
      (DividedPowerThickening.isCrisObject γ f hIC h_pC).ι)
