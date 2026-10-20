/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Thickening.Algebra
public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.Algebra.Category.Ring.Under.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace DividedPowerThickening

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {I : Ideal A} (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type v} [CommRing C] (f : A →+* C)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (h_pC : IsNilpotent (p : C))

/-- The quotient-ring assignment from affine divided-power thickenings to the
under-category of commutative `C`-algebras. -/
noncomputable def crystallineCAlgebraFunctor :
    CRIS γ f hIC h_pC ⥤ Under (CommRingCat.of C) where
  obj T := Under.mk (CommRingCat.ofHom T.quotient)
  map φ := Under.homMk
    (CommRingCat.ofHom (DividedPowerRing.quotientMap φ.map)) (sorry : _)
  map_id := sorry
  map_comp := sorry

/-- The category of affine divided-power thickenings has finite products. -/
instance cris_hasFiniteProducts :
    HasFiniteProducts (CRIS γ f hIC h_pC) := sorry

/-- The category of affine divided-power thickenings has finite nonempty colimits. -/
instance cris_hasFiniteNonemptyColimits :
    HasFiniteNonemptyColimits (CRIS γ f hIC h_pC) := sorry

/-- The quotient-ring assignment preserves finite nonempty colimits. -/
instance crystallineCAlgebraFunctor_preservesFiniteNonemptyColimits :
    PreservesFiniteNonemptyColimits (crystallineCAlgebraFunctor γ f hIC h_pC) := sorry

/-- The full subcategory of crystalline thickenings has finite nonempty colimits. -/
instance cris_hasFiniteNonemptyColimits_subcategory :
    HasFiniteNonemptyColimits (Cris γ f hIC h_pC) := sorry

/-- The inclusion of crystalline thickenings preserves finite nonempty colimits. -/
instance cris_inclusion_preservesFiniteNonemptyColimits :
    PreservesFiniteNonemptyColimits (isCrisObject γ f hIC h_pC).ι := sorry

end DividedPowerThickening
