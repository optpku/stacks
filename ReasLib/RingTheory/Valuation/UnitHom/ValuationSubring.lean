/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Valuation.UnitHom.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic.CrossRefAttribute

/-!
# Valuation subrings from homomorphisms on units

@stack 00IG

This leaf gives the valuation-subring, maximal-ideal, and unit-group views of a bundled
`AddValuation.UnitHom`.
-/

@[expose] public section

noncomputable section

universe u v

open Valuation

namespace AddValuation.UnitHom

variable {K : Type u} [Field K]
variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- The valuation subring induced by a bundled nonarchimedean homomorphism on units. -/
@[stacks 00IG "valuation subring induced by a homomorphism on units"]
abbrev valuationSubring (u : AddValuation.UnitHom K Γ) : ValuationSubring K :=
  u.toAddValuation.toValuation.valuationSubring

variable (u : AddValuation.UnitHom K Γ)

/-- Membership in the induced valuation subring is nonnegativity of the induced value. -/
@[stacks 00IG "membership in the induced valuation subring"]
theorem mem_valuationSubring_iff (x : K) :
    x ∈ u.valuationSubring ↔ 0 ≤ u.toAddValuation x := by
  rw [valuationSubring, Valuation.mem_valuationSubring_iff]
  change
    Multiplicative.ofAdd (OrderDual.toDual (u.toAddValuation x)) ≤
      Multiplicative.ofAdd (0 : (WithTop u.ValueGroup)ᵒᵈ) ↔ 0 ≤ u.toAddValuation x
  rw [Multiplicative.ofAdd_le]
  rfl

/-- Away from zero, valuation-subring membership is nonnegativity of the original unit value. -/
@[stacks 00IG "nonzero membership in the induced valuation subring"]
theorem mem_valuationSubring_iff_of_ne {x : K} (hx : x ≠ 0) :
    x ∈ u.valuationSubring ↔ 0 ≤ Multiplicative.toAdd (u (Units.mk0 x hx)) := by
  rw [u.mem_valuationSubring_iff, u.toAddValuation_apply_of_ne hx]
  exact u.rangeRestrict_nonneg_iff (Units.mk0 x hx)

/-- The carrier formula for the valuation subring, expressed using the original unit map. -/
@[stacks 00IG "zero-or-nonnegative valuation-subring membership"]
theorem mem_valuationSubring_iff_eq_zero_or_nonneg (x : K) :
    x ∈ u.valuationSubring ↔
      x = 0 ∨ ∀ hx : x ≠ 0, 0 ≤ Multiplicative.toAdd (u (Units.mk0 x hx)) := by
  constructor
  · intro hxA
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr fun hx' ↦ (u.mem_valuationSubring_iff_of_ne hx').mp hxA
  · rintro (rfl | hx)
    · rw [u.mem_valuationSubring_iff]
      simp
    · by_cases hx0 : x = 0
      · rw [hx0, u.mem_valuationSubring_iff]
        simp
      · exact (u.mem_valuationSubring_iff_of_ne hx0).mpr (hx hx0)

/-- Maximal-ideal membership is strict positivity of the induced value. -/
@[stacks 00IG "maximal ideal of the induced valuation subring"]
theorem mem_maximalIdeal_iff {a : u.valuationSubring} :
    a ∈ IsLocalRing.maximalIdeal u.valuationSubring ↔ 0 < u.toAddValuation a := by
  change
    a ∈ IsLocalRing.maximalIdeal u.toAddValuation.toValuation.valuationSubring ↔
      0 < u.toAddValuation a
  rw [Valuation.mem_maximalIdeal_iff]
  change
    Multiplicative.ofAdd (OrderDual.toDual (u.toAddValuation a)) <
      Multiplicative.ofAdd (0 : (WithTop u.ValueGroup)ᵒᵈ) ↔ 0 < u.toAddValuation a
  rw [Multiplicative.ofAdd_lt]
  rfl

/-- Away from zero, maximal-ideal membership is positivity of the original unit value. -/
@[stacks 00IG "nonzero membership in the induced maximal ideal"]
theorem mem_maximalIdeal_iff_of_ne {a : u.valuationSubring} (ha : (a : K) ≠ 0) :
    a ∈ IsLocalRing.maximalIdeal u.valuationSubring ↔
      0 < Multiplicative.toAdd (u (Units.mk0 (a : K) ha)) := by
  rw [u.mem_maximalIdeal_iff, u.toAddValuation_apply_of_ne ha]
  exact u.rangeRestrict_pos_iff (Units.mk0 (a : K) ha)

/-- The maximal-ideal formula expressed directly using the original unit map. -/
@[stacks 00IG "zero-or-positive maximal-ideal membership"]
theorem mem_maximalIdeal_iff_eq_zero_or_pos {a : u.valuationSubring} :
    a ∈ IsLocalRing.maximalIdeal u.valuationSubring ↔
      (a : K) = 0 ∨ ∀ ha : (a : K) ≠ 0,
        0 < Multiplicative.toAdd (u (Units.mk0 (a : K) ha)) := by
  constructor
  · intro ha
    by_cases h0 : (a : K) = 0
    · exact Or.inl h0
    · exact Or.inr fun ha' ↦ (u.mem_maximalIdeal_iff_of_ne ha').mp ha
  · rintro (h0 | ha)
    · have : a = 0 := Subtype.ext h0
      cases this
      simp
    · by_cases h0 : (a : K) = 0
      · have : a = 0 := Subtype.ext h0
        cases this
        simp
      · exact (u.mem_maximalIdeal_iff_of_ne h0).mpr (ha h0)

/-- Additive view of membership in the unit group of the induced valuation subring. -/
@[stacks 00IG "zero-valued units of the induced valuation subring"]
theorem mem_unitGroup_iff_toAdd_eq_zero (x : Kˣ) :
    x ∈ u.valuationSubring.unitGroup ↔ Multiplicative.toAdd (u x) = 0 := by
  rw [show x ∈ u.valuationSubring.unitGroup ↔ u.toAddValuation x = 0 by
    simpa [valuationSubring, AddValuation.toValuation_apply] using
      Valuation.mem_unitGroup_iff K u.toAddValuation.toValuation x]
  rw [u.toAddValuation_apply_unit]
  simpa [Units.mk0_val] using u.rangeRestrict_eq_zero_iff x

/-- Units of the induced valuation subring are the kernel of the original unit homomorphism. -/
@[simp, stacks 00IG "unit group of the induced valuation subring"]
theorem mem_unitGroup_iff (x : Kˣ) : x ∈ u.valuationSubring.unitGroup ↔ u x = 1 := by
  rw [u.mem_unitGroup_iff_toAdd_eq_zero]
  exact toAdd_eq_zero

/-- The unit group of the induced valuation subring as the kernel of the unit homomorphism. -/
@[simp, stacks 00IG "unit group as the kernel of the unit homomorphism"]
theorem unitGroup_eq_ker : u.valuationSubring.unitGroup = u.toMonoidHom.ker := by
  ext x
  rw [u.mem_unitGroup_iff, MonoidHom.mem_ker]
  rfl

end AddValuation.UnitHom
