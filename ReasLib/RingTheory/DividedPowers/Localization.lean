/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.RingTheory.Localization.Ideal

@[expose] public section

namespace DividedPowers

universe u v

variable {R : Type u} [CommRing R] {I : Ideal R}
variable (γ : DividedPowers I) (M : Submonoid R)
variable (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The divided-power operation on a localized ideal. For an ideal numerator
`a` and an invertible denominator `s`, its value at `a / s` is `γₙ(a) / sⁿ`.
The representative is selected from Mathlib's proved ideal-membership lemma,
not from an assumed existence of a divided-power structure. -/
noncomputable def localizationDpow (n : ℕ) (x : S) : S :=
  open scoped Classical in
  if hx : x ∈ I.map (algebraMap R S) then
    let rep := Classical.choose ((IsLocalization.mem_map_algebraMap_iff M S).mp hx)
    IsLocalization.mk' S (γ.dpow n rep.1) (rep.2 ^ n)
  else 0

/-- Outside the localized ideal the total operation is zero. -/
theorem localizationDpow_of_not_mem (n : ℕ) (x : S)
    (hx : x ∉ I.map (algebraMap R S)) : localizationDpow γ M S n x = 0 := by
  classical
  simp only [localizationDpow, dif_neg hx]

/-- The fraction formula is independent of the selected ideal representative. -/
theorem localizationDpow_mk' (n : ℕ) (a : R) (ha : a ∈ I) (s : M) :
    localizationDpow γ M S n (IsLocalization.mk' S a s) =
      IsLocalization.mk' S (γ.dpow n a) (s ^ n) := sorry

/-- Divided powers extended to a localization by the explicit fraction formula.
Only the algebraic laws remain proof obligations. -/
noncomputable def localization : DividedPowers (I.map (algebraMap R S)) where
  dpow := localizationDpow γ M S
  dpow_null := fun hx ↦ localizationDpow_of_not_mem γ M S _ _ hx
  dpow_zero := sorry
  dpow_one := sorry
  dpow_mem := sorry
  dpow_add := sorry
  dpow_mul := sorry
  mul_dpow := sorry
  dpow_comp := sorry

/-- The canonical localization map preserves divided powers. -/
theorem localization_isDPMorphism :
    IsDPMorphism γ (localization γ M S) (algebraMap R S) := sorry

/-- An extension along the localization map has the same explicit operations. -/
theorem localization_unique (δ : DividedPowers (I.map (algebraMap R S)))
    (hδ : IsDPMorphism γ δ (algebraMap R S)) : δ = localization γ M S := sorry

end DividedPowers
