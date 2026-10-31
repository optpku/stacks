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
      IsLocalization.mk' S (γ.dpow n a) (s ^ n) := by
  classical
  have hx : IsLocalization.mk' S a s ∈ I.map (algebraMap R S) :=
    (IsLocalization.mem_map_algebraMap_iff M S).2
      ⟨⟨⟨a, ha⟩, s⟩, IsLocalization.mk'_spec S a s⟩
  let rep := Classical.choose ((IsLocalization.mem_map_algebraMap_iff M S).mp hx)
  have hrep : IsLocalization.mk' S a s = IsLocalization.mk' S (rep.1 : R) rep.2 :=
    IsLocalization.eq_mk'_iff_mul_eq.2 (Classical.choose_spec
      ((IsLocalization.mem_map_algebraMap_iff M S).mp hx))
  obtain ⟨c, hc⟩ := IsLocalization.eq.mp hrep
  simp only [← mul_assoc] at hc
  have hd := congrArg (γ.dpow n) hc
  simp only [γ.dpow_mul ha, γ.dpow_mul rep.1.2, mul_pow] at hd
  simp only [localizationDpow, dif_pos hx]
  apply IsLocalization.eq.mpr
  refine ⟨c ^ n, ?_⟩
  simpa only [SubmonoidClass.coe_pow, mul_assoc] using hd.symm

/-- Divided powers extended to a localization by the explicit fraction formula.
Only the algebraic laws remain proof obligations. -/
noncomputable def localization : DividedPowers (I.map (algebraMap R S)) where
  dpow := localizationDpow γ M S
  dpow_null := fun hx ↦ localizationDpow_of_not_mem γ M S _ _ hx
  dpow_zero := by
    intro x hx
    obtain ⟨⟨a, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
    rw [← IsLocalization.eq_mk'_iff_mul_eq] at hs
    rw [hs, localizationDpow_mk' γ M S 0 a a.2 s, γ.dpow_zero a.2]
    simp [IsLocalization.mk'_one]
  dpow_one := by
    intro x hx
    obtain ⟨⟨a, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
    rw [← IsLocalization.eq_mk'_iff_mul_eq] at hs
    rw [hs, localizationDpow_mk' γ M S 1 a a.2 s, γ.dpow_one a.2, pow_one]
  dpow_mem := by
    intro n x hn hx
    obtain ⟨⟨a, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
    rw [← IsLocalization.eq_mk'_iff_mul_eq] at hs
    rw [hs, localizationDpow_mk' γ M S n a a.2 s]
    exact (IsLocalization.mem_map_algebraMap_iff M S).2
      ⟨⟨⟨_, γ.dpow_mem hn a.2⟩, s ^ n⟩, IsLocalization.mk'_spec S _ _⟩
  dpow_add := by
    intro n x y hx hy
    obtain ⟨⟨a, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
    obtain ⟨⟨b, t⟩, ht⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hy
    rw [← IsLocalization.eq_mk'_iff_mul_eq] at hs ht
    let a' : R := (a : R) * t
    let b' : R := (b : R) * s
    let u : M := s * t
    have ha' : a' ∈ I := I.mul_mem_right _ a.2
    have hb' : b' ∈ I := I.mul_mem_right _ b.2
    have hx' : x = IsLocalization.mk' S a' u := by
      rw [hs]
      exact (IsLocalization.mk'_cancel (S := S) (a : R) s t).symm
    have hy' : y = IsLocalization.mk' S b' u := by
      rw [ht]
      simpa only [u, b', mul_comm s t] using
        (IsLocalization.mk'_cancel (S := S) (b : R) t s).symm
    have hadd : IsLocalization.mk' S (a' + b') u =
        IsLocalization.mk' S a' u + IsLocalization.mk' S b' u := by
      rw [IsLocalization.mk'_eq_mul_mk'_one (a' + b') u, map_add, add_mul,
        ← IsLocalization.mk'_eq_mul_mk'_one a' u,
        ← IsLocalization.mk'_eq_mul_mk'_one b' u]
    rw [hx', hy', ← hadd, localizationDpow_mk' γ M S n (a' + b') (I.add_mem ha' hb') u]
    simp only [localizationDpow_mk' γ M S _ a' ha' u,
      localizationDpow_mk' γ M S _ b' hb' u]
    rw [γ.dpow_add ha' hb', IsLocalization.mk'_eq_mul_mk'_one, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← IsLocalization.mk'_mul, ← pow_add, Finset.mem_antidiagonal.mp hk]
    exact (IsLocalization.mk'_eq_mul_mk'_one _ _).symm
  dpow_mul := by
    intro n b x hx
    obtain ⟨r, t, rfl⟩ := IsLocalization.exists_mk'_eq M b
    obtain ⟨⟨a, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
    rw [← IsLocalization.eq_mk'_iff_mul_eq] at hs
    rw [hs, ← IsLocalization.mk'_mul,
      localizationDpow_mk' γ M S n (r * a) (I.mul_mem_left _ a.2) (t * s),
      γ.dpow_mul a.2, localizationDpow_mk' γ M S n a a.2 s,
      ← IsLocalization.mk'_pow, ← IsLocalization.mk'_mul, mul_pow]
  mul_dpow := by
    intro m n x hx
    obtain ⟨⟨a, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
    rw [← IsLocalization.eq_mk'_iff_mul_eq] at hs
    rw [hs, localizationDpow_mk' γ M S m a a.2 s,
      localizationDpow_mk' γ M S n a a.2 s,
      localizationDpow_mk' γ M S (m + n) a a.2 s,
      ← IsLocalization.mk'_mul, ← pow_add, γ.mul_dpow a.2,
      ← IsLocalization.mul_mk'_eq_mk'_of_mul, map_natCast]
  dpow_comp := by
    intro m n x hn hx
    obtain ⟨⟨a, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
    rw [← IsLocalization.eq_mk'_iff_mul_eq] at hs
    rw [hs, localizationDpow_mk' γ M S n a a.2 s,
      localizationDpow_mk' γ M S m (γ.dpow n a) (γ.dpow_mem hn a.2) (s ^ n),
      localizationDpow_mk' γ M S (m * n) a a.2 s,
      γ.dpow_comp hn a.2, ← pow_mul, Nat.mul_comm n m,
      ← IsLocalization.mul_mk'_eq_mk'_of_mul, map_natCast]

/-- The canonical localization map preserves divided powers. -/
theorem localization_isDPMorphism :
    IsDPMorphism γ (localization γ M S) (algebraMap R S) := by
  refine ⟨le_rfl, ?_⟩
  intro n a ha
  change localizationDpow γ M S n (algebraMap R S a) = _
  rw [← IsLocalization.mk'_one (M := M), localizationDpow_mk' γ M S n a ha 1]
  simp only [one_pow, IsLocalization.mk'_one]

/-- An extension along the localization map has the same explicit operations. -/
theorem localization_unique (δ : DividedPowers (I.map (algebraMap R S)))
    (hδ : IsDPMorphism γ δ (algebraMap R S)) : δ = localization γ M S := by
  apply DividedPowers.ext
  intro n x hx
  obtain ⟨⟨a, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
  rw [← IsLocalization.eq_mk'_iff_mul_eq] at hs
  change δ.dpow n x = localizationDpow γ M S n x
  rw [hs, localizationDpow_mk' γ M S n a a.2 s,
    IsLocalization.mk'_eq_mul_mk'_one, mul_comm (algebraMap R S (a : R)),
    δ.dpow_mul (Ideal.mem_map_of_mem _ a.2), hδ.dpow_comp a a.2,
    IsLocalization.mk'_eq_mul_mk'_one (γ.dpow n a) (s ^ n),
    ← IsLocalization.mk'_pow, one_pow, mul_comm]

end DividedPowers
