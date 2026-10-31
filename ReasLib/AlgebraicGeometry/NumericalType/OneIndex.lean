/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Genus
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace NumericalType

/-- A numerical type with one index and constant multiplicity, weight, and component genus. -/
public def oneIndex (multiplicity weight componentGenus : ℕ) (hm : 0 < multiplicity)
    (hw : 0 < weight) : NumericalType :=
  NumericalType.of 1 Nat.zero_lt_one (fun _ => multiplicity) (fun _ => weight)
    (fun _ => componentGenus) (fun _ _ => 0) (fun _ => hm) (fun _ => hw)
    (fun _ _ => rfl) (fun _ _ _ => le_rfl)
    (fun I hI hI_univ => False.elim (hI_univ (Set.Nonempty.eq_univ hI)))
    (fun _ => Finset.sum_eq_zero (fun j hj => zero_mul (multiplicity : ℤ)))
    (fun _ _ => dvd_zero _)

/-- The diagonal intersection of a one-index numerical type is zero. -/
public theorem oneIndex_intersection_self_eq_zero
    (T : NumericalType) (h_n : T.n = 1) (i : Fin T.n) :
    T.intersection i i = 0 := by
  classical
  have hsum := T.rowSum_eq_zero i
  rw [Finset.sum_eq_single i] at hsum
  · have hm : (T.multiplicity i : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (T.multiplicity_pos i))
    exact (mul_eq_zero.mp hsum).resolve_right hm
  · intro j hj hji
    exfalso
    apply hji
    apply Fin.ext
    have hjlt := j.isLt
    have hilt := i.isLt
    omega
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem oneIndex_eq_of_data (T : NumericalType)
    (multiplicity weight componentGenus : ℕ) (hm : 0 < multiplicity) (hw : 0 < weight)
    (hn : T.n = 1)
    (hdata : ∀ i : Fin T.n,
      T.multiplicity i = multiplicity ∧ T.weight i = weight ∧
        T.componentGenus i = componentGenus) :
    T = oneIndex multiplicity weight componentGenus hm hw := by
  have hmul : T.multiplicity = fun _ => multiplicity :=
    funext fun i => (hdata i).1
  have hweight : T.weight = fun _ => weight :=
    funext fun i => (hdata i).2.1
  have hcomp : T.componentGenus = fun _ => componentGenus :=
    funext fun i => (hdata i).2.2
  have hinter : T.intersection = fun _ _ => 0 := by
    funext i j
    have hij : j = i := by
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega
    subst j
    exact oneIndex_intersection_self_eq_zero T hn i
  cases T with
  | mk n npos mul inter w comp mulpos wpos sym off conn row dvd =>
    dsimp only at hn hmul hweight hcomp hinter
    subst n
    subst mul
    subst inter
    subst w
    subst comp
    rfl

private theorem oneIndex_bounded_finite (b : ℕ) :
    Set.Finite {T : NumericalType | T.n = 1 ∧ ∀ i : Fin T.n,
      T.multiplicity i ≤ b ∧ T.weight i ≤ b ∧ T.componentGenus i ≤ b} := by
  let f : Fin (b + 1) × Fin (b + 1) × Fin (b + 1) → NumericalType := fun p =>
    oneIndex (p.1.val + 1) (p.2.1.val + 1) p.2.2.val (Nat.succ_pos _) (Nat.succ_pos _)
  apply (Set.finite_range f).subset
  intro T hT
  rcases hT with ⟨hn, hbound⟩
  let i : Fin T.n := ⟨0, T.n_pos⟩
  obtain ⟨hm, hw, hc⟩ := hbound i
  have hmp := T.multiplicity_pos i
  have hwp := T.weight_pos i
  refine ⟨(⟨T.multiplicity i - 1, by omega⟩,
    ⟨T.weight i - 1, by omega⟩, ⟨T.componentGenus i, by omega⟩), ?_⟩
  dsimp only [f]
  symm
  apply oneIndex_eq_of_data T _ _ _ _ _ hn
  intro j
  have hji : j = i := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  subst j
  exact ⟨by omega, by omega, rfl⟩

/-- The genus of a one-index numerical type is its multiplicity-weighted component-genus expression. -/
public theorem oneIndex_genus_eq
    (T : NumericalType) (h_n : T.n = 1) (i : Fin T.n) :
    T.genus =
      1 + (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
        ((T.componentGenus i : ℤ) - 1) := by
  have hsum_single (f : Fin T.n → ℤ) : ∑ j, f j = f i := by
    rw [Finset.sum_eq_single i]
    · intro j hj hji
      exfalso
      apply hji
      apply Fin.ext
      omega
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  unfold genus
  rw [hsum_single, hsum_single]
  rw [oneIndex_intersection_self_eq_zero T h_n i]
  simp

private theorem oneIndex_zero_data
    (T : NumericalType) (h_n : T.n = 1) (hgenus : T.genus = 0)
    (i : Fin T.n) :
    T.componentGenus i = 0 ∧ T.multiplicity i = 1 ∧ T.weight i = 1 := by
  have hformula := oneIndex_genus_eq T h_n i
  have heq :
      1 + (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.componentGenus i : ℤ) - 1) = 0 := by
    exact hformula.symm.trans hgenus
  have hm : 0 < (T.multiplicity i : ℤ) := by
    exact_mod_cast T.multiplicity_pos i
  have hw : 0 < (T.weight i : ℤ) := by
    exact_mod_cast T.weight_pos i
  have hc : 0 ≤ (T.componentGenus i : ℤ) := by exact_mod_cast Nat.zero_le _
  have hcm : (T.componentGenus i : ℤ) - 1 = -1 := by
    have hle : (T.componentGenus i : ℤ) - 1 ≤ 0 := by
      by_contra hnot
      have hpos : 0 < (T.componentGenus i : ℤ) - 1 := lt_of_not_ge hnot
      have hprod : 0 < (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.componentGenus i : ℤ) - 1) :=
        mul_pos (mul_pos hm hw) hpos
      omega
    have hneg : (T.componentGenus i : ℤ) - 1 < 0 := by
      have hprod : 0 < (T.multiplicity i : ℤ) * (T.weight i : ℤ) := mul_pos hm hw
      by_contra hnot
      have hnonneg : 0 ≤ (T.componentGenus i : ℤ) - 1 := le_of_not_gt hnot
      have hprod' : 0 ≤ (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.componentGenus i : ℤ) - 1) :=
        mul_nonneg (le_of_lt hprod) hnonneg
      omega
    omega
  have hcomp : T.componentGenus i = 0 := by
    exact_mod_cast (show (T.componentGenus i : ℤ) = 0 by omega)
  have hmw : (T.multiplicity i : ℤ) * (T.weight i : ℤ) = 1 := by
    rw [hcm] at heq
    linarith [heq]
  have hm1z : (T.multiplicity i : ℤ) = 1 := by
    have hm1 : 1 ≤ (T.multiplicity i : ℤ) := by omega
    have hw1 : 1 ≤ (T.weight i : ℤ) := by omega
    have hml : (T.multiplicity i : ℤ) ≤
        (T.multiplicity i : ℤ) * (T.weight i : ℤ) := by
      simpa using (mul_le_mul_of_nonneg_left hw1 (le_of_lt hm))
    omega
  have hw1z : (T.weight i : ℤ) = 1 := by
    simpa [hm1z] using hmw
  refine ⟨hcomp, ?_, ?_⟩
  · exact_mod_cast hm1z
  · exact_mod_cast hw1z

/-- A negative-genus one-index numerical type has component genus zero and the corresponding factorization. -/
public theorem oneIndex_negative_classification
    (T : NumericalType) (h_n : T.n = 1) (g : ℤ) (hgenus : T.genus = g)
    (hg : g < 0) (i : Fin T.n) :
    T.componentGenus i = 0 ∧
      (T.multiplicity i : ℤ) * (T.weight i : ℤ) = 1 - g := by
  have hformula := oneIndex_genus_eq T h_n i
  have heq :
      1 + (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.componentGenus i : ℤ) - 1) = g :=
    hformula.symm.trans hgenus
  have hm : 0 < (T.multiplicity i : ℤ) := by
    exact_mod_cast T.multiplicity_pos i
  have hw : 0 < (T.weight i : ℤ) := by
    exact_mod_cast T.weight_pos i
  have hc : 0 ≤ (T.componentGenus i : ℤ) := by
    exact_mod_cast Nat.zero_le _
  have hcomp : T.componentGenus i = 0 := by
    by_contra hne
    have hc1 : 1 ≤ (T.componentGenus i : ℤ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hne)
    have hfactor : 0 ≤ (T.componentGenus i : ℤ) - 1 := by omega
    have hprod : 0 ≤ (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
        ((T.componentGenus i : ℤ) - 1) :=
      mul_nonneg (mul_nonneg (le_of_lt hm) (le_of_lt hw)) hfactor
    linarith
  have hprod : (T.multiplicity i : ℤ) * (T.weight i : ℤ) = 1 - g := by
    rw [show (T.componentGenus i : ℤ) = 0 by exact_mod_cast hcomp] at heq
    linarith [heq]
  exact ⟨hcomp, hprod⟩

/-- For a fixed negative genus, the one-index numerical types form a finite set. -/
public theorem oneIndex_negative_finite (g : ℤ) (hg : g < 0) :
    Set.Finite {T : NumericalType | T.n = 1 ∧ T.genus = g} := by
  apply (oneIndex_bounded_finite (1 - g).toNat).subset
  rintro T ⟨hn, hgenus⟩
  refine ⟨hn, ?_⟩
  intro i
  obtain ⟨hc, hprod⟩ := oneIndex_negative_classification T hn g hgenus hg i
  have hm : 1 ≤ (T.multiplicity i : ℤ) := by
    exact_mod_cast T.multiplicity_pos i
  have hw : 1 ≤ (T.weight i : ℤ) := by
    exact_mod_cast T.weight_pos i
  have hml : (T.multiplicity i : ℤ) ≤
      (T.multiplicity i : ℤ) * (T.weight i : ℤ) := by
    simpa using mul_le_mul_of_nonneg_left hw (by omega)
  have hwl : (T.weight i : ℤ) ≤
      (T.multiplicity i : ℤ) * (T.weight i : ℤ) := by
    simpa using mul_le_mul_of_nonneg_right hm (by omega)
  have hnat : ((1 - g).toNat : ℤ) = 1 - g := Int.toNat_of_nonneg (by omega)
  exact ⟨by omega, by omega, by omega⟩

/-- A genus-zero one-index numerical type has multiplicity one. -/
public theorem oneIndex_zero_multiplicity
    (T : NumericalType) (h_n : T.n = 1) (hgenus : T.genus = 0)
    (i : Fin T.n) :
    T.multiplicity i = 1 := by
  exact (oneIndex_zero_data T h_n hgenus i).2.1

/-- A genus-zero one-index numerical type has weight one. -/
public theorem oneIndex_zero_weight
    (T : NumericalType) (h_n : T.n = 1) (hgenus : T.genus = 0)
    (i : Fin T.n) :
    T.weight i = 1 := by
  exact (oneIndex_zero_data T h_n hgenus i).2.2

/-- A genus-zero one-index numerical type has component genus zero. -/
public theorem oneIndex_zero_componentGenus
    (T : NumericalType) (h_n : T.n = 1) (hgenus : T.genus = 0)
    (i : Fin T.n) :
    T.componentGenus i = 0 := by
  exact (oneIndex_zero_data T h_n hgenus i).1

/-- A genus-one one-index numerical type has component genus one. -/
public theorem oneIndex_one_componentGenus
    (T : NumericalType) (h_n : T.n = 1) (hgenus : T.genus = 1)
    (i : Fin T.n) :
    T.componentGenus i = 1 := by
  have hformula := oneIndex_genus_eq T h_n i
  have heq :
      1 + (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.componentGenus i : ℤ) - 1) = 1 :=
    hformula.symm.trans hgenus
  have hm : 0 < (T.multiplicity i : ℤ) := by
    exact_mod_cast T.multiplicity_pos i
  have hw : 0 < (T.weight i : ℤ) := by
    exact_mod_cast T.weight_pos i
  have hprod : (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
      ((T.componentGenus i : ℤ) - 1) = 0 := by linarith [heq]
  have hfactor : (T.componentGenus i : ℤ) - 1 = 0 := by
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · rcases mul_eq_zero.mp hzero with hmzero | hwzero
      · exact (ne_of_gt hm) hmzero |>.elim
      · exact (ne_of_gt hw) hwzero |>.elim
    · exact hzero
  have hc : (T.componentGenus i : ℤ) = 1 := by linarith [hfactor]
  exact_mod_cast hc

/-- A one-index numerical type of genus greater than one has component genus greater than one and the corresponding factorization. -/
public theorem oneIndex_positive_classification
    (T : NumericalType) (h_n : T.n = 1) (g : ℤ) (hgenus : T.genus = g)
    (hg : 1 < g) (i : Fin T.n) :
    1 < T.componentGenus i ∧
      (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.componentGenus i : ℤ) - 1) = g - 1 := by
  have hformula := oneIndex_genus_eq T h_n i
  have heq :
      1 + (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.componentGenus i : ℤ) - 1) = g :=
    hformula.symm.trans hgenus
  have hm : 0 < (T.multiplicity i : ℤ) := by
    exact_mod_cast T.multiplicity_pos i
  have hw : 0 < (T.weight i : ℤ) := by
    exact_mod_cast T.weight_pos i
  have hfactor_pos : 0 <
      (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
        ((T.componentGenus i : ℤ) - 1) := by
    linarith [heq, hg]
  have hcomp : 1 < T.componentGenus i := by
    have hfactor : 0 < (T.componentGenus i : ℤ) - 1 := by
      by_contra hnot
      have hfactor_nonpos : (T.componentGenus i : ℤ) - 1 ≤ 0 :=
        le_of_not_gt hnot
      have hprod_nonpos :
          (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
            ((T.componentGenus i : ℤ) - 1) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos
          (le_of_lt (mul_pos hm hw)) hfactor_nonpos
      linarith [hfactor_pos, hprod_nonpos]
    have hc : 1 < (T.componentGenus i : ℤ) := by linarith [hfactor]
    exact_mod_cast hc
  refine ⟨hcomp, ?_⟩
  linarith [heq]

/-- For a fixed genus greater than one, the one-index numerical types form a finite set. -/
public theorem oneIndex_positive_finite (g : ℤ) (hg : 1 < g) :
    Set.Finite {T : NumericalType | T.n = 1 ∧ T.genus = g} := by
  apply (oneIndex_bounded_finite g.toNat).subset
  rintro T ⟨hn, hgenus⟩
  refine ⟨hn, ?_⟩
  intro i
  obtain ⟨hc, hprod⟩ := oneIndex_positive_classification T hn g hgenus hg i
  have hm : 1 ≤ (T.multiplicity i : ℤ) := by
    exact_mod_cast T.multiplicity_pos i
  have hw : 1 ≤ (T.weight i : ℤ) := by
    exact_mod_cast T.weight_pos i
  have hc1 : 1 ≤ (T.componentGenus i : ℤ) - 1 := by
    have : (1 : ℤ) < (T.componentGenus i : ℤ) := by exact_mod_cast hc
    omega
  have hmw : 1 ≤ (T.multiplicity i : ℤ) * (T.weight i : ℤ) := by
    nlinarith [mul_nonneg (show 0 ≤ (T.multiplicity i : ℤ) - 1 by omega)
      (show 0 ≤ (T.weight i : ℤ) - 1 by omega)]
  have hml : (T.multiplicity i : ℤ) ≤
      (T.multiplicity i : ℤ) * (T.weight i : ℤ) := by
    simpa using mul_le_mul_of_nonneg_left hw (by omega)
  have hwl : (T.weight i : ℤ) ≤
      (T.multiplicity i : ℤ) * (T.weight i : ℤ) := by
    simpa using mul_le_mul_of_nonneg_right hm (by omega)
  have hmwle : (T.multiplicity i : ℤ) * (T.weight i : ℤ) ≤ g - 1 := by
    have hle := mul_le_mul_of_nonneg_left hc1 (show
      0 ≤ (T.multiplicity i : ℤ) * (T.weight i : ℤ) by omega)
    simpa [hprod] using hle
  have hcle : (T.componentGenus i : ℤ) - 1 ≤ g - 1 := by
    have hle := mul_le_mul_of_nonneg_right hmw (show
      0 ≤ (T.componentGenus i : ℤ) - 1 by omega)
    simpa [hprod] using hle
  have hnat : (g.toNat : ℤ) = g := Int.toNat_of_nonneg (by omega)
  exact ⟨by omega, by omega, by omega⟩

/-- The genus of the canonical one-index numerical type is the prescribed factorization expression. -/
public theorem genus_oneIndex (multiplicity weight componentGenus : ℕ) (hm : 0 < multiplicity)
    (hw : 0 < weight) :
    (oneIndex multiplicity weight componentGenus hm hw).genus =
      1 + (multiplicity : ℤ) * (weight : ℤ) * ((componentGenus : ℤ) - 1) := by
  exact oneIndex_genus_eq
    (oneIndex multiplicity weight componentGenus hm hw) rfl (0 : Fin 1)

/-- Equality with a canonical one-index numerical type is characterized by its indexed data. -/
public theorem eq_oneIndex_iff (T : NumericalType) (multiplicity weight componentGenus : ℕ)
    (hm : 0 < multiplicity) (hw : 0 < weight) :
    T = oneIndex multiplicity weight componentGenus hm hw ↔
      T.n = 1 ∧ ∀ i : Fin T.n,
        T.multiplicity i = multiplicity ∧ T.weight i = weight ∧
          T.componentGenus i = componentGenus := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
  · rintro ⟨hn, hdata⟩
    exact oneIndex_eq_of_data T multiplicity weight componentGenus hm hw hn hdata

end NumericalType
