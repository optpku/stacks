/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.Equivalence
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace NumericalType

private theorem symmetric_sum_sub_diagonal_even {ι : Type*}
    (s : Finset ι) (f : ι → ι → ℤ) (hsymm : ∀ i j, f i j = f j i) :
    Even ((∑ i ∈ s, ∑ j ∈ s, f i j) - ∑ i ∈ s, f i i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + ∑ i ∈ s, f a i, ?_⟩
    simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
    have hswap : ∑ i ∈ s, f i a = ∑ i ∈ s, f a i :=
      Finset.sum_congr rfl (fun i _ => hsymm i a)
    rw [hswap]
    omega

/-- The multiplicity-weighted sum of the diagonal intersection numbers of a
numerical type is even. -/
public theorem multiplicityDiagonalSum_even (T : NumericalType) :
    Even (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) := by
  have htotal : (∑ i, ∑ j, (T.multiplicity i : ℤ) * T.intersection i j *
      (T.multiplicity j : ℤ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, T.rowSum_eq_zero, mul_zero]
  -- The off-diagonal terms in the symmetric quadratic sum occur in equal pairs.
  have hquadratic := symmetric_sum_sub_diagonal_even Finset.univ
    (fun i j => (T.multiplicity i : ℤ) * T.intersection i j *
      (T.multiplicity j : ℤ)) (fun i j => by rw [T.symmetric i j]; ring)
  have hdiag : Even (∑ i, (T.multiplicity i : ℤ) * T.intersection i i *
      (T.multiplicity i : ℤ)) := by
    simpa only [htotal, zero_sub, even_neg] using hquadratic
  -- Replacing each squared multiplicity by the multiplicity changes the sum by an even integer.
  have hdiff : Even (∑ i, ((T.multiplicity i : ℤ) * T.intersection i i *
      (T.multiplicity i : ℤ) - (T.multiplicity i : ℤ) * T.intersection i i)) := by
    rw [even_iff_two_dvd]
    apply Finset.dvd_sum
    intro i _
    have hi := (Int.even_mul_pred_self (T.multiplicity i : ℤ)).mul_left
      (T.intersection i i)
    convert even_iff_two_dvd.mp hi using 1
    ring
  rw [Finset.sum_sub_distrib] at hdiff
  obtain ⟨a, ha⟩ := hdiag
  obtain ⟨b, hb⟩ := hdiff
  exact ⟨a - b, by omega⟩

private theorem genusExpression_expand (T : NumericalType) :
    1 + ∑ i, (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
          (T.intersection i i : ℚ) / 2) =
      1 + ((∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
        ((T.componentGenus i : ℤ) - 1) : ℤ) : ℚ) -
      ((∑ i, (T.multiplicity i : ℤ) * T.intersection i i : ℤ) : ℚ) / 2 := by
  push_cast
  calc
    _ = 1 + ∑ i, ((T.multiplicity i : ℚ) * (T.weight i : ℚ) *
        ((T.componentGenus i : ℚ) - 1) -
        (T.multiplicity i : ℚ) * (T.intersection i i : ℚ) / 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      ring

/-- The rational genus expression associated to a numerical type is the cast
of an integer. -/
public theorem genusExpression_isInteger (T : NumericalType) :
    ∃ g : ℤ, (g : ℚ) =
      1 + ∑ i, (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
          (T.intersection i i : ℚ) / 2) := by
  obtain ⟨k, hk⟩ := multiplicityDiagonalSum_even T
  refine ⟨1 + ∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
    ((T.componentGenus i : ℤ) - 1) - k, ?_⟩
  rw [genusExpression_expand, hk]
  push_cast
  ring

/-- The genus of a numerical type, computed as an integer using the even total
diagonal contribution. -/
public def genus (T : NumericalType) : ℤ :=
  1 + ∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
      ((T.componentGenus i : ℤ) - 1) -
    (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) / 2

/-- The integer formula computing the genus of a numerical type. -/
public theorem genus_def (T : NumericalType) :
    T.genus =
      1 + ∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.componentGenus i : ℤ) - 1) -
        (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) / 2 := rfl

/-- Casting the genus to `ℚ` gives the rational genus expression. -/
public theorem genus_cast (T : NumericalType) :
    (T.genus : ℚ) =
      1 + ∑ i, (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
          (T.intersection i i : ℚ) / 2) := by
  obtain ⟨k, hk⟩ := multiplicityDiagonalSum_even T
  have hdiv : (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) / 2 = k := by
    omega
  rw [genus, hdiv, genusExpression_expand, hk]
  push_cast
  ring

/-- An integer is the genus exactly when its cast is the rational genus expression. -/
public theorem genus_eq_iff (T : NumericalType) (g : ℤ) :
    T.genus = g ↔
      (g : ℚ) = 1 + ∑ i, (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
          (T.intersection i i : ℚ) / 2) := by
  constructor
  · intro h
    rw [← h]
    exact genus_cast T
  · intro h
    exact_mod_cast (genus_cast T).trans h.symm

namespace IsRelabeling

/-- Relabeling a numerical type preserves its genus. -/
public theorem genus_eq {T T' : NumericalType} {e : Fin T.n ≃ Fin T'.n}
    (h : IsRelabeling T T' e) : T.genus = T'.genus := by
  have hmain : (∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
      ((T.componentGenus i : ℤ) - 1)) =
      ∑ i, (T'.multiplicity i : ℤ) * (T'.weight i : ℤ) *
        ((T'.componentGenus i : ℤ) - 1) := by
    calc
      _ = ∑ i, (T'.multiplicity (e i) : ℤ) * (T'.weight (e i) : ℤ) *
          ((T'.componentGenus (e i) : ℤ) - 1) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [h.multiplicity_eq, h.weight_eq, h.componentGenus_eq]
      _ = _ := e.sum_comp (fun i => (T'.multiplicity i : ℤ) * (T'.weight i : ℤ) *
        ((T'.componentGenus i : ℤ) - 1))
  have hdiag : (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) =
      ∑ i, (T'.multiplicity i : ℤ) * T'.intersection i i := by
    calc
      _ = ∑ i, (T'.multiplicity (e i) : ℤ) * T'.intersection (e i) (e i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [h.multiplicity_eq, h.intersection_eq]
      _ = _ := e.sum_comp (fun i => (T'.multiplicity i : ℤ) * T'.intersection i i)
  rw [genus_def, genus_def, hmain, hdiag]

end IsRelabeling

end NumericalType
