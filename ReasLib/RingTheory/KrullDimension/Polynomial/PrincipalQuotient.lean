/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section

universe u

namespace MvPolynomial

/-- The principal quotient by a nonzero nonunit polynomial in two variables over a field has
Krull dimension one. -/
theorem ringKrullDim_quotient_span_singleton_eq_one_of_ne_zero_not_isUnit
    {k : Type u} [Field k] {f : MvPolynomial (Fin 2) k} (h0 : f ≠ 0)
    (hu : ¬ IsUnit f) :
    ringKrullDim (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}) = 1 := by
  have hdim : ringKrullDim (MvPolynomial (Fin 2) k) = 2 := by
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  have hupper := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (R := MvPolynomial (Fin 2) k) (mem_nonZeroDivisors_iff_ne_zero.mpr h0)
  rw [hdim] at hupper
  obtain ⟨M, hM, hle⟩ := (Ideal.span ({f} : Set (MvPolynomial (Fin 2) k))).exists_le_maximal
    (by simpa [Ideal.span_singleton_eq_top] using hu)
  let e : MvPolynomial (Fin 2) k ≃+* Polynomial (Polynomial k) :=
    ((finSuccEquiv k 1).trans (Polynomial.mapAlgEquiv (uniqueAlgEquiv k (Fin 1)))).toRingEquiv
  let M' := M.map e
  have : M'.IsMaximal := Ideal.map_isMaximal_of_equiv e
  have : (M'.under (Polynomial k)).IsMaximal :=
    Polynomial.isMaximal_comap_C_of_isJacobsonRing M'
  have hMheight : M.height = 2 := by
    rw [← e.height_map M, Polynomial.height_eq_height_add_one (M'.under (Polynomial k)) M',
      IsPrincipalIdealRing.height_eq_one_of_isMaximal _ (Polynomial.not_isField k)]
    rfl
  have hlower := @Ideal.height_le_ringKrullDim_quotient_add_one
    (MvPolynomial (Fin 2) k) _ _ f M hM.isPrime (hle (Ideal.subset_span (by simp)))
  rw [hMheight] at hlower
  exact ENat.WithBot.add_one_cancel.mp (le_antisymm hupper hlower)


/-- The principal quotient by a polynomial of positive total degree in two variables over a
field has Krull dimension one. -/
theorem ringKrullDim_quotient_span_singleton_eq_one
    {k : Type u} [Field k] {f : MvPolynomial (Fin 2) k} (hf : 0 < f.totalDegree) :
    ringKrullDim (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}) = 1 := by
  apply ringKrullDim_quotient_span_singleton_eq_one_of_ne_zero_not_isUnit
  · intro h
    simpa [h] using hf
  · intro h
    have := (isUnit_iff_totalDegree_of_isReduced.mp h).2
    omega

end MvPolynomial
