/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import ReasLib.RingTheory.Ideal.IdempotentLifting
import Mathlib.Tactic.CrossRefAttribute

/-!
# Criteria for henselian pairs

This leaf owns the etale-section, idempotent-lifting, and Gabber polynomial criteria for a
henselian pair. The predicates remain atomic; the source's five-way equivalence is exposed both
as a `List.TFAE` and through named binary equivalences.

@stack 09XI
-/

@[expose] public section

open Polynomial
open scoped Polynomial

universe u

namespace Ideal

variable {A : Type u} [CommRing A]

/-- Every section modulo `I` of an etale `A`-algebra lifts to an `A`-algebra map to `A`. -/
@[stacks 09XI "etale-section lifting criterion"]
def HasEtaleLiftProperty (I : Ideal A) : Prop :=
  ∀ ⦃A' : Type u⦄ [CommRing A'] [Algebra A A'] [Algebra.Etale A A'],
    Function.Surjective fun τ : A' →ₐ[A] A ↦ (Ideal.Quotient.mkₐ A I).comp τ

/-- A monic polynomial whose reduction modulo `I` is `X ^ n * (X - 1)` for some `n > 0`. -/
@[stacks 09XI "Gabber test polynomial"]
def IsGabberHenselPolynomial (I : Ideal A) (f : A[X]) : Prop :=
  ∃ n : ℕ, 0 < n ∧ f.Monic ∧
    f.map (Ideal.Quotient.mk I) = X ^ n * (X - 1)

/-- The Jacobson condition together with existence of a root in `1 + I` for every Gabber test
polynomial. -/
@[stacks 09XI "Gabber root criterion"]
def SatisfiesGabberRootCriterion (I : Ideal A) : Prop :=
  I ≤ Ring.jacobson A ∧
    ∀ ⦃f : A[X]⦄, I.IsGabberHenselPolynomial f → ∃ i : I, f.IsRoot (1 + ↑i)

private theorem isRoot_eq_of_sub_mem (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    {f : A[X]} {a b : A} (ha : f.IsRoot a) (hb : f.IsRoot b) (hab : b - a ∈ I)
    (hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a))) : b = a := by
  letI := isLocalHom_of_le_jacobson_bot I hI
  obtain ⟨c, hc⟩ := exists_mul_sq_add_linear_part_eq_eval_add f a (b - a)
  have hmod : Ideal.Quotient.mk I (b - a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hab
  have hunit : IsUnit (c * (b - a) + f.derivative.eval a) := by
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    simpa only [map_add, map_mul, hmod, mul_zero, zero_add] using hderiv
  have hmul : (c * (b - a) + f.derivative.eval a) * (b - a) = 0 := by
    calc
      (c * (b - a) + f.derivative.eval a) * (b - a) =
          c * (b - a) ^ 2 + f.derivative.eval a * (b - a) + f.eval a := by
        rw [ha.eq_zero]
        ring
      _ = f.eval (a + (b - a)) := hc
      _ = 0 := by simpa using hb
  exact sub_eq_zero.mp (hunit.mul_right_eq_zero.mp hmul)

private theorem isUnit_idempotent_derivative {e : A} (he : IsIdempotentElem e) :
    IsUnit ((X * (X - 1) : A[X]).derivative.eval e) := by
  have hmul : (e - 1 + e) * (e - 1 + e) = 1 := by
    calc
      (e - 1 + e) * (e - 1 + e) = 4 * (e * e - e) + 1 := by ring
      _ = 1 := by rw [he.eq, sub_self, mul_zero, zero_add]
  have hunit : IsUnit (e - 1 + e) := isUnit_iff_exists_inv.mpr ⟨e - 1 + e, hmul⟩
  simpa only [derivative_mul, derivative_X, derivative_sub, derivative_one, sub_zero,
    one_mul, mul_one, eval_add, eval_sub, eval_X, eval_one] using hunit

namespace HenselianPairCriteria

/-- Lemma 15.11.6: henselianity, etale-section lifting, finite- and integral-algebra idempotent
lifting, and Gabber's root criterion are equivalent. -/
@[stacks 09XI "Lemma 15.11.6"]
theorem tfae (I : Ideal A) :
    List.TFAE
      [ HenselianRing A I
      , I.HasEtaleLiftProperty
      , Ideal.HasFiniteAlgebraIdempotentLifting.{u, u} (A := A) I
      , Ideal.HasIntegralAlgebraIdempotentLifting.{u, u} (A := A) I
      , I.SatisfiesGabberRootCriterion
      ] := sorry

/-- Henselianity is equivalent to lifting etale sections modulo the ideal. -/
@[stacks 09XI "henselianity and etale-section lifting"]
theorem henselian_iff_etaleLift (I : Ideal A) :
    HenselianRing A I ↔ I.HasEtaleLiftProperty :=
  (tfae I).out 0 1

/-- Henselianity is equivalent to idempotent lifting for finite algebras. -/
@[stacks 09XI "henselianity and finite-algebra idempotent lifting"]
theorem henselian_iff_finiteIdempotentLifting (I : Ideal A) :
    HenselianRing A I ↔
      Ideal.HasFiniteAlgebraIdempotentLifting.{u, u} (A := A) I :=
  (tfae I).out 0 2

/-- Henselianity is equivalent to idempotent lifting for integral algebras. -/
@[stacks 09XI "henselianity and integral-algebra idempotent lifting"]
theorem henselian_iff_integralIdempotentLifting (I : Ideal A) :
    HenselianRing A I ↔
      Ideal.HasIntegralAlgebraIdempotentLifting.{u, u} (A := A) I :=
  (tfae I).out 0 3

/-- Henselianity is equivalent to Gabber's Jacobson-plus-root criterion. -/
@[stacks 09XI "henselianity and the Gabber root criterion"]
theorem henselian_iff_gabber (I : Ideal A) :
    HenselianRing A I ↔ I.SatisfiesGabberRootCriterion :=
  (tfae I).out 0 4

/-- A henselian pair has bijective reduction on idempotents for the identity algebra. -/
@[stacks 09XI "idempotents modulo a henselian ideal"]
theorem idempotentMap_bijective (I : Ideal A) [HenselianRing A I] :
    Function.Bijective (Ideal.Quotient.mk I).idempotentMap := by
  let f : A[X] := X * (X - 1)
  have hmonic : f.Monic := monic_X.mul (by simpa using (monic_X_sub_C (1 : A)))
  constructor
  · show Function.Injective (Ideal.Quotient.mk I).idempotentMap
    intro e d hed
    apply Subtype.ext
    have hmod := congrArg Subtype.val hed
    change Ideal.Quotient.mk I (e : A) = Ideal.Quotient.mk I (d : A) at hmod
    have he : f.IsRoot (e : A) := by
      simpa [f, IsRoot, mul_sub, sub_eq_zero, IsIdempotentElem] using e.property
    have hd : f.IsRoot (d : A) := by
      simpa [f, IsRoot, mul_sub, sub_eq_zero, IsIdempotentElem] using d.property
    exact (isRoot_eq_of_sub_mem I (HenselianRing.jac (R := A)) he hd
      (Ideal.Quotient.eq.mp hmod.symm)
      ((isUnit_idempotent_derivative e.property).map (Ideal.Quotient.mk I))).symm
  · show Function.Surjective (Ideal.Quotient.mk I).idempotentMap
    intro e
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e : A ⧸ I)
    have hroot : f.eval a ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← eval_map_apply]
      simp only [f, Polynomial.map_mul, map_X, Polynomial.map_sub,
        eval_mul, eval_sub, eval_X, ha, mul_sub, mul_one, e.property.eq, sub_self]
    have hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a)) := by
      rw [← eval_map_apply, ← derivative_map]
      simpa only [f, Polynomial.map_mul, map_X, Polynomial.map_sub, Polynomial.map_one, ha]
        using isUnit_idempotent_derivative e.property
    obtain ⟨b, hb, hba⟩ := HenselianRing.is_henselian f hmonic a hroot hderiv
    refine ⟨⟨b, ?_⟩, ?_⟩
    · change IsIdempotentElem b
      simpa [f, IsRoot, mul_sub, sub_eq_zero, IsIdempotentElem] using hb
    · show (Ideal.Quotient.mk I).idempotentMap ⟨b, _⟩ = e
      apply Subtype.ext
      change Ideal.Quotient.mk I b = (e : A ⧸ I)
      exact (Ideal.Quotient.eq.mpr hba).trans ha

end HenselianPairCriteria

namespace SatisfiesGabberRootCriterion

/-- Gabber's root criterion implies that the pair is henselian. -/
@[stacks 09XI "Gabber criterion implies henselianity"]
theorem henselianRing {I : Ideal A} (hI : I.SatisfiesGabberRootCriterion) :
    HenselianRing A I :=
  (HenselianPairCriteria.henselian_iff_gabber I).mpr hI

/-- The root in `1 + I` supplied by Gabber's criterion is unique. -/
@[stacks 09XI "uniqueness in the Gabber root criterion"]
theorem existsUnique {I : Ideal A} (hI : I.SatisfiesGabberRootCriterion)
    {f : A[X]} (hf : I.IsGabberHenselPolynomial f) :
    ∃! i : I, f.IsRoot (1 + ↑i) := by
  obtain ⟨i, hi⟩ := hI.2 hf
  obtain ⟨n, _, _, hfmod⟩ := hf
  have hi_mod : Ideal.Quotient.mk I (1 + (i : A)) = 1 := by
    rw [map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr i.property, add_zero]
  have hderiv : Ideal.Quotient.mk I (f.derivative.eval (1 + (i : A))) = 1 := by
    rw [← eval_map_apply, ← derivative_map, hfmod, hi_mod]
    simp
  refine ⟨i, hi, ?_⟩
  intro j hj
  apply Subtype.ext
  have hsub : (1 + (j : A)) - (1 + (i : A)) ∈ I := by
    convert I.sub_mem j.property i.property using 1
    ring
  have heq := isRoot_eq_of_sub_mem I (by simpa only [Ideal.jacobson_bot] using hI.1)
    hi hj hsub (by rw [hderiv]; exact isUnit_one)
  exact add_left_cancel heq

end SatisfiesGabberRootCriterion

end Ideal
