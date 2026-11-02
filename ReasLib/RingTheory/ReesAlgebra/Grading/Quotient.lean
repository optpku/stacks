/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Quotients of graded Rees algebras

The quotient of a ring by an ideal induces a graded map of Rees algebras.
Its homogeneous kernel is characterized coefficientwise.
-/

@[expose] public section

noncomputable section

universe u

open Polynomial

namespace ReesAlgebra.Grading

variable {A : Type u} [CommRing A]

/-- The Rees algebra map along `Ideal.Quotient.mk p`. -/
def quotientMap (I p : Ideal A) :
    reesAlgebra I →+* reesAlgebra (I.map (Ideal.Quotient.mk p)) :=
  map (Ideal.Quotient.mk p) Ideal.le_comap_map

/-- Mapping a Rees polynomial to the quotient maps its coefficients. -/
theorem quotientMap_apply (I p : Ideal A) (x : reesAlgebra I) :
    (quotientMap I p x).1 = Polynomial.map (Ideal.Quotient.mk p) x.1 := by
  rfl

/-- The quotient map preserves each graded Rees piece. -/
theorem quotientMap_mem_grade (I p : Ideal A) {n : ℕ} {x : reesAlgebra I}
    (hx : x ∈ grade I n) :
    quotientMap I p x ∈ grade (I.map (Ideal.Quotient.mk p)) n := by
  obtain ⟨a, rfl⟩ := hx
  have ha : Ideal.Quotient.mk p a.1 ∈ (I.map (Ideal.Quotient.mk p)) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ a.2
  refine ⟨⟨Ideal.Quotient.mk p a.1, ha⟩, ?_⟩
  apply Subtype.ext
  change monomial n (Ideal.Quotient.mk p a.1) =
    Polynomial.map (Ideal.Quotient.mk p) (monomial n a.1)
  exact (Polynomial.map_monomial _).symm

/-- The graded Rees algebra map induced by quotienting the base ring. -/
def quotientGradedMap (I p : Ideal A) :
    grade I →+*ᵍ grade (I.map (Ideal.Quotient.mk p)) where
  toRingHom := quotientMap I p
  map_mem := quotientMap_mem_grade I p

/-- The underlying ring map of the graded quotient map. -/
theorem quotientGradedMap_toRingHom (I p : Ideal A) :
    (quotientGradedMap I p).toRingHom = quotientMap I p := by
  rfl

private theorem map_grade_preimage {S : Type u} [CommRing S]
    {I : Ideal A} {J : Ideal S} (f : A →+* S) (hIJ : I ≤ Ideal.comap f J)
    (hf : Function.Surjective f) (hJ : J = I.map f)
    {n : ℕ} {x : reesAlgebra J} (hx : x ∈ grade J n) :
    ∃ y : reesAlgebra I, y ∈ grade I n ∧ map f hIJ y = x := by
  obtain ⟨a, rfl⟩ := hx
  have ha : a.1 ∈ (I ^ n).map f := by
    rw [Ideal.map_pow, ← hJ]
    exact a.2
  obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp ha
  refine ⟨linear I n ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, ?_⟩
  apply Subtype.ext
  change Polynomial.map f (monomial n b) = monomial n a.1
  rw [Polynomial.map_monomial, hba]

/-- A surjection of base rings induces a surjection of Rees algebras when the
target ideal is the image of the source ideal. -/
theorem map_surjective {S : Type u} [CommRing S] {I : Ideal A} {J : Ideal S}
    (f : A →+* S) (hIJ : I ≤ Ideal.comap f J) (hf : Function.Surjective f)
    (hJ : J = I.map f) : Function.Surjective (map f hIJ) := by
  classical
  intro x
  have h : ∀ n, ∃ y : reesAlgebra I, map f hIJ y = coeffMonomial J x n := by
    intro n
    obtain ⟨y, _, hy⟩ := map_grade_preimage f hIJ hf hJ (coeffMonomial_mem_grade J x n)
    exact ⟨y, hy⟩
  choose y hy using h
  refine ⟨∑ n ∈ x.1.support, y n, ?_⟩
  simp only [map_sum, hy]
  apply Subtype.ext
  change (reesAlgebra J).val (∑ n ∈ x.1.support, coeffMonomial J x n) = x.1
  rw [map_sum]
  exact x.1.as_sum_support.symm

/-- The homogeneous kernel of the graded Rees quotient map. -/
def strictTransformIdeal (I p : Ideal A) : HomogeneousIdeal (grade I) :=
  HomogeneousIdeal.comap (quotientGradedMap I p) ⊥

/-- Membership in the homogeneous kernel is coefficientwise membership in `p`. -/
theorem strictTransformIdeal_spec (I p : Ideal A) (x : reesAlgebra I) :
    x ∈ strictTransformIdeal I p ↔ ∀ n, x.1.coeff n ∈ p := by
  change quotientMap I p x = 0 ↔ _
  rw [Subtype.ext_iff, quotientMap_apply]
  simp only [Subalgebra.coe_zero, Polynomial.ext_iff, coeff_map, coeff_zero,
    Ideal.Quotient.eq_zero_iff_mem]

/-- The degree-`n` piece of the homogeneous kernel has coefficients in `I ^ n ∩ p`. -/
theorem strictTransformIdeal_grade (I p : Ideal A) (n : ℕ) (a : A) (ha : a ∈ I ^ n) :
    linear I n ⟨a, ha⟩ ∈ strictTransformIdeal I p ↔ a ∈ p := by
  rw [strictTransformIdeal_spec]
  constructor
  · intro h
    simpa only [linear_apply, coeff_monomial_same] using h n
  · intro h m
    by_cases hmn : m = n
    · subst m
      simpa only [linear_apply, coeff_monomial_same] using h
    · simp [linear_apply, coeff_monomial, Ne.symm hmn]

/-- The ideal underlying the homogeneous kernel equals the ring-map kernel. -/
theorem strictTransformIdeal_toIdeal (I p : Ideal A) :
    (strictTransformIdeal I p).toIdeal = RingHom.ker (quotientMap I p) := by
  ext x
  change quotientMap I p x = 0 ↔ quotientMap I p x = 0
  rfl

/-- Quotienting by a prime ideal gives a prime homogeneous kernel. -/
theorem isPrime_toIdeal_strictTransformIdeal (I p : Ideal A) [p.IsPrime] :
    (strictTransformIdeal I p).toIdeal.IsPrime := by
  rw [strictTransformIdeal_toIdeal]
  exact RingHom.ker_isPrime (quotientMap I p)

/-- If the center is not contained in `p`, the homogeneous kernel does not
contain the irrelevant ideal. -/
theorem not_irrelevant_le_strictTransformIdeal (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    ¬ HomogeneousIdeal.irrelevant (grade I) ≤ strictTransformIdeal I p := by
  intro h
  apply hI
  intro a ha
  have ha' : a ∈ I ^ 1 := by simpa only [pow_one] using ha
  apply (strictTransformIdeal_grade I p 1 a ha').mp
  apply h
  exact HomogeneousIdeal.mem_irrelevant_of_mem (grade I) Nat.zero_lt_one
    (show linear I 1 ⟨a, ha'⟩ ∈ grade I 1 from ⟨⟨a, ha'⟩, rfl⟩)

/-- The image of the irrelevant ideal contains the irrelevant ideal of the
quotient Rees algebra. -/
theorem quotientGradedMap_map_irrelevant (I p : Ideal A) :
    HomogeneousIdeal.irrelevant (grade (I.map (Ideal.Quotient.mk p))) ≤
      HomogeneousIdeal.map (quotientGradedMap I p) (HomogeneousIdeal.irrelevant (grade I)) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn x hx
  obtain ⟨y, hy, hxy⟩ := map_grade_preimage (Ideal.Quotient.mk p) Ideal.le_comap_map
    Ideal.Quotient.mk_surjective rfl hx
  change x ∈ (HomogeneousIdeal.map (quotientGradedMap I p)
    (HomogeneousIdeal.irrelevant (grade I))).toIdeal
  rw [← hxy]
  exact Ideal.mem_map_of_mem (quotientGradedMap I p)
    (HomogeneousIdeal.mem_irrelevant_of_mem (grade I) hn hy)

/-- The Rees quotient map is surjective. -/
theorem quotientMap_surjective (I p : Ideal A) :
    Function.Surjective (quotientMap I p) := by
  exact map_surjective (Ideal.Quotient.mk p) Ideal.le_comap_map
    Ideal.Quotient.mk_surjective rfl

end ReesAlgebra.Grading
