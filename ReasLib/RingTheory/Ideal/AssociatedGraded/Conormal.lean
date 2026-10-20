/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import ReasLib.RingTheory.Ideal.AssociatedGraded.DegreeZero

/-!
# The conormal algebra map

This file constructs the canonical map from the symmetric algebra of an
ideal's conormal module to its associated graded ring.
-/

@[expose] public section

noncomputable section

universe u

open Polynomial

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

private def degreeOneLinear : I →ₗ[R] reesAlgebra I where
  toFun := ReesAlgebra.Grading.degreeOne I
  map_add' x y := by
    apply Subtype.ext
    exact (monomial 1).map_add x.1 y.1
  map_smul' a x := by
    apply Subtype.ext
    exact (monomial 1).map_smul a x.1

private def associatedGradedDegreeOneLinear :
    I →ₗ[R] Ideal.AssociatedGraded.ring I :=
  (Ideal.AssociatedGraded.quotientMap I).toLinearMap.comp (degreeOneLinear I)

@[simp] private theorem associatedGradedDegreeOneLinear_apply
    (x : I) :
    associatedGradedDegreeOneLinear I x = Ideal.AssociatedGraded.degreeOne x :=
  rfl

private theorem associatedGradedDegreeOneLinear_mul
    (x y : I) :
    associatedGradedDegreeOneLinear I (x * y) = 0 := by
  rw [associatedGradedDegreeOneLinear_apply, Ideal.AssociatedGraded.degreeOne,
    Ideal.Quotient.eq_zero_iff_mem]
  have hx :
      algebraMap R (reesAlgebra I) (x : R) ∈ Ideal.AssociatedGraded.definingIdeal I :=
    Ideal.mem_map_of_mem (algebraMap R (reesAlgebra I)) x.2
  have hmul :
      ReesAlgebra.Grading.degreeOne I (x * y) =
        algebraMap R (reesAlgebra I) (x : R) * ReesAlgebra.Grading.degreeOne I y := by
    apply Subtype.ext
    simp [ReesAlgebra.Grading.degreeOne, Polynomial.C_mul_monomial, mul_comm]
  change ReesAlgebra.Grading.degreeOne I (x * y) ∈ Ideal.AssociatedGraded.definingIdeal I
  rw [hmul]
  exact Ideal.mul_mem_right _ _ hx

private noncomputable def idealConormalDegreeOneLinearR :
    I.Cotangent →ₗ[R] Ideal.AssociatedGraded.ring I :=
  Ideal.Cotangent.lift
    (associatedGradedDegreeOneLinear I)
    (associatedGradedDegreeOneLinear_mul I)

private noncomputable def idealConormalDegreeOneLinear :
    I.Cotangent →ₗ[R ⧸ I] Ideal.AssociatedGraded.ring I :=
  let f : I.Cotangent →ₗ[R] Ideal.AssociatedGraded.ring I :=
    idealConormalDegreeOneLinearR I
  { toFun := fun x ↦ f x
    map_add' := f.map_add
    map_smul' := by
      intro a x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      change f (algebraMap R (R ⧸ I) r • x) = algebraMap R (R ⧸ I) r • f x
      simpa only [IsScalarTower.algebraMap_smul] using f.map_smul r x }

@[simp] private theorem idealConormalDegreeOneLinear_toCotangent
    (x : I) :
    idealConormalDegreeOneLinear I (I.toCotangent x) =
      Ideal.AssociatedGraded.degreeOne x := by
  change idealConormalDegreeOneLinearR I (I.toCotangent x) =
    Ideal.AssociatedGraded.degreeOne x
  exact
    Ideal.Cotangent.lift_toCotangent
      (associatedGradedDegreeOneLinear I)
      (associatedGradedDegreeOneLinear_mul I)
      x

/-- The canonical algebra map from the symmetric algebra of `I / I²` to the associated graded
ring `⨁ n, I ^ n / I ^ (n + 1)`. -/
public noncomputable def idealConormalAlgebraQuotient :
    SymmetricAlgebra (R ⧸ I) I.Cotangent →ₐ[R ⧸ I]
      Ideal.AssociatedGraded.ring I := by
  let degreeOneLinear : I →ₗ[R] reesAlgebra I :=
    { toFun := ReesAlgebra.Grading.degreeOne I
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (monomial 1).map_add x.1 y.1
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact (monomial 1).map_smul a x.1 }
  let associatedGradedDegreeOneLinear :
      I →ₗ[R] Ideal.AssociatedGraded.ring I :=
    (Ideal.AssociatedGraded.quotientMap I).toLinearMap.comp degreeOneLinear
  have associatedGradedDegreeOneLinear_mul (x y : I) :
      associatedGradedDegreeOneLinear (x * y) = 0 := by
    rw [show associatedGradedDegreeOneLinear (x * y) =
      Ideal.AssociatedGraded.degreeOne (x * y) from rfl,
      Ideal.AssociatedGraded.degreeOne, Ideal.Quotient.eq_zero_iff_mem]
    have hx :
        algebraMap R (reesAlgebra I) (x : R) ∈
          Ideal.AssociatedGraded.definingIdeal I :=
      Ideal.mem_map_of_mem (algebraMap R (reesAlgebra I)) x.2
    have hmul :
        ReesAlgebra.Grading.degreeOne I (x * y) =
          algebraMap R (reesAlgebra I) (x : R) *
            ReesAlgebra.Grading.degreeOne I y := by
      apply Subtype.ext
      simp [ReesAlgebra.Grading.degreeOne, Polynomial.C_mul_monomial, mul_comm]
    change ReesAlgebra.Grading.degreeOne I (x * y) ∈
      Ideal.AssociatedGraded.definingIdeal I
    rw [hmul]
    exact Ideal.mul_mem_right _ _ hx
  let idealConormalDegreeOneLinearR :
      I.Cotangent →ₗ[R] Ideal.AssociatedGraded.ring I :=
    Ideal.Cotangent.lift associatedGradedDegreeOneLinear
      associatedGradedDegreeOneLinear_mul
  let idealConormalDegreeOneLinear :
      I.Cotangent →ₗ[R ⧸ I] Ideal.AssociatedGraded.ring I :=
    { toFun := fun x ↦ idealConormalDegreeOneLinearR x
      map_add' := idealConormalDegreeOneLinearR.map_add
      map_smul' := by
        intro a x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        change idealConormalDegreeOneLinearR (algebraMap R (R ⧸ I) r • x) =
          algebraMap R (R ⧸ I) r • idealConormalDegreeOneLinearR x
        simpa only [IsScalarTower.algebraMap_smul] using
          idealConormalDegreeOneLinearR.map_smul r x }
  exact SymmetricAlgebra.lift (A := Ideal.AssociatedGraded.ring I)
    idealConormalDegreeOneLinear

/-- The conormal algebra map sends a symmetric generator represented by `x : I` to the degree-one
class of `x` in the associated graded ring. -/
@[simp] public theorem idealConormalAlgebraQuotient_ι_toCotangent
    (x : I) :
    idealConormalAlgebraQuotient I
        ((SymmetricAlgebra.ι (R ⧸ I) I.Cotangent) (I.toCotangent x)) =
      Ideal.AssociatedGraded.degreeOne x := by
  rw [idealConormalAlgebraQuotient, SymmetricAlgebra.lift_ι_apply]
  exact idealConormalDegreeOneLinear_toCotangent I x

/-- The degree-one linear map underlying the conormal algebra quotient has homogeneous image. -/
public theorem idealConormalAlgebraQuotient_ι_mem_grade (x : I.Cotangent) :
    idealConormalAlgebraQuotient I
        ((SymmetricAlgebra.ι (R ⧸ I) I.Cotangent) x) ∈
      Ideal.AssociatedGraded.grade I 1 := sorry

/-- The canonical linear map from `I / I²` to the degree-one part of the associated graded
ring. -/
public noncomputable def idealConormalDegreeOne :
    I.Cotangent →ₗ[R] Ideal.AssociatedGraded.grade I 1 :=
  let f : I.Cotangent →ₗ[R] Ideal.AssociatedGraded.ring I :=
    ((idealConormalAlgebraQuotient I).toLinearMap.comp
      (SymmetricAlgebra.ι (R ⧸ I) I.Cotangent)).restrictScalars R
  { toFun := fun x ↦ ⟨f x, idealConormalAlgebraQuotient_ι_mem_grade I x⟩
    map_add' := fun x y ↦ Subtype.ext (f.map_add x y)
    map_smul' := fun r x ↦ Subtype.ext (f.map_smul r x) }

/-- The degree-one conormal map sends the cotangent class of an ideal element to its
homogeneous degree-one class. -/
@[simp] public theorem idealConormalDegreeOne_toCotangent (x : I) :
    idealConormalDegreeOne I (I.toCotangent x) =
      ⟨Ideal.AssociatedGraded.degreeOne x,
        Ideal.AssociatedGraded.degreeOne_mem_grade x⟩ := sorry

/-- The degree-one conormal map is natural on cotangent generators under ring homomorphisms
carrying one ideal into another. -/
public theorem idealConormalDegreeOne_naturality
    {S : Type*} [CommRing S] (J : Ideal S) (f : R →+* S)
    (hIJ : I ≤ Ideal.comap f J) (x : I) :
    Ideal.AssociatedGraded.mapGrade I J f hIJ 1
        (idealConormalDegreeOne I (I.toCotangent x)) =
      idealConormalDegreeOne J
        (J.toCotangent ⟨f x, hIJ x.2⟩) := sorry

/-- The canonical map from the symmetric algebra of an ideal's conormal module onto its
associated graded ring is surjective. -/
public theorem idealConormalAlgebraQuotient_surjective :
    Function.Surjective (idealConormalAlgebraQuotient I) := by
  let f := idealConormalAlgebraQuotient I
  let P : Subalgebra R (reesAlgebra I) :=
    (f.range.restrictScalars R).comap (Ideal.AssociatedGraded.quotientMap I)
  let Q : Subalgebra R R[X] := P.map (reesAlgebra I).val
  have hgen : Algebra.adjoin R
      (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) ≤ Q := by
    apply Algebra.adjoin_le
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨ReesAlgebra.Grading.degreeOne I ⟨r, hr⟩, ?_, rfl⟩
    change Ideal.AssociatedGraded.quotientMap I
      (ReesAlgebra.Grading.degreeOne I ⟨r, hr⟩) ∈ f.range
    refine ⟨SymmetricAlgebra.ι (R ⧸ I) I.Cotangent (I.toCotangent ⟨r, hr⟩), ?_⟩
    exact idealConormalAlgebraQuotient_ι_toCotangent I ⟨r, hr⟩
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hp : p.1 ∈ Q := by
    rw [adjoin_monomial_eq_reesAlgebra] at hgen
    exact hgen p.2
  obtain ⟨q, hq, heq⟩ := hp
  have heq' : q = p := Subtype.ext heq
  subst q
  exact hq
