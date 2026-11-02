/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import StacksCheckRecall

/-!
# Proj of a standard graded polynomial ring

@stack 00JQ

This file retains the concrete standard grading on `R[X]`, its degree-zero identification, and the
resulting isomorphism `Proj(R[X]) ~= Spec(R)` from Example 10.57.4. The direct-sum and localization
calculations used to establish these statements are proof infrastructure rather than chapter API.
-/

@[expose] public section

open scoped DirectSum
open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace Polynomial

variable (R : Type u) [CommRing R]

/-- The standard grading on `R[X]`, transported from the additive monoid algebra model `R[N]`. -/
abbrev standardGrading (n : ℕ) : Submodule R R[X] :=
  Submodule.map (Polynomial.toFinsuppIsoLinear R).symm.toLinearMap (AddMonoidAlgebra.grade R n)

instance instSetLikeGradedMonoidStandardGrading : SetLike.GradedMonoid (standardGrading R) where
  one_mem := ⟨1, SetLike.one_mem_graded (AddMonoidAlgebra.grade R),
    (Polynomial.toFinsuppIso R).symm.map_one⟩
  mul_mem i j a b ha hb := by
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact ⟨a * b, SetLike.mul_mem_graded ha hb,
      (Polynomial.toFinsuppIso R).symm.map_mul a b⟩

private theorem monomial_mem_standardGrading (n : ℕ) (a : R) :
    Polynomial.monomial n a ∈ standardGrading R n :=
  ⟨AddMonoidAlgebra.single n a, AddMonoidAlgebra.single_mem_grade n a,
    Polynomial.ofFinsupp_single n a⟩

/-- A homogeneous polynomial of degree `n` is its `n`-th coefficient times `X^n`. -/
theorem standardGrading_eq_C_mul_X_pow_of_mem {n : ℕ} {f : R[X]}
    (hf : f ∈ standardGrading R n) :
    f = Polynomial.C (f.coeff n) * Polynomial.X ^ n := by
  obtain ⟨a, ha, rfl⟩ := hf
  have hs := (AddMonoidAlgebra.mem_grade_iff R n a).mp ha
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_monomial]
  by_cases h : n = i
  · subst i
    simp
  · rw [if_neg h]
    exact Finsupp.notMem_support_iff.mp fun hi ↦ h (Finset.mem_singleton.mp (hs hi)).symm

/-- The standard grading is an internal direct-sum decomposition of the polynomial ring. -/
theorem standardGrading_isInternal : DirectSum.IsInternal (standardGrading R) := by
  let e := Submodule.orderIsoMapComap (Polynomial.toFinsuppIsoLinear R).symm
  have h := AddMonoidAlgebra.grade.isInternal (R := R) (ι := ℕ)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (iSupIndep_map_orderIso_iff e).2 h.submodule_iSupIndep
  · change (⨆ n, e (AddMonoidAlgebra.grade R n)) = ⊤
    rw [← e.map_iSup, h.submodule_iSup_eq_top, e.map_top]

instance instGradedAlgebraStandardGrading : GradedAlgebra (standardGrading R) :=
  DirectSum.IsInternal.gradedAlgebra (standardGrading_isInternal R)

/-- The homogeneous decomposition of a polynomial has the expected monomial components. -/
theorem standardGrading_decompose_eq_C_coeff_mul_X_pow (f : R[X]) (n : ℕ) :
    ((DirectSum.decompose (standardGrading R) f) n : Polynomial R) =
      Polynomial.C (f.coeff n) * Polynomial.X ^ n := by
  classical
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      simp only [DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add,
        Polynomial.coeff_add, map_add, add_mul, hf, hg]
  | monomial m a =>
      by_cases h : m = n
      · subst m
        rw [DirectSum.decompose_of_mem_same _ (monomial_mem_standardGrading R n a)]
        simp [Polynomial.C_mul_X_pow_eq_monomial]
      · rw [DirectSum.decompose_of_mem_ne _ (monomial_mem_standardGrading R m a) h]
        simp [Polynomial.coeff_monomial, h]

/-- The degree-zero part of the standard polynomial grading is canonically the coefficient ring. -/
noncomputable def standardGradingDegreeZeroRingEquiv : ↥(standardGrading R 0) ≃+* R where
  toFun f := f.1.coeff 0
  invFun r := ⟨Polynomial.C r, by
    simpa using monomial_mem_standardGrading R 0 r⟩
  left_inv f := Subtype.ext (by
    simpa using (standardGrading_eq_C_mul_X_pow_of_mem R f.2).symm)
  right_inv r := Polynomial.coeff_C_zero
  map_mul' f g := by simp
  map_add' f g := by simp

@[simp] theorem standardGradingDegreeZeroRingEquiv_apply (f : standardGrading R 0) :
    standardGradingDegreeZeroRingEquiv R f = f.1.coeff 0 := rfl

@[simp] theorem standardGradingDegreeZeroRingEquiv_symm_apply (r : R) :
    ((standardGradingDegreeZeroRingEquiv R).symm r : R[X]) = Polynomial.C r := rfl

end Polynomial

section

variable (R : Type u) [CommRing R]

/-- The degree-zero ring equivalence induces the canonical spectrum isomorphism. -/
noncomputable def standardGradingDegreeZeroSpecIso :
    Spec (.of ↥(Polynomial.standardGrading R 0)) ≅ Spec (.of R) :=
  (Scheme.Spec.mapIso (Polynomial.standardGradingDegreeZeroRingEquiv R).toCommRingCatIso.op).symm

/-- Example 10.57.4, map form: the natural morphism from the projective spectrum of standard
graded `R[X]` to `Spec(R)`. -/
@[stacks 00JQ "standard-grading structure morphism"]
noncomputable def polynomial_standardGrading_toSpec :
    Proj (Polynomial.standardGrading R) ⟶ Spec (.of R) :=
  Proj.toSpecZero (Polynomial.standardGrading R) ≫ (standardGradingDegreeZeroSpecIso R).hom

/-- Example 10.57.4: `Proj(R[X])` with `deg(X) = 1` is canonically isomorphic to `Spec(R)`.
The inverse is induced by evaluation at `X = 1`. -/
@[stacks 00JQ "standard polynomial Proj"]
noncomputable def polynomial_standardGrading_isoSpec :
    Proj (Polynomial.standardGrading R) ≅ Spec (.of R) where
  hom := polynomial_standardGrading_toSpec R
  inv := Proj.fromOfGlobalSections (Polynomial.standardGrading R)
    ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (Polynomial.evalRingHom (1 : R))) (by
      apply (Ideal.eq_top_iff_one _).mpr
      have hX : Polynomial.X ∈
          (HomogeneousIdeal.irrelevant (Polynomial.standardGrading R)).toIdeal :=
        HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < (1 : ℕ)) (by
          simpa using Polynomial.monomial_mem_standardGrading R 1 (1 : R))
      simpa using Ideal.mem_map_of_mem
        ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (Polynomial.evalRingHom (1 : R))) hX)
  hom_inv_id := by sorry
  inv_hom_id := by
    dsimp only [polynomial_standardGrading_toSpec]
    rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero, Category.assoc]
    change (Spec (.of R)).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom
        (((Scheme.ΓSpecIso (.of R)).inv.hom.comp (Polynomial.evalRingHom (1 : R))).comp
          (algebraMap (Polynomial.standardGrading R 0) (Polynomial R)))) ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.standardGradingDegreeZeroRingEquiv R).symm.toRingHom) = _
    rw [← Spec.map_comp]
    convert (Spec (.of R)).toSpecΓ_isoSpec_inv using 1
    rw [Scheme.isoSpec_Spec_inv]
    congr 2
    ext r
    change (Scheme.ΓSpecIso (.of R)).inv.hom
      (Polynomial.eval (1 : R) (Polynomial.C r)) = _
    simp

/-- The standard-grading structure morphism is an isomorphism. -/
instance polynomial_standardGrading_toSpec_isIso :
    IsIso (polynomial_standardGrading_toSpec R) :=
  inferInstanceAs (IsIso (polynomial_standardGrading_isoSpec R).hom)

/-- A relevant homogeneous prime of standard graded `R[X]` is extended from its contraction to
the coefficient ring. -/
@[stacks 00JQ "homogeneous prime extension formula"]
theorem polynomial_standardGrading_point_asIdeal_eq_map_comap_C
    (p : ProjectiveSpectrum (Polynomial.standardGrading R)) :
    p.asHomogeneousIdeal.toIdeal =
      Ideal.map Polynomial.C (Ideal.comap Polynomial.C p.asHomogeneousIdeal.toIdeal) := sorry

end


#check @Proj.toSpecZero
#check @ProjectiveSpectrum
#check @Polynomial.C
