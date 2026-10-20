/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic

/-!
# Homogeneous Stage Classes in an Associated Graded Ring

This leaf owns the canonical comparison between the degree-`n` homogeneous
piece of the quotient-Rees model and `I ^ n / I ^ (n + 1)`.  It keeps the
representative, linear, kernel, and computation APIs together so consumers do
not rebuild quotient presentations in theorem-local helper files.

@stack 00K8
-/

@[expose] public section

noncomputable section

universe u

namespace Ideal.AssociatedGraded

variable {R : Type u} [CommRing R]

/-- A representative in `I ^ n` determines a degree-`n` monomial in the Rees algebra. -/
theorem stageMonomial_mem_rees (I : Ideal R) (n : ℕ) (x : stage I R n) :
    Polynomial.monomial n (x : R) ∈ reesAlgebra I := sorry

/-- The homogeneous class in `gr_I(R)` represented by `x ∈ I ^ n`. -/
@[stacks 00K8 "homogeneous stage class"]
def stageClass (I : Ideal R) (n : ℕ) (x : stage I R n) : ring I :=
  Ideal.Quotient.mk (definingIdeal I)
    ⟨Polynomial.monomial n (x : R), stageMonomial_mem_rees I n x⟩

/-- A stage class represented in degree `n` belongs to the degree-`n` homogeneous piece. -/
theorem stageClass_mem_grade (I : Ideal R) (n : ℕ) (x : stage I R n) :
    stageClass I n x ∈ grade I n := sorry

/-- Multiplication of representatives respects addition of filtration degrees. -/
theorem stage_mul_mem (I : Ideal R) {m n : ℕ}
    (x : stage I R m) (y : stage I R n) :
    (x : R) * (y : R) ∈ stage I R (m + n) := sorry

/-- Multiplication of homogeneous stage classes is induced by multiplication in `R`. -/
@[stacks 00K8 "multiplication of homogeneous stage classes"]
theorem stageClass_mul (I : Ideal R) {m n : ℕ}
    (x : stage I R m) (y : stage I R n) :
    stageClass I (m + n) ⟨(x : R) * (y : R), stage_mul_mem I x y⟩ =
      stageClass I m x * stageClass I n y := sorry

/-- The degree-`n` monomial construction as a linear map into the Rees algebra. -/
noncomputable def stageToRees (I : Ideal R) (n : ℕ) :
    stage I R n →ₗ[R] reesAlgebra I :=
  LinearMap.codRestrict (reesAlgebra I).toSubmodule
    ((Polynomial.monomial n).comp (stage I R n).subtype)
    (stageMonomial_mem_rees I n)

/-- The linear presentation of the degree-`n` homogeneous piece by `I ^ n`. -/
@[stacks 00K8 "linear homogeneous stage presentation"]
noncomputable def stageClassLinear (I : Ideal R) (n : ℕ) :
    stage I R n →ₗ[R] grade I n :=
  LinearMap.codRestrict (grade I n)
    ((quotientMap I).toLinearMap.comp (stageToRees I n))
    (stageClass_mem_grade I n)

/-- Forgetting the grade subtype recovers the corresponding stage class. -/
@[simp] theorem stageClassLinear_coe (I : Ideal R) (n : ℕ) (x : stage I R n) :
    ((stageClassLinear I n x : grade I n) : ring I) = stageClass I n x := sorry

/-- Taking the stage class of a finite sum in one filtration degree is the
sum of the corresponding stage classes. -/
theorem stageClass_finset_sum
    {α : Type*} (I : Ideal R) (n : ℕ) (s : Finset α)
    (a : α → stage I R n) :
    stageClass I n (s.sum fun i ↦ a i) =
      s.sum fun i ↦ stageClass I n (a i) := by
  classical
  simpa only [← stageClassLinear_coe, map_sum, Submodule.coe_sum]

/-- The `n`-th coefficient of an element of the defining ideal lies in `I ^ (n + 1)`. -/
theorem coeff_mem_pow_succ_of_mem_definingIdeal (I : Ideal R) (n : ℕ)
    {y : reesAlgebra I} (hy : y ∈ definingIdeal I) :
    y.1.coeff n ∈ I ^ (n + 1) := sorry

/-- A degree-`n` monomial with coefficient in `I ^ (n + 1)` lies in the defining ideal. -/
theorem monomial_mem_definingIdeal (I : Ideal R) (n : ℕ) {a : R}
    (ha : a ∈ I ^ (n + 1)) :
    (⟨Polynomial.monomial n a,
        reesAlgebra.monomial_mem.mpr (Ideal.pow_le_pow_right (Nat.le_succ n) ha)⟩ :
      reesAlgebra I) ∈ definingIdeal I := sorry

/-- A stage class vanishes exactly when its representative lies in the next stage. -/
theorem stageClass_eq_zero_iff (I : Ideal R) (n : ℕ) (x : stage I R n) :
    stageClass I n x = 0 ↔ (x : R) ∈ stage I R (n + 1) := sorry

/-- Every degree-`n` homogeneous class has a representative in `I ^ n`. -/
theorem stageClassLinear_surjective (I : Ideal R) (n : ℕ) :
    Function.Surjective (stageClassLinear I n) := sorry

/-- The kernel of the degree-`n` stage presentation is the next filtration stage. -/
theorem stageClassLinear_ker (I : Ideal R) (n : ℕ) :
    LinearMap.ker (stageClassLinear I n) =
      (stage I R (n + 1)).submoduleOf (stage I R n) := sorry

/-- The degree-`n` homogeneous piece of `gr_I(R)` is canonically `I ^ n / I ^ (n + 1)`. -/
@[stacks 00K8 "associated graded degree-piece comparison"]
noncomputable def gradeEquivPiece (I : Ideal R) (n : ℕ) :
    grade I n ≃ₗ[R] piece I R n :=
  ((stageClassLinear I n).quotKerEquivOfSurjective
      (stageClassLinear_surjective I n)).symm.trans
    (Submodule.quotEquivOfEq _ _ (stageClassLinear_ker I n))

/-- Each homogeneous grade is canonically a module over the quotient ring
`R ⧸ I`, transported from its successive-stage quotient model. -/
@[stacks 00K8 "associated graded homogeneous quotient module"]
noncomputable instance gradeModuleQuotient (I : Ideal R) (n : ℕ) :
    Module (R ⧸ I) (grade I n) :=
  (gradeEquivPiece I n).toAddEquiv.module (R ⧸ I)

/-- The quotient action on each homogeneous grade is compatible with its
original `R`-module action. -/
@[stacks 00K8 "associated graded homogeneous quotient scalar tower"]
noncomputable instance gradeIsScalarTowerQuotient (I : Ideal R) (n : ℕ) :
    IsScalarTower R (R ⧸ I) (grade I n) :=
  LinearEquiv.isScalarTower (R := R) (A := R ⧸ I) (gradeEquivPiece I n)

/-- The degree-piece comparison is canonically linear over `R ⧸ I`. -/
@[stacks 00K8 "associated graded quotient-linear degree-piece comparison"]
noncomputable def gradeEquivPieceQuotient (I : Ideal R) (n : ℕ) :
    grade I n ≃ₗ[R ⧸ I] piece I R n :=
  (gradeEquivPiece I n).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- A maximal-ideal homogeneous grade carries its quotient action under the residue-field name. -/
noncomputable instance gradeModuleResidueField [IsLocalRing R] (n : ℕ) :
    Module (IsLocalRing.ResidueField R)
      (grade (IsLocalRing.maximalIdeal R) n) :=
  gradeModuleQuotient (IsLocalRing.maximalIdeal R) n

/-- For a local ring, the degree-piece comparison for the maximal ideal is
canonically linear over the residue field. -/
noncomputable def gradeEquivPieceResidueField [IsLocalRing R] (n : ℕ) :
    grade (IsLocalRing.maximalIdeal R) n ≃ₗ[IsLocalRing.ResidueField R]
      piece (IsLocalRing.maximalIdeal R) R n :=
  gradeEquivPieceQuotient (IsLocalRing.maximalIdeal R) n

/-- The degree-piece comparison sends a stage class to its quotient class. -/
@[simp] theorem gradeEquivPiece_stageClass (I : Ideal R) (n : ℕ)
    (x : stage I R n) :
    gradeEquivPiece I n
        ⟨stageClass I n x, stageClass_mem_grade I n x⟩ =
      (Submodule.Quotient.mk x : piece I R n) := sorry

/-- The degree-piece comparison computes directly on the linear stage presentation. -/
@[simp] theorem gradeEquivPiece_stageClassLinear (I : Ideal R) (n : ℕ)
    (x : stage I R n) :
    gradeEquivPiece I n (stageClassLinear I n x) =
      (Submodule.Quotient.mk x : piece I R n) := sorry

/-- The quotient-linear degree-piece comparison sends a stage class to its
successive-quotient class. -/
@[simp]
theorem gradeEquivPieceQuotient_stageClass (I : Ideal R) (n : ℕ)
    (x : stage I R n) :
    gradeEquivPieceQuotient I n
        ⟨stageClass I n x, stageClass_mem_grade I n x⟩ =
      (Submodule.Quotient.mk x : piece I R n) := by
  exact gradeEquivPiece_stageClass I n x

/-- The quotient-linear degree-piece comparison computes on the linear stage
presentation. -/
@[simp]
theorem gradeEquivPieceQuotient_stageClassLinear (I : Ideal R) (n : ℕ)
    (x : stage I R n) :
    gradeEquivPieceQuotient I n (stageClassLinear I n x) =
      (Submodule.Quotient.mk x : piece I R n) := by
  exact gradeEquivPiece_stageClassLinear I n x

/-- The residue-field degree-piece comparison sends a maximal-ideal stage
class to its successive-quotient class. -/
@[simp]
theorem gradeEquivPieceResidueField_stageClass [IsLocalRing R] (n : ℕ)
    (x : stage (IsLocalRing.maximalIdeal R) R n) :
    gradeEquivPieceResidueField (R := R) n
        ⟨stageClass (IsLocalRing.maximalIdeal R) n x,
          stageClass_mem_grade (IsLocalRing.maximalIdeal R) n x⟩ =
      (Submodule.Quotient.mk x :
        piece (IsLocalRing.maximalIdeal R) R n) := by
  exact gradeEquivPieceQuotient_stageClass (IsLocalRing.maximalIdeal R) n x

/-- The residue-field comparison computes on the linear maximal-ideal stage
presentation. -/
@[simp]
theorem gradeEquivPieceResidueField_stageClassLinear [IsLocalRing R] (n : ℕ)
    (x : stage (IsLocalRing.maximalIdeal R) R n) :
    gradeEquivPieceResidueField (R := R) n
        (stageClassLinear (IsLocalRing.maximalIdeal R) n x) =
      (Submodule.Quotient.mk x :
        piece (IsLocalRing.maximalIdeal R) R n) := by
  exact gradeEquivPieceQuotient_stageClassLinear
    (IsLocalRing.maximalIdeal R) n x

/-- A degree-zero stage class is the image of its representative under the
canonical algebra map into the associated graded ring. -/
@[simp] theorem stageClass_zero (I : Ideal R) (r : R) :
    stageClass I 0 ⟨r, mem_stage_zero I R r⟩ = algebraMap R (ring I) r := sorry

end Ideal.AssociatedGraded
