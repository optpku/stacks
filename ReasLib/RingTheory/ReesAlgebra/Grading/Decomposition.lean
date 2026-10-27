/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coefficient decomposition of a Rees algebra

This leaf gives the degreewise presentation of `reesAlgebra I` by the powers
`I ^ n`, together with the explicit internal direct-sum decomposition needed
to construct its graded-algebra structure.
-/

@[expose] public section

noncomputable section

universe u

open Polynomial
open scoped DirectSum

namespace ReesAlgebra.Grading

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

/-- The degree-`n` monomial in the Rees algebra associated to a coefficient in `I ^ n`. -/
def linearToFun (n : ℕ) (r : (I ^ n : Ideal R)) : reesAlgebra I :=
  ⟨monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩

/-- Degree-`n` Rees monomials preserve addition of their coefficients. -/
theorem linearToFun_add (n : ℕ) (x y : (I ^ n : Ideal R)) :
    linearToFun I n (x + y) = linearToFun I n x + linearToFun I n y := by
  apply Subtype.ext
  change monomial n (x.1 + y.1) = monomial n x.1 + monomial n y.1
  exact map_add (monomial n) x.1 y.1

/-- Degree-`n` Rees monomials preserve scalar multiplication of their coefficients. -/
theorem linearToFun_smul (n : ℕ) (a : R) (x : (I ^ n : Ideal R)) :
    linearToFun I n (a • x) = a • linearToFun I n x := by
  apply Subtype.ext
  change monomial n (a • x.1) = a • monomial n x.1
  exact (smul_monomial a n x.1).symm

/-- The linear inclusion of the coefficient ideal `I ^ n` as degree-`n`
monomials in `reesAlgebra I`. -/
@[stacks 052Q "Rees algebra graded-piece inclusion"]
def linear (I : Ideal R) (n : ℕ) : (I ^ n : Ideal R) →ₗ[R] reesAlgebra I where
  toFun := linearToFun I n
  map_add' := linearToFun_add I n
  map_smul' := linearToFun_smul I n

/-- The polynomial underlying `linear I n r` is the monomial
`r t ^ n`. -/
@[simp, stacks 052Q "Rees algebra graded-piece inclusion evaluation"]
theorem linear_apply (n : ℕ) (r : (I ^ n : Ideal R)) :
    ((linear I n r : reesAlgebra I) : R[X]) = monomial n r.1 := rfl

/-- The degree-`n` homogeneous piece `I ^ n t ^ n` of `reesAlgebra I`. -/
@[stacks 052Q "Rees algebra graded piece"]
def grade (n : ℕ) : Submodule R (reesAlgebra I) :=
  LinearMap.range (linear I n)

/-- The monomial with coefficient in `I ^ n` is the canonical element of the degree-`n` Rees
piece. -/
@[stacks 052Q "Rees algebra monomial in its graded piece"]
theorem grade_monomial (n : ℕ) (r : (I ^ n : Ideal R)) :
    (⟨monomial n r.1, (reesAlgebra.monomial_mem).2 r.2⟩ : reesAlgebra I) ∈
      grade I n := by
  exact ⟨r, rfl⟩

/-- The degree-`n` coefficient map from the homogeneous Rees piece to `I ^ n`. -/
@[stacks 052Q "Rees homogeneous-piece coefficient map",
  stacks 02O8 "Rees homogeneous-piece coefficient map"]
def coefficient (n : ℕ) : grade I n →ₗ[R] (I ^ n : Ideal R) :=
  ((Polynomial.lcoeff R n).comp
    ((reesAlgebra I).val.toLinearMap.comp (grade I n).subtype)).codRestrict
      (I ^ n) fun x ↦ x.1.2 n

/-- The degree-`n` monomial map from `I ^ n` to its homogeneous Rees piece. -/
@[stacks 052Q "Rees coefficient ideal to homogeneous piece",
  stacks 02O8 "Rees coefficient ideal to homogeneous piece"]
def toGrade (n : ℕ) : (I ^ n : Ideal R) →ₗ[R] grade I n :=
  (linear I n).codRestrict (grade I n) (LinearMap.mem_range_self (linear I n))

/-- Extracting the coefficient of a degree-`n` monomial recovers its coefficient. -/
theorem coefficient_toGrade (n : ℕ) (x : (I ^ n : Ideal R)) :
    coefficient I n (toGrade I n x) = x := by
  apply Subtype.ext
  change (monomial n x.1).coeff n = x.1
  exact coeff_monomial_same n x.1

/-- Rebuilding a homogeneous Rees element from its degree-`n` coefficient recovers it. -/
theorem toGrade_coefficient (n : ℕ) (x : grade I n) :
    toGrade I n (coefficient I n x) = x := by
  obtain ⟨r, hr⟩ := x.2
  have hx : toGrade I n r = x := Subtype.ext hr
  rw [← hx, coefficient_toGrade]

/-- The homogeneous degree-`n` Rees piece is linearly equivalent to `I ^ n` by coefficient
extraction. -/
@[stacks 052Q "Rees homogeneous piece coefficient equivalence",
  stacks 02O8 "Rees homogeneous piece coefficient equivalence"]
def coefficientEquiv (n : ℕ) : grade I n ≃ₗ[R] (I ^ n : Ideal R) :=
  { coefficient I n with
    invFun := toGrade I n
    left_inv := toGrade_coefficient I n
    right_inv := coefficient_toGrade I n }

/-- The multiplicative unit belongs to the degree-zero Rees piece. -/
theorem one_mem_grade : (1 : reesAlgebra I) ∈ grade I 0 := by
  refine ⟨⟨1, by simp⟩, ?_⟩
  apply Subtype.ext
  exact monomial_zero_one

/-- The product of elements in degrees `i` and `j` belongs to degree `i + j`. -/
theorem mul_mem_grade {i j : ℕ} {x y : reesAlgebra I}
    (hx : x ∈ grade I i) (hy : y ∈ grade I j) :
    x * y ∈ grade I (i + j) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  refine ⟨⟨a.1 * b.1, ?_⟩, ?_⟩
  · change a.1 * b.1 ∈ I ^ (i + j)
    rw [pow_add]
    exact Ideal.mul_mem_mul a.2 b.2
  · apply Subtype.ext
    exact (monomial_mul_monomial i j a.1 b.1).symm

/-- The explicit Rees pieces are multiplicatively graded. -/
@[stacks 052Q "Rees algebra graded multiplication"]
instance gradedMonoid :
    SetLike.GradedMonoid (grade I) where
  one_mem := one_mem_grade I
  mul_mem := fun {_ _} {_ _} hx hy ↦ mul_mem_grade I hx hy

/-- The coefficient monomial of a Rees element again belongs to its Rees
algebra. -/
@[stacks 052Q "Rees algebra coefficient monomial membership"]
theorem coeffMonomial_mem (x : reesAlgebra I) (n : ℕ) :
    monomial n (x.1.coeff n) ∈ reesAlgebra I := by
  exact reesAlgebra.monomial_mem.mpr (x.2 n)

/-- The Rees element represented by the degree-`n` coefficient monomial of
`x`. -/
@[stacks 052Q "Rees algebra coefficient monomial"]
def coeffMonomial (x : reesAlgebra I) (n : ℕ) : reesAlgebra I :=
  ⟨monomial n (x.1.coeff n), (reesAlgebra.monomial_mem).2 (x.2 n)⟩

/-- The coefficient monomial of `x` belongs to its matching homogeneous Rees
piece. -/
@[stacks 052Q "Rees algebra coefficient monomial graded membership"]
theorem coeffMonomial_mem_grade (x : reesAlgebra I) (n : ℕ) :
    coeffMonomial I x n ∈ grade I n := by
  exact grade_monomial I n ⟨x.1.coeff n, x.2 n⟩

/-- The finite-support coefficient decomposition of an element of
`reesAlgebra I` into its homogeneous monomials. -/
@[stacks 052Q "Rees algebra coefficient decomposition"]
noncomputable def decompose (x : reesAlgebra I) :
    ⨁ n, grade I n :=
  DirectSum.mk (fun n ↦ grade I n) x.1.support
    (fun n ↦ ⟨coeffMonomial I x n.1,
      coeffMonomial_mem_grade I x n.1⟩)

private theorem decompose_coe_apply (x : reesAlgebra I) (n : ℕ) :
    ((decompose I x n : reesAlgebra I) : R[X]) = monomial n (x.1.coeff n) := by
  classical
  by_cases hn : n ∈ x.1.support
  · show ((decompose I x n : reesAlgebra I) : R[X]) = monomial n (x.1.coeff n)
    simp only [decompose, DirectSum.mk_apply_of_mem hn]
    rfl
  · show ((decompose I x n : reesAlgebra I) : R[X]) = monomial n (x.1.coeff n)
    simp [decompose, DirectSum.mk_apply_of_notMem hn, notMem_support_iff.mp hn]

/-- A member of the degree-`n` Rees piece is the monomial determined by its
degree-`n` coefficient. -/
@[stacks 052Q "Rees algebra graded-piece monomial form"]
theorem grade_eq_monomial_coeff (n : ℕ) (y : grade I n) :
    ((y : reesAlgebra I) : R[X]) =
      monomial n (((y : reesAlgebra I) : R[X]).coeff n) := by
  obtain ⟨r, hr⟩ := y.2
  have hy : ((y : reesAlgebra I) : R[X]) = monomial n r.1 :=
    congrArg Subtype.val hr.symm
  rw [hy, coeff_monomial_same]

/-- A member of the degree-`m` Rees piece has zero coefficient in every
distinct degree `n`. -/
@[stacks 052Q "Rees algebra distinct graded coefficient vanishing"]
theorem grade_coeff_eq_zero_of_ne {m n : ℕ} (hmn : m ≠ n)
    (y : grade I m) :
    ((y : reesAlgebra I) : R[X]).coeff n = 0 := by
  rw [grade_eq_monomial_coeff I m y]
  exact coeff_monomial_of_ne _ hmn.symm

/-- Recomposition of a direct sum of Rees pieces has the expected coefficient
in every degree. -/
@[stacks 052Q "Rees algebra direct-sum coefficient evaluation"]
theorem grade_coeff_coeAddMonoidHom
    (y : ⨁ n, grade I n) (n : ℕ) :
    ((DirectSum.coeAddMonoidHom (grade I) y : reesAlgebra I) : R[X]).coeff n =
      ((y n : reesAlgebra I) : R[X]).coeff n := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of m y =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases hmn : m = n
    · subst m
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hmn)]
      simpa using grade_coeff_eq_zero_of_ne I hmn y
  | add y z hy hz =>
    simpa only [map_add, Subalgebra.coe_add, coeff_add, DirectSum.add_apply,
      Submodule.coe_add] using congrArg₂ (· + ·) hy hz

/-- Coefficient decomposition is a left inverse to canonical direct-sum
recomposition. -/
@[stacks 052Q "Rees algebra decomposition left inverse"]
theorem decompose_left_inv :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (grade I))
      (decompose I) := by
  intro x
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  rw [grade_coeff_coeAddMonoidHom, decompose_coe_apply, coeff_monomial_same]

/-- Coefficient decomposition is a right inverse to canonical direct-sum
recomposition. -/
@[stacks 052Q "Rees algebra decomposition right inverse"]
theorem decompose_right_inv :
    Function.RightInverse (DirectSum.coeAddMonoidHom (grade I))
      (decompose I) := by
  intro y
  apply DirectSum.ext
  intro n
  apply Subtype.ext
  apply Subtype.ext
  rw [decompose_coe_apply, grade_coeff_coeAddMonoidHom]
  exact (grade_eq_monomial_coeff I n (y n)).symm

/-- The canonical powers-of-an-ideal decomposition equips `reesAlgebra I`
with its graded `R`-algebra structure. -/
@[stacks 052Q "Rees algebra graded algebra structure"]
instance gradedAlgebra : GradedAlgebra (grade I) :=
  { gradedMonoid I with
    decompose' := decompose I
    left_inv := decompose_left_inv I
    right_inv := decompose_right_inv I }

/-- The degreewise Rees pieces form an internal direct-sum decomposition of
`reesAlgebra I`. -/
@[stacks 052Q "Rees algebra graded pieces internal decomposition"]
theorem grade_isInternal :
    DirectSum.IsInternal (grade I) :=
  DirectSum.Decomposition.isInternal (grade I)

/-- The degree-`n` component of the canonical Rees decomposition is the monomial
with coefficient `x.coeff n`. -/
@[simp, stacks 052Q "Rees algebra coefficient decomposition evaluation"]
theorem decompose_apply (x : reesAlgebra I) (n : ℕ) :
    ((DirectSum.decompose (grade I) x n : reesAlgebra I) : R[X]) =
      monomial n (x.1.coeff n) := by
  exact decompose_coe_apply I x n

end

end ReesAlgebra.Grading
