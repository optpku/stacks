/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Derivation.ToSquareZero
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Difference derivations with values in an ideal cotangent module

Two ring homomorphisms whose pointwise difference lies in an ideal define a class in `I / I²`.
When one homomorphism is the structural algebra map, these classes assemble into a derivation.
This file is purely algebraic; categorical wrappers live in the `ModuleCat` bridge.
-/

@[expose] public section

universe u v w z

namespace RingHom

variable {A : Type u} {B : Type v} {C : Type w}
variable [Semiring A] [Ring B] [Ring C]

/-- If two ring homomorphisms agree after a common target map, their pointwise difference lies in
the kernel of that target map. -/
theorem sub_mem_ker_of_comp_eq (f g : A →+* B) (q : B →+* C)
    (h : q.comp f = q.comp g) (x : A) :
    f x - g x ∈ RingHom.ker q := by
  apply RingHom.mem_ker.mpr
  rw [map_sub, sub_eq_zero]
  exact DFunLike.congr_fun h x

end RingHom

namespace Ideal.Cotangent

variable {A : Type u} {B : Type v}
variable [CommSemiring A] [CommRing B]

/-- The class of `f x - g x` in the cotangent module `I / I²`. -/
@[stacks 0E1Y "cotangent difference class"]
def differenceClass (I : Ideal B) (f g : A →+* B)
    (h : ∀ x : A, f x - g x ∈ I) (x : A) : I.Cotangent :=
  I.toCotangent ⟨f x - g x, h x⟩

/-- Difference classes preserve addition. -/
@[simp]
theorem differenceClass_add (I : Ideal B) (f g : A →+* B)
    (h : ∀ x : A, f x - g x ∈ I) (x y : A) :
    differenceClass I f g h (x + y) =
      differenceClass I f g h x + differenceClass I f g h y := by
  unfold differenceClass
  rw [← map_add]
  apply congrArg I.toCotangent
  apply Subtype.ext
  simp [add_sub_add_comm]

/-- Difference classes satisfy the Leibniz rule for the scalar action induced by the first map. -/
theorem differenceClass_mul (I : Ideal B) (f g : A →+* B)
    (h : ∀ x : A, f x - g x ∈ I) (x y : A) :
    differenceClass I f g h (x * y) =
      f x • differenceClass I f g h y +
        f y • differenceClass I f g h x := by
  unfold differenceClass
  rw [← map_smul, ← map_smul, ← map_add, Ideal.toCotangent_eq]
  change f (x * y) - g (x * y) -
    (f x * (f y - g y) + f y * (f x - g x)) ∈ I ^ 2
  rw [map_mul, map_mul]
  have hdiff : f x * f y - g x * g y -
      (f x * (f y - g y) + f y * (f x - g x)) =
      -((f x - g x) * (f y - g y)) := by ring
  rw [hdiff, pow_two]
  exact (I * I).neg_mem (Ideal.mul_mem_mul (h x) (h y))

/-- Difference classes vanish after precomposition when the two maps agree there. -/
@[simp]
theorem differenceClass_comp_eq_zero {R : Type z} [CommSemiring R]
    (I : Ideal B) (a : R →+* A) (f g : A →+* B)
    (hcomp : f.comp a = g.comp a)
    (h : ∀ x : A, f x - g x ∈ I) (x : R) :
    differenceClass I f g h (a x) = 0 := by
  have hx : f (a x) = g (a x) := DFunLike.congr_fun hcomp x
  unfold differenceClass
  apply (I.toCotangent_eq_zero _).mpr
  simp [hx]

variable {R : Type w} [CommSemiring R]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The two algebra maps become equal after quotienting by an ideal containing their pointwise
difference. -/
theorem differenceQuotientCompEq (I : Ideal B) (g : A →ₐ[R] B)
    (h : ∀ x : A, algebraMap A B x - g x ∈ I) :
    (Ideal.Quotient.mkₐ R I).comp (IsScalarTower.toAlgHom R A B) =
      (Ideal.Quotient.mkₐ R I).comp g := by
  ext x
  exact Ideal.Quotient.eq.mpr (h x)

/-- The linear map to `I / I²` induced by the difference between the structural algebra map and
another algebra map. -/
@[stacks 0E1Y "cotangent difference linear map"]
def differenceLinearMap (I : Ideal B) (g : A →ₐ[R] B)
    (h : ∀ x : A, algebraMap A B x - g x ∈ I) :
    A →ₗ[R] I.Cotangent :=
  (I.toCotangent.restrictScalars R).comp
    (diffToIdealOfQuotientCompEq I (IsScalarTower.toAlgHom R A B) g
      (differenceQuotientCompEq I g h))

/-- The difference linear map evaluates to the corresponding cotangent difference class. -/
@[simp]
theorem differenceLinearMap_apply (I : Ideal B) (g : A →ₐ[R] B)
    (h : ∀ x : A, algebraMap A B x - g x ∈ I) (x : A) :
    differenceLinearMap I g h x =
      differenceClass I (algebraMap A B) g.toRingHom h x := rfl

/-- The difference linear map satisfies the Leibniz rule. -/
theorem differenceLinearMap_leibniz (I : Ideal B) (g : A →ₐ[R] B)
    (h : ∀ x : A, algebraMap A B x - g x ∈ I) (x y : A) :
    differenceLinearMap I g h (x * y) =
      x • differenceLinearMap I g h y +
        y • differenceLinearMap I g h x := by
  simp only [differenceLinearMap_apply]
  simpa only [algebraMap_smul] using
    differenceClass_mul I (algebraMap A B) g.toRingHom h x y

/-- The derivation into `I / I²` determined by the difference between the structural algebra map
and another algebra map. -/
@[stacks 0E1Y "parallel-map difference derivation"]
def differenceDerivation (I : Ideal B) (g : A →ₐ[R] B)
    (h : ∀ x : A, algebraMap A B x - g x ∈ I) :
    Derivation R A I.Cotangent :=
  Derivation.mk' (differenceLinearMap I g h)
    (differenceLinearMap_leibniz I g h)

/-- The linear map underlying the difference derivation is `differenceLinearMap`. -/
@[simp]
theorem differenceDerivation_toLinearMap (I : Ideal B) (g : A →ₐ[R] B)
    (h : ∀ x : A, algebraMap A B x - g x ∈ I) :
    (differenceDerivation I g h : A →ₗ[R] I.Cotangent) =
      differenceLinearMap I g h := rfl

/-- The difference derivation evaluates to the corresponding cotangent difference class. -/
@[simp]
theorem differenceDerivation_apply (I : Ideal B) (g : A →ₐ[R] B)
    (h : ∀ x : A, algebraMap A B x - g x ∈ I) (x : A) :
    differenceDerivation I g h x =
      differenceClass I (algebraMap A B) g.toRingHom h x :=
  differenceLinearMap_apply I g h x

variable {C : Type z} [Ring C]

/-- The cotangent-valued difference derivation for two maps that agree after a common target
homomorphism. -/
@[stacks 0E1Y "kernel-valued parallel-map difference derivation"]
def kernelDifferenceDerivation (q : B →+* C) (g : A →ₐ[R] B)
    (htarget : q.comp (algebraMap A B) = q.comp g.toRingHom) :
    Derivation R A (RingHom.ker q).Cotangent :=
  differenceDerivation (RingHom.ker q) g
    (RingHom.sub_mem_ker_of_comp_eq
      (algebraMap A B) g.toRingHom q htarget)

/-- The kernel-valued difference derivation evaluates to the class of the pointwise difference. -/
@[simp]
theorem kernelDifferenceDerivation_apply (q : B →+* C) (g : A →ₐ[R] B)
    (htarget : q.comp (algebraMap A B) = q.comp g.toRingHom) (x : A) :
    kernelDifferenceDerivation q g htarget x =
      differenceClass (RingHom.ker q) (algebraMap A B) g.toRingHom
        (RingHom.sub_mem_ker_of_comp_eq
          (algebraMap A B) g.toRingHom q htarget) x :=
  differenceDerivation_apply (RingHom.ker q) g _ x

end Ideal.Cotangent

-- The values and linear maps are explicit, and all algebraic laws are proved above.
