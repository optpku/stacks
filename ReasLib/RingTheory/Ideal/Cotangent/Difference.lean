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
    f x - g x ∈ RingHom.ker q := sorry

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
      differenceClass I f g h x + differenceClass I f g h y := sorry

/-- Difference classes satisfy the Leibniz rule for the scalar action induced by the first map. -/
theorem differenceClass_mul (I : Ideal B) (f g : A →+* B)
    (h : ∀ x : A, f x - g x ∈ I) (x y : A) :
    differenceClass I f g h (x * y) =
      f x • differenceClass I f g h y +
        f y • differenceClass I f g h x := sorry

/-- Difference classes vanish after precomposition when the two maps agree there. -/
@[simp]
theorem differenceClass_comp_eq_zero {R : Type z} [CommSemiring R]
    (I : Ideal B) (a : R →+* A) (f g : A →+* B)
    (hcomp : f.comp a = g.comp a)
    (h : ∀ x : A, f x - g x ∈ I) (x : R) :
    differenceClass I f g h (a x) = 0 := sorry

variable {R : Type w} [CommSemiring R]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The two algebra maps become equal after quotienting by an ideal containing their pointwise
difference. -/
theorem differenceQuotientCompEq (I : Ideal B) (g : A →ₐ[R] B)
    (h : ∀ x : A, algebraMap A B x - g x ∈ I) :
    (Ideal.Quotient.mkₐ R I).comp (IsScalarTower.toAlgHom R A B) =
      (Ideal.Quotient.mkₐ R I).comp g := sorry

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
      differenceClass I (algebraMap A B) g.toRingHom h x := sorry

/-- The difference linear map satisfies the Leibniz rule. -/
theorem differenceLinearMap_leibniz (I : Ideal B) (g : A →ₐ[R] B)
    (h : ∀ x : A, algebraMap A B x - g x ∈ I) (x y : A) :
    differenceLinearMap I g h (x * y) =
      x • differenceLinearMap I g h y +
        y • differenceLinearMap I g h x := sorry

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
      differenceLinearMap I g h := sorry

/-- The difference derivation evaluates to the corresponding cotangent difference class. -/
@[simp]
theorem differenceDerivation_apply (I : Ideal B) (g : A →ₐ[R] B)
    (h : ∀ x : A, algebraMap A B x - g x ∈ I) (x : A) :
    differenceDerivation I g h x =
      differenceClass I (algebraMap A B) g.toRingHom h x := sorry

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
          (algebraMap A B) g.toRingHom q htarget) x := sorry

end Ideal.Cotangent

-- The values and linear maps are explicit; `sorryAx` is confined to algebraic law proofs.
