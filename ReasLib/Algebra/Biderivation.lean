/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Biderivations into bimodules

An `A`-biderivation of an `A`-algebra `B` with values in a `(B, B)`-bimodule `M` over `A`
is an `A`-linear map `B → M` satisfying the two-sided Leibniz identity.
-/

@[expose] public section

universe u v w

/-- An `A`-biderivation of `B` with values in a `(B, B)`-bimodule `M` over `A` is an
`A`-linear map `B → M` satisfying the Leibniz identity with respect to the left `B`-action
and the opposite right `B`-action. -/
structure Biderivation (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [Module Bᵐᵒᵖ M]
    [IsScalarTower A B M] [IsScalarTower A Bᵐᵒᵖ M]
    [SMulCommClass B Bᵐᵒᵖ M]
    extends B →ₗ[A] M where
  /-- Leibniz identity for the left `B`-action and the opposite right `B`-action. -/
  leibniz' (x y : B) :
    toLinearMap (x * y) = x • toLinearMap y + MulOpposite.op y • toLinearMap x

/-- The underlying `A`-linear map of an `A`-biderivation. -/
add_decl_doc Biderivation.toLinearMap

namespace Biderivation

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module A M] [Module B M] [Module Bᵐᵒᵖ M]
variable [IsScalarTower A B M] [IsScalarTower A Bᵐᵒᵖ M]
variable [SMulCommClass B Bᵐᵒᵖ M]

/-- Build an `A`-biderivation from an `A`-linear map satisfying the bimodule Leibniz identity. -/
def ofLinearMap (f : B →ₗ[A] M)
    (hleibniz : ∀ x y : B, f (x * y) = x • f y + MulOpposite.op y • f x) :
    Biderivation A B M where
  toLinearMap := f
  leibniz' := hleibniz

/-- Evaluation of an `A`-biderivation as a map `B → M`. -/
def apply (D : Biderivation A B M) : B → M :=
  D.toLinearMap

/-- Evaluating the smart constructor recovers the original `A`-linear map. -/
theorem ofLinearMap_apply (f : B →ₗ[A] M)
    (hleibniz : ∀ x y : B, f (x * y) = x • f y + MulOpposite.op y • f x) (x : B) :
    (ofLinearMap f hleibniz).apply x = f x := rfl

/-- The underlying linear map of the smart constructor is the original map. -/
theorem ofLinearMap_toLinearMap (f : B →ₗ[A] M)
    (hleibniz : ∀ x y : B, f (x * y) = x • f y + MulOpposite.op y • f x) :
    (ofLinearMap f hleibniz).toLinearMap = f := rfl

/-- An `A`-biderivation satisfies the bimodule Leibniz identity. -/
theorem leibniz (D : Biderivation A B M) (x y : B) :
    D.apply (x * y) = x • D.apply y + MulOpposite.op y • D.apply x :=
  D.leibniz' x y

/-- An `A`-biderivation respects scalar multiplication and satisfies the bimodule Leibniz identity. -/
theorem spec (D : Biderivation A B M) :
    (∀ a : A, ∀ x : B, D.apply (a • x) = a • D.apply x) ∧
      (∀ x y : B, D.apply (x * y) = x • D.apply y + MulOpposite.op y • D.apply x) :=
  ⟨fun a x => D.toLinearMap.map_smul a x, D.leibniz⟩

/-- An `A`-biderivation vanishes at `1`. -/
theorem map_one_eq_zero (D : Biderivation A B M) : D.apply 1 = 0 := by
  apply (add_eq_left (a := D.apply 1)).mp
  simpa only [one_mul, MulOpposite.op_one, one_smul] using (D.leibniz 1 1).symm

/-- An `A`-biderivation vanishes on the structure map `A → B`. -/
theorem map_algebraMap (D : Biderivation A B M) (a : A) :
    D.apply (algebraMap A B a) = 0 := by
  calc
    D.apply (algebraMap A B a) = D.apply (a • (1 : B)) := by
      rw [Algebra.algebraMap_eq_smul_one]
    _ = a • D.apply 1 := D.toLinearMap.map_smul a 1
    _ = 0 := by rw [D.map_one_eq_zero, smul_zero]

/-- Two `A`-biderivations agreeing as maps `B → M` are equal. -/
theorem ext {D1 D2 : Biderivation A B M} (h : ∀ x : B, D1.apply x = D2.apply x) :
    D1 = D2 := by
  cases D1 with
  | mk f hf =>
    cases D2 with
    | mk g hg =>
      have hfg : f = g := LinearMap.ext h
      cases hfg
      rfl

/-- The zero `A`-linear map satisfies the bimodule Leibniz identity. -/
theorem zero_leibniz (x y : B) :
    (0 : B →ₗ[A] M) (x * y) =
      x • (0 : B →ₗ[A] M) y + MulOpposite.op y • (0 : B →ₗ[A] M) x := by
  simp

/-- The zero `A`-biderivation. -/
def zero : Biderivation A B M :=
  ofLinearMap 0 zero_leibniz

/-- The zero `A`-biderivation evaluates to `0`. -/
theorem zero_apply (x : B) : (zero : Biderivation A B M).apply x = 0 := rfl

end Biderivation
