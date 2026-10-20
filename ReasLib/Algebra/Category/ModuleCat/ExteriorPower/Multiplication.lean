/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication of exterior powers in `ModuleCat`

The internal grading of `ExteriorAlgebra R M` supplies heterogeneous multiplication
`Λ^n(M) × Λ^m(M) → Λ^(n + m)(M)`.  This file bundles it as a morphism from the tensor
product and records the API needed by graded algebras and Koszul complexes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u v

namespace ModuleCat.exteriorPower

variable {R : Type u} [CommRing R]

/-- Heterogeneous multiplication between two degrees of the exterior algebra. -/
def gradedMulFun (M : ModuleCat.{v} R) {n m : ℕ}
    (x : M.exteriorPower n) (y : M.exteriorPower m) :
    M.exteriorPower (n + m) :=
  @GradedMonoid.GMul.mul ℕ (fun i ↦ ⋀[R]^i M) _ _ _ _ x y

/-- Exterior-power multiplication is additive in its left argument. -/
theorem gradedMulFun_add_left (M : ModuleCat.{v} R) {n m : ℕ}
    (x x' : M.exteriorPower n) (y : M.exteriorPower m) :
    gradedMulFun M (x + x') y = gradedMulFun M x y + gradedMulFun M x' y := sorry

/-- Exterior-power multiplication is linear in its left argument. -/
theorem gradedMulFun_smul_left (M : ModuleCat.{v} R) {n m : ℕ}
    (r : R) (x : M.exteriorPower n) (y : M.exteriorPower m) :
    gradedMulFun M (r • x) y = r • gradedMulFun M x y := sorry

/-- Exterior-power multiplication is additive in its right argument. -/
theorem gradedMulFun_add_right (M : ModuleCat.{v} R) {n m : ℕ}
    (x : M.exteriorPower n) (y y' : M.exteriorPower m) :
    gradedMulFun M x (y + y') = gradedMulFun M x y + gradedMulFun M x y' := sorry

/-- Exterior-power multiplication is linear in its right argument. -/
theorem gradedMulFun_smul_right (M : ModuleCat.{v} R) {n m : ℕ}
    (r : R) (x : M.exteriorPower n) (y : M.exteriorPower m) :
    gradedMulFun M x (r • y) = r • gradedMulFun M x y := sorry

/-- The multiplication morphism `Λ^n(M) ⊗ Λ^m(M) ⟶ Λ^(n + m)(M)`. -/
@[stacks 01CF "exterior-power multiplication"]
noncomputable def mul (M : ModuleCat.{v} R) (n m : ℕ) :
    ModuleCat.of R (M.exteriorPower n ⊗[R] M.exteriorPower m) ⟶
      M.exteriorPower (n + m) :=
  ModuleCat.ofHom <| TensorProduct.lift <| LinearMap.mk₂ R (gradedMulFun M)
    (gradedMulFun_add_left M) (gradedMulFun_smul_left M)
    (gradedMulFun_add_right M) (gradedMulFun_smul_right M)

/-- Exterior-power multiplication evaluates on a pure tensor by heterogeneous multiplication. -/
@[simp]
theorem mul_tmul (M : ModuleCat.{v} R) (n m : ℕ)
    (x : M.exteriorPower n) (y : M.exteriorPower m) :
    mul M n m (x ⊗ₜ[R] y) = gradedMulFun M x y := sorry

/-- Exterior-power multiplication concatenates alternating generators. -/
@[simp]
theorem mul_tmul_mk (M : ModuleCat.{v} R) (n m : ℕ)
    (x : Fin n → M) (y : Fin m → M) :
    mul M n m (mk x ⊗ₜ[R] mk y) = mk (Fin.append x y) := sorry

/-- Exterior-power multiplication is natural in the module. -/
theorem mul_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) (n m : ℕ) :
    ModuleCat.ofHom (TensorProduct.map (map f n).hom (map f m).hom) ≫ mul N n m =
      mul M n m ≫ map f (n + m) := sorry

/-- The linear degree-zero unit of exterior-power multiplication, available independently of
the universe restriction on Mathlib's monoidal structure for `ModuleCat`. -/
@[stacks 01CF "universe-general degree-zero exterior unit"]
noncomputable def oneLinear (M : ModuleCat.{v} R) :
    R →ₗ[R] M.exteriorPower 0 :=
  (exteriorPower.zeroEquiv R M).symm.toLinearMap

/-- The linear degree-zero unit sends one to the empty exterior product. -/
@[simp]
theorem oneLinear_apply_one (M : ModuleCat.{v} R) :
    oneLinear M (1 : R) = mk (fun i : Fin 0 ↦ Fin.elim0 i) := sorry

/-- The degree-zero unit of exterior-power multiplication in the same-universe monoidal
category supported by Mathlib. -/
@[stacks 01CF "degree-zero unit for exterior multiplication"]
noncomputable def one (M : ModuleCat.{u} R) :
    𝟙_ (ModuleCat.{u} R) ⟶ M.exteriorPower 0 :=
  ModuleCat.ofHom (oneLinear M)

/-- The degree-zero unit is the empty exterior product. -/
@[simp]
theorem one_apply_one (M : ModuleCat.{u} R) :
    one M (1 : R) = mk (fun i : Fin 0 ↦ Fin.elim0 i) := sorry

/-- The degree-zero unit is natural in the module. -/
theorem one_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    one M ≫ map f 0 = one N := sorry

/-- The Koszul sign acting on the product of degrees `n` and `m`. -/
noncomputable def koszulSignHom (M : ModuleCat.{v} R) (n m : ℕ) :
    M.exteriorPower (n + m) ⟶ M.exteriorPower (n + m) :=
  ModuleCat.ofHom (((-1 : R) ^ (n * m)) •
    (LinearMap.id : M.exteriorPower (n + m) →ₗ[R] M.exteriorPower (n + m)))

/-- The Koszul-sign endomorphism acts by the scalar `(-1)^(n * m)`. -/
@[simp]
theorem koszulSignHom_apply (M : ModuleCat.{v} R) (n m : ℕ)
    (x : M.exteriorPower (n + m)) :
    koszulSignHom M n m x = (-1 : R) ^ (n * m) • x := sorry

/-- Heterogeneous exterior multiplication is associative before identifying the two
parenthesizations of the degree. -/
theorem gradedMulFun_assoc (M : ModuleCat.{v} R) {n m k : ℕ}
    (x : M.exteriorPower n) (y : M.exteriorPower m) (z : M.exteriorPower k) :
    HEq (gradedMulFun M (gradedMulFun M x y) z)
      (gradedMulFun M x (gradedMulFun M y z)) := sorry

/-- Heterogeneous exterior multiplication is graded commutative before identifying
`n + m` with `m + n`. -/
theorem gradedMulFun_comm (M : ModuleCat.{v} R) {n m : ℕ}
    (x : M.exteriorPower n) (y : M.exteriorPower m) :
    HEq (gradedMulFun M y x)
      ((-1 : R) ^ (n * m) • gradedMulFun M x y) := sorry

/-- Exterior-power multiplication is associative, with the degree reindexing made explicit. -/
theorem mul_assoc (M : ModuleCat.{u} R) (n m k : ℕ) :
    (α_ (M.exteriorPower n) (M.exteriorPower m) (M.exteriorPower k)).hom ≫
        (M.exteriorPower n ◁ mul M m k) ≫ mul M n (m + k) =
      (mul M n m ▷ M.exteriorPower k) ≫ mul M (n + m) k ≫
        eqToHom (congrArg (fun d ↦ M.exteriorPower d) (Nat.add_assoc n m k)) := sorry

/-- The degree-zero element is a left unit for exterior-power multiplication. -/
theorem one_mul (M : ModuleCat.{u} R) (n : ℕ) :
    (λ_ (M.exteriorPower n)).hom =
      (one M ▷ M.exteriorPower n) ≫ mul M 0 n ≫
        eqToHom (congrArg (fun d ↦ M.exteriorPower d) (Nat.zero_add n)) := sorry

/-- The degree-zero element is a right unit for exterior-power multiplication. -/
theorem mul_one (M : ModuleCat.{u} R) (n : ℕ) :
    (ρ_ (M.exteriorPower n)).hom =
      (M.exteriorPower n ◁ one M) ≫ mul M n 0 ≫
        eqToHom (congrArg (fun d ↦ M.exteriorPower d) (Nat.add_zero n)) := sorry

/-- Exterior-power multiplication is graded commutative with respect to the symmetric
braiding and the Koszul sign. -/
theorem mul_braiding (M : ModuleCat.{u} R) (n m : ℕ) :
    (β_ (M.exteriorPower n) (M.exteriorPower m)).hom ≫ mul M m n =
      mul M n m ≫ koszulSignHom M n m ≫
        eqToHom (congrArg (fun d ↦ M.exteriorPower d) (Nat.add_comm n m)) := sorry

end ModuleCat.exteriorPower

