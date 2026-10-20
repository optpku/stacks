/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Bimodule.InternalHom
public import ReasLib.Algebra.Module.Bimodule.RelativeTensor.Map

/-!
# Tensor-Hom Currying for Algebra Bimodules

This file owns the universe-polymorphic concrete tensor-Hom equivalence for ordinary algebra
modules.  Its relative tensor quotient and instance-safe internal Hom live in independent leaves,
so consumers can import either construction without loading grading infrastructure.
-/

@[expose] public section

noncomputable section

namespace Module.Bimodule

universe i j u v w x y z t

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]

namespace TensorHom

open scoped _root_.RelativeTensor

variable {M : Type x} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
variable [IsScalarTower R Aᵐᵒᵖ M]
variable {N : Type y} [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
variable [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
variable [SMulCommClass A Bᵐᵒᵖ N]
variable {P : Type z} [AddCommGroup P] [Module R P] [Module Bᵐᵒᵖ P]
variable [IsScalarTower R Bᵐᵒᵖ P]

/-- Currying is additive in the second tensor variable. -/
theorem curryPairing_add_right (f : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P)
    (m : M) (n n' : N) :
    f (RelativeTensor.tmul (R := R) (A := A) m (n + n')) =
      f (RelativeTensor.tmul (R := R) (A := A) m n) +
        f (RelativeTensor.tmul (R := R) (A := A) m n') := sorry

/-- Currying is compatible with the right scalar action in the second tensor variable. -/
theorem curryPairing_smul_right (f : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P)
    (m : M) (b : Bᵐᵒᵖ) (n : N) :
    f (RelativeTensor.tmul (R := R) (A := A) m (b • n)) =
      b • f (RelativeTensor.tmul (R := R) (A := A) m n) := sorry

/-- Currying is additive in the first tensor variable. -/
theorem curryPairing_add_left (f : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P)
    (m m' : M) (n : N) :
    f (RelativeTensor.tmul (R := R) (A := A) (m + m') n) =
        f (RelativeTensor.tmul (R := R) (A := A) m n) +
        f (RelativeTensor.tmul (R := R) (A := A) m' n) := sorry

/-- The right-linear map obtained by fixing the first variable of a tensor map. -/
def curryLinearMap (f : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P) (m : M) : N →ₗ[Bᵐᵒᵖ] P where
  toFun := fun n => f (RelativeTensor.tmul (R := R) (A := A) m n)
  map_add' := by
    intro n n'
    exact curryPairing_add_right f m n n'
  map_smul' := by
    intro b n
    exact curryPairing_smul_right f m b n

/-- Currying is compatible with the left scalar action in the first tensor variable. -/
theorem curryPairing_smul_left (f : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P)
    (a : Aᵐᵒᵖ) (m : M) :
    InternalHom.ofLinearMap (B := B) (curryLinearMap f (a • m)) =
      a • InternalHom.ofLinearMap (B := B) (curryLinearMap f m) := sorry

/-- Curry a right `B`-linear map from the concrete relative tensor quotient. -/
@[stacks 09LN "ordinary tensor-Hom currying"]
def curry (f : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P) :
    M →ₗ[Aᵐᵒᵖ] InternalHom B N P where
  toFun := fun m ↦ InternalHom.ofLinearMap (B := B) (curryLinearMap f m)
  map_add' := fun m m' => by
    ext n
    exact curryPairing_add_left f m m' n
  map_smul' := fun a m => curryPairing_smul_left f a m

/-- The bilinear pairing underlying a curried right `A`-linear internal-Hom map. -/
theorem uncurryPairing_add
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P) (m m' : M) :
    (g (m + m')).toLinearMap.restrictScalars R =
      (g m).toLinearMap.restrictScalars R + (g m').toLinearMap.restrictScalars R := sorry

/-- The bilinear pairing underlying a curried map is `R`-linear in the first variable. -/
theorem uncurryPairing_smul
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P) (r : R) (m : M) :
    (g (r • m)).toLinearMap.restrictScalars R =
      r • (g m).toLinearMap.restrictScalars R := sorry

/-- The bilinear pairing underlying a curried right `A`-linear internal-Hom map. -/
def uncurryPairing
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P) :
    M →ₗ[R] N →ₗ[R] P where
  toFun := fun m ↦ (g m).toLinearMap.restrictScalars R
  map_add' := uncurryPairing_add g
  map_smul' := uncurryPairing_smul g

/-- The pairing underlying a curried internal-Hom map is balanced over `A`. -/
theorem uncurryPairing_balanced
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P) :
    RelativeTensor.IsBalanced (R := R) (A := A) (M := M) (N := N)
      (uncurryPairing (R := R) (A := A) (B := B) g) := sorry

/-- Descend a curried map to an `R`-linear map from the relative tensor quotient. -/
def uncurryLinear
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P) :
    (M ⊗ᵣ[R, A] N) →ₗ[R] P :=
  RelativeTensor.lift (R := R) (A := A) (M := M) (N := N)
    (uncurryPairing (R := R) (A := A) (B := B) g)
    (uncurryPairing_balanced (R := R) (A := A) (B := B) g)

/-- The descended uncurrying map is additive. -/
theorem uncurryLinear_add
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P)
    (x y : M ⊗ᵣ[R, A] N) :
    uncurryLinear (R := R) (A := A) (B := B) g (x + y) =
      uncurryLinear (R := R) (A := A) (B := B) g x +
        uncurryLinear (R := R) (A := A) (B := B) g y := sorry

/-- The descended uncurrying map is right-`B`-linear. -/
theorem uncurryLinear_smul
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P)
    (b : Bᵐᵒᵖ) (x : M ⊗ᵣ[R, A] N) :
    uncurryLinear (R := R) (A := A) (B := B) g (b • x) =
      b • uncurryLinear (R := R) (A := A) (B := B) g x := sorry

/-- Uncurry a right `A`-linear map into internal Hom to a right `B`-linear map from the
relative tensor quotient. -/
@[stacks 09LN "ordinary tensor-Hom uncurrying"]
def uncurry
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P) :
    (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P where
  toFun := uncurryLinear (R := R) (A := A) (B := B) g
  map_add' := uncurryLinear_add g
  map_smul' := uncurryLinear_smul g

/-- Currying evaluates on a pair by evaluating the original map on its pure tensor. -/
@[simp, stacks 09LN "evaluation formula for ordinary tensor-Hom currying"]
theorem curry_apply (f : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P) (m : M) (n : N) :
    curry f m n = f (RelativeTensor.tmul (R := R) (A := A) m n) := sorry

/-- Uncurrying evaluates on a pure tensor by applying the curried map twice. -/
@[simp, stacks 09LN "evaluation formula for ordinary tensor-Hom uncurrying"]
theorem uncurry_tmul
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P)
    (m : M) (n : N) :
    uncurry g (RelativeTensor.tmul (R := R) (A := A) m n) = g m n := sorry

/-- Currying is additive as a map between right-linear Hom spaces. -/
theorem curry_add
    (f f' : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P) :
    curry (f + f') = curry f + curry f' := sorry

/-- Currying is `R`-linear. -/
theorem curry_smul (r : R) (f : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P) :
    curry (r • f) = r • curry f := sorry

/-- Uncurrying a curry returns the original tensor map. -/
theorem uncurry_curry (f : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P) :
    uncurry (R := R) (A := A) (B := B) (curry (R := R) (A := A) (B := B) f) = f := sorry

/-- Currying an uncurried map returns the original internal-Hom map. -/
theorem curry_uncurry (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P) :
    curry (R := R) (A := A) (B := B)
        (uncurry (R := R) (A := A) (B := B) g) = g := sorry

/-- Maps from the concrete relative tensor quotient are canonically equivalent to right `A`-linear
maps into the right `B`-linear internal Hom. -/
@[stacks 09LN "ordinary tensor-Hom adjunction"]
def equiv :
    ((M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P) ≃ₗ[R]
      (M →ₗ[Aᵐᵒᵖ] InternalHom B N P) where
  toFun := curry
  invFun := uncurry
  map_add' := curry_add
  map_smul' := curry_smul
  left_inv := uncurry_curry
  right_inv := curry_uncurry

/-- The ordinary tensor-Hom equivalence is characterized on pure tensors by evaluation. -/
@[simp, stacks 09LN "pure-tensor formula for the ordinary tensor-Hom equivalence"]
theorem equiv_apply (f : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P) (m : M) (n : N) :
    equiv (R := R) (A := A) (B := B) f m n =
      f (RelativeTensor.tmul (R := R) (A := A) m n) := sorry

/-- The inverse ordinary tensor-Hom equivalence is characterized on pure tensors by evaluation. -/
@[simp, stacks 09LN "pure-tensor formula for the inverse ordinary tensor-Hom equivalence"]
theorem equiv_symm_apply
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P)
    (m : M) (n : N) :
    (equiv (R := R) (A := A) (B := B)).symm g
        (RelativeTensor.tmul (R := R) (A := A) m n) = g m n := sorry

variable {Q : Type t} [AddCommGroup Q] [Module R Q] [Module Bᵐᵒᵖ Q]
variable [IsScalarTower R Bᵐᵒᵖ Q]

/-- Tensor-Hom currying is natural in the target right `B`-module. -/
theorem equiv_natural_target (h : P →ₗ[Bᵐᵒᵖ] Q)
    (f : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P) :
    equiv (R := R) (A := A) (B := B) (h.comp f) =
      (InternalHom.mapTarget (A := A) h).comp
        (equiv (R := R) (A := A) (B := B) f) := sorry

/-- Tensor-Hom uncurrying is natural in the target right `B`-module. -/
theorem equiv_symm_natural_target (h : P →ₗ[Bᵐᵒᵖ] Q)
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P) :
    (equiv (R := R) (A := A) (B := B) (P := Q)).symm
        ((InternalHom.mapTarget (A := A) h).comp g) =
      h.comp ((equiv (R := R) (A := A) (B := B) (P := P)).symm g) := sorry

variable {N' : Type i} [AddCommGroup N'] [Module R N'] [Module A N'] [Module Bᵐᵒᵖ N']
variable [IsScalarTower R A N'] [IsScalarTower R Bᵐᵒᵖ N']
variable [SMulCommClass A Bᵐᵒᵖ N']

/-- Tensor-Hom currying is natural contravariantly in the middle bimodule. -/
theorem equiv_natural_middle
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (f : RelativeTensor.Product (R := R) (A := A) (M := M) (N := N') →ₗ[Bᵐᵒᵖ] P) :
    equiv (R := R) (A := A) (B := B) (N := N)
        (f.comp (RelativeTensor.mapRight (R := R) (A := A) (B := B) (M := M) g)) =
      (InternalHom.mapSource (R := R) (A := A) (B := B) (P := P) g).comp
        (equiv (R := R) (A := A) (B := B) (N := N') f) := sorry

/-- Tensor-Hom uncurrying is natural contravariantly in the middle bimodule. -/
theorem equiv_symm_natural_middle
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N' P) :
    (equiv (R := R) (A := A) (B := B) (N := N)).symm
        ((InternalHom.mapSource (R := R) (A := A) (B := B) (P := P) f).comp g) =
      ((equiv (R := R) (A := A) (B := B) (N := N')).symm g).comp
        (RelativeTensor.mapRight (R := R) (A := A) (B := B) (M := M) f) := sorry

variable {M' : Type j} [AddCommGroup M'] [Module R M'] [Module Aᵐᵒᵖ M']
variable [IsScalarTower R Aᵐᵒᵖ M']

/-- Tensor-Hom currying is natural contravariantly in the first right `A`-module. -/
theorem equiv_natural_left (g : M' →ₗ[Aᵐᵒᵖ] M)
    (f : (M ⊗ᵣ[R, A] N) →ₗ[Bᵐᵒᵖ] P) :
    equiv (R := R) (A := A) (B := B)
        (f.comp (RelativeTensor.mapLeft (R := R) (A := A) (B := B) (N := N) g)) =
      (equiv (R := R) (A := A) (B := B) f).comp g := sorry

/-- Tensor-Hom uncurrying is natural contravariantly in the first right `A`-module. -/
theorem equiv_symm_natural_left (f : M' →ₗ[Aᵐᵒᵖ] M)
    (g : M →ₗ[Aᵐᵒᵖ] InternalHom B N P) :
    (equiv (R := R) (A := A) (B := B) (M := M')).symm (g.comp f) =
      ((equiv (R := R) (A := A) (B := B) (M := M)).symm g).comp
        (RelativeTensor.mapLeft (R := R) (A := A) (B := B) (N := N) f) := sorry

/-- Tensor-Hom currying is simultaneously contravariantly natural in the first and middle
variables and covariantly natural in the target. -/
@[stacks 09LN "naturality of the ordinary tensor-Hom adjunction"]
theorem equiv_natural (f : M' →ₗ[Aᵐᵒᵖ] M)
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (h : P →ₗ[Bᵐᵒᵖ] Q)
    (φ : RelativeTensor.Product (R := R) (A := A) (M := M) (N := N') →ₗ[Bᵐᵒᵖ] P) :
    equiv (R := R) (A := A) (B := B) (M := M') (N := N) (P := Q)
        (h.comp (φ.comp
          (RelativeTensor.map (R := R) (A := A) (B := B) f g))) =
      (InternalHom.map (R := R) (A := A) (B := B) g h).comp
        ((equiv (R := R) (A := A) (B := B) φ).comp f) := sorry

/-- Tensor-Hom uncurrying is simultaneously contravariantly natural in the first and middle
variables and covariantly natural in the target. -/
@[stacks 09LN "inverse naturality of the ordinary tensor-Hom adjunction"]
theorem equiv_symm_natural (f : M' →ₗ[Aᵐᵒᵖ] M)
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (h : P →ₗ[Bᵐᵒᵖ] Q)
    (φ : M →ₗ[Aᵐᵒᵖ] InternalHom B N' P) :
    (equiv (R := R) (A := A) (B := B) (M := M') (N := N) (P := Q)).symm
        ((InternalHom.map (R := R) (A := A) (B := B) g h).comp (φ.comp f)) =
      h.comp (((equiv (R := R) (A := A) (B := B)
        (M := M) (N := N') (P := P)).symm φ).comp
          (RelativeTensor.map (R := R) (A := A) (B := B) f g)) := sorry

end TensorHom

end Module.Bimodule
