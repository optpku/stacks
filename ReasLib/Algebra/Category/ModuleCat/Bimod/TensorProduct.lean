/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.Algebra.Module.Bimodule.Hom

/-!
# Tensor-product coefficient modules

This file restricts modules over a tensor-product algebra to the commuting module actions used by
the concrete bimodule presentation.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Module.Bimodule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]

/-- The explicit carrier used when a module over `A ⊗[R] Bᵐᵒᵖ` is viewed as an `(A, B)`-bimodule. -/
def TensorProductModule (K : Type max v w u)
    [AddCommGroup K] [Module (A ⊗[R] Bᵐᵒᵖ) K] : Type max v w u :=
  ULift.{0} K

namespace TensorProductModule

variable {K : Type max v w u} [AddCommGroup K]
  [Module (A ⊗[R] Bᵐᵒᵖ) K]

/-- The additive structure on a restricted tensor-product module carrier. -/
instance instAddCommGroup : AddCommGroup (TensorProductModule (R := R) (A := A) (B := B) K) :=
  (Equiv.ulift : TensorProductModule (R := R) (A := A) (B := B) K ≃ K).addCommGroup

/-- The tensor-product algebra action on the restricted carrier. -/
instance instModuleCoeff : Module (A ⊗[R] Bᵐᵒᵖ)
    (TensorProductModule (R := R) (A := A) (B := B) K) :=
  (Equiv.ulift : TensorProductModule (R := R) (A := A) (B := B) K ≃ K).module _

/-- The induced `R`-module structure on a restricted tensor-product module carrier. -/
instance instModuleBase : Module R
    (TensorProductModule (R := R) (A := A) (B := B) K) :=
  Module.compHom _ (algebraMap R (A ⊗[R] Bᵐᵒᵖ))

/-- The induced left `A`-module structure on a restricted tensor-product module carrier. -/
instance instModuleLeft : Module A
    (TensorProductModule (R := R) (A := A) (B := B) K) :=
  Module.compHom _
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := Bᵐᵒᵖ)).toRingHom

/-- The induced right `B`-module structure on a restricted tensor-product module carrier. -/
instance instModuleRight : Module Bᵐᵒᵖ
    (TensorProductModule (R := R) (A := A) (B := B) K) :=
  Module.compHom _ (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := Bᵐᵒᵖ)).toRingHom

/-- The scalar tower from `R` through `A` on a restricted tensor-product module carrier. -/
instance instIsScalarTowerLeft : IsScalarTower R A
    (TensorProductModule (R := R) (A := A) (B := B) K) := by
  constructor
  intro r a k
  change (Algebra.TensorProduct.includeLeft (R := R) (S := R)
    (A := A) (B := Bᵐᵒᵖ) (r • a)) • k =
      (algebraMap R (A ⊗[R] Bᵐᵒᵖ) r) •
        ((Algebra.TensorProduct.includeLeft (R := R) (S := R)
          (A := A) (B := Bᵐᵒᵖ) a) • k)
  rw [map_smul, Algebra.smul_def, mul_smul]

/-- The scalar tower from `R` through `Bᵐᵒᵖ` on a restricted tensor-product module carrier. -/
instance instIsScalarTowerRight : IsScalarTower R Bᵐᵒᵖ
    (TensorProductModule (R := R) (A := A) (B := B) K) := by
  constructor
  intro r b k
  change (Algebra.TensorProduct.includeRight (R := R)
    (A := A) (B := Bᵐᵒᵖ) (r • b)) • k =
      (algebraMap R (A ⊗[R] Bᵐᵒᵖ) r) •
        ((Algebra.TensorProduct.includeRight (R := R)
          (A := A) (B := Bᵐᵒᵖ) b) • k)
  rw [map_smul, Algebra.smul_def, mul_smul]

/-- The left and right actions on a restricted tensor-product module commute. -/
instance instSMulCommClass : SMulCommClass A Bᵐᵒᵖ
    (TensorProductModule (R := R) (A := A) (B := B) K) := by
  constructor
  intro a b k
  change (Algebra.TensorProduct.includeLeft (R := R) (S := R)
    (A := A) (B := Bᵐᵒᵖ) a) •
      ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := Bᵐᵒᵖ) b) • k) =
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := Bᵐᵒᵖ) b) •
      ((Algebra.TensorProduct.includeLeft (R := R) (S := R)
        (A := A) (B := Bᵐᵒᵖ) a) • k)
  rw [← mul_smul, ← mul_smul]
  simp only [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The left action on a restricted tensor-product module is induced by the tensor-product action. -/
theorem smul_left (a : A) (k : TensorProductModule (R := R) (A := A) (B := B) K) :
    a • k = (Algebra.TensorProduct.includeLeft (R := R) (S := R)
      (A := A) (B := Bᵐᵒᵖ) a) • k := rfl

/-- The right action on a restricted tensor-product module is induced by the tensor-product action. -/
theorem smul_right (b : Bᵐᵒᵖ) (k : TensorProductModule (R := R) (A := A) (B := B) K) :
    b • k = (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := Bᵐᵒᵖ) b) • k := rfl

variable {K' : Type max v w u} [AddCommGroup K'] [Module (A ⊗[R] Bᵐᵒᵖ) K']

/-- The additive map induced on the restricted carriers by a tensor-product-linear map. -/
def mapAddHom (f : K →ₗ[A ⊗[R] Bᵐᵒᵖ] K') :
    TensorProductModule (R := R) (A := A) (B := B) K →+
      TensorProductModule (R := R) (A := A) (B := B) K' :=
  ((Equiv.ulift : TensorProductModule (R := R) (A := A) (B := B) K' ≃ K').addEquiv.symm.toAddMonoidHom.comp
      f.toAddMonoidHom).comp
    (Equiv.ulift : TensorProductModule (R := R) (A := A) (B := B) K ≃ K).addEquiv.toAddMonoidHom

/-- Lifting a tensor-product-linear map preserves the restricted left action. -/
theorem map_smul_left (f : K →ₗ[A ⊗[R] Bᵐᵒᵖ] K') (a : A)
    (k : TensorProductModule (R := R) (A := A) (B := B) K) :
    mapAddHom f (a • k) = a • mapAddHom f k := by
  change ULift.up (f ((Algebra.TensorProduct.includeLeft (R := R) (S := R)
    (A := A) (B := Bᵐᵒᵖ) a) • k.down)) =
      ULift.up ((Algebra.TensorProduct.includeLeft (R := R) (S := R)
        (A := A) (B := Bᵐᵒᵖ) a) • f k.down)
  exact congrArg ULift.up (f.map_smul _ k.down)

/-- Lifting a tensor-product-linear map preserves the restricted right action. -/
theorem map_smul_right (f : K →ₗ[A ⊗[R] Bᵐᵒᵖ] K') (b : Bᵐᵒᵖ)
    (k : TensorProductModule (R := R) (A := A) (B := B) K) :
    mapAddHom f (b • k) = b • mapAddHom f k := by
  change ULift.up (f ((Algebra.TensorProduct.includeRight (R := R)
    (A := A) (B := Bᵐᵒᵖ) b) • k.down)) =
      ULift.up ((Algebra.TensorProduct.includeRight (R := R)
        (A := A) (B := Bᵐᵒᵖ) b) • f k.down)
  exact congrArg ULift.up (f.map_smul _ k.down)

/-- A tensor-product-linear map restricts to a bimodule morphism on the lifted carriers. -/
def toHom (f : K →ₗ[A ⊗[R] Bᵐᵒᵖ] K') :
    Hom (R := R) (A := A) (B := B)
      (N := TensorProductModule (R := R) (A := A) (B := B) K)
      (N' := TensorProductModule (R := R) (A := A) (B := B) K') :=
  let g : TensorProductModule (R := R) (A := A) (B := B) K →ₗ[Bᵐᵒᵖ]
      TensorProductModule (R := R) (A := A) (B := B) K' :=
    { __ := mapAddHom f
      map_smul' := map_smul_right f }
  ⟨g, map_smul_left f⟩

/-- The underlying function of the restricted bimodule map is the original map on lifted inputs. -/
@[simp]
theorem toHom_apply (f : K →ₗ[A ⊗[R] Bᵐᵒᵖ] K') (k : K) :
    toHom (R := R) (A := A) (B := B) f ⟨k⟩ = ⟨f k⟩ := rfl

end TensorProductModule

end Module.Bimodule
