/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Module.RelativeDualizing.BaseChange

@[expose] public section

open AlgebraicGeometry
open scoped Algebra TensorProduct

universe u v

namespace Algebra.RelativeDualizingModule

/-- The map on scalar extensions induced by the chosen-model base-change map. -/
noncomputable def baseChangeTensorOf
    (A A₁ : Type u) (B' B B₁' B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing B'] [CommRing B]
    [CommRing B₁'] [CommRing B₁]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A₁ B₁'] [Algebra B₁' B₁] [Algebra A₁ B₁]
    [IsScalarTower A₁ B₁' B₁]
    [Algebra A A₁] [Algebra B' B₁'] [Algebra B B₁]
    [Algebra A B₁'] [IsScalarTower A B' B₁'] [IsScalarTower A A₁ B₁']
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [Algebra B' B₁] [IsScalarTower B' B B₁] [IsScalarTower B' B₁' B₁]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A₁ B₁)
    [Module.Finite A B'] [Module.Finite A₁ B₁']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁))))
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' B₁').toLinearMap) :
    B₁ ⊗[B] RelativeDualizingModule.of A B' B h_quasiFinite h_open →ₗ[B₁]
      RelativeDualizingModule.of A₁ B₁' B₁ h_quasiFinite₁ h_open₁ where
  toFun := TensorProduct.liftAddHom
    ({ toFun := fun b₁ ↦
        { toFun := fun x ↦ b₁ •
            baseChangeOf A A₁ B' B B₁' B₁ h_quasiFinite h_quasiFinite₁
              h_open h_open₁ h_baseChange h_finiteModel x
          map_zero' := by simp
          map_add' := by
            intro x y
            simp }
       map_zero' := by
         ext x
         simp
       map_add' := by
         intro b₁ c₁
         ext x
         simp [add_smul] } :
      B₁ →+
        (RelativeDualizingModule.of A B' B h_quasiFinite h_open →+
          RelativeDualizingModule.of A₁ B₁' B₁ h_quasiFinite₁ h_open₁))
    (by
      intro r b₁ x
      simp [Algebra.smul_def, smul_smul, mul_comm])
  map_add' := by
    intro x y
    exact map_add _ x y
  map_smul' := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul b₁ x =>
        simp [TensorProduct.smul_tmul', smul_smul]

/-- On a pure tensor, `baseChangeTensorOf` is scalar multiplication of the
chosen-model base-change map. -/
theorem baseChangeTensorOf_tmul
    (A A₁ : Type u) (B' B B₁' B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing B'] [CommRing B]
    [CommRing B₁'] [CommRing B₁]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A₁ B₁'] [Algebra B₁' B₁] [Algebra A₁ B₁]
    [IsScalarTower A₁ B₁' B₁]
    [Algebra A A₁] [Algebra B' B₁'] [Algebra B B₁]
    [Algebra A B₁'] [IsScalarTower A B' B₁'] [IsScalarTower A A₁ B₁']
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [Algebra B' B₁] [IsScalarTower B' B B₁] [IsScalarTower B' B₁' B₁]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A₁ B₁)
    [Module.Finite A B'] [Module.Finite A₁ B₁']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁))))
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' B₁').toLinearMap)
    (b₁ : B₁) (x : RelativeDualizingModule.of A B' B h_quasiFinite h_open) :
    baseChangeTensorOf A A₁ B' B B₁' B₁ h_quasiFinite h_quasiFinite₁
        h_open h_open₁ h_baseChange h_finiteModel (b₁ ⊗ₜ[B] x) =
      b₁ • baseChangeOf A A₁ B' B B₁' B₁ h_quasiFinite h_quasiFinite₁
        h_open h_open₁ h_baseChange h_finiteModel x := by
  rfl

/-- If `A → A₁` is flat, `baseChangeTensorOf` is bijective and hence induces
the base-change isomorphism. The tensor product is written with `B₁` on the
left, the canonical scalar-extension orientation in Lean. -/
theorem baseChangeTensorOf_bijective
    (A A₁ : Type u) (B' B B₁' B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing B'] [CommRing B]
    [CommRing B₁'] [CommRing B₁]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A₁ B₁'] [Algebra B₁' B₁] [Algebra A₁ B₁]
    [IsScalarTower A₁ B₁' B₁]
    [Algebra A A₁] [Algebra B' B₁'] [Algebra B B₁]
    [Algebra A B₁'] [IsScalarTower A B' B₁'] [IsScalarTower A A₁ B₁']
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [Algebra B' B₁] [IsScalarTower B' B B₁] [IsScalarTower B' B₁' B₁]
    [Module.Flat A A₁]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A₁ B₁)
    [Module.Finite A B'] [Module.Finite A₁ B₁']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁))))
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' B₁').toLinearMap) :
    Function.Bijective
      (baseChangeTensorOf A A₁ B' B B₁' B₁ h_quasiFinite h_quasiFinite₁
        h_open h_open₁ h_baseChange h_finiteModel) := sorry

/-- If `A → B` is flat, the relative-dualizing base-change map is bijective.
The tensor product uses the canonical scalar-extension orientation. -/
theorem baseChangeTensorOf_bijective_of_flat
    (A A₁ : Type u) (B' B B₁' B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing B'] [CommRing B]
    [CommRing B₁'] [CommRing B₁]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [Algebra A₁ B₁'] [Algebra B₁' B₁] [Algebra A₁ B₁]
    [IsScalarTower A₁ B₁' B₁]
    [Algebra A A₁] [Algebra B' B₁'] [Algebra B B₁]
    [Algebra A B₁'] [IsScalarTower A B' B₁'] [IsScalarTower A A₁ B₁']
    [Algebra A B₁] [IsScalarTower A B B₁] [IsScalarTower A A₁ B₁]
    [Algebra B' B₁] [IsScalarTower B' B B₁] [IsScalarTower B' B₁' B₁]
    [Module.Flat A B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    (h_quasiFinite₁ : Algebra.FiniteType.QuasiFinite A₁ B₁)
    [Module.Finite A B'] [Module.Finite A₁ B₁']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (h_open₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B₁' B₁))))
    (h_baseChange : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B B₁).toLinearMap)
    (h_finiteModel : IsBaseChange A₁
      (IsScalarTower.toAlgHom A B' B₁').toLinearMap) :
    Function.Bijective
      (baseChangeTensorOf A A₁ B' B B₁' B₁ h_quasiFinite h_quasiFinite₁
        h_open h_open₁ h_baseChange h_finiteModel) := sorry

end Algebra.RelativeDualizingModule
