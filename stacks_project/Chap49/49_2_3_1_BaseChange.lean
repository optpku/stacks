/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.BaseChange

@[expose] public section

open AlgebraicGeometry
open scoped Algebra.DualModule TensorProduct TensorProduct.Right

universe u v

/- The compatibility bridge exposes the complete type of the promoted base-change map. -/
#check (Algebra.RelativeDualizingModule.baseChangeOf :
  ∀ (A A₁ : Type u) (B' B B₁' B₁ : Type v)
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
      (IsScalarTower.toAlgHom A B' B₁').toLinearMap),
    Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open
      →ₛₗ[algebraMap B B₁]
        Algebra.RelativeDualizingModule.of A₁ B₁' B₁ h_quasiFinite₁ h_open₁)

/- The compatibility bridge also exposes the pure-tensor computation law. -/
#check (Algebra.RelativeDualizingModule.baseChangeOf_tmul :
  ∀ (A A₁ : Type u) (B' B B₁' B₁ : Type v)
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
    (f : Module.Dual A B') (b : B),
    Algebra.RelativeDualizingModule.baseChangeOf A A₁ B' B B₁' B₁
        h_quasiFinite h_quasiFinite₁ h_open h_open₁ h_baseChange h_finiteModel
        (f ⊗ₜ[B'] b) =
      h_finiteModel.toDual f ⊗ₜ[B₁'] algebraMap B B₁ b)
