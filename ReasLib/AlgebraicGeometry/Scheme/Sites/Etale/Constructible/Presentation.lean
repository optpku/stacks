/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.FiniteSum
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u w

namespace CategoryTheory.Sheaf

noncomputable section

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [HasFiniteCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]
variable [∀ (n : ℕ) (F : Fin n → Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)),
  HasCoproduct F]
variable [HasCokernels (Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ))]

/-- A constructible étale module sheaf is exactly a cokernel of a morphism between finite
coproducts of regular constant sheaves extended by zero from quasi-compact and quasi-separated
étale objects. -/
theorem isConstructibleEtaleModule_iff_exists_cokernel
    (hExtension : ∀ (U : X.Etale) (P : U.left.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (@etaleRestriction U.left X U.hom U.prop).op.HasLeftKanExtension P)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) :
    IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) F ↔
      ∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale),
        (∀ i, CompactSpace (U i).left) ∧
          (∀ i, QuasiSeparatedSpace (U i).left) ∧
            (∀ k, CompactSpace (V k).left) ∧
              (∀ k, QuasiSeparatedSpace (V k).left) ∧
                ∃ (φ :
                    finiteExtensionByZeroSum (X := X) (Λ := Λ)
                        (h := fun k ↦ (V k).prop)
                        (hKan := fun k P ↦ hExtension (V k) P)
                        (fun k ↦ (V k).left) (fun k ↦ (V k).hom) ⟶
                    finiteExtensionByZeroSum (X := X) (Λ := Λ)
                        (h := fun i ↦ (U i).prop)
                        (hKan := fun i P ↦ hExtension (U i) P)
                        (fun i ↦ (U i).left) (fun i ↦ (U i).hom)),
                  Nonempty (F ≅ cokernel φ) := sorry

/-- A constructible étale module sheaf is exactly a cokernel of a morphism between finite
coproducts of regular constant sheaves extended by zero from affine étale objects. -/
theorem isConstructibleEtaleModule_iff_exists_cokernel_affine
    (hExtension : ∀ (U : X.Etale) (P : U.left.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (@etaleRestriction U.left X U.hom U.prop).op.HasLeftKanExtension P)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)) :
    IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) F ↔
      ∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale),
        (∀ i, IsAffine (U i).left) ∧
          (∀ k, IsAffine (V k).left) ∧
            ∃ (φ :
                finiteExtensionByZeroSum (X := X) (Λ := Λ)
                    (h := fun k ↦ (V k).prop)
                    (hKan := fun k P ↦ hExtension (V k) P)
                    (fun k ↦ (V k).left) (fun k ↦ (V k).hom) ⟶
                  finiteExtensionByZeroSum (X := X) (Λ := Λ)
                    (h := fun i ↦ (U i).prop)
                    (hKan := fun i P ↦ hExtension (U i) P)
                    (fun i ↦ (U i).left) (fun i ↦ (U i).hom)),
              Nonempty (F ≅ cokernel φ) := sorry

end

end CategoryTheory.Sheaf
