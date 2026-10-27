/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.TensorReconstruction
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Reconstruction of absolute morphisms from coherent tensor functors

Tensor-compatible realizations are compared over arbitrary bases. Existence
for right exact symmetric tensor functors is stated over the absolute integer base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Functor CategoryTheory.Limits CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids GroupoidsOver
open scoped Bicategory TensorProduct MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Coh

/-- Compatibility of an isomorphism
`t : F ⋙ forget₂ ≅ toQCoh ⋙ tensorPullback f` with the tensor and unit
constraints of `F` and of `f*`. -/
def IsTensorPullbackCohIso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {U : Over S} [IsAffine U.left]
    (F : Coh X ⥤ FGModuleCat.{u} Γ(U.left, ⊤))
    [F.Monoidal]
    {f : GroupoidsOver.slice U ⟶ X}
    (t : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤)) (ModuleCat.{u} Γ(U.left, ⊤)) ≅
      toQCoh ⋙ QCoh.tensorPullback f) : Prop :=
  (∀ A B : Coh X,
      ((forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
          (ModuleCat.{u} Γ(U.left, ⊤))).mapIso (Functor.Monoidal.μIso F A B).symm).hom ≫
        ModuleCat.ofHom
            (TensorProduct.map (t.hom.app A).hom (t.hom.app B).hom) ≫
          QCoh.tensorPullback_tensorInv f (toQCoh.obj A) (toQCoh.obj B) ≫
            (QCoh.tensorPullback f).map (tensor_toQCohIso A B).inv =
        t.hom.app (tensor A B)) ∧
    t.hom.app (structureSheaf X) ≫
        (QCoh.tensorPullback f).map (structureSheaf_toQCohIso X).hom ≫
          (QCoh.tensorPullback_unit f).hom =
      ((forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
          (ModuleCat.{u} Γ(U.left, ⊤))).mapIso
            (F.mapIso (structureSheafIsoTensorUnit X) ≪≫
              (Functor.Monoidal.εIso F).symm)).hom

/-- Tensor-pullback compatibility is exactly the tensor equation and the structure-module unit equation. -/
theorem IsTensorPullbackCohIso.iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {U : Over S} [IsAffine U.left]
    (F : Coh X ⥤ FGModuleCat.{u} Γ(U.left, ⊤))
    [F.Monoidal]
    {f : GroupoidsOver.slice U ⟶ X}
    (t : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤)) (ModuleCat.{u} Γ(U.left, ⊤)) ≅
      toQCoh ⋙ QCoh.tensorPullback f) :
    IsTensorPullbackCohIso F t ↔
      (∀ A B : Coh X,
          ((forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
              (ModuleCat.{u} Γ(U.left, ⊤))).mapIso (Functor.Monoidal.μIso F A B).symm).hom ≫
            ModuleCat.ofHom
                (TensorProduct.map (t.hom.app A).hom (t.hom.app B).hom) ≫
              QCoh.tensorPullback_tensorInv f (toQCoh.obj A) (toQCoh.obj B) ≫
                (QCoh.tensorPullback f).map (tensor_toQCohIso A B).inv =
            t.hom.app (tensor A B)) ∧
        t.hom.app (structureSheaf X) ≫
            (QCoh.tensorPullback f).map (structureSheaf_toQCohIso X).hom ≫
              (QCoh.tensorPullback_unit f).hom =
          ((forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
              (ModuleCat.{u} Γ(U.left, ⊤))).mapIso
                (F.mapIso (structureSheafIsoTensorUnit X) ≪≫
                  (Functor.Monoidal.εIso F).symm)).hom :=
  Iff.rfl

/-- Two tensor-compatible realizations of a monoidal functor on coherent modules
are related by a 2-arrow inducing their prescribed comparison. -/
theorem existsUnique_hom_of_rightExactTensor_spec
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsNoetherian X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {U : Over S} [IsAffine U.left]
    (F : Coh X ⥤ FGModuleCat.{u} Γ(U.left, ⊤))
    [F.Monoidal]
    {f f' : GroupoidsOver.slice U ⟶ X}
    (t : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤)) (ModuleCat.{u} Γ(U.left, ⊤)) ≅
      toQCoh ⋙ QCoh.tensorPullback f)
    (t' : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤)) (ModuleCat.{u} Γ(U.left, ⊤)) ≅
      toQCoh ⋙ QCoh.tensorPullback f')
    (ht : IsTensorPullbackCohIso F t)
    (ht' : IsTensorPullbackCohIso F t') :
    ∃ α : f ⟶ f',
      t ≪≫ isoWhiskerLeft toQCoh (QCoh.tensorPullbackIso α) = t' :=
  sorry

/-- A right exact symmetric tensor functor from coherent modules on a Noetherian
algebraic stack with affine diagonal to finite modules over a Noetherian affine
scheme is induced by an essentially unique absolute morphism. -/
theorem existsUnique_hom_of_rightExactTensor
    {X : GroupoidsOver (Spec (.of (ULift.{u} ℤ)))} [AlgebraicStack X]
    [IsNoetherian X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {U : Over (Spec (.of (ULift.{u} ℤ)))} [IsAffine U.left] [AlgebraicGeometry.IsNoetherian U.left]
    (F : Coh X ⥤ FGModuleCat.{u} Γ(U.left, ⊤))
    [F.Braided] [PreservesFiniteColimits F] :
    ∃ (f : GroupoidsOver.slice U ⟶ X)
      (t : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
            (ModuleCat.{u} Γ(U.left, ⊤)) ≅
          toQCoh ⋙ QCoh.tensorPullback f),
      IsTensorPullbackCohIso F t ∧
        ∀ (f' : GroupoidsOver.slice U ⟶ X)
          (t' : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
              (ModuleCat.{u} Γ(U.left, ⊤)) ≅
            toQCoh ⋙ QCoh.tensorPullback f'),
          IsTensorPullbackCohIso F t' →
            ∃ α : f ⟶ f',
              t ≪≫ isoWhiskerLeft toQCoh (QCoh.tensorPullbackIso α) = t' :=
  sorry
end AlgebraicGeometry.AlgebraicStack.Coh
