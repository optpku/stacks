/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import stacks_project.Chap103.Lemma_103_17_3_Coherent
public import stacks_project.Chap106.Lemma_106_16_1
public import stacks_project.Chap106.Lemma_106_16_7

/-!
# Reconstruction of morphisms from right exact tensor functors on coherent modules

A right exact tensor functor on coherent modules of a Noetherian algebraic
stack with affine diagonal, landing in finitely generated modules over a
Noetherian ring, is the restriction of the affine tensor pullback of a unique
morphism from an affine scheme.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Functor CategoryTheory.Limits CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids GroupoidsOver
open scoped Bicategory TensorProduct MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Coh

/-- The coherent structure sheaf `O_X`, as the unit module on the fppf ringed
site. -/
def structureSheaf {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsLocallyNoetherian X] : Coh X where
  obj := SheafOfModules.unit (GroupoidsOver.structureSheaf X)
  property := instIsCoherentUnit X

/-- The underlying module of `structureSheaf X` is the unit on `O_X`. -/
theorem structureSheaf_obj {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    (structureSheaf X).obj = SheafOfModules.unit (GroupoidsOver.structureSheaf X) :=
  sorry

/-- The image of the coherent structure sheaf under `qCohLift` is the
quasi-coherent structure sheaf. -/
def structureSheaf_qCohLiftIso {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    qCohLift.obj (structureSheaf X) ≅ QCoh.structureSheaf X :=
  isoMk (quasiCoherentModuleProperty X) (Iso.refl _)

/-- The image of `tensor A B` under `qCohLift` is the quasi-coherent tensor of
the images of `A` and `B`. -/
def tensor_qCohLiftIso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (A B : Coh X) :
    qCohLift.obj (tensor A B) ≅ QCoh.tensor (qCohLift.obj A) (qCohLift.obj B) :=
  isoMk (quasiCoherentModuleProperty X) (Iso.refl _)

/-- Compatibility of an isomorphism
`t : F ⋙ forget₂ ≅ qCohLift ⋙ tensorPullback f` with the tensor and unit
constraints of `F` and of `f*`. -/
def IsTensorPullbackCohIso {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {U : Over S} [IsAffine U.left]
    (F : Coh X ⥤ FGModuleCat.{u} Γ(U.left, ⊤))
    (h_tensor : ∀ A B : Coh X, F.obj (tensor A B) ≅ F.obj A ⊗ F.obj B)
    (h_unit : F.obj (structureSheaf X) ≅
      FGModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤))
    {f : GroupoidsOver.slice U ⟶ X}
    (t : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤)) (ModuleCat.{u} Γ(U.left, ⊤)) ≅
      qCohLift ⋙ QCoh.tensorPullback f) : Prop :=
  (∀ A B : Coh X,
      ((forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
          (ModuleCat.{u} Γ(U.left, ⊤))).mapIso (h_tensor A B)).hom ≫
        ModuleCat.ofHom
            (TensorProduct.map (t.hom.app A).hom (t.hom.app B).hom) ≫
          QCoh.tensorPullback_tensorInv f (qCohLift.obj A) (qCohLift.obj B) ≫
            (QCoh.tensorPullback f).map (tensor_qCohLiftIso A B).inv =
        t.hom.app (tensor A B)) ∧
    t.hom.app (structureSheaf X) ≫
        (QCoh.tensorPullback f).map (structureSheaf_qCohLiftIso X).hom ≫
          (QCoh.tensorPullback_unit f).hom =
      ((forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
          (ModuleCat.{u} Γ(U.left, ⊤))).mapIso h_unit).hom

/-- Tensor-naturality of `t` against `h_tensor` and `h_unit` is the tensor square
with `tensorPullback_tensorInv` after `tensor_qCohLiftIso`, together with the
unit square after `structureSheaf_qCohLiftIso`. -/
theorem IsTensorPullbackCohIso.iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {U : Over S} [IsAffine U.left]
    (F : Coh X ⥤ FGModuleCat.{u} Γ(U.left, ⊤))
    (h_tensor : ∀ A B : Coh X, F.obj (tensor A B) ≅ F.obj A ⊗ F.obj B)
    (h_unit : F.obj (structureSheaf X) ≅
      FGModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤))
    {f : GroupoidsOver.slice U ⟶ X}
    (t : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤)) (ModuleCat.{u} Γ(U.left, ⊤)) ≅
      qCohLift ⋙ QCoh.tensorPullback f) :
    IsTensorPullbackCohIso F h_tensor h_unit t ↔
      (∀ A B : Coh X,
          ((forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
              (ModuleCat.{u} Γ(U.left, ⊤))).mapIso (h_tensor A B)).hom ≫
            ModuleCat.ofHom
                (TensorProduct.map (t.hom.app A).hom (t.hom.app B).hom) ≫
              QCoh.tensorPullback_tensorInv f (qCohLift.obj A) (qCohLift.obj B) ≫
                (QCoh.tensorPullback f).map (tensor_qCohLiftIso A B).inv =
            t.hom.app (tensor A B)) ∧
        t.hom.app (structureSheaf X) ≫
            (QCoh.tensorPullback f).map (structureSheaf_qCohLiftIso X).hom ≫
              (QCoh.tensorPullback_unit f).hom =
          ((forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
              (ModuleCat.{u} Γ(U.left, ⊤))).mapIso h_unit).hom :=
  sorry

/-- Theorem 106.16.8. Let `X` be a Noetherian algebraic stack with affine
diagonal. Let `B` be a Noetherian ring. Let `F : Coh X ⥤ FGModuleCat B` be a
right exact tensor functor. Then `F` comes from a unique morphism
`Spec(B) ⟶ X`. -/
@[stacks 0GRR]
theorem existsUnique_hom_of_rightExactTensor
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsNoetherian X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {U : Over S} [IsAffine U.left] [AlgebraicGeometry.IsNoetherian U.left]
    (F : Coh X ⥤ FGModuleCat.{u} Γ(U.left, ⊤))
    [PreservesFiniteColimits F]
    (h_tensor : ∀ A B : Coh X, F.obj (tensor A B) ≅ F.obj A ⊗ F.obj B)
    (h_unit : F.obj (structureSheaf X) ≅
      FGModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤)) :
    ∃ (f : GroupoidsOver.slice U ⟶ X)
      (t : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
            (ModuleCat.{u} Γ(U.left, ⊤)) ≅
          qCohLift ⋙ QCoh.tensorPullback f),
      IsTensorPullbackCohIso F h_tensor h_unit t ∧
        ∀ (f' : GroupoidsOver.slice U ⟶ X)
          (t' : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤))
              (ModuleCat.{u} Γ(U.left, ⊤)) ≅
            qCohLift ⋙ QCoh.tensorPullback f'),
          IsTensorPullbackCohIso F h_tensor h_unit t' →
            ∃ α : f ⟶ f',
              t ≪≫ isoWhiskerLeft qCohLift (QCoh.tensorPullbackIso α) = t' :=
  sorry

/-- Two realizing morphisms of a right exact tensor functor on coherent modules
are related by a 2-arrow inducing the given tensor comparison. -/
theorem existsUnique_hom_of_rightExactTensor_spec
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsNoetherian X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {U : Over S} [IsAffine U.left] [AlgebraicGeometry.IsNoetherian U.left]
    (F : Coh X ⥤ FGModuleCat.{u} Γ(U.left, ⊤))
    [PreservesFiniteColimits F]
    (h_tensor : ∀ A B : Coh X, F.obj (tensor A B) ≅ F.obj A ⊗ F.obj B)
    (h_unit : F.obj (structureSheaf X) ≅
      FGModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤))
    {f f' : GroupoidsOver.slice U ⟶ X}
    (t : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤)) (ModuleCat.{u} Γ(U.left, ⊤)) ≅
      qCohLift ⋙ QCoh.tensorPullback f)
    (t' : F ⋙ forget₂ (FGModuleCat.{u} Γ(U.left, ⊤)) (ModuleCat.{u} Γ(U.left, ⊤)) ≅
      qCohLift ⋙ QCoh.tensorPullback f')
    (ht : IsTensorPullbackCohIso F h_tensor h_unit t)
    (ht' : IsTensorPullbackCohIso F h_tensor h_unit t') :
    ∃ α : f ⟶ f',
      t ≪≫ isoWhiskerLeft qCohLift (QCoh.tensorPullbackIso α) = t' :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Coh
