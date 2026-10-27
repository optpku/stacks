/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.AugmentationResolution

/-! The canonical alternating-face complex and augmentation of abelian inverse images. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable (G : Sheaf K.toGrothendieck AddCommGrpCat.{w})
include h_morphism
include h_aug

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]

#check (CategoryTheory.SimplicialSites.inverseImageAugmentation C J K u0 G :
  CategoryTheory.SimplicialSites.inverseImageComplex C J K u0 G ⟶
    (ChainComplex.single₀ _).obj ((IsAugmentation.abelianInverseImage C J K u0).obj G))

#check (AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero (inverseImageAugmented C J K u0 G) :
  (inverseImageAugmentation C J K u0 G).f 0 = (inverseImageAugmented C J K u0 G).hom.app (op ⦋0⦌))

end CategoryTheory.SimplicialSites
