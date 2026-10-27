/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationResolution

/-! The canonical alternating-face complex and augmentation of abelian inverse images. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [IsFiberwiseSite F J]
variable [IsAugmentation F J K u0]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable (G : Sheaf K.toGrothendieck AddCommGrpCat.{w})

variable [HasSheafify (topology F J) AddCommGrpCat.{w}]

#check (CategoryTheory.Grothendieck.fiberInverseImageAugmentation F J K u0 G :
  CategoryTheory.Grothendieck.fiberInverseImageComplex F J K u0 G ⟶
    (ChainComplex.single₀ _).obj ((IsAugmentation.abelianInverseImage F J K u0).obj G))

#check (AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero (fiberInverseImageAugmented F J K u0 G) :
  (fiberInverseImageAugmentation F J K u0 G).f 0 = (fiberInverseImageAugmented F J K u0 G).hom.app (op ⦋0⦌))

end CategoryTheory.Grothendieck
