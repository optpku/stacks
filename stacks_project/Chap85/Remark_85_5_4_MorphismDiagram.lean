/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Remark_85_4_1_MorphismDiagram
public import stacks_project.Chap85.Remark_85_5_1_Morphism

public import ReasLib.CategoryTheory.Sites.Simplicial.Compatibility

/-!
# Compatibility of augmented simplicial sites

The defining compatibility condition is checked against the shared mathematical API.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialSites

section

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable {D' : Type u} [Category.{v} D'] (K' : Precoverage D')
variable (u0 : D ⥤ C.obj ⦋0⦌) (u0' : D' ⥤ C'.obj ⦋0⦌)
variable (α : C' ⟶ C) (v : D' ⥤ D)
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ P : D'ᵒᵖ ⥤ Type w, u0'.op.HasLeftKanExtension P]
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w), ((α.app n).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : D'ᵒᵖ ⥤ Type w, v.op.HasLeftKanExtension P]
variable [instC : IsMorphismDiagram C J] [instC' : IsMorphismDiagram C' J']
variable [hα : IsMorphism J J' α]
variable [h_aug : IsAugmentation C J K u0] [h_aug' : IsAugmentation C' J' K' u0']
include instC instC' hα h_aug h_aug'


#check (CategoryTheory.SimplicialSites.IsCompatible.iff J J' K K' u0 u0' α v :
  CategoryTheory.SimplicialSites.IsCompatible J J' K K' u0 u0' α v ↔
    IsExactMorphismOfSites K'.toGrothendieck K.toGrothendieck v ∧
      u0' ⋙ (α.app ⦋0⦌).toFunctor = v ⋙ u0)

end

end CategoryTheory.SimplicialSites
