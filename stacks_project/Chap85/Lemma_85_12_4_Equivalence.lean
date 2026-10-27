/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Definition_85_12_1_Cartesian
public import ReasLib.CategoryTheory.Sites.Simplicial.CartesianDescent

/-! Compatibility checks for coface descent on a simplicial site. -/

@[expose] public section

open CategoryTheory

universe u v w

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : CategoryTheory.SimplicialSites.IsMorphismDiagram.{u, v, w} C J]
variable (A : Type (w + 1)) [Category.{w} A]
variable [instWeakSheafifyA : ∀ n, HasWeakSheafify (J n).toGrothendieck A]
variable [instLeftKanA : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ A),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include instMorphismDiagram instWeakSheafify instLeftKan instWeakSheafifyA instLeftKanA

#check (CategoryTheory.SimplicialSites.Sheaf.cartesianEquivalence C J A :
  CategoryTheory.SimplicialSites.Sheaf.Cartesian C J A ≌
    CategoryTheory.SimplicialSites.Sheaf.FaceDescent C J A)
