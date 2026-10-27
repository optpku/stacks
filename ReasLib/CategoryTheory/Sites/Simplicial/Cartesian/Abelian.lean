/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.Simplicial.Cartesian

/-!
# Closure of cartesian abelian sheaves on a simplicial site
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

universe u v w u' v'

namespace CategoryTheory.SimplicialSites.Sheaf

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- Cartesian abelian sheaves on the total site of a diagram of morphisms of sites
form a weak Serre subcategory. -/
instance cartesianProperty_isWeakSerreClass
    [HasSheafify (topology C J) AddCommGrpCat.{w}] :
    IsWeakSerreClass
      (fun F : Sheaf (topology C J) AddCommGrpCat.{w} ↦ IsCartesian C J F) :=
  sorry

/-- A colimit of cartesian abelian sheaves on the total site of a diagram of
morphisms of sites is cartesian whenever that colimit exists. -/
instance cartesianProperty_isClosedUnderColimitsOfShape
    (ι : Type u') [Category.{v'} ι] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (fun F : Sheaf (topology C J) AddCommGrpCat.{w} ↦ IsCartesian C J F) ι :=
  sorry

end CategoryTheory.SimplicialSites.Sheaf
