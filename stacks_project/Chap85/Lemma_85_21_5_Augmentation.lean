/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.SliceAugmentation

@[expose] public section

universe u v

open CategoryTheory

variable {C : Type u} [Category.{v} C] (U : SimplicialObject C) {X : C}
variable (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

#check (CategoryTheory.SimplicialObject.sliceForget U a :
  CategoryTheory.SimplicialObject.sliceTotalSite U ⥤ Over X)
