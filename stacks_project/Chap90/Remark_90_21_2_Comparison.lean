/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.Comparison

/-!
# Morphisms of groupoids in functors as natural transformations

A morphism of groupoids in functors on `C` corresponds to a morphism of the
associated functors `C ⥤ Grpd`, where `Grpd` is regarded as a 1-category.
This comparison is at the level of `Hom` types, not an identification of
`GroupoidInFunctors` with `C ⥤ Grpd` or with the associated cofibered category.
-/

@[expose] public section

open CategoryTheory

universe u v w

#check (CategoryTheory.GroupoidInFunctors.Hom.toNatTrans :
  {C : Type u} → [CategoryTheory.Category.{v} C] →
    {G H : CategoryTheory.GroupoidInFunctors.{u, v, w} C} →
      CategoryTheory.GroupoidInFunctors.Hom G H → (G.toFunctor ⟶ H.toFunctor))
