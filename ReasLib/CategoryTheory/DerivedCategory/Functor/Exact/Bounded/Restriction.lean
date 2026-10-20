/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Preservation
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded restrictions of exact derived functors

An exact functor between abelian categories restricts canonically to the
bounded-below, bounded-above, and bounded derived categories.  The three
constructions are full-subcategory lifts of the same ambient derived functor.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactFunctor.Derived

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

namespace Plus

/-- An exact derived functor sends bounded-below objects to bounded-below
objects. -/
@[stacks 015F "exact derived functors preserve bounded-below objects"]
theorem objMem (F : A ⥤ₑ B) (X : DerivedCategory.Plus A) :
    (t.plus : ObjectProperty (DerivedCategory B))
      (F.mapDerivedCategory.obj X.obj) := sorry

/-- The restriction of an exact derived functor to bounded-below derived
categories. -/
@[stacks 015F "exact functors on bounded-below derived categories"]
noncomputable def functor (F : A ⥤ₑ B) :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus B :=
  ObjectProperty.FullSubcategory.restrict F.mapDerivedCategory (mapsTo F)

/-- Forgetting the bounded-below restriction recovers the ambient exact
derived functor on bounded-below objects. -/
@[stacks 015F "bounded-below exact derived inclusion comparison"]
noncomputable def compιIso (F : A ⥤ₑ B) :
    functor F ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    F.mapDerivedCategory (mapsTo F)

end Plus

namespace Minus

/-- An exact derived functor sends bounded-above objects to bounded-above
objects. -/
@[stacks 015F "exact derived functors preserve bounded-above objects"]
theorem objMem (F : A ⥤ₑ B) (X : DerivedCategory.Minus A) :
    (t.minus : ObjectProperty (DerivedCategory B))
      (F.mapDerivedCategory.obj X.obj) := sorry

/-- The restriction of an exact derived functor to bounded-above derived
categories. -/
@[stacks 015F "exact functors on bounded-above derived categories"]
noncomputable def functor (F : A ⥤ₑ B) :
    DerivedCategory.Minus A ⥤ DerivedCategory.Minus B :=
  ObjectProperty.FullSubcategory.restrict F.mapDerivedCategory (mapsTo F)

/-- Forgetting the bounded-above restriction recovers the ambient exact
derived functor on bounded-above objects. -/
@[stacks 015F "bounded-above exact derived inclusion comparison"]
noncomputable def compιIso (F : A ⥤ₑ B) :
    functor F ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.Minus.ι ⋙ F.mapDerivedCategory :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    F.mapDerivedCategory (mapsTo F)

end Minus

namespace Bounded

/-- An exact derived functor sends bounded objects to bounded objects. -/
@[stacks 015F "exact derived functors preserve bounded objects"]
theorem objMem (F : A ⥤ₑ B) (X : DerivedCategory.Bounded A) :
    (t.bounded : ObjectProperty (DerivedCategory B))
      (F.mapDerivedCategory.obj X.obj) := sorry

/-- The restriction of an exact derived functor to bounded derived
categories. -/
@[stacks 015F "exact functors on bounded derived categories"]
noncomputable def functor (F : A ⥤ₑ B) :
    DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded B :=
  ObjectProperty.FullSubcategory.restrict F.mapDerivedCategory (mapsTo F)

/-- Forgetting the bounded restriction recovers the ambient exact derived
functor on bounded objects. -/
@[stacks 015F "bounded exact derived inclusion comparison"]
noncomputable def compιIso (F : A ⥤ₑ B) :
    functor F ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ F.mapDerivedCategory :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    F.mapDerivedCategory (mapsTo F)

end Bounded

end CategoryTheory.ExactFunctor.Derived
