/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Over
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Singleton fixed-target families

This leaf exposes Mathlib's fully faithful singleton inclusion on slice categories and its
degreewise application to augmented simplicial objects.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits
open scoped CategoryTheory.SemiRepresentableFamily

namespace SemiRepresentableFamily.OverFamily

variable {C : Type u} [Category.{v} C]

/-- The fully faithful inclusion of an object over `X` as a singleton fixed-target family. -/
abbrev singletonFunctor (X : C) :
    CategoryTheory.Over X ⥤ SemiRepresentableFamily.OverFamily.{v, u, w} X :=
  FormalCoproduct.incl (CategoryTheory.Over X)

/-- The singleton functor agrees with the arrow-based singleton-family constructor. -/
@[simp] theorem singletonFunctor_obj (X : C) (Y : CategoryTheory.Over X) :
    (singletonFunctor.{w} X).obj Y = singleton Y.hom := by
  rfl

/-- The singleton functor has the unique map between its singleton index types. -/
@[simp] theorem singletonFunctor_map_f (X : C)
    {Y Z : CategoryTheory.Over X} (f : Y ⟶ Z) :
    ((singletonFunctor.{w} X).map f).f = fun _ ↦ PUnit.unit := by
  rfl

/-- The sole component of a mapped singleton family is the original slice morphism. -/
@[simp] theorem singletonFunctor_map_phi (X : C)
    {Y Z : CategoryTheory.Over X} (f : Y ⟶ Z)
    (i : ((singletonFunctor.{w} X).obj Y).index) :
    ((singletonFunctor.{w} X).map f).φ i = f := by
  rfl

end SemiRepresentableFamily.OverFamily

namespace SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- The singleton fixed-target family in every degree of an augmented simplicial object. -/
@[stacks 0GM9 "singleton-family simplicial object"]
def toOverFamily (A : SimplicialObject.Augmented C) :
    SimplicialObject (SemiRepresentableFamily.OverFamily.{v, u, w} A.right) :=
  A.toOver ⋙ SemiRepresentableFamily.OverFamily.singletonFunctor A.right

/-- In each degree, `A.toOverFamily` is the singleton family on the augmentation component. -/
@[simp] theorem toOverFamily_obj (A : SimplicialObject.Augmented C)
    (Delta : SimplexCategoryᵒᵖ) :
    A.toOverFamily.obj Delta =
      SemiRepresentableFamily.OverFamily.singleton (A.hom.app Delta) := by
  rfl

/-- Every degree of `A.toOverFamily` has one index. -/
@[simp] theorem toOverFamily_obj_index (A : SimplicialObject.Augmented C)
    (Delta : SimplexCategoryᵒᵖ) :
    (A.toOverFamily.obj Delta).index = PUnit := by
  rfl

/-- The source of the unique family member in degree `Delta` is `A.left.obj Delta`. -/
@[simp] theorem toOverFamily_obj_left (A : SimplicialObject.Augmented C)
    (Delta : SimplexCategoryᵒᵖ) (i : (A.toOverFamily.obj Delta).index) :
    ((A.toOverFamily.obj Delta).obj i).left = A.left.obj Delta := by
  rfl

/-- The unique structure arrow in degree `Delta` is the augmentation component. -/
@[simp] theorem toOverFamily_obj_hom (A : SimplicialObject.Augmented C)
    (Delta : SimplexCategoryᵒᵖ) (i : (A.toOverFamily.obj Delta).index) :
    ((A.toOverFamily.obj Delta).obj i).hom = A.hom.app Delta := by
  rfl

/-- Simplicial structure maps of singleton families have the unique index map. -/
@[simp] theorem toOverFamily_map_f (A : SimplicialObject.Augmented C)
    {Delta Delta' : SimplexCategoryᵒᵖ} (f : Delta ⟶ Delta') :
    (A.toOverFamily.map f).f = fun _ ↦ PUnit.unit := by
  rfl

/-- The underlying component of a singleton-family structure map is the corresponding
simplicial structure map. -/
@[simp] theorem toOverFamily_map_phi_left (A : SimplicialObject.Augmented C)
    {Delta Delta' : SimplexCategoryᵒᵖ} (f : Delta ⟶ Delta')
    (i : (A.toOverFamily.obj Delta).index) :
    ((A.toOverFamily.map f).φ i).left = A.left.map f := by
  rfl

end SimplicialObject.Augmented

end CategoryTheory
