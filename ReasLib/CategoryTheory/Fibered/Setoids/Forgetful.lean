/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Fibered.Groupoids.Forgetful
public import ReasLib.CategoryTheory.Fibered.Setoids.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetful computations for categories fibred in setoids

This leaf exposes the object, morphism, cell, and standard-fiber actions of the canonical maps
from setoid-fibred categories to groupoid-fibred and arbitrary fibred categories.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Setoids

/-- Forgetting thinness retains the underlying based category. -/
@[simp]
theorem toGroupoids.obj.toBasedCategory
    (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    ((toGroupoids C).obj X).toBasedCategory = X.toBasedCategory := sorry

/-- An object obtained by forgetting thinness still has its original setoid-fibred projection. -/
instance toGroupoids.obj.projectionInSetoids
    (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    Functor.IsFibered.InSetoids ((toGroupoids C).obj X).p := sorry

variable {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C}

/-- Forgetting thinness retains the underlying based functor. -/
@[simp]
theorem toGroupoids.map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor ((toGroupoids C).map F) =
      FiberedCategoryOver.Setoids.toBasedFunctor F := sorry

/-- Forgetting thinness retains the functor between total categories. -/
@[simp]
theorem toGroupoids.map.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toFunctor ((toGroupoids C).map F) =
      FiberedCategoryOver.Setoids.toFunctor F := sorry

/-- Forgetting thinness retains the induced functor on every standard fiber. -/
@[simp]
theorem toGroupoids.map.fiberFunctor (F : X ⟶ Y) (U : C) :
    FiberedCategoryOver.Groupoids.fiberFunctor ((toGroupoids C).map F) U =
      FiberedCategoryOver.Setoids.fiberFunctor F U := sorry

variable {F G : X ⟶ Y}

/-- Forgetting thinness retains the underlying based natural transformation of a
`2`-morphism. -/
@[simp]
theorem toGroupoids.map₂.hom (eta : F ⟶ G) :
    ((toGroupoids C).map₂ eta).hom = eta.hom := sorry

/-- Forgetting thinness retains the natural transformation between total categories. -/
@[simp]
theorem toGroupoids.map₂.toNatTrans (eta : F ⟶ G) :
    ((toGroupoids C).map₂ eta).hom.toNatTrans = eta.hom.toNatTrans := sorry

/-- Restricting a thinness-forgotten `2`-morphism to a standard fiber gives the original
fiberwise natural transformation. -/
@[simp]
theorem toGroupoids.map₂.fiber (eta : F ⟶ G) (U : C) :
    BasedNatTrans.fiber ((toGroupoids C).map₂ eta).hom U =
      BasedNatTrans.fiber eta.hom U := sorry

/-- Forgetting the setoid-fibre refinement retains the underlying based category. -/
@[simp]
theorem toFibered.obj.toBasedCategory
    (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    ((toFibered C).obj X).toBasedCategory = X.toBasedCategory := sorry

/-- An object obtained by forgetting the setoid-fibre refinement still has its original
setoid-fibred projection. -/
instance toFibered.obj.projectionInSetoids
    (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    Functor.IsFibered.InSetoids ((toFibered C).obj X).p := sorry

/-- Forgetting the setoid-fibre refinement retains the underlying based functor. -/
@[simp]
theorem toFibered.map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor ((toFibered C).map F) =
      FiberedCategoryOver.Setoids.toBasedFunctor F := sorry

/-- Forgetting the setoid-fibre refinement retains the functor between total categories. -/
@[simp]
theorem toFibered.map.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor ((toFibered C).map F) =
      FiberedCategoryOver.Setoids.toFunctor F := sorry

/-- Forgetting the setoid-fibre refinement retains the induced functor on every standard
fiber. -/
@[simp]
theorem toFibered.map.fiberFunctor (F : X ⟶ Y) (U : C) :
    FiberedCategoryOver.fiberFunctor ((toFibered C).map F) U =
      FiberedCategoryOver.Setoids.fiberFunctor F U := sorry

/-- Forgetting the setoid-fibre refinement retains the underlying based natural transformation
of a `2`-morphism. -/
@[simp]
theorem toFibered.map₂.hom (eta : F ⟶ G) :
    ((toFibered C).map₂ eta).hom = eta.hom := sorry

/-- Forgetting the setoid-fibre refinement retains the natural transformation between total
categories. -/
@[simp]
theorem toFibered.map₂.toNatTrans (eta : F ⟶ G) :
    ((toFibered C).map₂ eta).hom.toNatTrans = eta.hom.toNatTrans := sorry

/-- Fiber restriction of a setoid-forgotten `2`-morphism is the canonical restriction of its
original based natural transformation. -/
@[simp]
theorem toFibered.map₂.fiber (eta : F ⟶ G) (U : C) :
    FiberedCategoryOver.fiberNatTrans ((toFibered C).map₂ eta) U =
      BasedNatTrans.fiber eta.hom U := sorry

end FiberedCategoryOver.Setoids

end CategoryTheory
