module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Computations
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetful computations for categories fibred in groupoids

This leaf exposes the object, morphism, cell, and standard-fiber actions of
`FiberedCategoryOver.Groupoids.toFibered`.  Its statements are the domain-facing projections of
the generic full-subbicategory inclusion and locally induced lift computations.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

/-- Forgetting the groupoid-fibre refinement retains the underlying based category. -/
@[simp]
theorem toFibered.obj.toBasedCategory
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    ((toFibered C).obj X).toBasedCategory = X.toBasedCategory := sorry

/-- An object obtained by forgetting the groupoid-fibre refinement still has its original
groupoid-fibred projection. -/
instance toFibered.obj.projectionInGroupoids
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    Functor.IsFibered.InGroupoids ((toFibered C).obj X).p := sorry

variable {X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

/-- Forgetting the groupoid-fibre refinement retains the underlying based functor. -/
@[simp]
theorem toFibered.map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor ((toFibered C).map F) =
      FiberedCategoryOver.Groupoids.toBasedFunctor F := sorry

/-- Forgetting the groupoid-fibre refinement retains the functor between total categories. -/
@[simp]
theorem toFibered.map.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor ((toFibered C).map F) =
      FiberedCategoryOver.Groupoids.toFunctor F := sorry

/-- Forgetting the groupoid-fibre refinement retains the induced functor on every standard
fiber. -/
@[simp]
theorem toFibered.map.fiberFunctor (F : X ⟶ Y) (U : C) :
    FiberedCategoryOver.fiberFunctor ((toFibered C).map F) U =
      FiberedCategoryOver.Groupoids.fiberFunctor F U := sorry

variable {F G : X ⟶ Y}

/-- Forgetting the groupoid-fibre refinement retains the underlying based natural
transformation of a `2`-morphism. -/
@[simp]
theorem toFibered.map₂.hom (eta : F ⟶ G) :
    ((toFibered C).map₂ eta).hom = eta.hom := sorry

/-- Forgetting the groupoid-fibre refinement retains the natural transformation between total
categories. -/
@[simp]
theorem toFibered.map₂.toNatTrans (eta : F ⟶ G) :
    ((toFibered C).map₂ eta).hom.toNatTrans = eta.hom.toNatTrans := sorry

/-- Fiber restriction of a forgotten `2`-morphism is the canonical restriction of its original
based natural transformation. -/
@[simp]
theorem toFibered.map₂.fiber (eta : F ⟶ G) (U : C) :
    FiberedCategoryOver.fiberNatTrans ((toFibered C).map₂ eta) U =
      BasedNatTrans.fiber eta.hom U := sorry

end FiberedCategoryOver.Groupoids

end CategoryTheory
