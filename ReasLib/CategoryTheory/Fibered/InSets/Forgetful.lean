module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Computations
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InSets.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetful computations for categories fibred in sets

This leaf exposes the object, morphism, cell, and standard-fiber actions of
`FiberedCategoryOver.Sets.toGroupoids`.  The construction itself remains the canonical
property-implication map between full subbicategories.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets

/-- Forgetting discreteness retains the underlying based category. -/
@[simp]
theorem toGroupoids.obj.toBasedCategory
    (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    ((toGroupoids C).obj X).toBasedCategory = X.toBasedCategory := sorry

/-- Forgetting discreteness retains the total category. -/
@[simp]
theorem toGroupoids.obj.total
    (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    ((toGroupoids C).obj X).total = X.total := sorry

/-- Forgetting discreteness retains the projection functor. -/
@[simp]
theorem toGroupoids.obj.p
    (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    ((toGroupoids C).obj X).p = X.p := sorry

/-- An object obtained by forgetting discreteness still has its original discrete-fibration
projection.  This named instance keeps the stronger source property available to downstream
typeclass search. -/
instance toGroupoids.obj.projectionInSets
    (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    Functor.IsDiscreteFibration ((toGroupoids C).obj X).p := sorry

variable {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C}

/-- Forgetting discreteness retains the underlying based functor of a `1`-morphism. -/
@[simp]
theorem toGroupoids.map.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor ((toGroupoids C).map F) =
      FiberedCategoryOver.Sets.toBasedFunctor F := sorry

/-- Forgetting discreteness retains the functor between total categories. -/
@[simp]
theorem toGroupoids.map.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toFunctor ((toGroupoids C).map F) =
      FiberedCategoryOver.Sets.toFunctor F := sorry

/-- Forgetting discreteness retains the induced functor on every standard fiber. -/
@[simp]
theorem toGroupoids.map.fiberFunctor (F : X ⟶ Y) (U : C) :
    FiberedCategoryOver.Groupoids.fiberFunctor ((toGroupoids C).map F) U =
      FiberedCategoryOver.Sets.fiberFunctor F U := sorry

variable {F G : X ⟶ Y}

/-- Forgetting discreteness retains the underlying based natural transformation of a
`2`-morphism. -/
@[simp]
theorem toGroupoids.map₂.hom (eta : F ⟶ G) :
    ((toGroupoids C).map₂ eta).hom = eta.hom := sorry

/-- Forgetting discreteness retains the natural transformation between total-category
functors. -/
@[simp]
theorem toGroupoids.map₂.toNatTrans (eta : F ⟶ G) :
    ((toGroupoids C).map₂ eta).hom.toNatTrans = eta.hom.toNatTrans := sorry

/-- Restricting a forgotten `2`-morphism to a standard fiber gives the original fiberwise
natural transformation. -/
@[simp]
theorem toGroupoids.map₂.fiber (eta : F ⟶ G) (U : C) :
    BasedNatTrans.fiber ((toGroupoids C).map₂ eta).hom U =
      BasedNatTrans.fiber eta.hom U := sorry

end FiberedCategoryOver.Sets

end CategoryTheory
