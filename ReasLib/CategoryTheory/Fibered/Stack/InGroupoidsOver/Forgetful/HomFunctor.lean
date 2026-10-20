module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Forgetful.TwoCell
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom-functor action of the groupoid-stack forgetful pseudofunctor

This file records the object and morphism readouts of the functor induced by
`StackOver.Groupoids.forget J` on each Hom category.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Groupoids

variable {J : GrothendieckTopology C}

namespace forget

/-- On each Hom category, the forgetful map functor sends objects to their canonical
groupoid-fibred projections. -/
@[simp, stacks 02ZK "groupoid-stack forgetful Hom object"]
theorem mapFunctor.obj.toGroupoidsMor
    {X Y : StackOver.Groupoids.{u, v, w, vS} J} (F : X ⟶ Y) :
    ((StackOver.Groupoids.forget J).mapFunctor X Y).obj F =
      Hom.toGroupoidsMor F := sorry

/-- The based functor underlying an object of the forgetful map functor is the canonical based
projection. -/
@[simp, stacks 02ZK "groupoid-stack forgetful Hom based projection"]
theorem mapFunctor.obj.toBasedFunctor
    {X Y : StackOver.Groupoids.{u, v, w, vS} J} (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor
        (((StackOver.Groupoids.forget J).mapFunctor X Y).obj F) =
      Hom.toBasedFunctor F := sorry

/-- The total functor underlying an object of the forgetful map functor is the canonical total
projection. -/
@[simp, stacks 02ZK "groupoid-stack forgetful Hom total projection"]
theorem mapFunctor.obj.toFunctor
    {X Y : StackOver.Groupoids.{u, v, w, vS} J} (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toFunctor
        (((StackOver.Groupoids.forget J).mapFunctor X Y).obj F) =
      Hom.toFunctor F := sorry

/-- The fiber action underlying an object of the forgetful map functor is the canonical fiber
projection. -/
@[simp, stacks 02ZK "groupoid-stack forgetful Hom fiber projection"]
theorem mapFunctor.obj.fiberFunctor
    {X Y : StackOver.Groupoids.{u, v, w, vS} J}
    (F : X ⟶ Y) (U : C) :
    FiberedCategoryOver.Groupoids.fiberFunctor
        (((StackOver.Groupoids.forget J).mapFunctor X Y).obj F) U =
      Hom.fiberFunctor F U := sorry

/-- On each Hom category, the forgetful map functor sends morphisms to their named
groupoid-fibred projections. -/
@[simp, stacks 02ZK "groupoid-stack forgetful Hom morphism"]
theorem mapFunctor.map.toGroupoidsNatTrans
    {X Y : StackOver.Groupoids.{u, v, w, vS} J}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    ((StackOver.Groupoids.forget J).mapFunctor X Y).map eta =
      Hom₂.toGroupoidsNatTrans eta := sorry

/-- The based natural transformation underlying a morphism of the forgetful map functor is the
named based projection. -/
@[simp, stacks 02ZK "groupoid-stack forgetful Hom based morphism"]
theorem mapFunctor.map.toBasedNatTrans
    {X Y : StackOver.Groupoids.{u, v, w, vS} J}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (((StackOver.Groupoids.forget J).mapFunctor X Y).map eta).hom =
      Hom₂.toBasedNatTrans eta := sorry

/-- The total natural transformation underlying a morphism of the forgetful map functor is the
named total-category projection. -/
@[simp, stacks 02ZK "groupoid-stack forgetful Hom total morphism"]
theorem mapFunctor.map.toNatTrans
    {X Y : StackOver.Groupoids.{u, v, w, vS} J}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (((StackOver.Groupoids.forget J).mapFunctor X Y).map eta).hom.toNatTrans =
      Hom₂.toNatTrans eta := sorry

end forget

end StackOver.Groupoids

end CategoryTheory
