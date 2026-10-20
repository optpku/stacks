module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ordinary-category interface for stacks in groupoids

This file packages the object and morphism projections as an ordinary functor and gives its
isomorphism-level API.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Groupoids

variable {J : GrothendieckTopology C}

/-- Forget a stack in groupoids to its underlying groupoid-fibred category, on both objects and
morphisms. -/
@[stacks 02ZK "ordinary forgetful functor for groupoid stacks"]
def toGroupoids.functor (J : GrothendieckTopology C) :
    StackOver.Groupoids.{u, v} J ⥤ FiberedCategoryOver.Groupoids C where
  obj := toGroupoids
  map := Hom.toGroupoidsMor
  map_id := Hom.toGroupoidsMor.id
  map_comp := Hom.toGroupoidsMor.comp

/-- The object action of the ordinary forgetful functor is the underlying groupoid-fibred
category. -/
@[simp, stacks 02ZK "ordinary groupoid-stack forgetful object readout"]
theorem toGroupoids.functor.obj (J : GrothendieckTopology C)
    (X : StackOver.Groupoids J) :
    (toGroupoids.functor J).obj X = X.toGroupoids := sorry

/-- The morphism action of the ordinary forgetful functor is `Hom.toGroupoidsMor`. -/
@[simp, stacks 02ZK "ordinary groupoid-stack forgetful morphism readout"]
theorem toGroupoids.functor.map (J : GrothendieckTopology C)
    {X Y : StackOver.Groupoids J} (F : X ⟶ Y) :
    (toGroupoids.functor J).map F = Hom.toGroupoidsMor F := sorry

/-- Forget an isomorphism of stacks in groupoids to an isomorphism of their underlying
groupoid-fibred categories. -/
@[stacks 02ZK "ordinary groupoid-stack forgetful isomorphism"]
def toGroupoids.iso {X Y : StackOver.Groupoids J} (e : X ≅ Y) :
    X.toGroupoids ≅ Y.toGroupoids :=
  (toGroupoids.functor J).mapIso e

/-- The forward map of a forgotten isomorphism is the forgotten forward stack morphism. -/
@[simp, stacks 02ZK "forward map of ordinary forgotten isomorphism"]
theorem toGroupoids.iso.hom {X Y : StackOver.Groupoids J} (e : X ≅ Y) :
    (toGroupoids.iso e).hom = Hom.toGroupoidsMor e.hom := sorry

/-- The inverse map of a forgotten isomorphism is the forgotten inverse stack morphism. -/
@[simp, stacks 02ZK "inverse map of ordinary forgotten isomorphism"]
theorem toGroupoids.iso.inv {X Y : StackOver.Groupoids J} (e : X ≅ Y) :
    (toGroupoids.iso e).inv = Hom.toGroupoidsMor e.inv := sorry

/-- Forgetting a lifted groupoid-fibred isomorphism recovers the original isomorphism. -/
@[simp, stacks 02ZK "forgotten lifted groupoid-stack isomorphism"]
theorem toGroupoids.iso.ofGroupoids {X Y : StackOver.Groupoids J}
    (e : X.toGroupoids ≅ Y.toGroupoids) :
    toGroupoids.iso (isoOfGroupoids e) = e := sorry

/-- Lifting the forgotten groupoid-fibred isomorphism recovers the original stack
isomorphism. -/
@[simp, stacks 02ZK "lift after ordinary groupoid-stack forgetting"]
theorem isoOfGroupoids.toGroupoids {X Y : StackOver.Groupoids J} (e : X ≅ Y) :
    isoOfGroupoids (toGroupoids.iso e) = e := sorry

end StackOver.Groupoids

end CategoryTheory
