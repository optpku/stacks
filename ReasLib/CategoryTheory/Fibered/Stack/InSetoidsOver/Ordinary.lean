/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ordinary-category interface for stacks in setoids

This file packages the object and morphism projections as an ordinary functor and gives its
isomorphism-level API.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Setoids

variable {J : GrothendieckTopology C}

/-- Forget a stack in setoids to its underlying category fibred in setoids, on both objects and
morphisms. -/
@[stacks 02ZK "setoid-stack ordinary forgetful functor"]
def toSetoids.functor (J : GrothendieckTopology C) :
    StackOver.Setoids.{u, v} J ⥤ FiberedCategoryOver.Setoids C where
  obj := toSetoids
  map := Hom.toSetoidsMor
  map_id := Hom.toSetoidsMor.id
  map_comp := Hom.toSetoidsMor.comp

/-- The object action of the ordinary forgetful functor is the underlying setoid-fibred
category. -/
@[simp, stacks 02ZK "setoid-stack ordinary forgetful object readout"]
theorem toSetoids.functor.obj (J : GrothendieckTopology C) (X : StackOver.Setoids J) :
    (toSetoids.functor J).obj X = X.toSetoids := sorry

/-- The morphism action of the ordinary forgetful functor is `Hom.toSetoidsMor`. -/
@[simp, stacks 02ZK "setoid-stack ordinary forgetful morphism readout"]
theorem toSetoids.functor.map (J : GrothendieckTopology C)
    {X Y : StackOver.Setoids J} (F : X ⟶ Y) :
    (toSetoids.functor J).map F = Hom.toSetoidsMor F := sorry

/-- Forget an isomorphism of stacks in setoids to an isomorphism of their underlying
setoid-fibred categories. -/
@[stacks 02ZK "setoid-stack ordinary forgotten isomorphism"]
def toSetoids.iso {X Y : StackOver.Setoids J} (e : X ≅ Y) :
    X.toSetoids ≅ Y.toSetoids :=
  (toSetoids.functor J).mapIso e

/-- The forward map of a forgotten isomorphism is the forgotten forward stack morphism. -/
@[simp, stacks 02ZK "setoid-stack ordinary forgotten isomorphism forward readout"]
theorem toSetoids.iso.hom {X Y : StackOver.Setoids J} (e : X ≅ Y) :
    (toSetoids.iso e).hom = Hom.toSetoidsMor e.hom := sorry

/-- The inverse map of a forgotten isomorphism is the forgotten inverse stack morphism. -/
@[simp, stacks 02ZK "setoid-stack ordinary forgotten isomorphism inverse readout"]
theorem toSetoids.iso.inv {X Y : StackOver.Setoids J} (e : X ≅ Y) :
    (toSetoids.iso e).inv = Hom.toSetoidsMor e.inv := sorry

/-- Forgetting an isomorphism lifted from setoid-fibred categories recovers the original
isomorphism. -/
@[simp, stacks 02ZK "setoid-stack ordinary isomorphism lifting readout"]
theorem toSetoids.iso.ofSetoids
    {X Y : StackOver.Setoids J} (e : X.toSetoids ≅ Y.toSetoids) :
    toSetoids.iso (isoOfSetoids e) = e := sorry

/-- Lifting the forgotten setoid-fibred isomorphism of a stack isomorphism recovers the
original stack isomorphism. -/
@[simp, stacks 02ZK "setoid-stack ordinary isomorphism recovery"]
theorem isoOfSetoids.toSetoids {X Y : StackOver.Setoids J} (e : X ≅ Y) :
    isoOfSetoids (toSetoids.iso e) = e := sorry

end StackOver.Setoids

end CategoryTheory
