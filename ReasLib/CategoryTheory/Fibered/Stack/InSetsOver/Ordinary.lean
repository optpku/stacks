/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ordinary-category interface for stacks in sets

This file packages the object and morphism projections as an ordinary functor and gives its
isomorphism-level API.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Sets

variable {J : GrothendieckTopology C}

/-- Forget a stack in sets to its underlying category fibred in sets, on both objects and
morphisms. -/
@[stacks 02ZK "set-stack ordinary forgetful functor"]
def toSets.functor (J : GrothendieckTopology C) :
    StackOver.Sets.{u, v} J ⥤ FiberedCategoryOver.Sets C where
  obj := toSets
  map := Hom.toSetsMor
  map_id := Hom.toSetsMor.id
  map_comp := Hom.toSetsMor.comp

/-- The object action of the ordinary forgetful functor is the underlying set-fibred
category. -/
@[simp, stacks 02ZK "set-stack ordinary forgetful object readout"]
theorem toSets.functor.obj (J : GrothendieckTopology C) (X : StackOver.Sets J) :
    (toSets.functor J).obj X = X.toSets := sorry

/-- The morphism action of the ordinary forgetful functor is `Hom.toSetsMor`. -/
@[simp, stacks 02ZK "set-stack ordinary forgetful morphism readout"]
theorem toSets.functor.map (J : GrothendieckTopology C)
    {X Y : StackOver.Sets J} (F : X ⟶ Y) :
    (toSets.functor J).map F = Hom.toSetsMor F := sorry

/-- Forget an isomorphism of stacks in sets to an isomorphism of their underlying set-fibred
categories. -/
@[stacks 02ZK "set-stack ordinary forgotten isomorphism"]
def toSets.iso {X Y : StackOver.Sets J} (e : X ≅ Y) : X.toSets ≅ Y.toSets :=
  (toSets.functor J).mapIso e

/-- The forward map of a forgotten isomorphism is the forgotten forward stack morphism. -/
@[simp, stacks 02ZK "set-stack ordinary forgotten isomorphism forward readout"]
theorem toSets.iso.hom {X Y : StackOver.Sets J} (e : X ≅ Y) :
    (toSets.iso e).hom = Hom.toSetsMor e.hom := sorry

/-- The inverse map of a forgotten isomorphism is the forgotten inverse stack morphism. -/
@[simp, stacks 02ZK "set-stack ordinary forgotten isomorphism inverse readout"]
theorem toSets.iso.inv {X Y : StackOver.Sets J} (e : X ≅ Y) :
    (toSets.iso e).inv = Hom.toSetsMor e.inv := sorry

/-- Forgetting an isomorphism lifted from set-fibred categories recovers the original
isomorphism. -/
@[simp, stacks 02ZK "set-stack ordinary isomorphism lifting readout"]
theorem toSets.iso.ofSets {X Y : StackOver.Sets J} (e : X.toSets ≅ Y.toSets) :
    toSets.iso (isoOfSets e) = e := sorry

/-- Lifting the forgotten set-fibred isomorphism of a stack isomorphism recovers the original
stack isomorphism. -/
@[simp, stacks 02ZK "set-stack ordinary isomorphism recovery"]
theorem isoOfSets.toSets {X Y : StackOver.Sets J} (e : X ≅ Y) :
    isoOfSets (toSets.iso e) = e := sorry

end StackOver.Sets

end CategoryTheory
