module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Hom.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms of stacks in sets

This file lifts isomorphisms of set-fibred categories to the bundled stack layer and records the
forward and inverse computation rules.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Sets

variable {J : GrothendieckTopology C}

namespace isoOfSets

/-- Lifting the two directions of an underlying set-fibred isomorphism satisfies the first
inverse law. -/
@[stacks 02ZK "set-stack lifted isomorphism forward inverse law"]
theorem hom_comp_inv {X Y : StackOver.Sets J} (e : X.toSets ≅ Y.toSets) :
    Hom.ofSetsMor e.hom ≫ Hom.ofSetsMor e.inv = 𝟙 X := sorry

/-- Lifting the two directions of an underlying set-fibred isomorphism satisfies the second
inverse law. -/
@[stacks 02ZK "set-stack lifted isomorphism inverse forward law"]
theorem inv_comp_hom {X Y : StackOver.Sets J} (e : X.toSets ≅ Y.toSets) :
    Hom.ofSetsMor e.inv ≫ Hom.ofSetsMor e.hom = 𝟙 Y := sorry

end isoOfSets

/-- Lift an isomorphism of the underlying categories fibred in sets to an isomorphism of stacks
in sets. -/
@[stacks 02ZK "set-stack isomorphism lift"]
def isoOfSets {X Y : StackOver.Sets J} (e : X.toSets ≅ Y.toSets) : X ≅ Y where
  hom := Hom.ofSetsMor e.hom
  inv := Hom.ofSetsMor e.inv
  hom_inv_id := isoOfSets.hom_comp_inv e
  inv_hom_id := isoOfSets.inv_comp_hom e

namespace isoOfSets

/-- The underlying set-fibred morphism of the forward map of `isoOfSets` is the supplied forward
map. -/
@[simp, stacks 02ZK "set-stack lifted isomorphism forward readout"]
theorem hom.toSetsMor {X Y : StackOver.Sets J} (e : X.toSets ≅ Y.toSets) :
    Hom.toSetsMor (isoOfSets e).hom = e.hom := sorry

/-- The underlying set-fibred morphism of the inverse map of `isoOfSets` is the supplied inverse
map. -/
@[simp, stacks 02ZK "set-stack lifted isomorphism inverse readout"]
theorem inv.toSetsMor {X Y : StackOver.Sets J} (e : X.toSets ≅ Y.toSets) :
    Hom.toSetsMor (isoOfSets e).inv = e.inv := sorry

end isoOfSets

end StackOver.Sets

end CategoryTheory
