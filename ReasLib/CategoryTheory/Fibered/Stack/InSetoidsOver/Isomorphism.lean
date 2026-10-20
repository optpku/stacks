module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Hom.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms of stacks in setoids

This file lifts isomorphisms of setoid-fibred categories to the bundled stack layer and records
the forward and inverse computation rules.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Setoids

variable {J : GrothendieckTopology C}

namespace isoOfSetoids

/-- Lifting the two directions of an underlying setoid-fibred isomorphism satisfies the first
inverse law. -/
@[stacks 02ZK "setoid-stack lifted isomorphism forward inverse law"]
theorem hom_comp_inv {X Y : StackOver.Setoids J} (e : X.toSetoids ≅ Y.toSetoids) :
    Hom.ofSetoidsMor e.hom ≫ Hom.ofSetoidsMor e.inv = 𝟙 X := sorry

/-- Lifting the two directions of an underlying setoid-fibred isomorphism satisfies the second
inverse law. -/
@[stacks 02ZK "setoid-stack lifted isomorphism inverse forward law"]
theorem inv_comp_hom {X Y : StackOver.Setoids J} (e : X.toSetoids ≅ Y.toSetoids) :
    Hom.ofSetoidsMor e.inv ≫ Hom.ofSetoidsMor e.hom = 𝟙 Y := sorry

end isoOfSetoids

/-- Lift an isomorphism of the underlying categories fibred in setoids to an isomorphism of
stacks in setoids. -/
@[stacks 02ZK "setoid-stack isomorphism lift"]
def isoOfSetoids {X Y : StackOver.Setoids J} (e : X.toSetoids ≅ Y.toSetoids) : X ≅ Y where
  hom := Hom.ofSetoidsMor e.hom
  inv := Hom.ofSetoidsMor e.inv
  hom_inv_id := isoOfSetoids.hom_comp_inv e
  inv_hom_id := isoOfSetoids.inv_comp_hom e

namespace isoOfSetoids

/-- The underlying setoid-fibred morphism of the forward map of `isoOfSetoids` is the supplied
forward map. -/
@[simp, stacks 02ZK "setoid-stack lifted isomorphism forward readout"]
theorem hom.toSetoidsMor {X Y : StackOver.Setoids J} (e : X.toSetoids ≅ Y.toSetoids) :
    Hom.toSetoidsMor (isoOfSetoids e).hom = e.hom := sorry

/-- The underlying setoid-fibred morphism of the inverse map of `isoOfSetoids` is the supplied
inverse map. -/
@[simp, stacks 02ZK "setoid-stack lifted isomorphism inverse readout"]
theorem inv.toSetoidsMor {X Y : StackOver.Setoids J} (e : X.toSetoids ≅ Y.toSetoids) :
    Hom.toSetoidsMor (isoOfSetoids e).inv = e.inv := sorry

end isoOfSetoids

end StackOver.Setoids

end CategoryTheory
