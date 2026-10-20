/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Hom.Construction

/-!
# Computations for morphisms of stacks in setoids

This file records the inverse, identity, and composition laws for the direct bridges between
stack morphisms and setoid-fibred morphisms.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Setoids.Hom

variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Setoids J}

/-- Projecting a lifted setoid-fibred morphism recovers the original morphism. -/
@[simp, stacks 0433 "stack-in-setoids morphism projection"]
theorem toSetoidsMor.ofSetoidsMor (F : X.toSetoids ⟶ Y.toSetoids) :
    toSetoidsMor (ofSetoidsMor F) = F := sorry

/-- Lifting the setoid-fibred projection of a stack morphism recovers that morphism. -/
@[simp, stacks 0433 "stack-in-setoids morphism lift projection"]
theorem ofSetoidsMor.toSetoidsMor (F : X ⟶ Y) :
    ofSetoidsMor (toSetoidsMor F) = F := sorry

/-- Forgetting an identity morphism of stacks in setoids gives the identity morphism of the
underlying category fibred in setoids. -/
@[simp, stacks 0433 "stack-in-setoids morphism identity"]
theorem toSetoidsMor.id (X : StackOver.Setoids J) :
    toSetoidsMor (𝟙 X) = 𝟙 X.toSetoids := sorry

/-- Forgetting a composite of morphisms of stacks in setoids gives the composite of their
underlying setoid-fibred morphisms. -/
@[simp, stacks 0433 "stack-in-setoids morphism composition"]
theorem toSetoidsMor.comp {Z : StackOver.Setoids J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toSetoidsMor (F ≫ G) = toSetoidsMor F ≫ toSetoidsMor G := sorry

/-- The forward ambient based cell of `toSetoidsMor.compIso` is the identity. -/
@[simp, stacks 0433 "setoid-stack composition comparison forward readout"]
theorem toSetoidsMor.compIso.hom
    {Z : StackOver.Setoids J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    (toSetoidsMor.compIso F G).hom.hom =
      𝟙 (FiberedCategoryOver.Setoids.toBasedFunctor
        (toSetoidsMor F ≫ toSetoidsMor G)) := sorry

/-- The inverse ambient based cell of `toSetoidsMor.compIso` is the identity. -/
@[simp, stacks 0433 "setoid-stack composition comparison inverse readout"]
theorem toSetoidsMor.compIso.inv
    {Z : StackOver.Setoids J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    (toSetoidsMor.compIso F G).inv.hom =
      𝟙 (FiberedCategoryOver.Setoids.toBasedFunctor
        (toSetoidsMor (F ≫ G))) := sorry

/-- Lifting the identity setoid-fibred morphism gives the identity morphism of stacks in
setoids. -/
@[simp, stacks 0433 "stack-in-setoids lifted identity"]
theorem ofSetoidsMor.id (X : StackOver.Setoids J) :
    ofSetoidsMor (𝟙 X.toSetoids) = 𝟙 X := sorry

/-- Lifting a composite of setoid-fibred morphisms gives the composite of their lifts. -/
@[simp, stacks 0433 "stack-in-setoids lifted composition"]
theorem ofSetoidsMor.comp {Z : StackOver.Setoids J}
    (F : X.toSetoids ⟶ Y.toSetoids) (G : Y.toSetoids ⟶ Z.toSetoids) :
    ofSetoidsMor (F ≫ G) = ofSetoidsMor F ≫ ofSetoidsMor G := sorry

end StackOver.Setoids.Hom

end CategoryTheory
