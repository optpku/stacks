/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Hom.Construction

/-!
# Computations for morphisms of stacks in sets

This file records the inverse, identity, and composition laws for the direct bridges between
stack morphisms and set-fibred morphisms.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Sets.Hom

variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Sets J}

/-- Projecting a lifted set-fibred morphism recovers the original morphism. -/
@[simp, stacks 042Z "stack-in-sets morphism projection"]
theorem toSetsMor.ofSetsMor (F : X.toSets ⟶ Y.toSets) :
    toSetsMor (ofSetsMor F) = F := sorry

/-- Lifting the set-fibred projection of a stack morphism recovers that morphism. -/
@[simp, stacks 042Z "stack-in-sets morphism lift projection"]
theorem ofSetsMor.toSetsMor (F : X ⟶ Y) :
    ofSetsMor (toSetsMor F) = F := sorry

/-- Forgetting an identity morphism of stacks in sets gives the identity morphism of the
underlying categories fibred in sets. -/
@[simp, stacks 042Z "stack-in-sets morphism identity"]
theorem toSetsMor.id (X : StackOver.Sets J) :
    toSetsMor (𝟙 X) = 𝟙 X.toSets := sorry

/-- Forgetting a composite of morphisms of stacks in sets gives the composite of the underlying
set-fibred morphisms. -/
@[simp, stacks 042Z "stack-in-sets morphism composition"]
theorem toSetsMor.comp {Z : StackOver.Sets J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toSetsMor (F ≫ G) = toSetsMor F ≫ toSetsMor G := sorry

/-- Lifting the identity set-fibred morphism gives the identity morphism of stacks in sets. -/
@[simp, stacks 042Z "stack-in-sets lifted identity"]
theorem ofSetsMor.id (X : StackOver.Sets J) :
    ofSetsMor (𝟙 X.toSets) = 𝟙 X := sorry

/-- Lifting a composite of set-fibred morphisms gives the composite of their lifts. -/
@[simp, stacks 042Z "stack-in-sets lifted composition"]
theorem ofSetsMor.comp {Z : StackOver.Sets J}
    (F : X.toSets ⟶ Y.toSets) (G : Y.toSets ⟶ Z.toSets) :
    ofSetsMor (F ≫ G) = ofSetsMor F ≫ ofSetsMor G := sorry

end StackOver.Sets.Hom

end CategoryTheory
