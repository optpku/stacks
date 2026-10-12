/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for morphisms of stacks in groupoids

This file records the inverse, identity, and composition laws for the canonical bridge between
stack morphisms and groupoid-fibred morphisms.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Groupoids.Hom

variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Groupoids J}

/-- Projecting a lifted groupoid-fibred morphism recovers the original morphism. -/
@[simp, stacks 02ZK "projection after groupoid-stack morphism lift"]
theorem toGroupoidsMor.lift (F : X.toGroupoids ⟶ Y.toGroupoids) :
    toGroupoidsMor (lift F) = F := sorry

/-- Lifting the groupoid-fibred projection of a stack morphism recovers that morphism. -/
@[simp, stacks 02ZK "lift after groupoid-stack morphism projection"]
theorem lift.toGroupoidsMor (F : X ⟶ Y) :
    lift (toGroupoidsMor F) = F := sorry

/-- Forgetting an identity stack morphism gives the identity groupoid-fibred morphism. -/
@[simp, stacks 02ZK "groupoid-stack morphism identity projection"]
theorem toGroupoidsMor.id (X : StackOver.Groupoids J) :
    toGroupoidsMor (𝟙 X) = 𝟙 X.toGroupoids := sorry

/-- Forgetting a composite of stack morphisms gives the composite of their groupoid-fibred
projections. -/
@[simp, stacks 02ZK "groupoid-stack morphism composition projection"]
theorem toGroupoidsMor.comp {Z : StackOver.Groupoids J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toGroupoidsMor (F ≫ G) = toGroupoidsMor F ≫ toGroupoidsMor G := sorry

/-- Lifting the identity groupoid-fibred morphism gives the identity stack morphism. -/
@[simp, stacks 02ZK "groupoid-stack lifted identity morphism"]
theorem lift.id (X : StackOver.Groupoids J) :
    lift (𝟙 X.toGroupoids) = 𝟙 X := sorry

/-- Lifting a composite of groupoid-fibred morphisms gives the composite of their lifts. -/
@[simp, stacks 02ZK "groupoid-stack lifted morphism composition"]
theorem lift.comp {Z : StackOver.Groupoids J}
    (F : X.toGroupoids ⟶ Y.toGroupoids)
    (G : Y.toGroupoids ⟶ Z.toGroupoids) :
    lift (F ≫ G) = lift F ≫ lift G := sorry

end StackOver.Groupoids.Hom

end CategoryTheory
