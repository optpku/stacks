/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids.FiberIsoClassPresheaf.Criterion
public import ReasLib.CategoryTheory.Fibered.Setoids.Components.Grothendieck
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Hom.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated stacks in sets: bundled basic API

This leaf packages the neutral fibrewise-components construction for a stack in setoids.  It
owns the stack proof, the bundled object, and the represented morphism API; functorial and
pseudofunctorial consequences are provided by the sibling leaves.
-/

@[expose] public section

universe uC uS vC vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type uC} [Category.{vC} C]

namespace StackOver.Setoids

variable {J : GrothendieckTopology C}

/-- The associated category fibred in sets inherits the full stack-in-sets condition from the
original stack in setoids. This is the strong reusable owner; its site-level consequence is the
generic `IsStack.InSets.toOnSite` projection. -/
@[stacks 0432 "associated sets stack-in-sets instance"]
instance associatedSets.isStackInSets (X : StackOver.Setoids J) :
    IsStack.InSets J X.toSetoids.associatedSets.p := sorry

/-- The canonical stack in sets associated to a stack in setoids.  Its underlying set-fibred
category is the category of elements of the fiberwise isomorphism-class presheaf. -/
@[stacks 0432 "associated stack in sets"]
noncomputable def associatedSets (X : StackOver.Setoids J) : StackOver.Sets J :=
  StackOver.Sets.mk X.toSetoids.associatedSets
    (IsStack.InSets.toOnSite (associatedSets.isStackInSets X))

namespace associatedSets

/-- Forgetting the stack proof recovers the canonical associated category fibred in sets. -/
@[simp, stacks 0432 "associated set-fibred view"]
theorem toSets (X : StackOver.Setoids J) :
    X.associatedSets.toSets = X.toSetoids.associatedSets := sorry

/-- A morphism of stacks in setoids induces the canonical morphism between their associated
stacks in sets. The underlying map is the existing fibrewise-components Grothendieck map. -/
@[stacks 0432 "functoriality of associated stacks in sets"]
noncomputable def map {X Y : StackOver.Setoids J} (F : X ⟶ Y) :
    X.associatedSets ⟶ Y.associatedSets :=
  StackOver.Sets.Hom.ofSetsMor
    (FiberedCategoryOver.Setoids.components.mapHom
      (StackOver.Setoids.Hom.toSetoidsMor F))

namespace map

/-- Forgetting an associated-stack morphism recovers the neutral Grothendieck map on fibrewise
components. -/
@[simp, stacks 0432 "underlying associated-stack morphism"]
theorem toSetsMor {X Y : StackOver.Setoids J} (F : X ⟶ Y) :
    StackOver.Sets.Hom.toSetsMor (map F) =
      FiberedCategoryOver.Setoids.components.mapHom
        (StackOver.Setoids.Hom.toSetoidsMor F) := sorry

/-- The associated-stack construction sends identity morphisms to identity morphisms. -/
@[simp, stacks 0432 "associated-stack identity"]
theorem id (X : StackOver.Setoids J) :
    map (𝟙 X) = 𝟙 X.associatedSets := sorry

/-- The associated-stack construction preserves composition of morphisms. -/
@[simp, stacks 0432 "associated-stack composition"]
theorem comp {X Y Z : StackOver.Setoids J}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) = map F ≫ map G := sorry

/-- A `2`-morphism of setoid stacks identifies the induced morphisms of associated stacks in
sets. -/
@[stacks 0432 "associated-stack two-cell extensionality"]
theorem eq_of_hom {X Y : StackOver.Setoids J} {F G : X ⟶ Y} (eta : F ⟶ G) :
    map F = map G := sorry

end map

end associatedSets

/- Data audit: `associatedSets.map` delegates to the explicit quotient and category-of-elements
maps owned by `components.mapHom`. The bundled object only adds the stack-on-site proof; no
representatives of fibrewise isomorphism classes are selected here. -/

end StackOver.Setoids

end CategoryTheory
