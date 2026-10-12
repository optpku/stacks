/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Basic

/-!
# Morphisms of stacks in sets

This file provides the direct forgetful and lifting constructions between morphisms of stacks in
sets and morphisms of the corresponding set-fibred categories.
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

/-- The underlying morphism of stacks in setoids. -/
@[stacks 042Z "stack-in-sets setoid morphism owner"]
abbrev toSetoidsMor (F : X ⟶ Y) : X.toSetoids ⟶ Y.toSetoids :=
  (StackOver.Sets.forget J).map F

/-- The underlying morphism of stacks in groupoids, obtained through the canonical setoid owner.

This is a named readout rather than a second construction: the set-valued layer is a
specialization of stacks in setoids, whose ambient groupoid morphism remains the canonical
owner for downstream groupoid-level arguments.
-/
@[stacks 042Z "stack-in-sets groupoid morphism readout"]
abbrev toGroupoidsMor (F : X ⟶ Y) : X.toGroupoids ⟶ Y.toGroupoids :=
  StackOver.Setoids.Hom.toGroupoidsMor (toSetoidsMor F)

/-- The underlying morphism of categories fibred in sets. -/
@[stacks 042Z "stack-in-sets set morphism owner"]
def toSetsMor (F : X ⟶ Y) : X.toSets ⟶ Y.toSets :=
  FiberedCategoryOver.Sets.ofBasedFunctor
    (StackOver.Setoids.Hom.toBasedFunctor (toSetoidsMor F))

/-- The underlying morphism of the ambient categories fibred over `C`.

The definition follows the same chain as the setoid layer, so consumers can move to the
fibered-category API without rebuilding a based functor or choosing a local instance.
-/
@[stacks 042Z "stack-in-sets fibred morphism readout"]
abbrev toFiberedMor (F : X ⟶ Y) :
    X.toFiberedCategoryOver ⟶ Y.toFiberedCategoryOver :=
  StackOver.Groupoids.Hom.toFiberedMor (toGroupoidsMor F)

/-- Forgetting the set-valued owner from `toSetsMor F` retains the same underlying based
functor as the setoid-stack view of `F`. -/
@[simp, stacks 042Z "stack-in-sets morphism forgetful comparison"]
theorem toSetsMor.toSetoids (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toBasedFunctor
        (StackOver.Setoids.Hom.toSetoidsMor (toSetoidsMor F)) =
      FiberedCategoryOver.Sets.toBasedFunctor (toSetsMor F) := sorry

/-- The underlying based functor of a morphism of stacks in sets. -/
@[stacks 042Z "stack-in-sets based morphism owner"]
abbrev toBasedFunctor (F : X ⟶ Y) :=
  FiberedCategoryOver.Sets.toBasedFunctor (toSetsMor F)

/-- The underlying total-category functor of a morphism of stacks in sets. -/
@[stacks 042Z "stack-in-sets total morphism owner"]
abbrev toFunctor (F : X ⟶ Y) :=
  FiberedCategoryOver.Sets.toFunctor (toSetsMor F)

/-- The strict commutation of the underlying total functor with the projections. -/
@[stacks 042Z "stack-in-sets morphism projection equation"]
abbrev comm (F : X ⟶ Y) : toFunctor F ⋙ Y.p = X.p :=
  FiberedCategoryOver.Sets.comm (toSetsMor F)

/-- The induced functor on the fibre over `U`. -/
@[stacks 042Z "stack-in-sets fiber morphism owner"]
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  FiberedCategoryOver.Sets.fiberFunctor (toSetsMor F) U

/-- A morphism of stacks in sets is an equivalence over the base when its underlying based
functor is an equivalence. -/
@[stacks 042Z "stack-in-sets morphism equivalence predicate"]
abbrev IsEquivalence (F : X ⟶ Y) : Prop := (toBasedFunctor F).IsEquivalence

/-- Lift a morphism of the underlying stacks in setoids to a morphism of stacks in sets. -/
@[stacks 042Z "stack-in-sets setoid morphism lift"]
abbrev lift (F : X.toSetoids ⟶ Y.toSetoids) : X ⟶ Y :=
  Bicategory.InducedBicategory.mkHom F

/-- Lift a morphism of the underlying categories fibred in sets to a morphism of stacks in sets. -/
@[stacks 042Z "stack-in-sets set morphism lift"]
def ofSetsMor (F : X.toSets ⟶ Y.toSets) : X ⟶ Y :=
  lift (StackOver.Setoids.Hom.ofSetoidsMor
    (FiberedCategoryOver.Setoids.ofBasedFunctor
      (FiberedCategoryOver.Sets.toBasedFunctor F)))

end StackOver.Sets.Hom

end CategoryTheory
