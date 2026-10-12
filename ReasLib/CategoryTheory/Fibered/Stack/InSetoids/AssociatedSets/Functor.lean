/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids.AssociatedSets.Basic
public import ReasLib.CategoryTheory.Fibered.Setoids.Components.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Forgetful
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated stacks in sets: functorial API

This leaf descends the neutral fibrewise-components pseudofunctor through the homotopy category
and then lifts it to the bundled stack-in-sets owner.  It does not duplicate the category-of-
elements construction owned by `FiberedCategoryOver.Setoids.components`.
-/

@[expose] public section

universe uC uS vC vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type uC} [Category.{vC} C]

namespace StackOver.Setoids

variable {J : GrothendieckTopology C}

namespace associatedSets

/-- The underlying set-fibred functor obtained by applying fibrewise components to setoid
stacks. Its source is the homotopy `1`-category because fibrewise components identify
`2`-isomorphic morphisms. -/
@[stacks 0432 "associated set-fibred functor"]
noncomputable def fiberedFunctor (J : GrothendieckTopology C) :
    Bicategory.HomotopyCategory (StackOver.Setoids J) ⥤
      FiberedCategoryOver.Sets C :=
  Bicategory.HomotopyCategory.map
      (StackOver.Setoids.toSetoids.pseudofunctor J).toPseudofunctor ⋙
    FiberedCategoryOver.Setoids.components C

/-- The object action of `fiberedFunctor` is the canonical associated category fibred in
sets. -/
@[simp, stacks 0432 "associated set-fibred object action"]
theorem fiberedFunctor.obj (X : StackOver.Setoids J) :
    (fiberedFunctor J).obj (Bicategory.HomotopyCategory.mk X) =
      X.toSetoids.associatedSets := sorry

/-- On a represented morphism, `fiberedFunctor` is the existing Grothendieck map on
fibrewise components. -/
@[simp, stacks 0432 "associated set-fibred morphism action"]
theorem fiberedFunctor.map {X Y : StackOver.Setoids J} (F : X ⟶ Y) :
    (fiberedFunctor J).map (Bicategory.HomotopyCategory.mkHom F) =
      FiberedCategoryOver.Setoids.components.mapHom
        (StackOver.Setoids.Hom.toSetoidsMor F) := sorry

/-- Fibrewise components of a setoid stack satisfy descent as a category fibred in sets. -/
@[stacks 0432 "fibrewise components preserve stacks"]
theorem fiberedFunctor.obj_mem
    (X : Bicategory.HomotopyCategory (StackOver.Setoids J)) :
    IsStack.OnSite.Sets.objectProperty J ((fiberedFunctor J).obj X) := sorry

/-- The canonical functor from the homotopy `1`-category of setoid stacks to stacks in sets.
It lifts `fiberedFunctor` through the direct full-subbicategory presentation of set stacks and
then uses the established equivalence with `StackOver.Sets J`. -/
@[stacks 0432 "associated stacks in sets functor"]
noncomputable def functor (J : GrothendieckTopology C) :
    Bicategory.HomotopyCategory (StackOver.Setoids J) ⥤ StackOver.Sets J :=
  (IsStack.OnSite.Sets.objectProperty J).lift
      (fiberedFunctor J) (fiberedFunctor.obj_mem (J := J)) ⋙
    ObjectProperty.FullSubbicategory.fromFullSubcategory
      (IsStack.OnSite.Sets.objectProperty J) ⋙
    StackOver.Sets.Restrict.toStack (J := J)

/-- The stack-valued associated-sets functor has the existing `associatedSets` object action. -/
@[simp, stacks 0432 "associated stack object action"]
theorem functor.obj (X : StackOver.Setoids J) :
    (functor J).obj (Bicategory.HomotopyCategory.mk X) = X.associatedSets := sorry

/-- On represented morphisms, the stack-valued associated-sets functor has the existing `map`
action. -/
@[simp, stacks 0432 "associated stack morphism action"]
theorem functor.map {X Y : StackOver.Setoids J} (F : X ⟶ Y) :
    (functor J).map (Bicategory.HomotopyCategory.mkHom F) = map F := sorry

/-- Forgetting the stack proof from the associated-sets functor recovers the neutral
set-fibred `fiberedFunctor`. -/
@[stacks 0432 "associated stack forgetful comparison"]
theorem functor.comp_toSets (J : GrothendieckTopology C) :
    functor J ⋙ StackOver.Sets.toSets.functor J = fiberedFunctor J := sorry

/-- The associated-sets functor is an equivalence after passing from setoid stacks to their
homotopy `1`-category. -/
@[stacks 0432 "associated-stacks equivalence on homotopy categories"]
instance functor.isEquivalence (J : GrothendieckTopology C) :
    (functor J).IsEquivalence := sorry

end associatedSets

/- Data audit: `fiberedFunctor` delegates to the existing homotopy-category functor
`StackOver.Setoids.toSetoids.pseudofunctor` followed by `components`; `functor` only adds the
stack-property witness through the shared direct-to-nested restriction bridge. -/

end StackOver.Setoids

end CategoryTheory
