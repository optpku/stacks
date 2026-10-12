/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids.FiberIsoClassPresheaf.Criterion
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids.AssociatedSets.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids.AssociatedSets.Comparison
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.6.3: a category fibered in setoids is a stack exactly when its presheaf of fiberwise
isomorphism classes is a sheaf. -/
@[stacks 0432]
#check @IsStack.InSetoids.iff_fiberIsoClass_isSheaf

#check @IsStack.InSetoids.iff_associatedSets
#check @StackOver.Setoids.associatedSets
#check @StackOver.Setoids.associatedSets.toSets

/- The associated-sets construction is functorial on the homotopy category and therefore defines
a pseudofunctor from setoid stacks to the locally discrete bicategory of set stacks. -/
#check @StackOver.Setoids.associatedSets.fiberedFunctor
#check @StackOver.Setoids.associatedSets.functor
#check @StackOver.Setoids.associatedSets.functor.obj
#check @StackOver.Setoids.associatedSets.functor.map
#check @StackOver.Setoids.associatedSets.functor.comp_toSets
#check @StackOver.Setoids.associatedSets.pseudofunctor
#check @StackOver.Setoids.associatedSets.pseudofunctor.obj
#check @StackOver.Setoids.associatedSets.pseudofunctor.map
#check @StackOver.Setoids.associatedSets.pseudofunctor.map₂
#check @StackOver.Setoids.associatedSets.pseudofunctor.mapId
#check @StackOver.Setoids.associatedSets.pseudofunctor.mapComp

/- Represented-morphism compatibility remains available for consumers working directly in the
setoid-stack bicategory. -/
#check @StackOver.Setoids.associatedSets.map
#check @StackOver.Setoids.associatedSets.map.toSetsMor
#check @StackOver.Setoids.associatedSets.map.id
#check @StackOver.Setoids.associatedSets.map.comp
#check @StackOver.Setoids.associatedSets.map.eq_of_hom
#check @FiberedCategoryOver.Setoids.toAssociatedSets.naturalityIso
#check @FiberedCategoryOver.Setoids.toAssociatedSets.naturalityIso.hom.app
#check @FiberedCategoryOver.Setoids.toAssociatedSets.naturalityIso.inv.app
#check @StackOver.Setoids.toAssociatedSets.naturalityIso
#check @StackOver.Setoids.toAssociatedSets.naturalityIso.hom.app
#check @StackOver.Setoids.toAssociatedSets.naturalityIso.inv.app
#check @StackOver.Setoids.toAssociatedSets
#check @StackOver.Setoids.toAssociatedSets.toSetoidsMor
#check @StackOver.Setoids.toAssociatedSets.isEquivalence

/- The source-facing stack predicate reduces to the ordinary stack condition once the setoid
fiber structure is fixed. -/
#check @IsStack.InSetoids.iff_isStackOnSite

end CategoryTheory
