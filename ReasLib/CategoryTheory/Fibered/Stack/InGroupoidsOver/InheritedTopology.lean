module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Stack.InheritedTopology.Composition
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver

/-!
# Inherited-topology stacks in groupoids

This module specializes the projection-level inherited-topology criterion to morphisms of the
bundled bicategory `StackOver.Groupoids J`.
-/

@[expose] public section

universe uC uX vC vX

namespace CategoryTheory

namespace StackOver.Groupoids.Hom

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Groupoids.{uC, vC, uX, vX} J}

/-- Lemma 8.10.5 (tag 06NX): a morphism of stacks in groupoids whose total functor is fibered
in groupoids is a stack in groupoids for the topology inherited from the target stack. -/
@[stacks 06NX]
theorem inheritedTopology.isStackInGroupoids
    (F : X ⟶ Y)
    [Functor.IsFibered.InGroupoids (toFunctor F)] :
    IsStack.InGroupoids (Y.p.inheritedTopology J) (toFunctor F) := sorry

end StackOver.Groupoids.Hom

end CategoryTheory
