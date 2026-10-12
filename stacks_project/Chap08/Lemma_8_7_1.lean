/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Setoids
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.7.1 (1), relative part: relative inertia is a stack on the site. -/
@[stacks 036Y "(1), relative inertia is a stack"]
#check @StackOver.relativeInertia

/- Lemma 8.7.1 (1), absolute part: absolute inertia is a stack on the site. -/
@[stacks 036Y "(1), absolute inertia is a stack"]
#check @StackOver.inertia

/- Lemma 8.7.1 (2), relative part: relative inertia is a stack in groupoids. -/
@[stacks 036Y "(2), relative inertia is a stack in groupoids"]
#check @StackOver.Groupoids.relativeInertia

/- Lemma 8.7.1 (2), absolute part: absolute inertia is a stack in groupoids. -/
@[stacks 036Y "(2), absolute inertia is a stack in groupoids"]
#check @StackOver.Groupoids.inertia

/- Lemma 8.7.1 (3), relative part: relative inertia is a stack in setoids. -/
@[stacks 036Y "(3), relative inertia is a stack in setoids"]
#check @StackOver.Setoids.relativeInertia

/- Lemma 8.7.1 (3), absolute part: absolute inertia is a stack in setoids. -/
@[stacks 036Y "(3), absolute inertia is a stack in setoids"]
#check @StackOver.Setoids.inertia

/- The shared owner also exposes stronger closure lemmas: the target of relative inertia only
needs to be a prestack, and the source and target total categories may live in independent
universes. -/
#check @BasedCategory.RelativeInertia.isStackOnSite
#check @BasedCategory.RelativeInertia.isStackInGroupoids
#check @BasedCategory.RelativeInertia.isStackInSetoids

/- Fixed-universe bundled morphisms specialize the same closure statements. -/
#check @FiberedCategoryOver.RelativeInertia.isStackOnSite
#check @FiberedCategoryOver.RelativeInertia.isStackInGroupoids
#check @FiberedCategoryOver.RelativeInertia.isStackInSetoids

end CategoryTheory
