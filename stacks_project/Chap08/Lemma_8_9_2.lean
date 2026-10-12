/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Stackification
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.9.2 (0436): every morphism from the source of a groupoid stackification to a stack
factors through the stackification up to an invertible `2`-cell. The groupoid owner accepts the
stackification predicate directly. -/
@[stacks 0436 "factorization through a groupoid stackification"]
#check @FiberedCategoryOver.Groupoids.Hom.IsStackification.lift

/- The local-equivalence and heterogeneous forms remain reusable companions. -/
#check @FiberedCategoryOver.Groupoids.Hom.IsLocalEquivalence.lift
#check @CartesianBasedFunctor.IsStackification.lift

/- The corresponding uniqueness APIs retain the chosen factorization cells. The heterogeneous
owner is the operational form for enlarged-universe stackification targets. -/
#check @FiberedCategoryOver.Groupoids.Hom.IsStackification.liftIsoUnique
#check @CartesianBasedFunctor.IsStackification.liftIsoUnique

/- The Hom-category universal properties package existence and uniqueness together. -/
#check @StackOver.Groupoids.Hom.precomp_isEquivalence
#check @FiberedCategoryOver.Groupoids.Hom.IsStackification.precomp_isEquivalence

end CategoryTheory
