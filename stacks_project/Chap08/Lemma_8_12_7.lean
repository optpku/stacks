/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.InGroupoids
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.12.7 (tag 04WH): an explicitly chosen localized pushforward projection of a category
fibred in groupoids is again fibred in groupoids. -/
@[stacks 04WH]
#check @Functor.Pushforward.projectionInGroupoids
#check @FiberedCategoryOver.Groupoids.Pushforward.ProjectionChoice
#check @FiberedCategoryOver.Groupoids.Pushforward.ProjectionChoice.ofRawWith
#check @FiberedCategoryOver.Groupoids.Pushforward.ProjectionChoice.ofRaw
#check @FiberedCategoryOver.Groupoids.Pushforward.ProjectionChoice.canonical
#check @FiberedCategoryOver.Groupoids.Pushforward.ProjectionChoice.toFibered
#check @FiberedCategoryOver.Groupoids.pushforward
#check @FiberedCategoryOver.Groupoids.pushforward.total
#check @FiberedCategoryOver.Groupoids.pushforward.toFibered

end CategoryTheory
