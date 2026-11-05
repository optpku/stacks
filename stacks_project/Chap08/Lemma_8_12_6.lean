/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Cartesian
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.12.6 (tag 04WG): an explicitly chosen projection from the localized pushforward is
fibered and can be bundled without a local instance. -/
@[stacks 04WG]
#check @Functor.Pushforward.projectionIsFibered
#check @Functor.pushforward
#check @Functor.Pushforward.ProjectionChoice.canonical
#check @FiberedCategoryOver.Pushforward.ProjectionChoice
#check @FiberedCategoryOver.Pushforward.ProjectionChoice.ofRawWith
#check @FiberedCategoryOver.Pushforward.ProjectionChoice.ofRaw
#check @FiberedCategoryOver.Pushforward.ProjectionChoice.canonical
#check @FiberedCategoryOver.pushforward
#check @FiberedCategoryOver.pushforward.total
#check @FiberedCategoryOver.pushforward.p

/- Preservation of strongly cartesian arrows in Lemma 8.12.6 (tag 04WG). -/
#check @Functor.Pushforward.Q.map.isStronglyCartesian.ofSnd

end CategoryTheory
