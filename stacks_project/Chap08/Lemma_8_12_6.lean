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

/- The strongly-cartesian criterion underlying Lemma 8.12.6 (tag 04WG). -/
#check @Functor.Pushforward.Q.map.isStronglyCartesian.iffSnd
#check @Functor.Pushforward.Q.map.isStronglyCartesian.ofSnd
#check @Functor.Pushforward.Q.snd.isStronglyCartesian.ofMap

end CategoryTheory
