module

public import ReasLib.CategoryTheory.Fibered.Pullback.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Definition 8.12.4 (tag 04WE): the source notation `f_* X` for a morphism of sites is
formally the pullback of the fibered category `X` along the functor on underlying sites.
The topology and the site-morphism packaging play no role in this construction, so the reusable
owner is the functorial `FiberedCategoryOver.pullback`. -/
@[stacks 04WE]
#check @FiberedCategoryOver.pullback

end CategoryTheory
