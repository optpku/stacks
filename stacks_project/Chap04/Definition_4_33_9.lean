module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe u v w vS

variable (C : Type u) [Category.{v} C]

/- Definition 4.33.9: `FiberedCategoryOver C` is the `2`-category of categories fibred over
`C`, functors over `C` preserving strongly cartesian arrows, and vertical natural
transformations. The reusable owner is the locally induced bicategory inside `BasedCategory C`;
it does not choose cleavages. -/
@[stacks 02XP "2-category of fibred categories over the base"]
#check (FiberedCategoryOver.{u, v, w, vS} C :
  Type max (w + 1) (vS + 1) u v)

/- Companion recall: fibredness is the object property defining the carrier. -/
#check BasedCategory.isFibered

/- Companion recall: preservation of strongly cartesian arrows is the hom property. -/
#check FiberedCategoryOver.homProperty

/- Companion recall: the canonical strict pseudofunctor forgets to categories over `C`. -/
#check FiberedCategoryOver.toBased

/- Companion recall: the universe-polymorphic presentation of an individual cartesian
`1`-morphism. -/
#check CartesianBasedFunctor

end CategoryTheory
