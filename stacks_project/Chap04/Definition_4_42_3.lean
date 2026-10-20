module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

/- Definition 4.42.3: a `1`-morphism of categories fibred in groupoids over `C` is
representable when every base change along a morphism from a slice fibration is representable.
The reusable owner is the morphism property `relativelyRepresentable` in the ordinary fixed
bicategory. -/
@[stacks 02Y7]
#check (relativelyRepresentable (C := C) :
  MorphismProperty (Groupoids C))

end FiberedCategoryOver.Groupoids

end CategoryTheory
