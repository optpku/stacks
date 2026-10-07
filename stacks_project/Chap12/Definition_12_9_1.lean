module

public import Mathlib.CategoryTheory.Simple
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] (X : C)

/- Definition 12.9.1: simplicity is the canonical predicate saying that `X` is nonzero and has
only the two trivial subobjects. -/
@[stacks 0FCE]
#check Simple X

/- The subobject-order characterization is the canonical elimination interface. -/
#check simple_iff_subobject_isSimpleOrder X

end CategoryTheory
