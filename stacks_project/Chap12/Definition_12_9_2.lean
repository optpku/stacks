module

public import Mathlib.CategoryTheory.Noetherian
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Definition 12.9.2 (1): `isArtinianObject` is the canonical object property for the descending
chain condition on subobjects. -/
@[stacks 0FCF]
#check (isArtinianObject : ObjectProperty C)

#check @IsArtinianObject C
#check isArtinianObject_iff_antitone_chain_condition

/- Definition 12.9.2 (2): the source's category-level condition is objectwise Artinianity.  This
does not add the essential-smallness field carried by mathlib's stronger class `Artinian C`. -/
#check ∀ X : C, IsArtinianObject X
#check Artinian C

end CategoryTheory
