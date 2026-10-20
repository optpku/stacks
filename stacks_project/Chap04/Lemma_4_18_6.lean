module

public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Criteria
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C]

/- Lemma 4.18.6: finite nonempty colimits, binary coproducts with coequalizers, and binary
coproducts with pushouts are equivalent conditions. -/
@[stacks 04AW "three equivalent criteria for finite nonempty colimits"]
#check (HasFiniteNonemptyColimits.tfae C :
  [HasFiniteNonemptyColimits C, HasBinaryCoproducts C ∧ HasCoequalizers C,
    HasBinaryCoproducts C ∧ HasPushouts C].TFAE)

end CategoryTheory.Limits
