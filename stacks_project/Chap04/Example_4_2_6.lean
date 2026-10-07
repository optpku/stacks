module

public import ReasLib.CategoryTheory.SingleObj.Reconstruction
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable (G : Type u) [Group G]
variable {C : Type u} [Category.{v} C] [Subsingleton C] (c : C)

/- Example 4.2.6 (1): a group `G` determines the one-object groupoid `SingleObj G`; its unique
hom-type is `G`, and `SingleObj.comp_as_mul` identifies composition with the group law. -/
@[stacks 0019 "group to one-object groupoid"]
#check (SingleObj.groupoid G : Groupoid (SingleObj G))

/- The converse needs an equivalence without introducing new bundled data at the statement stage.
`SingleObj.functor (MonoidHom.id (End c))` is the canonical realization functor;
`SingleObj.Reconstruction.toEnd` only identifies endomorphisms of an already constructed model, while
`Functor.asEquivalence` derives bundled equivalence data from an `IsEquivalence` instance. Thus the
source is represented by the `IsEquivalence` property of the explicit canonical functor.
The neutral owner observes that groupoidness is unnecessary for this categorical equivalence:
`c : C` supplies existence and `[Subsingleton C]` supplies uniqueness. Downstream users can
recover a bundled equivalence with `Functor.asEquivalence`. -/

/- Example 4.2.6 (2): if a groupoid `C` has the chosen object `c` and a subsingleton object type,
then the canonical functor from `SingleObj (End c)` to `C` is an equivalence. -/
@[stacks 0019 "one-object groupoid from endomorphism group"]
#check (SingleObj.Reconstruction.isEquivalence c :
  (SingleObj.functor (MonoidHom.id (End c))).IsEquivalence)

/- The explicit equivalence packages the same forward and inverse constructions for consumers
that need to transport objects or morphisms, rather than only query the equivalence property. -/
@[stacks 0019 "explicit one-object reconstruction equivalence"]
#check (SingleObj.Reconstruction.equivalence c : SingleObj (End c) ≌ C)

end CategoryTheory
