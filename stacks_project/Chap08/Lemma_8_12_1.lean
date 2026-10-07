module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Cleavage
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.12.1 (tag 04WB): base change of a fibred projection along an arbitrary functor is
again fibred. -/
@[stacks 04WB]
#check @Limits.CategoricalPullback.Left.isFibered

/- The reusable data form retains the cleavage induced from the right leg, together with its
chosen reindexing object, cartesian arrow, map, and functor. -/
#check @Functor.Cleavage.ofRight
#check @Limits.CategoricalPullback.Cleavage.chosen
#check @Limits.CategoricalPullback.Cleavage.chosen.reindexObj
#check @Limits.CategoricalPullback.Cleavage.chosen.cartesianHom
#check @Limits.CategoricalPullback.Cleavage.chosen.reindexMap
#check @Limits.CategoricalPullback.Cleavage.chosen.reindex

end CategoryTheory
