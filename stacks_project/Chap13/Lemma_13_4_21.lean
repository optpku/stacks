module

import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Composition.Naturality
import StacksCheckRecall

@[expose] public section

/- Lemma 13.4.21 is owned by the reusable exact-composition API for delta functors. -/
@[stacks 0151] #check @CategoryTheory.DeltaFunctor.postcomposeExactFunctor
#check @CategoryTheory.DeltaFunctor.postcomposeExactFunctor.δ
#check @CategoryTheory.DeltaFunctor.postcomposeExactFunctor.functor
#check @CategoryTheory.DeltaFunctor.precomposeExactFunctor
#check @CategoryTheory.DeltaFunctor.precomposeExactFunctor.δ
#check @CategoryTheory.DeltaFunctor.precomposeExactFunctor.functor

end
