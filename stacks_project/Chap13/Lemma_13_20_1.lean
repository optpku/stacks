module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
import StacksCheckRecall

@[expose] public section

/- Lemma 13.20.1 is the reusable bounded K-injective computation result and
its degree-zero injective specialization. -/
@[stacks 05TH] #check
  @CategoryTheory.Functor.KInjective.Bounded.computesAtOfInjectivePlus
@[stacks 05TH] #check @CategoryTheory.Functor.RightAcyclic.Bounded.of_injective
@[stacks 05TH] #check @CategoryTheory.Functor.RightAcyclic.of_injective

end
