module

import ReasLib.CategoryTheory.Filtration.Derived.Injective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.26.12

The bounded-below filtered-injective model, its equivalence certificate, and the resulting
equivalence are owned by a common namespace in ReasLib. No chapter-level alias is needed.
-/

namespace CategoryTheory.FilteredObject.FiniteDerived.Plus.FilteredInjective

/- Lemma 13.26.12 (`015Q`): bounded-below complexes of finite filtered-injective objects compute
the bounded-below finite filtered derived category. -/
@[stacks 015Q] #check @isEquivalence

/- The canonical functor whose equivalence is asserted by the lemma. -/
#check @functor

/- The proposition-level equivalence certificate used by downstream derived constructions. -/
#check @IsEquivalence

/- The canonical bundled equivalence under enough injectives. -/
#check @equivalenceOfEnoughInjectives

end CategoryTheory.FilteredObject.FiniteDerived.Plus.FilteredInjective
