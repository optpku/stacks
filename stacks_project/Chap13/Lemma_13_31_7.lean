module

import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KInjective.Global
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.31.7

K-injective replacements are modeled by the reusable
`CochainComplex.KInjectiveResolution` right-resolution facade. The global right-derived
existence criterion therefore belongs to the neutral K-injective computation API.
-/

/- Lemma 13.31.7 (Stacks 070K) (1): K-injective resolutions at every
complex give global right-derived existence. -/
@[stacks 070K] #check
  @CategoryTheory.Functor.KInjective.RightDerived.hasFunctor_of_kInjective_resolutions

/- Lemma 13.31.7 (Stacks 070K) (2): a K-injective complex computes the
right-derived value of every functor out of the homotopy category. -/
@[stacks 070K] #check
  @CategoryTheory.Functor.KInjective.computesAt
