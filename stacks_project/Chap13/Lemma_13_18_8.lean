module

import ReasLib.Algebra.Homology.DerivedCategory.KInjective.Bounded
import StacksCheckRecall

@[expose] public section

/- Lemma 13.18.8 is the bounded-below injective view of Mathlib's canonical
homotopy-to-derived map bijection. -/
@[stacks 05TG] #check @CochainComplex.IsKInjective.Qh_map_bijective
@[stacks 05TG] #check @CochainComplex.InjectivePlus.toDerived_map_bijective

end
