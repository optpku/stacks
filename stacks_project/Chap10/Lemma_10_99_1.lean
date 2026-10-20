module

public import ReasLib.RingTheory.Flatness.LocalCriterion
import StacksCheckRecall

@[expose] public section

/-!
@stack 00ME

# A local criterion for injectivity and flat cokernels
-/

/- Lemma 10.99.1 (1): closed-fiber injectivity implies injectivity of the original linear map. -/
@[stacks 00ME "(1)"]
#check @LinearMap.injective_of_mod_maximalIdeal_injective

/- Lemma 10.99.1 (2): the same hypothesis makes the quotient by the range flat. -/
@[stacks 00ME "(2)"]
#check @LinearMap.flat_quotient_range_of_mod_maximalIdeal_injective

#print axioms LinearMap.injective_of_mod_maximalIdeal_injective
#print axioms LinearMap.flat_quotient_range_of_mod_maximalIdeal_injective
