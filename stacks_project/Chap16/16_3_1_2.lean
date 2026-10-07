module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Cotangent.PresentationSequence

@[expose] public section

/- 16.3.1.2: adding the same free summand to the first two terms preserves the
exact conormal sequence and the surjectivity of its right map. -/
@[stacks 07EX]
#check @Algebra.Generators.Cotangent.exact_stabilized_postcomp_equiv
