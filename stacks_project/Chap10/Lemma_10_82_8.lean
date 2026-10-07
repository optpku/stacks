module

public import ReasLib.LinearAlgebra.UniversallyInjective.Operations
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.82.8 (Tag 05CH): right tensoring preserves universal injectivity.

@stack 05CH
-/
@[stacks 05CH]
#check LinearMap.universallyInjective_rTensor
