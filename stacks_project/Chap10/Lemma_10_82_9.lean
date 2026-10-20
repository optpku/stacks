module

public import ReasLib.LinearAlgebra.UniversallyInjective.Operations
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.82.9 (Tag 05CI): composition preserves universal injectivity.

@stack 05CI
-/
@[stacks 05CI]
#check LinearMap.universallyInjective_comp
