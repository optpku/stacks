module

public import ReasLib.RingTheory.Coherent.Operations
public import ReasLib.RingTheory.Coherent.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.ShortComplex
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.90.3

@stack 05CW
-/

/-!
# Chapter 10 Compatibility Facade

Lemma 10.90.3 is represented by the neutral closure API for coherent modules.
-/

/- Lemma 10.90.3 (Tag 05CW): finite submodules of coherent modules are coherent; the shared
module also exposes the kernel, image, cokernel, equivalence, and short-exact closure APIs used
by its downstream applications. -/
@[stacks 05CW "finite presentation"]
#check @finitePresentation_of_coherent
@[stacks 05CW "finite submodule"]
#check @coherent_submodule_of_finite
@[stacks 05CW "linear equivalence invariance"]
#check @coherent_of_linearEquiv
@[stacks 05CW "finite kernel"]
#check @ker_finite_of_finite_of_coherent
@[stacks 05CW "coherent range"]
#check @range_coherent_of_finite_of_coherent
@[stacks 05CW "coherent cokernel"]
#check @cokernel_coherent_of_finite_of_coherent
@[stacks 05CW "coherent kernel"]
#check @ker_coherent_of_coherent
@[stacks 05CW "coherent cokernel criterion"]
#check @cokernel_coherent_of_coherent
@[stacks 05CW "short-exact source as kernel"]
#check @CategoryTheory.ShortComplex.ShortExact.sourceEquivKer
@[stacks 05CW "short-exact target as quotient"]
#check @CategoryTheory.ShortComplex.ShortExact.quotientRangeEquivTarget
@[stacks 05CW "short-exact middle coherence"]
#check @CategoryTheory.ShortComplex.coherent_X2_of_shortExact
@[stacks 05CW "short-exact source coherence"]
#check @CategoryTheory.ShortComplex.coherent_X1_of_shortExact
@[stacks 05CW "short-exact target coherence"]
#check @CategoryTheory.ShortComplex.coherent_X3_of_shortExact
