module

public import ReasLib.Algebra.Module.End.FiniteLength
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.121.1 (0GSY)

This source file keeps the legacy repository path `Lemma_15_121_1`.  The concrete finite-length
endomorphism invariants and their short-exact API are owned by
`ReasLib.Algebra.Module.End.FiniteLength`.

@stack 0GSY
-/

/- Lemma 15.121.1 (1): the determinant is multiplicative in a compatible short exact
sequence. -/
@[stacks 0GSY "Lemma 15.121.1 (1): determinant multiplicativity"]
#check @Module.End.finiteLengthDeterminant_eq_mul_of_shortExact

/- Lemma 15.121.1 (2): the trace is additive in a compatible short exact sequence. -/
@[stacks 0GSY "Lemma 15.121.1 (2): trace additivity"]
#check @Module.End.finiteLengthTrace_eq_add_of_shortExact

/- Lemma 15.121.1 (3): the characteristic polynomial is multiplicative in a compatible short
exact sequence. -/
@[stacks 0GSY "Lemma 15.121.1 (3): characteristic-polynomial multiplicativity"]
#check @Module.End.finiteLengthCharpoly_eq_mul_of_shortExact

#check @Module.End.toPolynomialModule
#check @Module.End.StableCompositionSeries.factorMap
#check @Module.End.finiteLengthDeterminant
#check @Module.End.finiteLengthTrace
#check @Module.End.finiteLengthCharpoly

#print axioms Module.End.StableCompositionSeries.factorMap
#print axioms Module.End.finiteLengthDeterminant

end
