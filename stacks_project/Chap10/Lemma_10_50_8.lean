module

public import ReasLib.RingTheory.Valuation.Algebraic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.50.8

@stack 0AAV

The algebraic-extension statement is owned by `ValuationSubring`; contraction
itself remains the canonical bundled `ValuationSubring.comap` construction.
-/

@[stacks 0AAV]
#check @ValuationSubring.not_isField_comap_algebraMap_of_isAlgebraic

@[stacks 0AAV "valuation-subring contraction"]
#check @ValuationSubring.comap

@[stacks 0AAV "algebraic field criterion"]
#check @isField_of_isIntegral_of_isField'
