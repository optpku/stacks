module

public import ReasLib.Algebra.Module.FinitePresentation.PreValuationRing
import StacksCheckRecall

/-!
# Lemma 15.125.3 (0ASP)

@stack 0ASP

The canonical owner uses `PreValuationRing R`, the project notion corresponding
to the equivalent generalized-valuation-ring conditions in Lemma 15.125.2.  Its
conclusion retains the source's finite family and actual linear isomorphism.
-/

@[expose] public section

/- Lemma 15.125.3 (0ASP), cyclic decomposition of finitely presented modules. -/
@[stacks 0ASP] #check
  @Module.FinitePresentation.exists_linearEquiv_directSum_principalQuotients_of_preValuationRing

#print axioms
  Module.FinitePresentation.exists_linearEquiv_directSum_principalQuotients_of_preValuationRing
