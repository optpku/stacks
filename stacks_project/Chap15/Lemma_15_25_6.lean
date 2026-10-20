module

public import ReasLib.Algebra.Module.FinitePresentation.ValuationRing
import StacksCheckRecall

/-!
# Lemma 15.25.6

@stack 053E

Finite-presentation results for flat finite-type algebras and finite modules over valuation rings
are owned by the reusable valuation-ring API.
-/

@[expose] public section

/- Lemma 15.25.6 (1): a flat finite-type algebra over a valuation ring is finitely presented. -/
@[stacks 053E "Lemma 15.25.6 (1)"]
#check @Algebra.FinitePresentation.ofFlatFiniteTypeValuationRing

/- Lemma 15.25.6 (2): a finite module over a finite-type algebra over a valuation ring is
finitely presented when it is flat over the valuation ring. -/
@[stacks 053E "Lemma 15.25.6 (2)"]
#check @Module.FinitePresentation.ofFiniteFlatFiniteTypeValuationRing
