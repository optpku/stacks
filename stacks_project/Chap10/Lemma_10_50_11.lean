module

public import Mathlib.RingTheory.Valuation.LocalSubring
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.50.11

@stack 090P
-/

/-!
# Valuation-subring intersection principles

Lemma 10.50.11 (Tag 090P) is a canonical recall block.  Its four source
clauses are owned by the generic integrally-closed subring and local-subring
theorems; specializing those owners to the image of a normal domain in its
fraction field belongs to the consumer, not to a chapter-local wrapper.
-/

/- Lemma 10.50.11 (1) (Tag 090P): existence of a valuation subring excluding an element outside an
integrally closed subring. -/
@[stacks 090P]
#check @Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn

/- Lemma 10.50.11 (2) (Tag 090P): the local-subring version of valuation-subring existence. -/
@[stacks 090P]
#check @LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn

/- Lemma 10.50.11 (3) (Tag 090P): an integrally closed subring is the intersection of containing
valuation subrings. -/
@[stacks 090P]
#check @Subring.eq_iInf_of_isIntegrallyClosedIn

/- Lemma 10.50.11 (4) (Tag 090P): a locally integrally closed local subring is the intersection of
dominating valuation subrings. -/
@[stacks 090P]
#check @LocalSubring.eq_iInf_of_isIntegrallyClosedIn
