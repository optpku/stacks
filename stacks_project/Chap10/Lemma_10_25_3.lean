module

public import ReasLib.RingTheory.Localization.TotalQuotient
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.25.3

@stack 02LW

Both source clauses are exposed as concrete algebra equivalences.  The second
is the canonical specialization of the first to the nonzerodivisor submonoid.
-/

-- Lemma 10.25.3 (1): localization at nonzerodivisors does not change the
-- total quotient ring.
@[stacks 02LW "(1)"]
#check @Localization.fractionRingAlgEquiv

-- Lemma 10.25.3 (2): taking the total quotient ring twice gives the same
-- `R`-algebra up to canonical equivalence.
@[stacks 02LW "(2)"]
#check @FractionRing.iteratedAlgEquiv
