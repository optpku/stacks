module

public import ReasLib.RingTheory.Normal.Nagata.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Universally Japanese Criterion

@stack 0351

This source file recalls the reusable finite-type `N-1` criterion for the
universally Japanese condition.
-/

-- Lemma 10.162.3, tag `0351`: a ring is universally Japanese if every finite-type
-- domain algebra over it is `N-1`.
@[stacks 0351]
#check @UniversallyJapaneseRing.of_forall_finiteType_isN1
