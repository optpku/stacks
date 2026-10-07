module

public import ReasLib.RingTheory.IntegralClosure.FlatEpimorphism
import StacksCheckRecall

@[expose] public section

/-!
# Integral closure for flat injective epimorphisms

Lemma 15.105.21 is owned by the reusable flat-epimorphism theorem.

@stack 092V
-/

/- Lemma 15.105.21: a flat injective epimorphism from a ring of weak dimension
at most one introduces no new integral elements. -/
@[stacks 092V "Lemma 15.105.21"]
#check @Algebra.IsEpi.isIntegrallyClosedIn_of_flat_of_injective_of_weakDimensionLE_one
