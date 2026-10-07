module

public import ReasLib.RingTheory.Flatness.FiniteInjective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.21.5 (0533)

@stack 0533
-/

/- Lemma 15.21.5, Stacks `0533`: flatness descends from a finite injective scalar extension over
a Noetherian ring. -/
@[stacks 0533 "Lemma 15.21.5, flatness descent along a finite injective map"]
#check @Module.Flat.of_finite_injective_baseChange
