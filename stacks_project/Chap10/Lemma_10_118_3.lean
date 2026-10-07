module

public import ReasLib.RingTheory.GenericFlatness.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Generic Freeness over a Finite-Type Algebra

The source theorem is recalled through the canonical generic-flatness owner.

@stack 051T
-/

/- Lemma 10.118.3: if `R` is a domain, `S` is finite type over `R`, and `M`
is finite over `S`, some nonzero principal localization makes `S` and `M`
free over the localized base and finitely presented over the indicated rings.
These four conclusions are recorded by `GenericFlatness.LocalizationCondition`. -/
@[stacks 051T]
#check @GenericFlatness.exists_nonzero_away_of_finiteType
