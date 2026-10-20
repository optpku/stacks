module

public import ReasLib.Algebra.Module.Injective.FractionRing
import StacksCheckRecall

@[expose] public section

universe u v

/- Example 47.5.4
For a domain `R` with fraction field `K`, the canonical inclusion
`Algebra.linearMap R K` is an injective hull of `R`. -/
@[stacks 08Y5] #check (IsFractionRing.algebraMap_isInjectiveHull :
  ∀ (R : Type u) [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K],
    (Algebra.linearMap R K).IsInjectiveHull)
