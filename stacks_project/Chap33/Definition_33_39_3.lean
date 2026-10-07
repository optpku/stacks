module

public import ReasLib.RingTheory.Normalization.Basic
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 33.39.3 (0C3T): the normalization `δ`-invariant is the canonical
`Normalization.deltaInvariant A`, whose definition is independent of reducedness, Nagata, and
dimension hypotheses. -/
@[stacks 0C3T] #check
  (Normalization.deltaInvariant : ∀ (A : Type u) [CommRing A], ℕ∞)

#check
  (Normalization.deltaInvariant_def :
    ∀ (A : Type u) [CommRing A],
      Normalization.deltaInvariant A = Module.length A (Normalization.quotient A))

end
