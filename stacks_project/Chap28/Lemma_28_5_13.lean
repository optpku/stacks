module

public import ReasLib.AlgebraicGeometry.Noetherian.CountableDense
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u

/- Lemma 28.5.13: if `S` is a Noetherian scheme and `T ⊆ S` is an infinite dense subset, then
`T` contains a countable subset which is dense in `S`. -/
@[stacks 0G2F] #check
  (AlgebraicGeometry.Scheme.exists_countable_dense_subset_of_infinite_dense :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {T : Set S},
      Dense T → T.Infinite → ∃ E ⊆ T, E.Countable ∧ Dense E)
