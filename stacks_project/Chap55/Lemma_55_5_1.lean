module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.LinearTwo

/- Lemma 55.5.1: in a numerical type with more than two indices, two distinct
`(-2)`-indices with positive intersection have, up to reordering, one of the
three displayed weighted linear configurations. -/
@[stacks 0C7M] #check (NumericalType.linearTwoClassification :
  ∀ (T : NumericalType), 2 < T.n → ∀ (v : Fin 2 ↪ Fin T.n),
    (∀ r, NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r)) →
    0 < T.intersection (v 0) (v 1) →
    ∃ p : Equiv.Perm (Fin 2),
      NumericalType.IsLinearTwoConfiguration T (p.toEmbedding.trans v))
