module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Minimality

/- Lemma 55.3.13 -/
@[stacks 0C7B] #check (NumericalType.one_le_genus :
  ∀ (T : NumericalType) (hminimal : T.IsMinimal) (hn : 1 < T.n), 1 ≤ T.genus)
