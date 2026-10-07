module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex

@[expose] public section

namespace NumericalType

/- Definition 55.3.16: an index is a `(-2)`-index exactly when its component genus
is zero and its diagonal matrix entry is `-2` times its weight. -/
@[stacks 0C7E] #check (NumericalType.IsMinusTwoIndex :
  {n : ℕ} → (Fin n → ℕ) → (Fin n → ℕ) →
    Matrix (Fin n) (Fin n) ℤ → Fin n → Prop)

end NumericalType
