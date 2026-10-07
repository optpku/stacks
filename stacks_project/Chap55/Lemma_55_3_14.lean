module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.NumericalType.InvariantBounds

namespace NumericalType

/- Lemma 55.3.14: a minimal numerical type with more than one index has genus at
least its topological genus. -/
@[stacks 0C7C] #check (NumericalType.topologicalGenus_le_genus :
  (T : NumericalType) → T.IsMinimal → 1 < T.n → (T.topologicalGenus : ℤ) ≤ T.genus)

end NumericalType
