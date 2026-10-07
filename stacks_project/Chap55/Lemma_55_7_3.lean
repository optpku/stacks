module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.InvariantBounds

@[expose] public section

namespace NumericalType

/- Lemma 55.7.3: for a minimal numerical type of genus `g ≥ 2`, every
multiplicity-weighted absolute intersection is bounded by `768 * g`. -/
@[stacks 0C9W] #check (NumericalType.absoluteIntersectionBound :
  (g : ℤ) → 2 ≤ g → (T : NumericalType) → T.genus = g → T.IsMinimal →
    (i j : Fin T.n) → (T.multiplicity i : ℤ) * |T.intersection i j| ≤ 768 * g)

end NumericalType
