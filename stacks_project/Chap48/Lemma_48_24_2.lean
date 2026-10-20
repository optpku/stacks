module

import ReasLib.AlgebraicGeometry.Scheme.Gorenstein.CohenMacaulay
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Gorenstein

/- Lemma 48.24.2 -/
@[stacks 0C00] #check (AlgebraicGeometry.Scheme.Gorenstein.instCohenMacaulay :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.Scheme.Gorenstein X],
    AlgebraicGeometry.Scheme.CohenMacaulay X)

end AlgebraicGeometry.Scheme.Gorenstein
