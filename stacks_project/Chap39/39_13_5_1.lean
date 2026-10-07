module

import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
import StacksCheckRecall

universe u

/- 39.13.5.1: The map `(pr₀, c ∘ (i, 1))` identifies `pullback G.t G.t` with
`pullback G.s G.t`. -/
@[stacks 03C7] #check (AlgebraicGeometry.GroupoidScheme.targetComparisonIso :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
    CategoryTheory.Limits.pullback G.t G.t ≅
      CategoryTheory.Limits.pullback G.s G.t)
