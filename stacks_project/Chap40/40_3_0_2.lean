module

import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
import StacksCheckRecall

universe u

/- 40.3.0.2: The map `(pr₀, c ∘ (i, 1))` identifies `pullback G.t G.t` with
`pullback G.s G.t`. -/
@[stacks 04LG] #check
  (AlgebraicGeometry.GroupoidScheme.targetComparisonIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      CategoryTheory.Limits.pullback G.t G.t ≅ CategoryTheory.Limits.pullback G.s G.t)
