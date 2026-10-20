module

import Mathlib.AlgebraicGeometry.Noetherian
import StacksCheckRecall

universe u

/- Lemma 28.5.4: A locally Noetherian scheme is quasi-separated. -/
@[stacks 01OY]
#check (AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}, [AlgebraicGeometry.IsLocallyNoetherian X] →
    QuasiSeparatedSpace X)
