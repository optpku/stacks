/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.EtaleLocal

universe u

/- Definition 41.21.4: on a locally Noetherian scheme, a normal crossings divisor is an
effective Cartier divisor which is étale-locally a strict normal crossings divisor at every
point of its support. -/
@[stacks 0BSF] #check (@AlgebraicGeometry.IsNormalCrossingsDivisor :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.IsLocallyNoetherian X →
    X.IdealSheafData → Prop)
