module

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/- Lemma 29.2.7: a closed immersion is separated. -/
@[stacks 01QU] #check
  (AlgebraicGeometry.IsSeparated.isSeparated_of_mono f : AlgebraicGeometry.IsSeparated f)

end AlgebraicGeometry
