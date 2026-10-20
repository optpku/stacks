/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
