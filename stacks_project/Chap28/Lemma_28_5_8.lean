/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.Noetherian
import StacksCheckRecall

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} [IsNoetherian X]

/- Lemma 28.5.8: any morphism of schemes `f : X ⟶ Y` with `X` Noetherian is quasi-compact. This is
exactly the canonical instance `AlgebraicGeometry.quasiCompact_of_noetherianSpace_source`,
specialized through `AlgebraicGeometry.IsNoetherian.noetherianSpace`. -/
@[stacks 01P0]
#check (AlgebraicGeometry.quasiCompact_of_noetherianSpace_source (X := X) (Y := Y) :
  ∀ f : X ⟶ Y, QuasiCompact f)

end AlgebraicGeometry
