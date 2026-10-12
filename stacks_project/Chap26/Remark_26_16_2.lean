/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Forget

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/- Remark 26.16.2: the fibre product of two scheme morphisms is a fibre
product in locally ringed spaces. -/
@[stacks 01JN "canonical underlying locally ringed-space pullback"]
#check Scheme.Pullback.isPullback_toLocallyRingedSpace f g

/- Generic and cone-level interfaces inherited from the canonical pullback square. -/
#check (Scheme.Pullback.isPullback_toLocallyRingedSpace f g).isLimit
#check Scheme.forgetToLocallyRingedSpace_hasPullback f g
#check Scheme.forgetToLocallyRingedSpace_preservesPullbacks

end AlgebraicGeometry
