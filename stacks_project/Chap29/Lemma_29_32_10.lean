/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Differentials.BaseChange
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X X' S S' : Scheme.{u}}
variable (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
variable (hpb : IsPullback g' f' f g)

/- Lemma 29.32.10: for a cartesian square of schemes, the canonical comparison
`(g')^* Ω_{X/S} ⟶ Ω_{X'/S'}` is an isomorphism. -/
@[stacks 01V0] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.comparison_isIso_of_isPullback hpb :
    IsIso
      (RingedSpace.Hom.Differentials.comparison
        (hpb.toCommSq.map
          (Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace))))

end AlgebraicGeometry
