/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials

/-!
# Base change of relative differentials on schemes

The canonical comparison from the pullback of relative differentials to the relative
differentials of a cartesian base change is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

variable {X X' S S' : Scheme.{u}}
variable {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- For a cartesian square of schemes, the canonical comparison from the pullback of
relative differentials to the relative differentials after base change is an isomorphism. -/
instance comparison_isIso_of_isPullback (hpb : IsPullback g' f' f g) :
    IsIso
      (RingedSpace.Hom.Differentials.comparison
        (hpb.toCommSq.map
          (Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace))) := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
