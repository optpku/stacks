module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bilimit transfer for full-subbicategory pseudopullback cones

This leaf contains the universal-property layer for `PseudoPullbackCone.inFull`. Concrete cone
data and their ambient readouts are owned by `FullSubbicategory.Basic`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u w' v' u'

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {C : Type u'} [Bicategory.{w', v'} C]
variable (P : ObjectProperty C)

variable {X Y Z : P.FullSubbicategory}
variable {f : X ⟶ Z} {g : Y ⟶ Z}

/-- A bilimit pseudopullback cone remains bilimit after restriction to a full subbicategory,
provided its apex belongs to the selected object property. -/
@[stacks 02XQ "bilimit transfer to a full subbicategory"]
instance inFull.isBilimit
    (S : PseudoPullbackCone f.hom g.hom) [S.IsBilimit] (hpt : P S.pt) :
    (inFull P S hpt).IsBilimit := sorry

/- The instance defers only the universal-property proof; no cone data are selected here. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
