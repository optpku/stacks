/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Pith.Bilimit

/-!
# Biterminality after restricting a pseudopullback cone to the pith

This module adds the property-level consequence of the data construction in
`PseudoPullbackCone.toPith`. It is kept separate from that construction so users needing only
the pith cone do not import the bicategory of readable cone morphisms.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

namespace toPith

/-- Explicitly transport a bilimit witness to biterminality after restricting to the pith. -/
theorem isBiterminalOf (P : PseudoPullbackCone f g) (h : P.IsBilimit) :
    Bicategory.IsBiterminal P.toPith := sorry
/- Proof strategy: apply `toPith.isBilimitOf` and then
`PseudoPullbackCone.isBiterminal_of_isBilimit` in `Pith B`. -/

/-- Restricting a bilimit pseudopullback cone to the pith produces a biterminal object in the
bicategory of readable pith-valued pseudopullback cones. -/
instance isBiterminal (P : PseudoPullbackCone f g) [P.IsBilimit] :
    Bicategory.IsBiterminal P.toPith := sorry
/- Proof strategy: `toPith.isBilimit` preserves the represented bilimit property, then apply
`PseudoPullbackCone.isBiterminal_of_isBilimit` in the locally groupoidal bicategory `Pith B`. -/

end toPith

end Bicategory.PseudoPullbackCone

end CategoryTheory
