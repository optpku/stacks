/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Symmetry.Bilimit

/-!
# Biterminality under pseudopullback symmetry

This leaf is the locally-groupoidal bridge from the represented bilimit API to the
biterminal formulation used for `2`-fibre products. It is kept separate from `Symmetry.Basic`
and `Symmetry.Bilimit`, since the biterminal bridge needs the readable cone bicategory.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- A biterminal readable pseudopullback cone remains biterminal after exchanging its legs. -/
theorem swap.isBiterminalOf [IsLocallyGroupoid B]
    (P : PseudoPullbackCone f g) (h : Bicategory.IsBiterminal P) :
    Bicategory.IsBiterminal P.swap := sorry
/- Proof strategy: use `isBilimit_of_isBiterminal` on `P`, transport the represented bilimit
property with `swap.isBilimitOf`, and apply `isBiterminal_of_isBilimit` to `P.swap`. -/

/-- A biterminal readable pseudopullback cone has a biterminal swapped cone. -/
instance swap.isBiterminal [IsLocallyGroupoid B]
    (P : PseudoPullbackCone f g) [Bicategory.IsBiterminal P] :
    Bicategory.IsBiterminal P.swap := sorry

/-- A readable pseudopullback cone is biterminal whenever its swapped cone is biterminal. -/
theorem isBiterminalOfSwap [IsLocallyGroupoid B]
    (P : PseudoPullbackCone f g) (h : Bicategory.IsBiterminal P.swap) :
    Bicategory.IsBiterminal P := sorry
/- Proof strategy: apply `swap.isBiterminalOf` to `P.swap` and use `swap.involution`. -/

/-- In a locally groupoidal bicategory, exchanging the legs preserves biterminality. -/
@[simp]
theorem swap.isBiterminal_iff [IsLocallyGroupoid B]
    (P : PseudoPullbackCone f g) :
    Bicategory.IsBiterminal P.swap ↔ Bicategory.IsBiterminal P := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
