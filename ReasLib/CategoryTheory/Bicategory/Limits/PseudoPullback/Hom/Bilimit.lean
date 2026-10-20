/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Biterminal
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Functoriality

/-!
# Biterminal and bilimit readable pseudopullback cones

This property leaf transports the generic pseudocone biterminal/bilimit bridge across the
normalization biequivalence. The basic readable morphism statements themselves require no
bilimit hypothesis.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- In a locally groupoidal ambient bicategory, biterminality among readable cospan-shaped
cones is equivalent to the generic representability-based bilimit property. -/
@[stacks 003Q "2-fibre product as a biterminal cospan-shaped bilimit"]
theorem isBiterminal_iff_isBilimit
    [IsLocallyGroupoid B] (S : PseudoPullbackCone f g) :
    Bicategory.IsBiterminal S ↔ S.IsBilimit := sorry

/-- A readable bilimit pseudopullback cone in a locally groupoidal bicategory is biterminal in
the bicategory of readable cones. -/
theorem isBiterminal_of_isBilimit [IsLocallyGroupoid B]
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    Bicategory.IsBiterminal S := sorry

/-- A biterminal readable pseudopullback cone in a locally groupoidal bicategory satisfies the
represented bilimit universal property. -/
theorem isBilimit_of_isBiterminal [IsLocallyGroupoid B]
    (S : PseudoPullbackCone f g) [Bicategory.IsBiterminal S] :
    S.IsBilimit := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
