/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Pith.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Bilimits after restriction to the pith

This property leaf records that taking the cores of the hom-categories preserves the
represented bilimit property of a readable pseudopullback cone.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Explicitly transport a bilimit witness when restricting a pseudopullback cone to the
pith. -/
theorem toPith.isBilimitOf (P : PseudoPullbackCone f g) (h : P.IsBilimit) :
    P.toPith.IsBilimit := sorry

/-- Restricting a bilimit pseudopullback cone to the pith preserves its bilimit property. -/
instance toPith.isBilimit (P : PseudoPullbackCone f g) [P.IsBilimit] :
    P.toPith.IsBilimit := sorry

end CategoryTheory.Bicategory.PseudoPullbackCone
