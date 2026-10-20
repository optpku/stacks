/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Pith.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Symmetry.Basic

/-!
# Compatibility of pith restriction with pseudopullback symmetry

The pith restriction is defined fieldwise, so it commutes with exchanging the two cospan legs.
This small computation leaf keeps that naturality fact available without importing bilimit or
biterminal infrastructure.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Restricting a readable pseudopullback cone to the pith commutes with exchanging its legs. -/
@[simp]
theorem toPith.swap (P : PseudoPullbackCone f g) :
    P.toPith.swap = P.swap.toPith := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
