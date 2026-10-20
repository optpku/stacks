/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Positive
public import ReasLib.CategoryTheory.InverseSystem.OrderDual.Limits

/-!
# Limits of Positive Inverse Systems

This leaf specializes the generic order-dual limit compatibility to the successor map of a positive
inverse system.  It is independent of any additive or concrete realization of the target category.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.PNatInverseSystem

variable {C : Type u} [Category.{v} C]

/-- A limit projection to the successor stage followed by the successor transition is the
projection to the current stage. -/
theorem limitProjection_comp_stepMap (F : PNatInverseSystem C) [HasLimit F] (n : ℕ+) :
    limit.π F (OrderDual.toDual (n + 1)) ≫ F.stepMap n =
      limit.π F (OrderDual.toDual n) := sorry

end CategoryTheory.PNatInverseSystem
