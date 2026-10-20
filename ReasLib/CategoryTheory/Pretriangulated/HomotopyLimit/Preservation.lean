/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Preservation of Sequential Homotopy Limits

A triangulated functor which preserves countable products carries a Milnor
triangle presentation to one for the mapped sequential system.
-/

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.HomotopyLimit.IsOf

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {E : Type u₂} [Category.{v₂} E] [Limits.HasZeroObject E] [Preadditive E]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]

/-- Stacks 08TC: a triangulated functor preserves a specified sequential homotopy limit as soon
as it preserves the product of that particular tower.  This is the family-level interface used
when global preservation of all countable products would be unnecessarily strong. -/
@[stacks 08TC "homotopy limit under a functor preserving the specified product"]
theorem mapOfPreservesProduct {K : SequentialInverseSystem D} {X : D}
    (h : HomotopyLimit.IsOf K X) (F : D ⥤ E)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    [PreservesLimit (Discrete.functor K.family) F] :
    HomotopyLimit.IsOf (K ⋙ F) (F.obj X) := sorry

/-- Stacks 08TC: a triangulated functor preserving countable products preserves sequential
homotopy limits. -/
@[stacks 08TC]
theorem map {K : SequentialInverseSystem D} {X : D} (h : HomotopyLimit.IsOf K X)
    (F : D ⥤ E) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) F] :
    HomotopyLimit.IsOf (K ⋙ F) (F.obj X) := sorry

end CategoryTheory.HomotopyLimit.IsOf
