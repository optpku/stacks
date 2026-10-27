/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Limits.HasLimits

@[expose] public section

universe u v uA vA z

namespace CategoryTheory

/-- A site bounded by a universe admits global sections with values in any
category having all limits in that universe. -/
instance hasGlobalSectionsFunctor_of_univLE
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type uA) [Category.{vA} A] [UnivLE.{max u v, z}]
    [Limits.HasLimitsOfSize.{z, z} A] [HasWeakSheafify J A] :
    HasGlobalSectionsFunctor J A := sorry

end CategoryTheory
