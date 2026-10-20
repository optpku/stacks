/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

@[expose] public section

open CategoryTheory TopCat TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Sections of an injective abelian sheaf restrict surjectively along inclusions of opens. -/
theorem restriction_surjective_of_injective
    {X : TopCat.{u}} (I : X.Sheaf AddCommGrpCat.{u}) [Injective I]
    {U V : Opens X} (hVU : V ≤ U) :
    Function.Surjective (I.presheaf.map (homOfLE hVU).op) := sorry

/-- Every injective abelian sheaf is flasque. -/
@[instance] theorem injective_isFlasque
    {X : TopCat.{u}} (I : X.Sheaf AddCommGrpCat.{u}) [Injective I] :
    IsFlasque I := sorry

end TopCat.Sheaf

end
