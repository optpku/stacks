/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Biproduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Adjoining the structure module raises the finite local rank by one. -/
instance instIsFiniteLocallyFreeOfRankBiprodUnit
    {X : Scheme.{u}} (C : X.Modules) (r : ℕ) [C.IsFiniteLocallyFreeOfRank r] :
    (C ⊞ 𝟙_ X.Modules).IsFiniteLocallyFreeOfRank (r + 1) := sorry

end AlgebraicGeometry.Scheme.Modules
