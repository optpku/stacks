/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RankLocus

/-! Compatibility facade for the canonical public owner. -/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.rankOpenSubspace :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E], ℕ → OpenSubspace X)
