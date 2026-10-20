/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.RankLocus

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

/- A compatibility check for the clopen rank-locus construction. -/
#check (AlgebraicGeometry.Scheme.Modules.rankClopen :
  ∀ {X : Scheme.{u}} (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ), Clopens X)
