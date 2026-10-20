/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Distance

@[expose] public section

/- 52.18.0.1: For a Noetherian scheme `Y` and a closed subset `Z`, both source
notations `δ_Z^Y` and `δ_Z` denote `Y.distanceTo Z : Y → ℕ∞`. -/
@[stacks 0EIX] #check (AlgebraicGeometry.Scheme.distanceTo :
  (Y : AlgebraicGeometry.Scheme) → [AlgebraicGeometry.IsNoetherian Y] →
    TopologicalSpace.Closeds Y → Y → ℕ∞)
