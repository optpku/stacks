/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.PerfectComparison
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 36.38.4: for a Noetherian regular scheme, the canonical map from
perfect-complex `K₀` to coherent-sheaf `K₀'` is bijective. -/
@[stacks 0FDI] #check
  (AlgebraicGeometry.Scheme.K0.toK0'_bijective :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
      [AlgebraicGeometry.Scheme.Regular X],
      Function.Bijective (AlgebraicGeometry.Scheme.K0.toK0' X))
