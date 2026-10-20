/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion.Exact

universe u

/- 30.17.5.1: for a closed immersion `i : Z ⟶ X`, an invertible module `L`, and `n : ℕ`,
the canonical sequence `0 ⟶ 𝓘 ⊗ L^{⊗ n} ⟶ L^{⊗ n} ⟶ i_* i^* L^{⊗ n} ⟶ 0` is short
exact. -/
@[stacks 0B8T] #check
  (AlgebraicGeometry.Scheme.Modules.ClosedImmersion.tensorPowerSequence_shortExact :
    ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
      [AlgebraicGeometry.IsClosedImmersion i]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L] (n : ℕ),
      (AlgebraicGeometry.Scheme.Modules.ClosedImmersion.sequence i
        (AlgebraicGeometry.RingedSpace.TensorPower.sheaf L n)).ShortExact)
