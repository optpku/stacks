/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.WeilCohomology
import StacksCheckRecall

@[expose] public section

universe u

/- Proposition 50.22.1: over a characteristic-zero field, the canonical graded relative
de Rham cohomology functor on smooth projective schemes is a Weil cohomology theory. -/
@[stacks 0FWD] #check (AlgebraicGeometry.Scheme.DeRham.existsWeilTheory :
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ T : WeilCohomology.SchemeClassicalTheory.Object k k,
      T.IsWeil ∧ AlgebraicGeometry.Scheme.DeRham.RealizesCohomology T)
