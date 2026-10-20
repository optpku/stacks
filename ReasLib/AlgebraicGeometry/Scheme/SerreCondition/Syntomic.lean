/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Depth
public import ReasLib.AlgebraicGeometry.Scheme.ObjectProperty.AffineDescent

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.satisfiesSerreConditionS

/-- For every `k`, being locally Noetherian and satisfying `(S_k)` is local for the
syntomic precoverage. -/
instance syntomicLocal (k : ℕ) :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} ↦ IsLocallyNoetherian X ∧ Scheme.satisfiesSerreConditionS X k)
      Scheme.bigSyntomicPrecoverage := sorry

end AlgebraicGeometry.Scheme.satisfiesSerreConditionS
