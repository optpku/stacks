/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Smooth
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.satisfiesSerreConditionR

/- Lemma 35.18.3: being locally Noetherian and satisfying `(R_k)` is local for the
smooth precoverage. -/
@[stacks 036C] #check
  (AlgebraicGeometry.Scheme.satisfiesSerreConditionR.smoothLocal :
    ∀ k : ℕ,
      ObjectProperty.IsLocal
        (fun X : AlgebraicGeometry.Scheme.{u} ↦
          AlgebraicGeometry.IsLocallyNoetherian X ∧
            AlgebraicGeometry.Scheme.satisfiesSerreConditionR X k)
        AlgebraicGeometry.Scheme.bigSmoothPrecoverage)

end AlgebraicGeometry.Scheme.satisfiesSerreConditionR
