/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineConic
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

/- Exercise 111.34.3 -/
@[stacks 0296]
#check
  (AlgebraicGeometry.AffineConicOverLine.exists_rational_section :
    ∀ (A B C : Polynomial ℂ), A ≠ 0 → B ≠ 0 → C ≠ 0 →
      ∃ U : AlgebraicGeometry.AffineConicOverLine.base.Opens,
        Nonempty U ∧
          ∃ σ : U.toScheme ⟶
              AlgebraicGeometry.AffineConicOverLine.total A B C,
            σ ≫ AlgebraicGeometry.AffineConicOverLine.toBase A B C = U.ι)
