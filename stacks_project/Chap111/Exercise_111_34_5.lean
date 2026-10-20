/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CubicNoSection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Exercise 111.34.5: the cubic family `1 + t * x ^ 3 + t ^ 2 * y ^ 3`
over `Spec (Polynomial ℂ)` has no section over a nonempty open of the base. -/
@[stacks 0297]
#check (AlgebraicGeometry.CubicNoSection.not_exists_nonempty_open_section :
  ¬ ∃ (U : AlgebraicGeometry.CubicNoSection.base.Opens), Nonempty U ∧
    ∃ σ : U.toScheme ⟶ AlgebraicGeometry.CubicNoSection.totalSpace,
      σ ≫ AlgebraicGeometry.CubicNoSection.π = U.ι)
