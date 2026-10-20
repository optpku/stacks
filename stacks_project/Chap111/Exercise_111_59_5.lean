/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.EqualEndpoint
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.EqualEndpoint
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

/- Exercise 111.59.5 -/
@[stacks 0DT4] #check
  (AlgebraicGeometry.EqualEndpoint.rationalMilnorLineExample :
    Invertible (lineBundle ℚ (-1 : ℚˣ)) ∧
      ¬ Nonempty (lineBundle ℚ (-1 : ℚˣ) ≅ 𝟙_ (scheme ℚ).Modules) ∧
      Nontrivial Γ(lineBundle ℚ (-1 : ℚˣ), ⊤) ∧
      Nontrivial Γ(tensorPowerInt (lineBundle ℚ (-1 : ℚˣ)) (-1), ⊤))
