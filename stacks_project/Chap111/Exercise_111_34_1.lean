/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.LocalizationAwayXT
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.LocalizationAwayXT

/- Exercise 111.34.1 (1): there is no morphism `σ : base ⟶ scheme` such that
`σ ≫ toBase = 𝟙 base`. -/
@[stacks 0294] #check
  (AlgebraicGeometry.LocalizationAwayXT.not_exists_section :
    ¬ ∃ σ : base ⟶ scheme, σ ≫ toBase = 𝟙 base)

/- Exercise 111.34.1 (2): there exist a nonempty open `U ⊆ base` and a morphism
`σ : U.toScheme ⟶ scheme` such that `σ ≫ toBase = U.ι`. -/
@[stacks 0294] #check
  (AlgebraicGeometry.LocalizationAwayXT.exists_rational_section :
    ∃ U : base.Opens, Nonempty U ∧ ∃ σ : U.toScheme ⟶ scheme, σ ≫ toBase = U.ι)

end AlgebraicGeometry.LocalizationAwayXT
