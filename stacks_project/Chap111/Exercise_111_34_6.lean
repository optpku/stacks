/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CubicNoSectionSurface
import StacksCheckRecall

@[expose] public section

open CategoryTheory

open AlgebraicGeometry.CubicNoSectionSurface

/- Exercise 111.34.6: the diagonal cubic hypersurface over `Spec ℂ[s, t]`
admits no section over any nonempty open of the base. -/
@[stacks 0298] #check
  (AlgebraicGeometry.CubicNoSectionSurface.not_exists_nonempty_open_section :
    ¬ ∃ (U : base.Opens), Nonempty U ∧ ∃ σ : U.toScheme ⟶ totalSpace, σ ≫ π = U.ι)
