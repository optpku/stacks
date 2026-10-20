/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine

/-- On the projective line over a field, a finite locally free module cannot have five global
sections while its first twist has only four global sections. -/
theorem not_exists_cohomologyFinrank_zero_five_four {k : Type u} [Field k] :
    ¬ ∃ (ℰ : (scheme k).Modules) (_ : ℰ.IsFiniteLocallyFree),
      Scheme.Hom.cohomologyFinrank (toSpec k) ℰ 0 = 5 ∧
        Scheme.Hom.cohomologyFinrank (toSpec k) (ProjectiveSpace.twist k 1 ℰ 1) 0 = 4 := sorry

/-- On the projective line over a field, a finite locally free module cannot have five first
cohomology classes after its first twist and only four before twisting. -/
theorem not_exists_cohomologyFinrank_one_five_four {k : Type u} [Field k] :
    ¬ ∃ (ℰ : (scheme k).Modules) (_ : ℰ.IsFiniteLocallyFree),
      Scheme.Hom.cohomologyFinrank (toSpec k) (ProjectiveSpace.twist k 1 ℰ 1) 1 = 5 ∧
        Scheme.Hom.cohomologyFinrank (toSpec k) ℰ 1 = 4 := sorry

/-- A finite locally free module on the projective line over a field has cohomology dimensions
`(1, 1)`, `(2, 0)`, and `(4, a)` at twists `0`, `1`, and `2` exactly when `a = 0`. -/
theorem exists_specified_cohomology_iff {k : Type u} [Field k] (a : ℤ) :
    (∃ (ℰ : (scheme k).Modules) (_ : ℰ.IsFiniteLocallyFree),
        Scheme.Hom.cohomologyFinrank (toSpec k) ℰ 0 = 1 ∧
          Scheme.Hom.cohomologyFinrank (toSpec k) ℰ 1 = 1 ∧
        Scheme.Hom.cohomologyFinrank (toSpec k) (ProjectiveSpace.twist k 1 ℰ 1) 0 = 2 ∧
          Scheme.Hom.cohomologyFinrank (toSpec k) (ProjectiveSpace.twist k 1 ℰ 1) 1 = 0 ∧
        Scheme.Hom.cohomologyFinrank (toSpec k) (ProjectiveSpace.twist k 1 ℰ 2) 0 = 4 ∧
          (Scheme.Hom.cohomologyFinrank (toSpec k) (ProjectiveSpace.twist k 1 ℰ 2) 1 : ℤ) =
            a) ↔
      a = 0 := sorry

end AlgebraicGeometry.ProjectiveLine
