/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Exercise 111.60.4 (1): over a field `k`, on `X = scheme k`, there is no finite locally free
`𝒪_X`-module `ℰ` with `h⁰(X, ℰ) = 5` and `h⁰(X, ℰ(1)) = 4`. -/
@[stacks 0EEN] #check (AlgebraicGeometry.ProjectiveLine.not_exists_cohomologyFinrank_zero_five_four :
    ∀ {k : Type u} [Field k],
      ¬ ∃ (ℰ : (AlgebraicGeometry.ProjectiveLine.scheme k).Modules)
        (_ : ℰ.IsFiniteLocallyFree),
        Scheme.Hom.cohomologyFinrank (AlgebraicGeometry.ProjectiveLine.toSpec k) ℰ 0 = 5 ∧
          Scheme.Hom.cohomologyFinrank (AlgebraicGeometry.ProjectiveLine.toSpec k)
            (AlgebraicGeometry.ProjectiveSpace.twist k 1 ℰ 1) 0 = 4)

/- Exercise 111.60.4 (2): over a field `k`, on `X = scheme k`, there is no finite locally free
`𝒪_X`-module `ℰ` with `h¹(X, ℰ(1)) = 5` and `h¹(X, ℰ) = 4`. -/
@[stacks 0EEN] #check (AlgebraicGeometry.ProjectiveLine.not_exists_cohomologyFinrank_one_five_four :
    ∀ {k : Type u} [Field k],
      ¬ ∃ (ℰ : (AlgebraicGeometry.ProjectiveLine.scheme k).Modules)
        (_ : ℰ.IsFiniteLocallyFree),
        Scheme.Hom.cohomologyFinrank (AlgebraicGeometry.ProjectiveLine.toSpec k)
            (AlgebraicGeometry.ProjectiveSpace.twist k 1 ℰ 1) 1 = 5 ∧
          Scheme.Hom.cohomologyFinrank (AlgebraicGeometry.ProjectiveLine.toSpec k) ℰ 1 = 4)

/- Exercise 111.60.4 (3): a finite locally free module on the projective line realizes the stated
cohomology table at twists `0`, `1`, and `2` exactly when `a = 0`. -/
@[stacks 0EEN] #check (AlgebraicGeometry.ProjectiveLine.exists_specified_cohomology_iff :
    ∀ {k : Type u} [Field k] (a : ℤ),
      (∃ (ℰ : (AlgebraicGeometry.ProjectiveLine.scheme k).Modules)
          (_ : ℰ.IsFiniteLocallyFree),
          Scheme.Hom.cohomologyFinrank (AlgebraicGeometry.ProjectiveLine.toSpec k) ℰ 0 = 1 ∧
            Scheme.Hom.cohomologyFinrank (AlgebraicGeometry.ProjectiveLine.toSpec k) ℰ 1 = 1 ∧
          Scheme.Hom.cohomologyFinrank (AlgebraicGeometry.ProjectiveLine.toSpec k)
              (AlgebraicGeometry.ProjectiveSpace.twist k 1 ℰ 1) 0 = 2 ∧
            Scheme.Hom.cohomologyFinrank (AlgebraicGeometry.ProjectiveLine.toSpec k)
              (AlgebraicGeometry.ProjectiveSpace.twist k 1 ℰ 1) 1 = 0 ∧
          Scheme.Hom.cohomologyFinrank (AlgebraicGeometry.ProjectiveLine.toSpec k)
              (AlgebraicGeometry.ProjectiveSpace.twist k 1 ℰ 2) 0 = 4 ∧
            (Scheme.Hom.cohomologyFinrank (AlgebraicGeometry.ProjectiveLine.toSpec k)
              (AlgebraicGeometry.ProjectiveSpace.twist k 1 ℰ 2) 1 : ℤ) = a) ↔
        a = 0)
