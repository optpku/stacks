/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Branch
import StacksCheckRecall

universe u

/- Definition 68.24.4: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x ∈ |X|`. The number of branches of `X` at `x` is `X.branchNumberAt x`, which is
either `n ∈ ℕ` if the equivalent conditions of Lemma 68.24.3 hold, or else `∞`. -/
@[stacks 0DQ9] #check (AlgebraicGeometry.AlgebraicSpace.branchNumberAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    (x : AlgebraicGeometry.AlgebraicSpace.Points X), ℕ∞)
#check AlgebraicGeometry.AlgebraicSpace.branchNumberAt_def
#check AlgebraicGeometry.AlgebraicSpace.branchNumberAt_eq_nat_iff
#check AlgebraicGeometry.AlgebraicSpace.branchNumberAt_eq_iSup_elementary_minimalPrimes
