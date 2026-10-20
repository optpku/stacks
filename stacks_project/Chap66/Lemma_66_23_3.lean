/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricBranch.Characterization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 66.23.3
For an algebraic space and a point, the five finite positive branch-count conditions
on étale scheme charts and the geometric branch number are equivalent.
-/
@[stacks 0DQ3] #check
  (AlgebraicGeometry.AlgebraicSpace.geometricBranchNumber_eq_nat_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) (n : ℕ),
      0 < n →
        List.TFAE
          [AlgebraicGeometry.AlgebraicSpace.stalkMinimalPrimesBoundAttained x n,
            AlgebraicGeometry.AlgebraicSpace.irreducibleComponentsBoundAttained x n,
            AlgebraicGeometry.AlgebraicSpace.branchNumberBoundAttained x n,
            AlgebraicGeometry.AlgebraicSpace.geometricBranchNumberEq x n,
            X.geometricBranchNumber x = n])
