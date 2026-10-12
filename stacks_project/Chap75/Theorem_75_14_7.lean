/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Theorem_75_14_7_Qcqs
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Theorem 75.14.7: approximation by perfect complexes holds on every quasi-compact,
quasi-separated algebraic space. -/
@[stacks 08HP] #check
  (HasApproximationByPerfectComplexes.of_qcqs :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X],
      HasApproximationByPerfectComplexes X)
