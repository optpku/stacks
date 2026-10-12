/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_13_1_GeometricBranch
public import stacks_project.Chap100.Definition_100_13_1_GeometricallyUnibranch
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
  (x : AlgebraicStack.Points X)

/- Definition 100.13.1 (1): let `X` be an algebraic stack. Let `x ∈ |X|`. The
number of geometric branches of `X` at `x` is `n ∈ ℕ` if the equivalent
conditions of Lemma 100.7.4 hold for `GermProperty.geometricBranchEq n`, and
`⊤` otherwise. -/
@[stacks 0DQH] #check (AlgebraicGeometry.AlgebraicStack.geometricBranchNumberAt X x : ℕ∞)

/- Definition 100.13.1 (2): we say `X` is geometrically unibranch at `x` if the
number of geometric branches of `X` at `x` is `1`. -/
@[stacks 0DQH] #check AlgebraicGeometry.AlgebraicStack.GeometricallyUnibranchAt
