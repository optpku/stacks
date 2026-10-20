module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.GeometricBranch
public import ReasLib.AlgebraicGeometry.AlgebraicStack.GeometricallyUnibranch
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Definition 100.13.1 (1): let `X` be an algebraic stack. Let `x ∈ |X|`. The
number of geometric branches of `X` at `x` is `n ∈ ℕ` if the equivalent
conditions of Lemma 100.7.4 hold for `GermProperty.geometricBranchEq n`, and
`⊤` otherwise. -/
@[stacks 0DQH] #check (AlgebraicGeometry.AlgebraicStack.geometricBranchNumberAt :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    AlgebraicStack.Points X → ℕ∞)

/- Definition 100.13.1 (2): we say `X` is geometrically unibranch at `x` if the
number of geometric branches of `X` at `x` is `1`. -/
@[stacks 0DQH] #check (AlgebraicGeometry.AlgebraicStack.GeometricallyUnibranchAt :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    AlgebraicStack.Points X → Prop)
