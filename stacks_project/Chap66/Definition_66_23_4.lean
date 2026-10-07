module

public import stacks_project.Chap66.Definition_66_23_4_GeometricBranch
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 66.23.4: for a scheme `S`, an algebraic space `X` over `S`, and a point
`x ∈ |X|`, the number of geometric branches of `X` at `x` is the common value
`X.geometricBranchNumberAt xbar` at any geometric point `xbar` with `xbar.liesOver x`,
equal to `n` when the equivalent conditions of Lemma 66.23.3 hold, and `⊤` otherwise. -/
@[stacks 0DQ4] #check
  (AlgebraicGeometry.AlgebraicSpace.geometricBranchNumberAt :
    {S : AlgebraicGeometry.Scheme.{u}} → (X : AlgebraicGeometry.AlgebraicSpace S) →
      AlgebraicGeometry.AlgebraicSpace.GeometricPoint X → ℕ∞)
