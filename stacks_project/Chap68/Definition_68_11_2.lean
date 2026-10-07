module

public import stacks_project.Chap68.Definition_68_11_2_ResidueField
import StacksCheckRecall

@[expose] public section

/- Definition 68.11.2: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x ∈ |X|`. The residue field of `X` at `x` is the unique field `κ(x)` which comes
equipped with a monomorphism `Spec(κ(x)) ⟶ X` representing `x`. -/
@[stacks 0EMW] #check AlgebraicGeometry.AlgebraicSpace.residueField
@[stacks 0EMW] #check AlgebraicGeometry.AlgebraicSpace.fromSpecResidueField
