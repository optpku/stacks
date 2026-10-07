module

public import stacks_project.Chap63.«63_4_0_1_FormalSum»
public import stacks_project.Chap63.«63_4_0_1_SectionsSupportedIn»
import StacksCheckRecall

@[expose] public section

/- 63.4.0.1: for a locally quasi-finite morphism `f : X ⟶ Y`, an abelian sheaf
`F` on `X_étale`, and `V` in `Y_étale`, a typical finite formal sum is
`s = ∑ i, FreeAbelianGroup.of (t i)`, where each `t i : FiniteSupportTerm f F V`
is a pair `(Z_i, s_i)` with `Z_i ⊂ X_V` a locally closed subscheme finite over
`V` and `s_i ∈ H_{Z_i}(F)`. -/
@[stacks 0F6J] #check AlgebraicGeometry.Scheme.Etale.FiniteSupportFormalSum.sum

end
