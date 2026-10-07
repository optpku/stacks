module

public import stacks_project.Chap107.Definition_107_3_4_Multiplicity
import StacksCheckRecall

@[expose]
public section

/- Definition 107.3.4: for a locally Noetherian algebraic stack `X` and an
irreducible component `T` of `|X|`, the multiplicity of `T` in `X` equals
the scheme-level multiplicity of any irreducible component `T'` of a scheme
`U` admitting a smooth morphism `U ⟶ X` with `f(T') ⊆ T`. -/
@[stacks 0DR8] #check AlgebraicGeometry.AlgebraicStack.irreducibleComponentMultiplicity
