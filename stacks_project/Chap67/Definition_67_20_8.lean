module

public import stacks_project.Chap67.Definition_67_20_8_Over
import StacksCheckRecall

@[expose] public section

/- Definition 67.20.8: for a scheme `S`, an algebraic space `X` over `S`, and a
quasi-coherent sheaf of `𝒪_X`-algebras `A`, the relative spectrum of `A` over `X`,
or simply the spectrum of `A` over `X`, is the affine morphism
`relativeSpecπ A : relativeSpec A ⟶ X` corresponding to `A` under the
equivalence of categories of Lemma 67.20.7. -/
@[stacks 081W] #check AlgebraicGeometry.AlgebraicSpace.relativeSpecπ
