module

public import stacks_project.Chap73.Definition_73_7_1_FppfCover
import StacksCheckRecall

@[expose] public section

/- Definition 73.7.1: let `S` be a scheme, and let `X` be an algebraic space over `S`.
An fppf covering of `X` is a family of morphisms `{fᵢ : Xᵢ ⟶ X}` of algebraic spaces
over `S` such that each `fᵢ` is `Flat` and `LocallyOfFinitePresentation` and such that
`|X| = ⋃ᵢ |fᵢ|(|Xᵢ|)`, i.e., the morphisms are jointly surjective. -/
@[stacks 03Y8] #check AlgebraicGeometry.AlgebraicSpace.FppfCovering

#check AlgebraicGeometry.AlgebraicSpace.FppfCover
#check AlgebraicGeometry.AlgebraicSpace.FppfCovering.source_spec
