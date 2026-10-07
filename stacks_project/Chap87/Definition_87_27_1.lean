module

public import stacks_project.Chap87.Lemma_87_27_3_ClosedImmersion
import StacksCheckRecall

@[expose] public section

/- Definition 87.27.1: a morphism `f : Y ⟶ X` of formal algebraic spaces over a
scheme `S` is a closed immersion if it is representable by algebraic spaces and
a closed immersion in the sense of Bootstrap, Definition 80.4.1, i.e. the
Bootstrap transfer `relativeAlgebraicSpaces (@AlgebraicSpace.IsClosedImmersion S)`. -/
@[stacks 0ANP] #check AlgebraicGeometry.FormalAlgebraicSpace.ClosedImmersion
