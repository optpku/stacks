module

public import stacks_project.Chap109.Definition_109_19_2_Sheaf
import StacksCheckRecall

@[expose] public section

/- Definition 109.19.2: for a family of curves `f : X ⟶ S` with Cohen–Macaulay
fibres equidimensional of dimension 1, the relative dualizing sheaf is the
`𝒪_X`-module `sheaf C = cohomologySheaf C.complex (-1)` studied in
Lemma 109.19.1. -/
@[stacks 0E6Q] #check AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex.sheaf
