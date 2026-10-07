module

import stacks_project.Chap70.Lemma_70_23_3_BaseChange
import stacks_project.Chap70.Lemma_70_23_3_SchemeTheoreticImage
import StacksCheckRecall

/- Lemma 70.23.3: In Situation 70.23.1, if `X ⟶ B` is quasi-separated and of
finite type, and a good diagram `X ⟶ W` over `B ⟶ B_i` is given as in 70.23.2.1,
then for `i' ≥ i` the scheme-theoretic image `X_{i'}` of
`X ⟶ B_{i'} ×_{B_i} W` satisfies `X = lim_{i' ≥ i} X_{i'}`. -/
@[stacks 0CP9] #check
  AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram.nonempty_isLimit_schemeTheoreticImageCone
