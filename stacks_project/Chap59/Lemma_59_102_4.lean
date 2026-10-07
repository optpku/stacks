module

public import stacks_project.Chap59.Lemma_59_102_4_Comparison
import StacksCheckRecall

@[expose] public section

/-!
Lemma 59.102.4 (0F0I) is the concrete ph/étale comparison package on `Over S`.
The reusable owner is `PhComparison.situation`, with coefficient family
`torsionPiInverseImage` and morphism class `properOver`.
-/

open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PhComparison
open CategoryTheory.GrothendieckTopology

/- Lemma 59.102.4 (1): proper morphisms in `Over S` admit pullbacks. -/
@[stacks 0F0I "(1)"]
#check @properOver_hasPullbacks

/- Proper morphisms in `Over S` are stable under base change. -/
@[stacks 0F0I "(1)"]
#check @properOver_isStableUnderBaseChange

/- Lemma 59.102.4 (2): inverse image preserves the torsion `π⁻¹` coefficient family. -/
@[stacks 0F0I "(2)"]
#check @torsionPiInverseImage_inverseImage_mem

/- Lemma 59.102.4 (3): torsion `π⁻¹` coefficients are sheaves for the ph topology. -/
@[stacks 0F0I "(3)"]
#check @torsionPiInverseImage_isSheafPh

/- Lemma 59.102.4 (4): higher direct images along proper morphisms preserve `A'_X`. -/
@[stacks 0F0I "(4)"]
#check @torsionPiInverseImage_higherDirectImage_mem

/- Lemma 59.102.4 (5): ph coverings admit étale refinements by proper morphisms. -/
@[stacks 0F0I "(5)"]
#check @tau_covering_refinement

/- The five source clauses are packaged by the concrete comparison situation. -/
@[stacks 0F0I]
#check @situation

end
