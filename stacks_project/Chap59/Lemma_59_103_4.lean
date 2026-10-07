module

public import stacks_project.Chap59.Lemma_59_103_4_Situation
public import stacks_project.Chap59.Lemma_59_103_4_TorsionPullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme

/- Lemma 59.103.4: the identity comparison ε : (Sch/S)_h ⟶ (Sch/S)_étale,
with P the class of proper morphisms and A'_X the sheaves on (Sch/X)_étale
isomorphic to π_X⁻¹ of a torsion abelian sheaf on X_étale, satisfies
properties (1)–(5) of Situation 21.30.1. -/
@[stacks 0F0J]
#check @HComparison.comparisonSituation

end
