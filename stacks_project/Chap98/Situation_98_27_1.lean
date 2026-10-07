module

public import stacks_project.Chap98.Situation_98_27_1_Contraction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace

/- Situation 98.27.1: let S be a locally Noetherian scheme. Let X' be an
algebraic space locally of finite type over S. Let T' ⊂ |X'| be a closed
subset. Let U' ⊂ X' be the open subspace with |U'| = |X'| \ T'. Let W be a
locally Noetherian formal algebraic space over S with W_red locally of finite
type over S. Finally, let g : completionAlong X' T' ⟶ W be a formal
modification. Lean records this standing data as ContractionSituation. -/
@[stacks 0GH8]
#check ContractionSituation

#check ContractionSituation.of

#check ContractionSituation.spec

#check ContractionSituation.openComplement

#check ContractionSituation.completion
