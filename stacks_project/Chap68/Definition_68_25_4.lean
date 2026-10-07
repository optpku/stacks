module

public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
import StacksCheckRecall

@[expose] public section

/- Definition 68.25.4: Let `S` be a scheme. Let `X` be a decent and locally
Noetherian algebraic space over `S`. We say `X` is universally catenary if for
every morphism `Y ⟶ X` of algebraic spaces which is locally of finite type and
with `Y` decent, the algebraic space `Y` is catenary. -/
@[stacks 0ED7] #check AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary
#check AlgebraicGeometry.AlgebraicSpace.universallyCatenary_iff
