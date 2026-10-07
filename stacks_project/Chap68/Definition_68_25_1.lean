module

public import stacks_project.Chap68.Definition_68_25_1_Catenary
import StacksCheckRecall

@[expose] public section

/- Definition 68.25.1: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
We say `X` is catenary if `|X|` is catenary (Topology, Definition 5.11.4 / `CatenarySpace`). -/
@[stacks 0ED4] #check AlgebraicGeometry.AlgebraicSpace.IsCatenary
#check AlgebraicGeometry.AlgebraicSpace.isCatenary_iff
