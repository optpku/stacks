module

public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
import StacksCheckRecall

@[expose] public section

/- Definition 87.29.1: let `A → B` be a continuous map of topological rings
(More on Algebra, Definition 15.36.1). We say `B` is topologically of finite type
over `A` if there exists an `A`-algebra map `MvPolynomial (Fin n) A →ₐ[A] B`
whose image is dense in `B`. -/
@[stacks 0ANS] #check Algebra.TopologicallyOfFiniteType
