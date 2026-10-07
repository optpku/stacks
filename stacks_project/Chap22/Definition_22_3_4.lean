module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.TensorProduct
import StacksCheckRecall

/-!
# Definition 22.3.4

The Koszul tensor product of cochain differential graded algebras is owned by
`ReasLib.Algebra.Homology.CochainDGAlgebra.TensorProduct`.
-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
variable (A B : CochainDGAlgebra.{u, v} R)

/- Definition 22.3.4 (065W): the tensor product of cochain differential graded algebras. -/
@[stacks 065W]
#check (CochainDGAlgebra.tensorProduct A B : CochainDGAlgebra.{u, v} R)
