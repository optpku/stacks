module

public import stacks_project.Chap92.«92_15_0_1_TensorProduct»
import StacksCheckRecall

open Algebra.CotangentComplex
open scoped TensorProduct

universe u

variable (R A B : Type u)
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable [Algebra B (A ⊗[R] B)]
variable [IsScalarTower R A (A ⊗[R] B)] [IsScalarTower R B (A ⊗[R] B)]

/- 92.15.0.1: for a ring R and R-algebras A, B, the tensor-product diagram in
D(Mod (A ⊗[R] B)) has middle row the transitivity triangle of
R → A → A ⊗[R] B, middle column the transitivity triangle of
R → B → A ⊗[R] B, identity equalities on tensor R A (A ⊗[R] B) and
tensor R B (A ⊗[R] B), and a new object E = tensorProductCone filling the
upper-right corner so that the top row
tensor R A (A ⊗[R] B) ⟶ derived B (A ⊗[R] B) ⟶ E and the right column
tensor R B (A ⊗[R] B) ⟶ derived A (A ⊗[R] B) ⟶ E are distinguished.
E is the mapping cone of the sum of the two transitivity maps into
derived R (A ⊗[R] B). -/
@[stacks 09D9]
#check tensorProductCone R A B

#check sumMap R A B
#check tensorProductConeInr R A B
#check tensorProductTopMap R A B
#check tensorProductRightMap R A B
#check tensorProductFromOverB R A B
#check tensorProductFromOverA R A B
#check transitivityTriangle R A (A ⊗[R] B)
#check transitivityTriangle R B (A ⊗[R] B)
