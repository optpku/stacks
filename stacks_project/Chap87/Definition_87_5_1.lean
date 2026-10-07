module

public import stacks_project.Chap87.Definition_87_5_1_Taut
import StacksCheckRecall

@[expose] public section

/- Definition 87.5.1: a continuous homomorphism `φ : A →+* B` of linearly
topologized rings is taut if for every open ideal `I` of `A` the closure of
`Ideal.map φ I` is open in `B` and these closures form a fundamental system of
open ideals of `B`. -/
@[stacks 0AMX] #check @RingHom.IsTaut
