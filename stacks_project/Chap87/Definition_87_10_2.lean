module

public import stacks_project.Chap87.Lemma_87_10_3_Types
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Definition 87.10.2: for a scheme `S` and an affine formal algebraic space
`X` over `S`, we say `X` is countably indexed if the equivalent conditions of
Lemma 87.10.1 hold. -/
@[stacks 0AIJ] #check IsCountablyIndexedAffine
