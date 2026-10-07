module

public import stacks_project.Chap75.Lemma_75_5_6_Instances
public import stacks_project.Chap75.Lemma_75_5_6_Tensor
import StacksCheckRecall

/- Lemma 75.5.6: for a scheme `S` and an algebraic space `X` over `S`, the derived
tensor product of two objects of `D_QCoh(𝒪_X)` again lies in `D_QCoh(𝒪_X)`. -/
@[stacks 08F5] #check AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.tensorRight.mapsTo
