module

public import stacks_project.Chap103.Definition_103_7_1_Comparison
public import stacks_project.Chap103.Definition_103_7_1_FlatBaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Definition 103.7.1: let `X` be an algebraic stack and let `F` in
`Mod(X_étale, 𝒪_X)`. We say `F` has the flat base change property if and only
if the comparison `c_φ : f_small^*(F|_{U'_étale}) ⟶ F|_{U_étale}` is an
isomorphism whenever `φ : x ⟶ x'` lies over a flat morphism of schemes
`f : U ⟶ U'`. -/
@[stacks 0762] #check AlgebraicGeometry.GroupoidsOver.HasFlatBaseChange
