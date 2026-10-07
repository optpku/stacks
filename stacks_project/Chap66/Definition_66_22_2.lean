module

public import stacks_project.Chap66.Definition_66_22_2_Point
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Definition_66_22_2_Henselization
import StacksCheckRecall

open AlgebraicGeometry

universe u

@[expose] public section

/- Definition 66.22.2 (1): the étale local ring of an algebraic space `X` at a geometric
point `xbar` lying over `xbar.image ∈ |X|` is the stalk of the structure sheaf `𝒪_X` on
`X_étale` at `xbar`. Notation: `𝒪_{X, xbar}`. -/
@[stacks 04KG] #check AlgebraicSpace.etaleLocalRing

/- Definition 66.22.2 (2): the strict henselization of an algebraic space `X` at a geometric
point `xbar` is the scheme `Spec(𝒪_{X, xbar})`. -/
@[stacks 04KG] #check AlgebraicSpace.strictHenselizationScheme
