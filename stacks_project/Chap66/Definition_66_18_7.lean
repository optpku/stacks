module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap66.Definition_66_18_1_Site
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u w

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/- Definition 66.18.7: let `S` be a scheme and let `X` be an algebraic space over `S`.
The étale topos of `X`, or more precisely the small étale topos of `X`, is the category
`Sheaf (smallEtaleTopology X) (Type w)` of sheaves of sets on the small étale site of `X`. -/
@[stacks 04JT] #check Sheaf X.smallEtaleTopology (Type w)
