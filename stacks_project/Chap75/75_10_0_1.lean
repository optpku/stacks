module

public import stacks_project.Chap75.«75_10_0_1_Stalk»
import StacksCheckRecall

open AlgebraicGeometry.AlgebraicSpace.Modules

/- 75.10.0.1: for an étale morphism `j : U ⟶ X` of algebraic spaces over `S`, a sheaf of
`𝒪_X`-modules `F`, and a geometric point `ubar` of `U`, the stalk of the étale restriction
`restrict F j` at `ubar` is canonically identified with the stalk of `F` at `ubar.map j`. -/
@[stacks 08GT] #check restrictStalkIso
