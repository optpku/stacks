module

import StacksCheckRecall
public import stacks_project.Chap87.«87_2_0_2_FormalScheme»
public import stacks_project.Chap87.«87_2_0_2_LocallyTopologicallyRingedSpace»
public import stacks_project.Chap87.«87_2_0_2_PseudoDiscrete»

open AlgebraicGeometry

/- 87.2.0.2: the comparison functor Schemes ⟶ Formal Schemes sending a scheme `(X, 𝒪_X)` to
the same underlying space equipped with the pseudo-discrete sheaf of topological rings `𝒪'_X`
whose underlying sheaf of rings is `𝒪_X`. -/
@[stacks 0AI0] #check Scheme.toFormalScheme
