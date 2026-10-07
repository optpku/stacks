module

import StacksCheckRecall
public import stacks_project.Chap96.«96_10_3_3_Comparison»
public import stacks_project.Chap96.«96_10_3_3_Restriction»

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- 96.10.3.3: for a 2-commutative triangle of 1-morphisms of categories fibred
in groupoids over `(Sch/S)_fppf` with `𝒰`, `𝒱` represented by algebraic spaces
`U`, `V`, and `F` an étale sheaf of `𝒪_𝒳`-modules, the sheaf-level comparison
induces a comparison morphism of `𝒪_{U_étale}`-modules
`c_φ : a_small^*(g^* F |_{V_étale}) ⟶ f^* F |_{U_étale}`, owned by
`GroupoidsOver.moduleComparisonSpace`. -/
@[stacks 076R] #check AlgebraicGeometry.GroupoidsOver.moduleComparisonSpace
