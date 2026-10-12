/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Definition_42_38_8_ChernClass
import StacksCheckRecall

/- Definition 42.38.8 (1): For `0 ≤ i ≤ r`, the `i`th Chern class of a rank-`r`
finite locally free module `E` is the degree-`i` bivariant class `ChernClass.component`. -/
@[stacks 0FE1] #check @AlgebraicGeometry.ChernClass.component

/- Definition 42.38.8 (2): The total Chern class `c(E)` is the sum of its homogeneous
components `c₀(E), …, cᵣ(E)`, viewed in the nonhomogeneous Chow-cohomology ring. -/
@[stacks 0FE1] #check @AlgebraicGeometry.ChernClass.total
