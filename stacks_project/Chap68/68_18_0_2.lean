/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.«68_18_0_2_Fibre»
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

/- 68.18.0.2: consider a cartesian square `W ⟶ Z` over `X ⟶ Y` of algebraic spaces over a
scheme `S`, with maps `p : W ⟶ X`, `q : W ⟶ Z`, `f : X ⟶ Y`, and `g : Z ⟶ Y`. Let
`x ∈ |X|` and `z ∈ |Z|` map to the same point of `|Y|`. The fibre is the set
`F_{x, z} = { w ∈ |W| | Points.map p w = x ∧ Points.map q w = z }`. -/
@[stacks 0AC2] #check Points.fibre
