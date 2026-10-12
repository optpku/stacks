/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap109.Definition_109_20_1_Prestable
import StacksCheckRecall

@[expose] public section

/- Definition 109.20.1: a family of curves `f : X ⟶ S` is prestable if it is
at-worst-nodal of relative dimension 1 and `𝒪_S ⟶ f_* 𝒪_X` is an isomorphism
after any base change. -/
@[stacks 0E6T] #check AlgebraicGeometry.AlgebraicSpace.Prestable
