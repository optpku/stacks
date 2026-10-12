/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_48_1_IntegralClosure
import StacksCheckRecall

@[expose] public section

/- Definition 67.48.2: for a scheme `S`, an algebraic space `X` over `S`, and a
quasi-coherent sheaf `A` of `𝒪_X`-algebras, the integral closure of `𝒪_X` in `A`
is the quasi-coherent `𝒪_X`-subalgebra `A' ⊂ A` constructed in Lemma 67.48.1. -/
@[stacks 0821] #check AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.integralClosure

/- The inclusion of the integral closure as a quasi-coherent `𝒪_X`-subalgebra of `A`. -/
@[stacks 0821] #check AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.inclusion
