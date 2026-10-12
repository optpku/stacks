/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_47_3_RationalFunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Definition 67.47.2: for a scheme `S` and an algebraic space `X` over `S`, a rational function
on `X` is a rational map from `X` to the affine line `𝔸¹_S`. -/
@[stacks 0EMN] #check
  (AlgebraicGeometry.AlgebraicSpace.RationalFunction :
    {S : Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))

#check AlgebraicGeometry.AlgebraicSpace.RationalMap
#check AlgebraicGeometry.AlgebraicSpace.affineLine
