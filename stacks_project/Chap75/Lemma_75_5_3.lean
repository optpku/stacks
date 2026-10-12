/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_5_3_Coproducts
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/- Lemma 75.5.3: for a scheme `S` and an algebraic space `X` over `S`, the
category `D_QCoh(𝒪_X)` has direct sums. -/
@[stacks 08F3] #check (hasCoproducts X : HasCoproducts.{u} (DerivedQCoh X))
