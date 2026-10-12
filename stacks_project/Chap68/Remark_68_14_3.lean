/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_15_3
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

section

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme (reduction X)]

/- Remark 68.14.3: We will see in Limits of Spaces, Lemma 70.15.3 that an
algebraic space whose reduction is a scheme is a scheme. -/
@[stacks 049D] #check (IsScheme.of_reduction X : IsScheme X)

end
