/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap107.Definition_107_4_1_VersalRing
import StacksCheckRecall

@[expose] public section

/- Definition 107.2.2
In Situation 107.2.1 let x0 : Spec(k) ⟶ X be a morphism, where k is a finite
type field over S. A versal ring to X at x0 is a complete Noetherian local
S-algebra A with residue field k such that there exists a versal formal object
(A, ξ_n, f_n) as in Artin's Axioms, Definition 98.12.1 with ξ_1 ≅ x0 (a
2-isomorphism). This is owned by AlgebraicGeometry.AlgebraicStack.IsVersalRing. -/
@[stacks 0DQV] #check AlgebraicGeometry.AlgebraicStack.IsVersalRing

#check AlgebraicGeometry.AlgebraicStack.IsVersalRing.spec
#check AlgebraicGeometry.AlgebraicStack.IsVersalRing.iff
