/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap107.Definition_107_5_14_PseudoCatenary
import StacksCheckRecall

@[expose] public section

/- Definition 107.5.14: a locally Noetherian algebraic stack `X` is
pseudo-catenary if there exists a smooth and surjective morphism `U ⟶ X`
whose source is a universally catenary scheme. -/
@[stacks 0DRU] #check AlgebraicGeometry.AlgebraicStack.IsPseudoCatenary

#check AlgebraicGeometry.AlgebraicStack.isPseudoCatenary_iff_existsSurjectiveSmooth
