/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap109.Lemma_109_23_4_Contraction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

/- Lemma 109.23.4 (1) -/
@[stacks 0E8A] #check exists_contractionToStable

/- Lemma 109.23.4 (2) -/
@[stacks 0E8A] #check contractionToStable_unique
