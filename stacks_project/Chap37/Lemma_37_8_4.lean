/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap37.Definition_37_8_1_FormallyEtale
import StacksCheckRecall

/- Lemma 37.8.4: A base change of a formally étale morphism is formally étale. -/
@[stacks 02HJ] #check
  (AlgebraicGeometry.FormallyEtale.instIsStableUnderBaseChange :
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      @AlgebraicGeometry.FormallyEtale)
