/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.RelativeCupProductBaseChange
import StacksCheckRecall

@[expose] public section

/- [stacks 0H99] Lemma 20.31.8: relative derived cup products commute with the canonical
derived base-change maps when the square comparison respects the four pullback-tensor
comparisons.  The categorical owner is independent of ringed spaces and derived categories. -/
@[stacks 0H99] #check @CategoryTheory.relativeDerivedCupProduct_baseChange_commSq
