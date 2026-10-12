/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
import StacksCheckRecall

/-!
# Lemma 10.11.3

@stack 00HA
-/

@[expose] public section

/- Chap10 Lemma 10 11 3 (Lemma 10.11.3): every module is a filtered colimit of finitely
presented modules. -/
@[stacks 00HA]
#check @ModuleCat.isFinitePresentation_ind
