/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Henselian
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.94.10 (0G3H)

@stack 0G3H
-/

/- Lemma 15.94.10 (Stacks `0G3H`): if `A`, viewed as an `A`-module, is derived complete with
respect to an ideal `I`, then `(A, I)` is a Henselian pair. -/
@[stacks 0G3H "Lemma 15.94.10, derived completeness gives a Henselian pair"]
#check @ModuleCat.IsDerivedCompleteWithRespectTo.henselianRing
