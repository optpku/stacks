/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Projective.InfiniteRank
import StacksCheckRecall

/-!
# Lemma 15.129.3

@stack 0GVH

The finite-free summand statement is recalled from its canonical ReasLib owner.
-/

@[expose] public section

-- Lemma 15.129.3: finite free summand containing a prescribed element.
@[stacks 0GVH]
#check @Module.Projective.existsFiniteFreeProdSummandContaining
