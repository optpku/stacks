/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Eilenberg
import StacksCheckRecall

/-!
# Lemma 15.129.2

The free-complement statement is recalled from its canonical ReasLib owner.

@stack 0GVG
-/

@[expose] public section

-- Lemma 15.129.2: every projective module has a free complement.
@[stacks 0GVG]
#check @Module.Projective.exists_free_prod_free
