/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Module.Support.BaseChange
import StacksCheckRecall

/-!
# Lemma 10.40.6

@stack 0BUR
-/

@[expose] public section

/-
Lemma 10.40.6 (Stacks tag `0BUR`).  The chapter item is a direct recall of
the reusable support formula for tensor-product scalar extension.  The
canonical owner is `Module.support_tensorProduct_eq_preimage_comap`; keeping
the numbered chapter theorem as a second owner would duplicate the API.
-/
@[stacks 0BUR]
#check @Module.support_tensorProduct_eq_preimage_comap
