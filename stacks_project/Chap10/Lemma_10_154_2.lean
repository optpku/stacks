/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.IndEtale.Composition
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.154.2, tag `0BSI`, is the canonical composition theorem for
ind-etale ring maps.

@stack 0BSI
-/

@[stacks 0BSI]
#check @RingHom.IndEtale.Raw.comp
