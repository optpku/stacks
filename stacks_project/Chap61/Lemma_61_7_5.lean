/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.IndEtale.Composition
import StacksCheckRecall

@[expose] public section

/- Lemma 61.7.5: if `B → C` is an A-algebra map of ind-étale A-algebras,
then `C` is an ind-étale B-algebra. -/
@[stacks 097M] #check @RingHom.IndEtale.of_over_common_base

#check @RingHom.IndEtale.Raw.of_over_common_base
