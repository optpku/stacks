/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.PrimeChain
import StacksCheckRecall

/-!
# Lemma 10.103.9

@stack 0AAE
-/

@[expose] public section

/-
Lemma 10.103.9 (Stacks tag `0AAE`) is a direct recall of the shared maximal
prime-chain dimension formula. The canonical owner is
`Module.CohenMacaulay.ringKrullDim_eq_length_of_maximal_chain`; retaining
the former chapter-level theorem would create a second public owner for the
same statement.
-/
@[stacks 0AAE]
#check @Module.CohenMacaulay.ringKrullDim_eq_length_of_maximal_chain
