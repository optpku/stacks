module

import StacksCheckRecall
public import ReasLib.RingTheory.CohenMacaulay.Maximal

@[expose] public section

/-!
# Chapter 10 Compatibility Facade

Definition 10.103.8 is owned by the neutral maximal Cohen-Macaulay module API.

@stack 00NF
-/

/- Definition 10.103.8 (Tag 00NF): `Module.MaximalCohenMacaulay R M` records the finite local
module condition `moduleDepth R M = ringKrullDim R`, with bridges to ordinary
`Module.CohenMacaulay`. -/
@[stacks 00NF "maximal Cohen-Macaulay modules"]
#check @Module.MaximalCohenMacaulay
@[stacks 00NF "nontriviality consequence"]
#check @Module.MaximalCohenMacaulay.nontrivial
@[stacks 00NF "support dimension consequence"]
#check @Module.MaximalCohenMacaulay.supportDim_eq_ringKrullDim
@[stacks 00NF "Cohen-Macaulay consequence"]
#check @Module.MaximalCohenMacaulay.toCohenMacaulay
@[stacks 00NF "instance consequence"]
#check @Module.cohenMacaulay_of_maximalCohenMacaulay
