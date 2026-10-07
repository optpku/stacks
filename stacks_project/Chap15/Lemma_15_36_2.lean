module

import StacksCheckRecall
public import ReasLib.RingTheory.Topology.Adic.Continuity

/-!
Lemma 15.36.2 (07E9): continuity of an adically continuous ring homomorphism is witnessed
by a positive-power containment. The reusable owner is `RingHom.AdicContinuous` in ReasLib.
@stack 07E9
-/

@[stacks 07E9] #check @RingHom.AdicContinuous.continuous_iff_exists_pos
