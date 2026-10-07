module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Tensor
import StacksCheckRecall

/-!
# Tensor description of the extended alternating Cech complex

@stack 0G6H
-/

@[expose] public section

/- Lemma 15.29.2: the extended alternating Cech complex of an `R`-module `M` is obtained by
tensoring the ring-valued extended complex by `M`. -/
@[stacks 0G6H "Lemma 15.29.2"]
#check @LocalizedModule.Away.Cech.Alternating.Tensor.extendedIso

#check @LocalizedModule.Away.Cech.Alternating.Tensor.codomainLinearEquiv
#check @LocalizedModule.Away.Cech.Alternating.Tensor.conerveIso
#check @LocalizedModule.Away.Cech.Alternating.Tensor.complexIso
