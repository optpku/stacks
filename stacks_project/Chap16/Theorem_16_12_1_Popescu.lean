module

public import ReasLib.RingTheory.RingHom.IndSmooth.Popescu
import StacksCheckRecall

@[expose] public section

/- Theorem 16.12.1 (Popescu): regular Noetherian ring maps are filtered
colimits of smooth maps. -/
@[stacks 07GC]
#check @RingHom.Regular.indSmooth

#check @RingHom.Regular.hasFactorisations
