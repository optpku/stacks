module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.IndSmooth.Nilpotent

@[expose] public section

/- Proposition 16.5.3: ind-smoothness of a flat map lifts from the quotient by
a nilpotent source ideal. -/
@[stacks 07CM]
#check @RingHom.IndSmooth.of_quotient_nilpotent
