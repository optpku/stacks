/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.IndSmooth.Nilpotent

@[expose] public section

/- Proposition 16.5.3: ind-smoothness of a flat map lifts from the quotient by
a nilpotent source ideal. -/
@[stacks 07CM]
#check @RingHom.IndSmooth.of_quotient_nilpotent
