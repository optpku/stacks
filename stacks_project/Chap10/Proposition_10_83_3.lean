module

import StacksCheckRecall
public import ReasLib.RingTheory.Finiteness.Projective.Descent

@[expose] public section

/-!
# Faithfully Flat Descent of Finite Projectivity Recall

The source statement is the direct faithfully-flat descent theorem owned by
`Module.FiniteProjective`.

@stack 058S
-/

/- Proposition 10.83.3, tag 058S: finite projectivity descends from a
faithfully flat scalar extension. -/
@[stacks 058S "faithfully flat descent of finite projective modules"]
#check @Module.FiniteProjective.of_tensorProduct
