module

public import stacks_project.Chap90.Definition_90_21_4_Functors
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 90.21.4: a groupoid in functors on `C` is representable if it is
isomorphic to a coyoneda form `(coyoneda.obj (op U), coyoneda.obj (op R), s, t, c)`
for objects `U`, `R` of `C` such that the pushout `R ⨿_{s, U, t} R` exists. -/
@[stacks 06K6]
#check GroupoidInFunctors.IsRepresentable
