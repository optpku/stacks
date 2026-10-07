module

public import ReasLib.RingTheory.RingHom.QuotientLift.LocallyNilpotent
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.138.17

@stack 07K4

Smooth algebras lift maps across quotients by locally nilpotent ideals.
-/

@[stacks 07K4 "lifting across a locally nilpotent quotient"]
#check @Algebra.Smooth.exists_lift_of_quotient_by_isLocallyNilpotent
