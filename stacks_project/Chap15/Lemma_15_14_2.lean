module

import StacksCheckRecall
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed

@[expose] public section

/- Lemma 15.14.2: a ring is absolutely integrally closed exactly when every
nonconstant monic polynomial has a root. -/
/-!
@stack 0DCM
-/
@[stacks 0DCM "Lemma 15.14.2"]
#check @IsAbsolutelyIntegrallyClosed.iff_forall_monic_exists_root
