module

public import ReasLib.RingTheory.Regular.JRing.CompleteLocal
import StacksCheckRecall

/-!
# Lemma 15.48.6

@stack 07PI
-/

@[expose] public section

/-! # Lemma 15.48.6: complete local domains are J-0 -/

/- Lemma 15.48.6, tag `07PI`: every Noetherian complete local domain is `J-0`. -/
@[stacks 07PI "complete local domains are J-0"]
#check @IsJ0Ring.completeLocalDomain
