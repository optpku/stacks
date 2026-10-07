module

public import ReasLib.FieldTheory.Perfect.Criteria
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.45.2 (Tag 030Z) is a direct recall of the canonical perfect-field
Frobenius criteria.  The perfect-field/perfect-ring conversion remains the
upstream owner API; the source-facing root criterion is in `PerfectField`.

@stack 030Z
-/

#check @PerfectField.toPerfectRing
#check @PerfectRing.toPerfectField

@[stacks 030Z]
#check @PerfectField.iff_surjective_frobenius

@[stacks 030Z]
#check @PerfectField.iff_charZero_or_exists_pthRoot
