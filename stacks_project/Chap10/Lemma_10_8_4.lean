module

public import ReasLib.Algebra.Module.DirectLimit.Zero
import StacksCheckRecall

@[expose] public section

open Module.DirectLimit

/-!
# Eventual vanishing in a directed module colimit

@stack 00D7

The reusable owner makes the `DecidableEq I` parameter of Mathlib's direct-limit carrier explicit;
the chapter entry is therefore a thin recall rather than a second local classical instance.
-/

/- Lemma 10.8.4 (Tag 00D7), eventual zero criterion. -/
@[stacks 00D7]
#check @Module.DirectLimit.stageMap_eq_zero_iff

/- Canonical ingredients used by the owner. -/
#check @Module.DirectLimit.of.zero_exact
#check @Module.DirectLimit.of_f

end
