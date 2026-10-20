module

public import ReasLib.RingTheory.Flatness.MittagLeffler.SupportingSubmodule
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.89.6

@stack 0AS6
-/

/- Chap10 Lemma 10 89 6 (Lemma 10.89.6): every tensor over a flat Mittag-Leffler module has a
least finite supporting submodule. -/
@[stacks 0AS6]
#check @Module.MittagLeffler.exists_least_finite_tensorSupport
