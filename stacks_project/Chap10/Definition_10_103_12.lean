module

public import ReasLib.RingTheory.CohenMacaulay.Module.Local
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.103.12

@stack 0AAH

Definition 10.103.12 is owned by the neutral primewise Cohen-Macaulay module API.
-/

/- Definition 10.103.12 (Tag 0AAH): `Module.LocallyCohenMacaulay R M` means that every prime
localization of the finite module `M` is Cohen-Macaulay. -/
@[stacks 0AAH "locally Cohen-Macaulay module"]
#check @Module.LocallyCohenMacaulay
