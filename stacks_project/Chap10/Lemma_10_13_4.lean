module

public import ReasLib.LinearAlgebra.ExteriorPower.RestrictScalars.Presentation
import StacksCheckRecall

/-!
# Exterior-power relations after changing scalars

Stacks tag `0H1C` is false as written.  The corrected statement identifies
the kernel with the inverse image of the intrinsic repeated-entry relations.
The ReasLib theorem is stronger: it accepts an arbitrary linear map into the
canonical restriction of the target module, without requiring a second module
action or scalar-tower instance on its raw carrier.

@stack 0H1C
-/

@[expose] public section

@[stacks 0H1C "corrected scalar-change exterior presentation"]
#check @exteriorPower.RestrictScalars.ker_quotient
