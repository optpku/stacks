module

public import ReasLib.RingTheory.RegularLocalRing.Flatness
import StacksCheckRecall

@[expose] public section

/-!
# Flatness from regular parameters

The reusable criterion is owned by
`Module.Flat.of_regularSystemOfParameters_image_isRegular`.

@stack 07DY
-/

/- Lemma 10.128.2 (Tag 07DY): a local algebra over a regular local ring is flat when a regular
system of parameters maps to a regular sequence in the target. -/
@[stacks 07DY]
#check @Module.Flat.of_regularSystemOfParameters_image_isRegular
