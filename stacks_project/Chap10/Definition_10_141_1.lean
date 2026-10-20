module

public import ReasLib.RingTheory.RingHom.SmallExtension
import StacksCheckRecall

/-!
# Definition 10.141.1

@stack 02HS
-/

@[expose] public section

/- Definition 10.141.1 [02HS]: the reusable owner of small extensions is
`RingHom.IsSmallExtension`; its source and target local-Artinian API, surjectivity, and
length-one kernel API are provided by `ReasLib.RingTheory.RingHom.SmallExtension`. -/
@[stacks 02HS]
#check @RingHom.IsSmallExtension
