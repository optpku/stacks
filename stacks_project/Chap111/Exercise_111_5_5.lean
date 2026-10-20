module

public import ReasLib.Algebra.Module.Int.FlatNotFree
import StacksCheckRecall

@[expose] public section

/- Exercise 111.5.5: The fraction ring of `ℤ_{(2)}` is a flat but not free
module over `ℤ_{(2)}`. -/
@[stacks 02CU] #check (Int.fractionRing_not_free :
  ¬ Module.Free Int.localizationAtTwo (FractionRing Int.localizationAtTwo))

#check (Int.fractionRing_flat :
  Module.Flat Int.localizationAtTwo (FractionRing Int.localizationAtTwo))
