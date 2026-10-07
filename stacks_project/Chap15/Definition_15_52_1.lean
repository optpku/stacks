module

public import ReasLib.RingTheory.Excellent
import StacksCheckRecall

/-!
# Definition 15.52.1

@stack 07QT
-/

@[expose] public section

/- Definition 15.52.1 (1): quasi-excellent rings. -/
@[stacks 07QT "(1)"]
#check @IsQuasiExcellentRing

/- Definition 15.52.1 (2): excellent rings. -/
@[stacks 07QT "(2)"]
#check @IsExcellentRing

#check @IsQuasiExcellentRing.ofComponents
#check @IsExcellentRing.ofComponents
#check @isQuasiExcellentRing_iff
#check @isExcellentRing_iff
