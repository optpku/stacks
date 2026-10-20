module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Derived
import StacksCheckRecall

/-! 21.53 support is a recall surface; reusable comparison data lives in ReasLib. -/

@[expose] public section

open CategoryTheory

#check @CategoryTheory.Sheaf.constantSheafOverObjIso
#check @CategoryTheory.Sheaf.constantSheafOverIso
#check @CategoryTheory.Sheaf.constantSheafOverDerivedIso
#check @CategoryTheory.Sheaf.overPullbackAdditiveOfFamily
#check @CategoryTheory.Sheaf.overPullbackPreservesFiniteLimitsOfFamily
#check @CategoryTheory.Sheaf.overPullbackPreservesFiniteColimitsOfFamily

end
