/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Derived
import StacksCheckRecall

/-! Compatibility recall for the ReasLib owners of exact derived restriction on slice sites. -/

@[expose] public section

open CategoryTheory

#check @CategoryTheory.Sheaf.moduleCatPreadditive
#check @CategoryTheory.Sheaf.sheafModulePreadditive
#check @CategoryTheory.Sheaf.sheafModuleOverPreadditive
#check @CategoryTheory.Sheaf.constantSheafPreservesZeroMorphisms
#check @CategoryTheory.Sheaf.constantSheafOverPreservesZeroMorphisms
#check @CategoryTheory.Sheaf.overPullbackPreservesZeroMorphisms
#check @CategoryTheory.Sheaf.overPullbackAdditiveOfFamily
#check @CategoryTheory.Sheaf.overPullbackPreservesFiniteLimitsOfFamily
#check @CategoryTheory.Sheaf.overPullbackPreservesFiniteColimitsOfFamily

end
