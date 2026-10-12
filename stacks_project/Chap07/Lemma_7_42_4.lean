/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Sheafification
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.42.4

The comparison is owned by the reusable almost-cocontinuity API.  This file
records its source label and the two useful formal presentations.
-/

@[expose] public section

/- Lemma 7.42.4 (04B8): for a continuous almost cocontinuous functor, the
sheafification comparison is invertible on presheaves uniquely inhabited over
sheaf-theoretically empty target objects. -/
@[stacks 04B8] #check @CategoryTheory.Functor.IsAlmostCocontinuous.continuousSheafificationComparison_app_isIso
#check @CategoryTheory.Functor.IsAlmostCocontinuous.continuousSheafificationComparison_hom_app_isIso
#check @CategoryTheory.Presheaf.HasUniqueSectionsOn.continuousSheafificationComparison_isIso
#check @CategoryTheory.Presheaf.HasUniqueSectionsOn.continuousSheafificationComparison_hom_isIso
#check @CategoryTheory.sheafifyLift_isIso_of_isLocallyBijective
