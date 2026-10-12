/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.FilteredColimits.Ordinal
public import ReasLib.CategoryTheory.Sites.Sheaf.Colimit
public import ReasLib.SetTheory.Ordinal.Cofinality
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.17.10 core recall

The former core mixed ordinal synchronization, a presieve presentation, and
the canonical sheafified-colimit comparison.  Each has a neutral ReasLib
owner; the construction-specific secondary-cover indices are proof support,
not a public Chapter 7 API.
-/

@[expose] public section

@[stacks 0GS0] #check @CategoryTheory.Sheaf.sheafifyColimitIso

#check @CategoryTheory.Sheaf.sheafifyColimitIso_ι_hom
#check @CategoryTheory.Sheaf.sheafifyColimitIso_ι_inv
#check @CategoryTheory.Presieve.ofArrows_uncurry_eq
#check @Ordinal.ToType.exists_upperBound_of_lift_mk_lt_cof
#check @CategoryTheory.Precoverage.FilteredColimitSections.isIso_of_ordinal
