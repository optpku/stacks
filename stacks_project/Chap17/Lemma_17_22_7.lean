/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation.FilteredColimit
import StacksCheckRecall

/-!
# Lemma 17.22.7

Internal Hom out of a finitely presented module sheaf commutes with filtered colimits.  The
neutral ringed-site owner specializes directly to modules on a ringed space.
-/

@[expose] public section

/- Lemma 17.22.7 (0GMV): the canonical filtered-colimit comparison for `ihom F` is an
isomorphism. -/
@[stacks 0GMV]
#check @SheafOfModules.IsFinitePresentation.FilteredColimit.ihom_isIso

#check @SheafOfModules.IsFinitePresentation.FilteredColimit.ihomComparison
#check @SheafOfModules.IsFinitePresentation.FilteredColimit.ihomComparison_ι
#check @SheafOfModules.IsFinitePresentation.FilteredColimit.ihomComparisonInv
#check @SheafOfModules.IsFinitePresentation.FilteredColimit.ihomComparisonIso
