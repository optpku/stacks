/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Derived
import StacksCheckRecall

@[expose] public section

open SheafOfModules.RingedSite

/- Lemma 18.35.2 (08TY): a locally surjective polynomial presentation computes the canonical naive
cotangent complex in the derived category.  ReasLib owns the presentation model and the
presentation-independence statement. -/
@[stacks 08TY]
#check @NaiveCotangent.Presentation.ofGeneratorsIso

#check @NaiveCotangent.Presentation.derivedComparison
#check @NaiveCotangent.Presentation.derivedComparison_isIso
#check @NaiveCotangent.Presentation.derivedComparisonIso
#check @NaiveCotangent.Presentation.derivedComparisonIso_hom
#check @NaiveCotangent.Presentation.ofGeneratorsIso_hom
#check @NaiveCotangent.Presentation.isIsomorphic

#check @NaiveCotangent.Presentation.ofGenerators
#check @NaiveCotangent.Presentation.ofGenerators_X_negOne
#check @NaiveCotangent.Presentation.ofGenerators_X_zero
#check @NaiveCotangent.Presentation.ofGenerators_d_negOne_zero
#check @NaiveCotangent.Presentation.toCanonicalMap_f_negOne
#check @NaiveCotangent.Presentation.toCanonicalMap_f_zero
