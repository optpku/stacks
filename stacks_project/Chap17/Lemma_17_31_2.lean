/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Derived
import StacksCheckRecall

@[expose] public section

open SheafOfModules.RingedSite

/- Lemma 17.31.2 (08TL): a locally surjective presentation of a sheaf of algebras computes its
canonical naive cotangent complex. The site-level ReasLib theorem specializes directly to an
opens site. -/
@[stacks 08TL]
#check @NaiveCotangent.Presentation.ofGeneratorsIso

#check @NaiveCotangent.Presentation.derivedComparison
#check @NaiveCotangent.Presentation.derivedComparison_isIso
#check @NaiveCotangent.Presentation.derivedComparisonInv
#check @NaiveCotangent.Presentation.derivedComparison_comp_derivedComparisonInv
#check @NaiveCotangent.Presentation.derivedComparisonInv_comp_derivedComparison
#check @NaiveCotangent.Presentation.derivedComparisonIso
#check @NaiveCotangent.Presentation.derivedComparisonIso_hom
#check @NaiveCotangent.Presentation.derivedComparisonIso_inv
#check @NaiveCotangent.Presentation.ofGeneratorsIso_hom
#check @NaiveCotangent.Presentation.isIsomorphic
#check @NaiveCotangent.Presentation.toCanonicalMap
#check @NaiveCotangent.Presentation.toCanonicalMap_f_negOne
#check @NaiveCotangent.Presentation.toCanonicalMap_f_zero
