/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

/- Lemma 21.10.3 (Tag 03AX): a covering family determines a coefficient-natural comparison from
its Čech complex to derived sections. Applying homology gives the usual degreewise maps from
Čech cohomology to site cohomology. -/

@[stacks 03AX "existence of a derived Cech-to-site comparison"]
#check @CategoryTheory.Cech.derivedComparison_nonempty

#check @CategoryTheory.Cech.derivedSource
#check @CategoryTheory.Cech.derivedTarget
#check @CategoryTheory.Cech.DerivedComparison
#check @CategoryTheory.Cech.DerivedComparison.homology

#check @CategoryTheory.Cech.derivedSourceHomologyIso
#check @CategoryTheory.Cech.derivedTarget_homology_isIsomorphic

#check @CategoryTheory.Cech.DegreeComparison
#check @CategoryTheory.Cech.DerivedComparison.DegreeSystem
#check @CategoryTheory.Cech.DerivedComparison.DegreeSystem.degreeComparison
#check @CategoryTheory.Cech.DerivedComparison.degreeSystem_nonempty
#check @CategoryTheory.Cech.IsComparison
#check @CategoryTheory.Cech.comparison_exists

/- The source-facing selected-cover specialization only assumes its iterated fibre products. -/
#check @CategoryTheory.Cech.FixedTarget.derivedSource
#check @CategoryTheory.Cech.FixedTarget.cohomologyOnSheaves
#check @CategoryTheory.Cech.FixedTarget.DerivedComparison
@[stacks 03AX "selected-cover specialization"]
#check @CategoryTheory.Cech.FixedTarget.derivedComparison_nonempty
#check @CategoryTheory.Cech.FixedTarget.derivedSourceHomologyIso
#check @CategoryTheory.Cech.FixedTarget.DerivedComparison.homology
#check @CategoryTheory.Cech.FixedTarget.DerivedComparison.degreeComparison
#check @CategoryTheory.Cech.FixedTarget.DerivedComparison.degreeComparison_zero_isIso_app
