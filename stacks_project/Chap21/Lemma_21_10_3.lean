/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
