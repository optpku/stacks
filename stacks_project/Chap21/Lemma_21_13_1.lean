/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Cohomology.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.13.1

The localized module-cohomology object and its comparisons with the underlying additive sheaf
live in ReasLib.  This chapter entry only recalls the source-facing comparison.
-/

/- Lemma 21.13.1 (079Y): cohomology over a presheaf of sets of the underlying additive sheaf
agrees with module cohomology after localization at its sheafification. -/
@[stacks 079Y]
#check @SheafOfModules.Cohomology.underlyingOverPresheaf_isomorphic

#check @SheafOfModules.Cohomology.underlyingOverSheaf_isomorphic
#check @RingedSite.Localization.AtSheaf.moduleCohomology
#check @CategoryTheory.Sheaf.cohomologyOverSheaf
#check @CategoryTheory.Sheaf.cohomologyOverPresheaf
