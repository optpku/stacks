/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion.Cohomology.Images
import StacksCheckRecall

@[expose] public section

/- Lemma 20.36.5 (0DXG) uses the canonical stage-one images of the module-valued site-cohomology
tower.  Their intersection and the Mittag–Leffler consequence are owned by ReasLib, so this
chapter file remains a direct source-label recall. -/

#check @CategoryTheory.siteModuleCohomologyFunctor
#check @CategoryTheory.siteModuleCohomologyModuleTower
#check @CategoryTheory.siteModuleCohomologyTransitionMapLinear
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsPresented

@[stacks 0DXG "stage-one cohomology image"]
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Cohomology.stageOneImage

@[stacks 0DXG "intersection of stage-one cohomology images"]
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Cohomology.stageOneImageInf

#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Cohomology.stageOneImageInf_le
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Cohomology.stageOneImageInf_isFiniteLength_of

@[stacks 0DXG "Mittag-Leffler tail from stage-one images"]
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Cohomology.isMittagLeffler_of_stageOneImageFinite
