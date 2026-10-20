/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion.Cohomology
import StacksCheckRecall

@[expose] public section

/- Lemma 20.36.4 (0BLC) is the site-cohomology specialization of the principal-torsion
Mittag–Leffler owner.  The cohomology functors and module-valued tower are imported directly from
ReasLib; no dependency on the preceding chapter facade is needed. -/

#check @CategoryTheory.siteModuleCohomologyFunctor
#check @CategoryTheory.siteModuleCohomologyModuleFunctor
#check @CategoryTheory.siteModuleCohomologyModuleTower
#check @CategoryTheory.siteModuleCohomologyTransitionMapLinear
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.IsPresented

@[stacks 0BLC "Mittag-Leffler tail from stage-one finiteness"]
#check @CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Cohomology.isMittagLeffler_of_stageOneFinite
