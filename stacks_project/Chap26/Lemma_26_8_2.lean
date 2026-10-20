/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedImmersion.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.8.2: a closed immersion into an affine scheme is classified by a unique quotient
ideal; the reusable ideal is the kernel on global sections. -/
@[stacks 01IH] #check LocallyRingedSpace.Hom.AffineQuotient.existsUniqueIdeal
#check LocallyRingedSpace.Hom.globalSectionsKernelIdeal
#check LocallyRingedSpace.Hom.AffineQuotient.spec
#check LocallyRingedSpace.Hom.AffineQuotient.ι
#check LocallyRingedSpace.Hom.AffineQuotient.comparison
#check LocallyRingedSpace.Hom.AffineQuotient.comparison_ι
#check LocallyRingedSpace.Hom.AffineQuotient.comparison_isIso
#check LocallyRingedSpace.Hom.AffineQuotient.ideal_eq_of_isIsomorphic
