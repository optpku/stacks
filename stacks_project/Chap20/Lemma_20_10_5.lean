/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech.RightDerived
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveResolution
import StacksCheckRecall

@[expose] public section

/- Lemma 20.10.5 (Tag 01EN): for a covering family, Cech cohomology is the universal delta
functor and agrees with the right derived functors of its degree-zero branch. The reusable owner
has a stronger cover-independent core; this recall keeps the source's `CoversTop` hypothesis in
the public chapter-facing entry. The complex comparison is a roof through a total complex, so the
chapter deliberately recalls the derived comparison rather than claiming a direct chain map. -/

open CategoryTheory
open SheafOfModules.RingedSite.Cech

@[stacks 01EN] #check @deltaFunctor_isUniversal_of_coversTop
@[stacks 01EN] #check @degreeZero
@[stacks 01EN] #check @rightDerived
@[stacks 01EN] #check @derivedDeltaFunctor
@[stacks 01EN] #check @canonicalZeroIso
@[stacks 01EN] #check @canonicalDeltaIso
@[stacks 01EN] #check @canonicalDegreeIso

/- The injective-resolution computation remains the generic owner used by the total-complex roof. -/
#check @CategoryTheory.InjectiveResolution.isoRightDerivedObj
