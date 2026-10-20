/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- 21.2.0.5 (071G): cohomology over an object of a ringed site is computed from the evaluated
injective-resolution complex. -/
@[stacks 071G "objectwise module cohomology from an injective resolution"]
#check @SheafOfModules.cohomologyAtObject_isomorphic_homology_of_injectiveResolution

/- The objectwise cohomology functor is the canonical left-hand owner. -/
#check @SheafOfModules.cohomologyAtObjectFunctor
