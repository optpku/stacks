/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Cohomology
import StacksCheckRecall

@[expose] public section

open RingedSite.Hom

/- 21.2.0.6 (071H): module global cohomology is computed by applying global sections to an
injective resolution and taking homology.  The reusable owner keeps the coefficient as a module
sheaf; it is not the additive-sheaf statement 071E. -/
@[stacks 071H "module cohomology from an injective resolution"]
#check @moduleGlobalCohomology_isomorphic_homology_of_injectiveResolution
