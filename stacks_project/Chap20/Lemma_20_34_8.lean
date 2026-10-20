/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.Underlying
import StacksCheckRecall

@[expose] public section

/- Lemma 20.34.8 (0G74): derived sections with support and derived global sections with support
agree with the corresponding constructions on underlying additive sheaves after forgetting
module structure.  The bundled owner separates the exact derived forgetful functors from the
module and additive models, and exposes both functor-level and objectwise comparisons. -/

@[stacks 0G74]
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Underlying.ambientForget
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Underlying.closedForget
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Underlying.moduleLocalCohomology
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Underlying.abelianLocalCohomology
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Underlying.localCohomology_isomorphic
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Underlying.localCohomology_obj_isomorphic
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Underlying.moduleGlobalSections
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Underlying.abelianGlobalSections
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Underlying.globalSections_isomorphic
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.Derived.Underlying.globalSections_obj_isomorphic
