/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ClosedSubset.SectionsWithSupport
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry SheafOfModules.ClosedSubset

noncomputable section

universe u

namespace AlgebraicGeometry

open SheafOfModules.ClosedSubset.SectionsWithSupport

variable {X : RingedSpace.{u}} (Z : Closeds X)

/- Remark 17.13.5 (0G6N): sections supported on `Z` form a functor from `𝒪_X`-modules to
`𝒪_X|_Z`-modules. -/
@[stacks 0G6N "closed-support functor"]
#check (𝓗[Z] : X.Modules ⥤ SheafOfModules.ClosedSubset.Modules X.ringCatSheaf Z)

/- Remark 17.13.5 (0G6N): the closed-support subsheaf has the expected sectionwise
characterization. -/
@[stacks 0G6N "sections"]
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.mem_range_subsheaf_app_iff

/- Remark 17.13.5 (0G6N): it is the greatest module subsheaf supported on `Z`. -/
@[stacks 0G6N "maximality"]
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.isGreatest_subsheaf

/- Companion: any module subsheaf supported on `Z` lies below the canonical one. -/
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.le_subsheaf_of_support_subset

/- Remark 17.13.5 (0G6N): the closed-support functor is left exact. -/
@[stacks 0G6N "left exact"]
#check (functor_leftExact X.ringCatSheaf Z :
  leftExactFunctor X.Modules (SheafOfModules.ClosedSubset.Modules X.ringCatSheaf Z) (𝓗[Z]))

/- Companion: as a right adjoint, the closed-support functor preserves all limits. -/
#check (inferInstance : PreservesLimits (𝓗[Z]))

/- Remark 17.13.5 (0G6N): closed support is not exact in general. -/
@[stacks 0G6N "not exact in general"]
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.exists_not_exact

end AlgebraicGeometry
