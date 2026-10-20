/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Underlying.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage.Underlying
import StacksCheckRecall

@[expose] public section

/-!
# Cohomology after forgetting module structure

The two comparisons are properties of the underlying-additive-sheaf functor, not chapter-local
constructions.  The reusable owners expose the open-cohomology comparison at bounded-derived
functor level and the higher-direct-image comparison at natural-functor level.
-/

/- Lemma 20.13.3 (1): after forgetting its `Γ(U, 𝒪_X)`-module structure, module cohomology on
`U` agrees with the cohomology of the underlying additive sheaf. -/
@[stacks 01F1]
#check @AlgebraicGeometry.RingedSpace.moduleCohomologyAtOpenForget_obj_eq_underlyingSheafCohomology

/- The bounded right-derived comparison is the reusable functorial owner of part (1). -/
#check @AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Underlying.boundedModule_isIsomorphic

/- Lemma 20.13.3 (2): forgetting module structure commutes with higher direct image. -/
@[stacks 01F1]
#check @AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.Underlying.obj_isIsomorphic

/- Natural functors, rather than isolated objects, are the primary downstream interface. -/
#check @AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.Underlying.functor_isIsomorphic
