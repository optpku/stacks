/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.AffineDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.LocallyOfFiniteType

/-- Being locally of finite type for scheme morphisms is local on the target for
the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.LocallyOfFiniteType
