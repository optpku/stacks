/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.FaithfullyFlat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.AffineDescent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.BaseChange

@[expose] public section

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- Perfectness of scheme morphisms is local on the target for the fpqc precoverage. -/
instance isPerfectRingMap_isLocalAtTargetFpqc :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap)
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.LocallyOfType
