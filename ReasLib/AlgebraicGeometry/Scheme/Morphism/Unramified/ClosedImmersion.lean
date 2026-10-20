/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

/-!
# Closed immersions are unramified

Every closed immersion is unramified. The G-unramified condition is equivalent to finite type of
the kernel ideal sheaf.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {X Z : Scheme.{u}} {i : Z ⟶ X}

/-- Every closed immersion of schemes is unramified. -/
theorem IsClosedImmersion.unramified [hi : IsClosedImmersion i] : Unramified i := by
  exact
    { toFormallyUnramified := inferInstance
      toLocallyOfFiniteType := inferInstance }

/-- A closed immersion of schemes is G-unramified exactly when its kernel ideal sheaf is of finite
type. -/
theorem IsClosedImmersion.gUnramified_iff_idealSheaf_isFiniteType
    [hi : IsClosedImmersion i] :
    GUnramified i ↔
      SheafOfModules.IsFiniteType (RingedSpace.Hom.idealSheaf i.toShHom) := by
  constructor
  · intro h
    exact
      (closedImmersion_locallyOfFinitePresentation_iff_idealSheaf_isFiniteType hi).mp
        h.toLocallyOfFinitePresentation
  · intro h
    exact
      { toFormallyUnramified := inferInstance
        toLocallyOfFinitePresentation :=
          (closedImmersion_locallyOfFinitePresentation_iff_idealSheaf_isFiniteType hi).mpr h }

end AlgebraicGeometry
