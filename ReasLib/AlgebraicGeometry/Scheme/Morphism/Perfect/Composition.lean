/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.RingTheory.RingHom.Perfect.Composition

/-!
# Composition of perfect scheme morphisms

Scheme morphisms locally induced by perfect ring maps are closed under composition.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- Scheme morphisms locally induced by perfect ring maps are stable under composition. -/
instance instIsPerfectRingMapStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap) := sorry

/-- The composite of two scheme morphisms locally induced by perfect ring maps is again
locally induced by perfect ring maps. -/
instance isPerfectRingMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsPerfectRingMap f]
    [LocallyOfType RingHom.IsPerfectRingMap g] :
    LocallyOfType RingHom.IsPerfectRingMap (f ≫ g) := sorry

end AlgebraicGeometry.LocallyOfType
