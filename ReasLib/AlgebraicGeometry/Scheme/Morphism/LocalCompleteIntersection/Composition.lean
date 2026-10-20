/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.RingTheory.CompleteIntersection.Local.Composition

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- Scheme morphisms locally induced by local complete-intersection ring maps are stable under
composition. -/
instance instIsLocalCompleteIntersectionStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsLocalCompleteIntersection) := sorry

/-- The composite of two scheme morphisms locally induced by local complete-intersection ring
maps is again locally induced by local complete-intersection ring maps. -/
instance isLocalCompleteIntersection_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f]
    [LocallyOfType RingHom.IsLocalCompleteIntersection g] :
    LocallyOfType RingHom.IsLocalCompleteIntersection (f ≫ g) := sorry

end AlgebraicGeometry.LocallyOfType
