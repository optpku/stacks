/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The structure sheaf of the source of a finite type flat morphism with geometrically integral
fibres is universally pure over the target. -/
theorem isUniversallyPureOver_of_flat_of_geometricallyIntegral
    {X S : Scheme.{u}} (f : X ⟶ S) [Hom.FiniteType f] [Flat f]
    [GeometricallyIntegral f] :
    Modules.IsUniversallyPureOver
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) f := sorry

end AlgebraicGeometry.Scheme
