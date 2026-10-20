/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Triangulated
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Property
public import ReasLib.CategoryTheory.Pretriangulated.K0.GrothendieckGroup

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The zeroth Grothendieck group of perfect derived `O_X`-modules. -/
abbrev K0 (X : Scheme.{u}) : Type (u + 1) :=
  TriangulatedK0 (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))

/-- The zeroth Grothendieck group of coherent `O_X`-modules on a locally Noetherian
scheme. -/
abbrev K0' (X : Scheme.{u}) [IsLocallyNoetherian X] : Type (u + 1) :=
  ObjectProperty.GrothendieckGroup
    (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)

end AlgebraicGeometry.Scheme
