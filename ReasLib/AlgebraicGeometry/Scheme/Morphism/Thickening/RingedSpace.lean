/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Conormal
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution

/-! # First-order scheme thickenings and their underlying ringed spaces -/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A first-order thickening of schemes is a first-order thickening of the underlying
ringed spaces. -/
instance instIsFirstOrderThickening_toShHom {X Y : Scheme.{u}} (h : X ⟶ Y)
    [IsFirstOrderThickening h] :
    RingedSpace.IsFirstOrderThickening h.toShHom := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Thickening

open AlgebraicGeometry.RingedSpace.Thickening (conormalToTargetModule targetModuleToIdealModule)
open AlgebraicGeometry.RingedSpace.Hom (conormalSheaf idealModule)

/-- The square-zero identification of the inverse-image conormal sheaf with the
kernel ideal module of a first-order thickening of schemes. -/
def conormalToIdeal {Y Y' : Scheme.{u}} (h : Y ⟶ Y') [IsFirstOrderThickening h] :
    conormalSheaf h.toShHom ⟶ idealModule h.toShHom :=
  conormalToTargetModule h.toShHom ≫ targetModuleToIdealModule h.toShHom

/-- The comparison `conormalToIdeal` is an isomorphism. -/
instance instIsIso_conormalToIdeal {Y Y' : Scheme.{u}} (h : Y ⟶ Y')
    [IsFirstOrderThickening h] : IsIso (conormalToIdeal h) := sorry

/-- Canonical isomorphism between the conormal sheaf and the kernel ideal module of a
first-order thickening. -/
def conormalIdealIso {Y Y' : Scheme.{u}} (h : Y ⟶ Y') [IsFirstOrderThickening h] :
    conormalSheaf h.toShHom ≅ idealModule h.toShHom :=
  asIso (conormalToIdeal h)

end AlgebraicGeometry.Scheme.Thickening
