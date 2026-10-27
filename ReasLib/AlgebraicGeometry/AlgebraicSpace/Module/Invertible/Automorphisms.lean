/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Endomorphism
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.StructureModule

/-! # Automorphisms of invertible modules -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Automorphisms of an invertible module induce automorphisms of the monoidal unit. -/
def autToAutUnit {Y : AlgebraicSpace S} (L : Y.Modules)
    (hL : isInvertibleObject L) (α : Aut L) : Aut (𝟙_ Y.Modules) :=
  (@isInvertibleObject.tensorInverseIso Y.Modules _ _ L hL).conjAut
    ((tensorRight (@isInvertibleObject.inverse Y.Modules _ _ L hL)).mapIso α)

/-- Automorphisms of the monoidal unit induce automorphisms of an invertible module. -/
def autUnitToAut {Y : AlgebraicSpace S} (L : Y.Modules) (β : Aut (𝟙_ Y.Modules)) :
    Aut L :=
  (λ_ L).conjAut ((tensorRight L).mapIso β)

/-- The left inverse law of `autToAutUnit`. -/
theorem autToAutUnit_left {Y : AlgebraicSpace S} (L : Y.Modules)
    (hL : isInvertibleObject L) (α : Aut L) :
    autUnitToAut L (autToAutUnit L hL α) = α := sorry

/-- The right inverse law of `autToAutUnit`. -/
theorem autToAutUnit_right {Y : AlgebraicSpace S} (L : Y.Modules)
    (hL : isInvertibleObject L) (β : Aut (𝟙_ Y.Modules)) :
    autToAutUnit L hL (autUnitToAut L β) = β := sorry

/-- Automorphisms of an invertible module determine automorphisms of the structure module. -/
def autToUnitAut {Y : AlgebraicSpace S} (L : Y.Modules)
    (hL : isInvertibleObject L) (α : Aut L) :
    Aut (SheafOfModules.unit (structureSheaf Y)) :=
  (Modules.structureModuleIsoTensorUnit Y).symm.conjAut (autToAutUnit L hL α)

/-- Automorphisms of the structure module determine automorphisms of an invertible module. -/
def unitAutToAut {Y : AlgebraicSpace S} (L : Y.Modules)
    (β : Aut (SheafOfModules.unit (structureSheaf Y))) : Aut L :=
  autUnitToAut L ((Modules.structureModuleIsoTensorUnit Y).conjAut β)

end AlgebraicGeometry.AlgebraicSpace.Modules
