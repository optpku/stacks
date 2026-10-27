/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
import Mathlib.Tactic.CrossRefAttribute

/-!
# Scheme and ringed-space presentations of quasicoherent modules

The ambient module categories on a scheme and on its underlying ringed space have identical
mathematical data but distinct category instances.  This file restricts the explicit ambient
presentation equivalence to the quasicoherent full subcategories. The restricted equivalence is
the sole data owner; its forward and inverse functors are projections rather than independently
constructed restrictions.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.QCoh

namespace ringedSpaceEquivalence

/-- Pulling the ringed-space quasicoherence property back along the ambient presentation
equivalence gives Mathlib's scheme quasicoherence property. -/
theorem propertyInverseImage (X : Scheme.{u}) :
    (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace).inverseImage
        (Scheme.Modules.ringedSpaceEquivalence X).functor =
      quasiCoherentModuleProperty X := by
  rfl

/-- Quasicoherence in the two ambient module presentations is equivalent objectwise. -/
@[simp]
theorem property_iff {X : Scheme.{u}} (M : X.Modules) :
    RingedSpace.quasiCoherentModuleProperty X.toRingedSpace
        ((Scheme.Modules.toRingedSpace X).obj M) ↔
      quasiCoherentModuleProperty X M :=
  Iff.rfl

end ringedSpaceEquivalence

/-- The canonical equivalence between the two presentations of quasicoherent modules on a
scheme. -/
@[stacks 01BE "quasicoherent presentation equivalence"]
def ringedSpaceEquivalence (X : Scheme.{u}) : QCoh X ≌ RingedSpace.QCoh X.toRingedSpace :=
  (Scheme.Modules.ringedSpaceEquivalence X).congrFullSubcategory
    (ringedSpaceEquivalence.propertyInverseImage X)

/-- The forward projection of the canonical quasicoherent presentation equivalence. -/
abbrev toRingedSpace (X : Scheme.{u}) : QCoh X ⥤ RingedSpace.QCoh X.toRingedSpace :=
  (ringedSpaceEquivalence X).functor

/-- The inverse projection of the canonical quasicoherent presentation equivalence. -/
abbrev fromRingedSpace (X : Scheme.{u}) : RingedSpace.QCoh X.toRingedSpace ⥤ QCoh X :=
  (ringedSpaceEquivalence X).inverse

namespace ringedSpaceEquivalence

/-- The canonical quasicoherent equivalence is compatible with the two ambient inclusion
functors in its forward direction. -/
def inclusionIso (X : Scheme.{u}) :
    toRingedSpace X ⋙ RingedSpace.QCoh.inclusion X.toRingedSpace ≅
      inclusion X ⋙ Scheme.Modules.toRingedSpace X :=
  Iso.refl _

/-- The canonical quasicoherent equivalence is compatible with the two ambient inclusion
functors in its inverse direction. -/
def inverseInclusionIso (X : Scheme.{u}) :
    fromRingedSpace X ⋙ inclusion X ≅
      RingedSpace.QCoh.inclusion X.toRingedSpace ⋙ Scheme.Modules.fromRingedSpace X :=
  Iso.refl _

/-- The canonical forward inclusion comparison is componentwise the identity. -/
@[simp]
theorem inclusionIso_hom_app {X : Scheme.{u}} (M : QCoh X) :
    (inclusionIso X).hom.app M =
      𝟙 ((Scheme.Modules.toRingedSpace X).obj M.obj) := by
  rfl

/-- The inverse of the canonical forward inclusion comparison is componentwise the identity. -/
@[simp]
theorem inclusionIso_inv_app {X : Scheme.{u}} (M : QCoh X) :
    (inclusionIso X).inv.app M =
      𝟙 ((Scheme.Modules.toRingedSpace X).obj M.obj) := by
  rfl

/-- The canonical inverse inclusion comparison is componentwise the identity. -/
@[simp]
theorem inverseInclusionIso_hom_app {X : Scheme.{u}}
    (M : RingedSpace.QCoh X.toRingedSpace) :
    (inverseInclusionIso X).hom.app M =
      𝟙 ((Scheme.Modules.fromRingedSpace X).obj M.obj) := by
  rfl

/-- The inverse of the canonical inverse inclusion comparison is componentwise the identity. -/
@[simp]
theorem inverseInclusionIso_inv_app {X : Scheme.{u}}
    (M : RingedSpace.QCoh X.toRingedSpace) :
    (inverseInclusionIso X).inv.app M =
      𝟙 ((Scheme.Modules.fromRingedSpace X).obj M.obj) := by
  rfl

end ringedSpaceEquivalence

namespace toRingedSpace

/-- The forward projection of the presentation equivalence leaves the underlying module sheaf
unchanged. -/
@[simp]
theorem obj_obj {X : Scheme.{u}} (M : QCoh X) :
    ((toRingedSpace X).obj M).obj = M.obj := by
  rfl

/-- The forward projection of the presentation equivalence leaves the underlying morphism
unchanged. -/
@[simp]
theorem map_hom {X : Scheme.{u}} {M N : QCoh X} (f : M ⟶ N) :
    ((toRingedSpace X).map f).hom = f.hom := by
  rfl

end toRingedSpace

namespace fromRingedSpace

/-- The inverse projection of the presentation equivalence leaves the underlying module sheaf
unchanged. -/
@[simp]
theorem obj_obj {X : Scheme.{u}} (M : RingedSpace.QCoh X.toRingedSpace) :
    ((fromRingedSpace X).obj M).obj = M.obj := by
  rfl

/-- The inverse projection of the presentation equivalence leaves the underlying morphism
unchanged. -/
@[simp]
theorem map_hom {X : Scheme.{u}} {M N : RingedSpace.QCoh X.toRingedSpace} (f : M ⟶ N) :
    ((fromRingedSpace X).map f).hom = f.hom := by
  rfl

end fromRingedSpace

variable (X : Scheme.{u})

#synth (toRingedSpace X).IsEquivalence
#synth (fromRingedSpace X).IsEquivalence

end AlgebraicGeometry.Scheme.QCoh
