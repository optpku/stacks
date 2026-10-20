/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation

/-!
# Pullback of finitely presented modules

Pullback along a scheme morphism restricts to the full subcategories of finitely presented
modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FinitePresentationModules

/-- Pullback of a finitely presented module is finitely presented. -/
theorem pullback_mem {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ℱ : FinitePresentationModules Y) :
    finitePresentationModuleProperty X ((Scheme.Modules.pullback f).obj ℱ.obj) := sorry

/-- Pullback on the full subcategories of finitely presented modules. -/
noncomputable def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FinitePresentationModules Y ⥤ FinitePresentationModules X :=
  ObjectProperty.lift (finitePresentationModuleProperty X)
    (inclusion Y ⋙ Scheme.Modules.pullback f) (pullback_mem f)

/-- The underlying sheaf of the restricted pullback is the usual module pullback. -/
@[simp]
theorem pullback_obj_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ℱ : FinitePresentationModules Y) :
    ((pullback f).obj ℱ).obj = (Scheme.Modules.pullback f).obj ℱ.obj := rfl

/-- On morphisms the restricted pullback is the usual module pullback. -/
@[simp]
theorem pullback_map_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ℱ 𝒢 : FinitePresentationModules Y} (φ : ℱ ⟶ 𝒢) :
    ((pullback f).map φ).hom = (Scheme.Modules.pullback f).map φ.hom := rfl

end AlgebraicGeometry.FinitePresentationModules
