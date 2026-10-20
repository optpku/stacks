/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections

/-!
# Pullback of module sections on ringed spaces

The pullback of a global section is induced by the unit of the canonical pullback-pushforward
adjunction. This construction is available for every morphism of ringed spaces and does not
require finality of the map on opens.
-/

@[expose] public section

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Y : RingedSpace.{u}}

/-- The additive map on top-open values induced by the unit `F ⟶ f_* f^* F` of the canonical
module pullback-pushforward adjunction. -/
noncomputable abbrev globalSectionsPullback (f : X ⟶ Y) (F : Y.Modules) :
    RingedSpace.moduleGlobalSections F ⟶
      RingedSpace.moduleGlobalSections ((pullback f).obj F) :=
  RingedSpace.Modules.Hom.app ((pullbackPushforwardAdjunction f).unit.app F) ⊤

/-- Pullback of a compatible global section along a morphism of ringed spaces. -/
@[stacks 0H78 "pullback of module sections"]
noncomputable def pullbackSections (f : X ⟶ Y) {F : Y.Modules} (s : F.sections) :
    ((pullback f).obj F).sections :=
  RingedSpace.sectionFromTop ((pullback f).obj F)
    ((globalSectionsPullback f F).hom (s.1 (op ⊤)))

/-- Evaluating a pulled-back section at the top open gives the adjunction-unit map on top-open
values. -/
@[simp]
theorem pullbackSections_apply_top (f : X ⟶ Y) {F : Y.Modules} (s : F.sections) :
    (pullbackSections f s).1 (op ⊤) =
      (globalSectionsPullback f F).hom (s.1 (op ⊤)) := sorry

/-- Pullback of sections is natural in the module sheaf. -/
theorem pullbackSections_naturality
    (f : X ⟶ Y) {F G : Y.Modules} (φ : F ⟶ G) (s : F.sections) :
    SheafOfModules.sectionsMap ((pullback f).map φ) (pullbackSections f s) =
      pullbackSections f (SheafOfModules.sectionsMap φ s) := sorry

end AlgebraicGeometry.RingedSpace.Hom
