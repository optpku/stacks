/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.Module.Quasicoherent
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Quasi-coherent modules on simplicial schemes
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- The property of being a quasi-coherent module on the simplicial Zariski site. -/
abbrev quasiCoherentModuleProperty (U : SimplicialObject Scheme.{u}) :
    ObjectProperty (SheafOfModules.{u} (structureSheaf U)) :=
  SheafOfModules.isQuasicoherent (structureSheaf U)

/-- Quasi-coherence on a simplicial scheme is the quasi-coherence predicate for its
structure sheaf. -/
theorem quasiCoherentModuleProperty_eq (U : SimplicialObject Scheme.{u}) :
    quasiCoherentModuleProperty U =
      SheafOfModules.isQuasicoherent (structureSheaf U) := rfl

/-- Membership in the quasi-coherent module property is equivalent to quasi-coherence. -/
theorem mem_QCoh_iff (U : SimplicialObject Scheme.{u})
    {M : SheafOfModules.{u} (structureSheaf U)} :
    quasiCoherentModuleProperty U M ↔ M.IsQuasicoherent := Iff.rfl

/-- The full subcategory of quasi-coherent modules on a simplicial scheme. -/
abbrev QCoh (U : SimplicialObject Scheme.{u}) :=
  (quasiCoherentModuleProperty U).FullSubcategory

/-- The inclusion of quasi-coherent modules into all module sheaves. -/
abbrev QCoh.inclusion (U : SimplicialObject Scheme.{u}) :
    QCoh U ⥤ SheafOfModules.{u} (structureSheaf U) :=
  (quasiCoherentModuleProperty U).ι

/-- Pullback along a morphism of simplicial schemes preserves the quasi-coherent
module property. -/
theorem modulePullback_le_inverseImage {V U : SimplicialObject Scheme.{u}}
    (f : V ⟶ U) :
    quasiCoherentModuleProperty U ≤
      (quasiCoherentModuleProperty V).inverseImage (modulePullback f) := by
  intro M hM
  exact modulePullback_isQuasicoherent f M

end AlgebraicGeometry.SimplicialObject
