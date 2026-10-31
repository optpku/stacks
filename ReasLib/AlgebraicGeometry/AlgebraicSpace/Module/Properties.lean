/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Sheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeRestriction
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The canonical site-level quasicoherence predicate for a small étale module. -/
abbrev IsQuasicoherent (F : Modules X) : Prop :=
  SheafOfModules.isQuasicoherent (structureSheaf X) F

/-- The canonical site-level finite-type predicate for a small étale module. -/
abbrev IsFiniteType (F : Modules X) : Prop :=
  SheafOfModules.IsFiniteType (M := (F : SheafOfModules (structureSheaf X)))

/-- The canonical site-level finite-presentation predicate for a small étale module. -/
abbrev IsFinitePresentation (F : Modules X) : Prop :=
  SheafOfModules.IsFinitePresentation (M := (F : SheafOfModules (structureSheaf X)))

/-- Quasicoherence of a small étale module is tested on every étale scheme chart. -/
theorem isQuasicoherent_iff_forall_chart (F : Modules X) :
    IsQuasicoherent F ↔
      ∀ U : site X, SheafOfModules.IsQuasicoherent.{u} ((toScheme U).obj F) := sorry

/-- Finite type of a small étale module is tested on every étale scheme chart. -/
theorem isFiniteType_iff_forall_chart (F : Modules X) :
    IsFiniteType F ↔
      ∀ U : site X, SheafOfModules.IsFiniteType.{u} ((toScheme U).obj F) := sorry

/-- Finite presentation of a small étale module is tested on every étale scheme chart. -/
theorem isFinitePresentation_iff_forall_chart (F : Modules X) :
    IsFinitePresentation F ↔
      ∀ U : site X, SheafOfModules.IsFinitePresentation.{u} ((toScheme U).obj F) := sorry

theorem isQuasicoherent_iff (F : Modules X) :
    IsQuasicoherent F ↔
      ∀ U : site X, SheafOfModules.IsQuasicoherent.{u} ((toScheme U).obj F) :=
  isQuasicoherent_iff_forall_chart F

theorem isFiniteType_iff (F : Modules X) :
    IsFiniteType F ↔
      ∀ U : site X, SheafOfModules.IsFiniteType.{u} ((toScheme U).obj F) :=
  isFiniteType_iff_forall_chart F

theorem isFinitePresentation_iff (F : Modules X) :
    IsFinitePresentation F ↔
      ∀ U : site X, SheafOfModules.IsFinitePresentation.{u} ((toScheme U).obj F) :=
  isFinitePresentation_iff_forall_chart F

/-- The compatibility name is the canonical site-level quasicoherence predicate. -/
theorem isQuasicoherent_iff_site (F : Modules X) :
    IsQuasicoherent F ↔ SheafOfModules.IsQuasicoherent F := Iff.rfl

/-- The compatibility name is the canonical site-level finite-type predicate. -/
theorem isFiniteType_iff_site (F : Modules X) :
    IsFiniteType F ↔ SheafOfModules.IsFiniteType F := Iff.rfl

/-- The compatibility name is the canonical site-level finite-presentation predicate. -/
theorem isFinitePresentation_iff_site (F : Modules X) :
    IsFinitePresentation F ↔ SheafOfModules.IsFinitePresentation F := Iff.rfl


end AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules
