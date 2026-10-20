/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RegularSection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular sections of module sheaves on ringed spaces

This file specializes the canonical module-sheaf regularity condition
`SheafOfModules.IsRegularSection` to the structure sheaf of a ringed space.  The condition is
meaningful for every module sheaf; applications to invertible module sheaves add invertibility at
their own source-facing boundary.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The morphism from the structure module induced by a global section of a module sheaf; the
ringed-space specialization of `SheafOfModules.regularSectionHom`. -/
abbrev regularSectionHom (ℒ : X.Modules) (s : ℒ.sections) :
    SheafOfModules.unit X.ringCatSheaf ⟶ ℒ :=
  SheafOfModules.regularSectionHom ℒ s

/-- A global section of a module sheaf is regular when its induced morphism from the structure
module is a monomorphism; the ringed-space specialization of `SheafOfModules.IsRegularSection`. -/
@[stacks 01WY "categorical regularity of a global module-sheaf section"]
abbrev IsRegularSection (ℒ : X.Modules) (s : ℒ.sections) : Prop :=
  SheafOfModules.IsRegularSection ℒ s

/-- A regular section is exactly a global section whose induced morphism from the structure
module is a monomorphism. -/
theorem isRegularSection_iff_mono (ℒ : X.Modules) (s : ℒ.sections) :
    IsRegularSection ℒ s ↔ Mono (regularSectionHom ℒ s) :=
  SheafOfModules.isRegularSection_iff_mono ℒ s

end AlgebraicGeometry.RingedSpace
