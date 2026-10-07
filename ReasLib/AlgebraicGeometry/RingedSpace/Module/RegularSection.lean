module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular sections of module sheaves on ringed spaces

This file owns the categorical regularity condition for a global section of a module sheaf on a
ringed space.  The condition is meaningful for every module sheaf; applications to invertible
module sheaves add invertibility at their own source-facing boundary.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The morphism from the structure module induced by a global section of a module sheaf. -/
abbrev regularSectionHom (ℒ : X.Modules) (s : ℒ.sections) :
    SheafOfModules.unit X.ringCatSheaf ⟶ ℒ :=
  ℒ.unitHomEquiv.symm s

/-- A global section of a module sheaf is regular when its induced morphism from the structure
module is a monomorphism. -/
@[stacks 01WY "categorical regularity of a global module-sheaf section"]
abbrev IsRegularSection (ℒ : X.Modules) (s : ℒ.sections) : Prop :=
  Mono (regularSectionHom ℒ s)

/-- A regular section is exactly a global section whose induced morphism from the structure
module is a monomorphism. -/
theorem isRegularSection_iff_mono (ℒ : X.Modules) (s : ℒ.sections) :
    IsRegularSection ℒ s ↔ Mono (regularSectionHom ℒ s) := sorry

end AlgebraicGeometry.RingedSpace
