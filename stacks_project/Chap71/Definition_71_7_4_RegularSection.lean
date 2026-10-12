/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_29_1_RingedSite

/-!
# Regular sections of module sheaves on algebraic spaces

This file owns the categorical regularity condition for a global section of a module sheaf on
an algebraic space. The condition is meaningful for every module sheaf on the small étale site;
applications to invertible sheaves add invertibility at their own source-facing boundary.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The morphism `𝒪_X ⟶ ℒ` induced by a global section of a module sheaf, sending `f` to
`f * s`. -/
abbrev regularSectionHom (ℒ : X.Modules) (s : ℒ.sections) :
    SheafOfModules.unit (structureSheaf X) ⟶ ℒ :=
  ℒ.unitHomEquiv.symm s

/-- A global section of a module sheaf is regular when its induced morphism from the structure
sheaf is a monomorphism. -/
abbrev IsRegularSection (ℒ : X.Modules) (s : ℒ.sections) : Prop :=
  Mono (regularSectionHom ℒ s)

/-- The morphism induced by a global section recovers that section under `unitHomEquiv`. -/
theorem unitHomEquiv_regularSectionHom (ℒ : X.Modules) (s : ℒ.sections) :
    ℒ.unitHomEquiv (regularSectionHom ℒ s) = s :=
  sorry

/-- A regular section is exactly a global section whose induced morphism from the structure
sheaf is a monomorphism. -/
theorem isRegularSection_iff_mono (ℒ : X.Modules) (s : ℒ.sections) :
    IsRegularSection ℒ s ↔ Mono (regularSectionHom ℒ s) :=
  sorry

/-- The identity section of `𝒪_X` is regular. -/
instance instIsRegularSection_unit :
    IsRegularSection (SheafOfModules.unit (structureSheaf X) : X.Modules)
      ((SheafOfModules.unit (structureSheaf X)).unitHomEquiv (𝟙 _)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
