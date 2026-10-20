module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RegularSection

/-!
# Regular sections of module sheaves on algebraic spaces

This file specializes the canonical module-sheaf regularity condition
`SheafOfModules.IsRegularSection` to the small étale site of an algebraic space. The condition
is meaningful for every module sheaf on the small étale site;
applications to invertible sheaves add invertibility at their own source-facing boundary.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The morphism `𝒪_X ⟶ ℒ` induced by a global section of a module sheaf, sending `f` to
`f * s`; the algebraic-space specialization of `SheafOfModules.regularSectionHom`. -/
abbrev regularSectionHom (ℒ : X.Modules) (s : ℒ.sections) :
    SheafOfModules.unit (structureSheaf X) ⟶ ℒ :=
  SheafOfModules.regularSectionHom ℒ s

/-- A global section of a module sheaf is regular when its induced morphism from the structure
sheaf is a monomorphism; the algebraic-space specialization of
`SheafOfModules.IsRegularSection`. -/
abbrev IsRegularSection (ℒ : X.Modules) (s : ℒ.sections) : Prop :=
  SheafOfModules.IsRegularSection ℒ s

/-- The morphism induced by a global section recovers that section under `unitHomEquiv`. -/
theorem unitHomEquiv_regularSectionHom (ℒ : X.Modules) (s : ℒ.sections) :
    ℒ.unitHomEquiv (regularSectionHom ℒ s) = s :=
  SheafOfModules.unitHomEquiv_regularSectionHom ℒ s

/-- A regular section is exactly a global section whose induced morphism from the structure
sheaf is a monomorphism. -/
theorem isRegularSection_iff_mono (ℒ : X.Modules) (s : ℒ.sections) :
    IsRegularSection ℒ s ↔ Mono (regularSectionHom ℒ s) :=
  SheafOfModules.isRegularSection_iff_mono ℒ s

/-- The identity section of `𝒪_X` is regular. -/
instance instIsRegularSection_unit :
    IsRegularSection (SheafOfModules.unit (structureSheaf X) : X.Modules)
      ((SheafOfModules.unit (structureSheaf X)).unitHomEquiv (𝟙 _)) :=
  SheafOfModules.isRegularSection_unit

end AlgebraicGeometry.AlgebraicSpace
