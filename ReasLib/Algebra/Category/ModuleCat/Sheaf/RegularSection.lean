module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Regular sections of sheaves of modules

This file is the canonical owner of the categorical regularity condition for a global section of
a sheaf of modules over an arbitrary sheaf of rings on a site: the section `s` of `ℒ` is regular
when the induced morphism `𝒪 ⟶ ℒ`, `f ↦ f * s`, is a monomorphism.  Ringed-space and
algebraic-space specializations (`AlgebraicGeometry.RingedSpace.IsRegularSection`,
`AlgebraicGeometry.AlgebraicSpace.IsRegularSection`) are thin abbreviations of this owner.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- The morphism from the unit sheaf of modules induced by a global section, sending a local
function `f` to `f * s`. -/
abbrev regularSectionHom (ℒ : SheafOfModules.{u} R) (s : ℒ.sections) :
    SheafOfModules.unit R ⟶ ℒ :=
  ℒ.unitHomEquiv.symm s

/-- A section of a sheaf of modules is regular when the morphism from the unit sheaf
induced by that section is a monomorphism. -/
abbrev IsRegularSection (ℒ : SheafOfModules.{u} R) (s : ℒ.sections) : Prop :=
  Mono (regularSectionHom ℒ s)

/-- The morphism induced by a global section recovers that section under `unitHomEquiv`. -/
@[simp]
theorem unitHomEquiv_regularSectionHom (ℒ : SheafOfModules.{u} R) (s : ℒ.sections) :
    ℒ.unitHomEquiv (regularSectionHom ℒ s) = s :=
  ℒ.unitHomEquiv.apply_symm_apply s

/-- A regular section is exactly a global section whose induced morphism from the unit sheaf is
a monomorphism. -/
theorem isRegularSection_iff_mono (ℒ : SheafOfModules.{u} R) (s : ℒ.sections) :
    IsRegularSection ℒ s ↔ Mono (regularSectionHom ℒ s) :=
  Iff.rfl

/-- The identity section of the unit sheaf of modules is regular. -/
instance isRegularSection_unit :
    IsRegularSection (SheafOfModules.unit R)
      ((SheafOfModules.unit R).unitHomEquiv (𝟙 _)) := by
  simp only [IsRegularSection, regularSectionHom, Equiv.symm_apply_apply]
  infer_instance

end SheafOfModules
