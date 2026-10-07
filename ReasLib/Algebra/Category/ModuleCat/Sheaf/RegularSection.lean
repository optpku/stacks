module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf

@[expose] public section

open CategoryTheory

noncomputable section

universe v u₁ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- A section of a sheaf of modules is regular when the morphism from the unit sheaf
induced by that section is a monomorphism. -/
abbrev IsRegularSection (ℒ : SheafOfModules.{u} R) (s : ℒ.sections) : Prop :=
  Mono (ℒ.unitHomEquiv.symm s)

end SheafOfModules
