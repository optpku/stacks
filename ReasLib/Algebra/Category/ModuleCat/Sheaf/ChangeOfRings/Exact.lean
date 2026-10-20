module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Exactness of restriction of scalars for module sheaves -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w z

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R R' : Sheaf J RingCat.{w}}

/-- Restriction of scalars for module sheaves preserves finite limits. -/
instance restrictScalars_preservesFiniteLimits (α : R ⟶ R') :
    PreservesFiniteLimits (restrictScalars.{z} α) := sorry

/-- Restriction of scalars for module sheaves preserves finite colimits. -/
instance restrictScalars_preservesFiniteColimits (α : R ⟶ R') :
    PreservesFiniteColimits (restrictScalars.{z} α) := sorry

end SheafOfModules
