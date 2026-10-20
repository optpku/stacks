module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StructureSheaf

@[expose] public section

universe u z

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The category of presheaves of modules over the structure sheaf of a category
fibred in groupoids over the big fppf site of a scheme. -/
abbrev PMod (X : GroupoidsOver S) :=
  PresheafOfModules.{z} (structureSheaf X).obj

/-- The category of fppf sheaves of modules over the structure sheaf of a
category fibred in groupoids over the big fppf site of a scheme. -/
abbrev Mod (X : GroupoidsOver S) :=
  SheafOfModules.{z} (structureSheaf X)

end AlgebraicGeometry.GroupoidsOver
