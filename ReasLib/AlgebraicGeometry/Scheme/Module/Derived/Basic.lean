module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Derived categories of modules on schemes

This file supplies the canonical derived-category instance for module sheaves on a scheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Scheme modules use the standard derived category attached to their abelian category. -/
@[stacks 07VK "canonical derived category of scheme modules"]
noncomputable instance schemeModulesHasDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory X.Modules :=
  HasDerivedCategory.standard X.Modules

end AlgebraicGeometry.Scheme.Modules
