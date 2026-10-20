module

public import ReasLib.Algebra.Module.IdealPower.Serre
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

/-!
# Derived Objects with Ideal-Power-Torsion Cohomology

This module defines the full subcategory of derived modules whose cohomology is power torsion
for a fixed ideal, together with its inclusion into the ambient derived category.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.DerivedCategory

variable {A : Type u} [CommRing A]

/-- The full subcategory of derived `A`-modules whose cohomology modules are
`I`-power torsion. -/
abbrev IdealPowerTorsion (I : Ideal A) :=
  CohomologyIn (ModuleCat.isIdealPowerTorsion I)

namespace IdealPowerTorsion

/-- The inclusion of derived `A`-modules with `I`-power-torsion cohomology into
the ambient derived category. -/
abbrev inclusion (I : Ideal A) :
    IdealPowerTorsion I ⥤ DerivedCategory (ModuleCat A) :=
  (cohomologyIn (ModuleCat.isIdealPowerTorsion I)).ι

end IdealPowerTorsion

end CategoryTheory.DerivedCategory
