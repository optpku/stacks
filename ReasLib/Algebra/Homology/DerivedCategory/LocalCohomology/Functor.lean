/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- The local-cohomology functor is the composite of derived ideal-power torsion with
the comparison into the derived category of objects having ideal-power-torsion cohomology. -/
noncomputable abbrev functor (I : Ideal A) :
    DerivedCategory (ModuleCat A) ⥤
      DerivedCategory.CohomologyIn (ModuleCat.isIdealPowerTorsion I) :=
  ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
    CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I)

end CategoryTheory.DerivedCategory.LocalCohomology

end
