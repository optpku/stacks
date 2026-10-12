/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.FlatBaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Torsion

@[expose] public section

open CategoryTheory
open ModuleCat
open ModuleCat.IdealPower
open ModuleCat.IdealPower.DerivedBaseChange

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The restriction comparison is the mate of the local-cohomology counit under
the adjunction over the base ring. -/
noncomputable def restrictionComparison (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (RΓA : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓB : DerivedCategory (ModuleCat B) ⥤ IdealPowerTorsion (I.map f))
    (hA : IdealPowerTorsion.inclusion I ⊣ RΓA)
    (hB : IdealPowerTorsion.inclusion (I.map f) ⊣ RΓB) :
    RΓB ⋙ restriction f I ⟶ derivedRestrictionOfScalars f ⋙ RΓA where
  app M := hA.homEquiv _ _
    ((derivedRestrictionOfScalars f).map (hB.counit.app M))
  naturality := sorry

/-- The component of the restriction comparison is its defining adjoint
transpose. -/
theorem restrictionComparison_app (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (RΓA : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓB : DerivedCategory (ModuleCat B) ⥤ IdealPowerTorsion (I.map f))
    (hA : IdealPowerTorsion.inclusion I ⊣ RΓA)
    (hB : IdealPowerTorsion.inclusion (I.map f) ⊣ RΓB)
    (M : DerivedCategory (ModuleCat B)) :
    (restrictionComparison f I hI RΓA RΓB hA hB).app M =
      hA.homEquiv _ _
        ((derivedRestrictionOfScalars f).map (hB.counit.app M)) := sorry

/-- Restriction of scalars gives an invertible comparison of the two local-
cohomology right adjoints. -/
noncomputable instance restrictionComparisonIsIso (f : A →+* B) (I : Ideal A)
    (hI : I.FG)
    (RΓA : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓB : DerivedCategory (ModuleCat B) ⥤ IdealPowerTorsion (I.map f))
    (hA : IdealPowerTorsion.inclusion I ⊣ RΓA)
    (hB : IdealPowerTorsion.inclusion (I.map f) ⊣ RΓB) :
    IsIso (restrictionComparison f I hI RΓA RΓB hA hB) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
