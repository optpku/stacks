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

/-- The counit from derived ideal-power torsion, after the canonical comparison with
the subcategory of derived modules having ideal-power-torsion cohomology. -/
noncomputable def idealTorsionCounit (I : Ideal A) :
    ((ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
        CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I)) ⋙
      IdealPowerTorsion.inclusion I) ⟶ 𝟭 (DerivedCategory (ModuleCat A)) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (ModuleCat.IdealPowerTorsion.derivedTorsion I)
      (CohomologyIn.Comparison.compιIso (ModuleCat.isIdealPowerTorsion I)).hom ≫
    (ModuleCat.IdealPowerTorsion.derivedAdjunction I).counit

/-- The natural comparison from derived ideal-power torsion to a chosen right adjoint
for the closed-support subcategory. -/
noncomputable def idealToClosedSupport (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) :
    ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
        CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I) ⟶ RΓZ where
  app K := hRΓZ.homEquiv _ _ ((idealTorsionCounit I).app K)
  naturality := sorry

/-- The comparison from derived ideal torsion to closed-support local cohomology
is characterized by factoring the derived ideal-torsion counit through the adjunction counit. -/
theorem idealToClosedSupport_fac (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) :
    Functor.whiskerRight (idealToClosedSupport I hI RΓZ hRΓZ)
        (IdealPowerTorsion.inclusion I) ≫ hRΓZ.counit = idealTorsionCounit I := sorry

variable [IsNoetherianRing A]

/-- The counit of derived ideal-power torsion is an isomorphism on every
object whose cohomology is ideal-power torsion over a Noetherian ring. -/
noncomputable instance idealTorsionCounitAppIsIso (I : Ideal A)
    (K : IdealPowerTorsion I) :
    IsIso ((idealTorsionCounit I).app K.obj) := sorry

/-- The comparison from the derived category of ideal-power-torsion modules
to derived objects with ideal-power-torsion cohomology is an equivalence. -/
noncomputable instance idealPowerTorsionDerivedComparisonIsEquivalence
    (I : Ideal A) :
    (CohomologyIn.Comparison.functor
      (ModuleCat.isIdealPowerTorsion I : ObjectProperty (ModuleCat A))).IsEquivalence := sorry

/-- The comparison from derived ideal torsion to a chosen right adjoint for
closed-support local cohomology is an isomorphism over a Noetherian ring. -/
noncomputable instance idealToClosedSupportIsIso (I : Ideal A)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) :
    IsIso (idealToClosedSupport I (Ideal.fg_of_isNoetherianRing I) RΓZ hRΓZ) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
