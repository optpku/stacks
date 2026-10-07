module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.BaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion.Comparison

@[expose] public section

open CategoryTheory
open DerivedCategory.CechCompletion
open CategoryTheory.DerivedCategory.LocalCohomology.BaseChange

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A B : Type u} [CommRing A] [CommRing B]
  [IsNoetherianRing A] [IsNoetherianRing B]

/-- The scalar extension of the ideal-power to closed-support comparison is an
isomorphism on the regular object. -/
@[instance]
noncomputable instance regularIdealToClosedSupportBaseChangeIsIso
    (f : A →+* B) (I : Ideal A)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ) :
    IsIso
      ((ModuleCat.derivedExtensionOfScalars f).map
        ((IdealPowerTorsion.inclusion I).map
          ((idealToClosedSupport I (Ideal.fg_of_isNoetherianRing I) RΓZ hRΓZ).app
            regular))) := sorry

/-- The target torsion-subcategory component of the local-cohomology base-change
comparison is an isomorphism on the regular object. -/
@[instance]
noncomputable instance regularClosedSupportBaseChangeIsIso
    (f : A →+* B) (I : Ideal A)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓY : DerivedCategory (ModuleCat B) ⥤ IdealPowerTorsion (I.map f))
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (hRΓY : IdealPowerTorsion.inclusion (I.map f) ⊣ RΓY) :
    IsIso
      ((IdealPowerTorsion.inclusion (I.map f)).map
        ((comparison f I (Ideal.fg_of_isNoetherianRing I) RΓZ RΓY hRΓZ hRΓY).app
          regular)) := sorry

/-- The ideal-power to closed-support comparison over the target is an isomorphism
on the scalar extension of the regular source object. -/
@[instance]
noncomputable instance regularIdealToClosedSupportOverTargetIsIso
    (f : A →+* B) (I : Ideal A)
    (RΓY : DerivedCategory (ModuleCat B) ⥤ IdealPowerTorsion (I.map f))
    (hRΓY : IdealPowerTorsion.inclusion (I.map f) ⊣ RΓY) :
    IsIso
      ((IdealPowerTorsion.inclusion (I.map f)).map
        ((idealToClosedSupport (I.map f)
          (Ideal.fg_of_isNoetherianRing (I.map f)) RΓY hRΓY).app
            ((ModuleCat.derivedExtensionOfScalars f).obj regular))) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
