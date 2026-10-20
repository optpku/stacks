module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CompletionMap
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Subobject.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open RingedSite.Hom

universe u

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-- Restriction to a slice carries a derived completion map for a finite-type ideal sheaf
to a derived completion map for the restricted ideal sheaf. -/
theorem derivedCompletion_restrict
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (U : C) {K Khat : RingedSiteDerived J O} (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η) :
    IsDerivedCompletion.{u, u, u, u} (imageSubobject (I.arrow.over U) : Subobject (unitModule (J.over U) (O.over U)))
      ((localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).map η) := sorry

end RingedSite.Hom.ModuleDerived
