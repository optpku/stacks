module

public import stacks_project.Chap52.Lemma_52_6_8
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completion.Localization
import StacksCheckRecall

public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open RingedSite.Hom RingedSite.Hom.ModuleDerived

universe u

/- Remark 52.6.14 (Localization and derived completion): restriction to a slice preserves
derived completion maps for a finite-type ideal sheaf. -/
@[stacks 0A0F] #check
  (RingedSite.Hom.ModuleDerived.derivedCompletion_restrict :
    ∀ {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
      [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
      [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
      [HasWeakSheafify J AddCommGrpCat.{u}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      [HasWeakSheafify J CommRingCat.{u}]
      [J.WEqualsLocallyBijective CommRingCat.{u}]
      {O : Sheaf J CommRingCat.{u}}
      (I : Subobject (unitModule J O))
      [(I : ringedSiteModuleCategory J O).IsFiniteType]
      (U : C) {K Khat : RingedSiteDerived J O} (η : K ⟶ Khat),
      IsDerivedCompletion.{u, u, u, u} I η →
        IsDerivedCompletion.{u, u, u, u}
          (imageSubobject (I.arrow.over U) : Subobject (unitModule (J.over U) (O.over U)))
          ((localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).map η))

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

variable (I : Subobject (unitModule J O))
variable [(I : ringedSiteModuleCategory J O).IsFiniteType]
variable (U : C) {K Khat : RingedSiteDerived J O} (η : K ⟶ Khat)
variable (hη : IsDerivedCompletion.{u, u, u, u} I η)
variable {L : RingedSiteDerived (J.over U) (O.over U)}
variable (ηU : (localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).obj K ⟶ L)
variable (hηU : IsDerivedCompletion.{u, u, u, u}
  (imageSubobject (I.arrow.over U) : Subobject (unitModule (J.over U) (O.over U))) ηU)

-- The canonical comparison goes from the local completion to the restricted global completion.
#check
  (IsDerivedCompletion.comparisonIso
    (imageSubobject (I.arrow.over U) : Subobject (unitModule (J.over U) (O.over U)))
    hηU (derivedCompletion_restrict I U η hη) :
    L ≅ (localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).obj Khat)

-- The canonical comparison factors the restricted global completion map.
#check
  (IsDerivedCompletion.comparison_fac
    (imageSubobject (I.arrow.over U) : Subobject (unitModule (J.over U) (O.over U)))
    hηU (derivedCompletion_restrict I U η hη) :
    ηU ≫ (IsDerivedCompletion.comparisonIso
      (imageSubobject (I.arrow.over U) : Subobject (unitModule (J.over U) (O.over U)))
      hηU (derivedCompletion_restrict I U η hη)).hom =
        (localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).map η)
