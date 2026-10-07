module

public import stacks_project.Chap52.Lemma_52_6_8
public import Mathlib.CategoryTheory.Subobject.Limits

public section

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open RingedSite.Hom RingedSite.Hom.ModuleDerived

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-- Remark 52.6.14 (Localization and derived completion) (1): restriction of a derived completion map to a slice is a derived completion map for the restricted ideal. -/
@[stacks 0A0F]
theorem derivedCompletion_restrict
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (U : C) {K Khat : RingedSiteDerived J O} (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η) :
    IsDerivedCompletion.{u, u, u, u} (imageSubobject (I.arrow.over U) : Subobject (unitModule (J.over U) (O.over U)))
      ((localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).map η) := sorry

/-- Remark 52.6.14 (Localization and derived completion) (2): the canonical comparison isomorphism from a local completion target to the restricted global completion target. -/
@[stacks 0A0F]
noncomputable def derivedCompletionRestrictionIso
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (U : C) {K Khat : RingedSiteDerived J O} (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η)
    {L : RingedSiteDerived (J.over U) (O.over U)}
    (ηU : (localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).obj K ⟶ L)
    (hηU : IsDerivedCompletion.{u, u, u, u} (imageSubobject (I.arrow.over U) : Subobject (unitModule (J.over U) (O.over U))) ηU) :
    L ≅ (localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).obj Khat :=
  asIso (IsDerivedCompletion.comparison (imageSubobject (I.arrow.over U) : Subobject (unitModule (J.over U) (O.over U))) hηU
    (derivedCompletion_restrict I U η hη))

/-- The comparison isomorphism factors restriction of the global completion map through the local completion map. -/
theorem derivedCompletionRestrictionIso_hom
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (U : C) {K Khat : RingedSiteDerived J O} (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η)
    {L : RingedSiteDerived (J.over U) (O.over U)}
    (ηU : (localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).obj K ⟶ L)
    (hηU : IsDerivedCompletion.{u, u, u, u} (imageSubobject (I.arrow.over U) : Subobject (unitModule (J.over U) (O.over U))) ηU) :
    ηU ≫ (derivedCompletionRestrictionIso I U η hη ηU hηU).hom =
      (localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).map η := sorry
