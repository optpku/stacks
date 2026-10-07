module

public import stacks_project.Chap52.Lemma_52_6_8

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

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

/-- Proposition 52.6.12: for a finite-type ideal sheaf, the inclusion of the
derived-complete objects into the derived category admits a left adjoint. -/
@[stacks 099F]
instance derivedCompleteInclusionIsRightAdjoint
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType] :
    (derivedCompleteObjectProperty I).ι.IsRightAdjoint := sorry

end RingedSite.Hom.ModuleDerived
