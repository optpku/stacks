module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completion
import StacksCheckRecall

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

/- Proposition 52.6.12: Let (C, O) be a ringed site. Let I ⊆ O be a finite-type
sheaf of ideals. There exists a left adjoint to the inclusion functor
D_comp(O) → D(O). -/
@[stacks 099F] #check
  (RingedSite.Hom.ModuleDerived.Completion.inclusionIsRightAdjoint.{u, u, u} :
    ∀ (I : Subobject (unitModule J O))
      [hI : (I : ringedSiteModuleCategory J O).IsFiniteType],
      (derivedCompleteObjectProperty.{u, u, u, u} I).ι.IsRightAdjoint)

end RingedSite.Hom.ModuleDerived
