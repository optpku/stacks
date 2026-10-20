module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CompletedTensor
import StacksCheckRecall

@[expose] public section

open CategoryTheory SheafOfModules.RingedSite

noncomputable section

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

/- Remark 52.6.15 (Completed tensor product): completing the derived tensor defines a
bifunctor on derived-complete modules, with derived sheaf internal Hom as its right adjoint. -/
@[stacks 099G] #check (RingedSite.Hom.ModuleDerived.completedTensorProductHomEquiv :
  ∀ (I : Subobject (unitModule J O))
    [hI : (I : ringedSiteModuleCategory J O).IsFiniteType]
    (K L M : DerivedCompleteCategory I),
    (K ⟶ completedInternalHom I L M) ≃ (completedTensorProduct I K L ⟶ M))

#check (RingedSite.Hom.ModuleDerived.completedTensorProductFunctor :
  ∀ (I : Subobject (unitModule J O))
    [hI : (I : ringedSiteModuleCategory J O).IsFiniteType],
    DerivedCompleteCategory I × DerivedCompleteCategory I ⥤ DerivedCompleteCategory I)

#check (RingedSite.Hom.ModuleDerived.completedTensorProductFunctor_obj :
  ∀ (I : Subobject (unitModule J O))
    [hI : (I : ringedSiteModuleCategory J O).IsFiniteType]
    (K L : DerivedCompleteCategory I),
    (completedTensorProductFunctor I).obj (K, L) = completedTensorProduct I K L)

#check (RingedSite.Hom.ModuleDerived.completedInternalHom_obj :
  ∀ (I : Subobject (unitModule J O)) (L M : DerivedCompleteCategory I),
    (completedInternalHom I L M).obj = InternalHom.obj L.obj M.obj)

end RingedSite.Hom.ModuleDerived
