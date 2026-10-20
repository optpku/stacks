module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ClosedSubset.SectionsWithSupport
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry SheafOfModules.ClosedSubset

noncomputable section

universe u

namespace AlgebraicGeometry

open SheafOfModules.ClosedSubset.SectionsWithSupport

variable {X : RingedSpace.{u}} (Z : Closeds X)
variable (G : SheafOfModules.ClosedSubset.Modules X.ringCatSheaf Z) (F : X.Modules)

/- Lemma 17.13.6 (0G6P): closed-subset pushforward is left adjoint to the functor of sections
supported on the closed subset. -/
@[stacks 0G6P]
#check (adjunction X.ringCatSheaf Z :
  SheafOfModules.ClosedSubset.pushforward X.ringCatSheaf Z ⊣ 𝓗[Z])

/- Lemma 17.13.6: the source Hom-set bijection is the Hom equivalence of the canonical
adjunction. -/
#check ((adjunction X.ringCatSheaf Z).homEquiv G F :
  ((SheafOfModules.ClosedSubset.pushforward X.ringCatSheaf Z).obj G ⟶ F) ≃
    (G ⟶ (𝓗[Z]).obj F))

#check ((adjunction X.ringCatSheaf Z).homEquiv G F).bijective

#check @SheafOfModules.ClosedSubset.SectionsWithSupport.inclusionPushforwardInv
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.inclusionPushforward_hom_inv_id
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.inclusionPushforward_inv_hom_id
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.inclusionPushforwardIso
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.pullbackPushforwardCounitAppInv
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.pullbackPushforwardCounitApp_hom_inv_id
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.pullbackPushforwardCounitApp_inv_hom_id
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.pullbackPushforwardCounitAppIso
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.objectPullbackPushforwardUnitAppInv
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.objectPullbackPushforwardUnitApp_hom_inv_id
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.objectPullbackPushforwardUnitApp_inv_hom_id
#check @SheafOfModules.ClosedSubset.SectionsWithSupport.objectPullbackPushforwardUnitAppIso

end AlgebraicGeometry
