module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.SheafCompleteness
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.SheafCompleteness.BoundedReduction

/-!
# Proposition 61.21.1

Derived completeness of sheaves of `Λ`-modules on a site with enough weakly
contractible objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite SheafOfModules.RingedSite.IdealSheaf
open RingedSite.Hom.ModuleDerived RingedSite.Hom.ModuleDerived.ConstantCompletion

noncomputable section

universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (I : Ideal Λ)

/- Proposition 61.21.1 (1): derived-complete sheaves form a weak Serre class. -/
@[stacks 099Q] #check
  (RingedSite.Hom.ModuleDerived.derivedCompleteSheaf_isWeakSerreClass J I :
    J.HasEnoughObjectsWithProperty J.IsWeaklyContractible →
      IsWeakSerreClass (derivedCompleteSheafProperty J I))

/- Proposition 61.21.1 (2): adic completeness is derived completeness and vanishing
of the intersection of the ideal-power submodules. -/
@[stacks 099Q] #check
  (RingedSite.Hom.ModuleDerived.isIso_toAdicLimit_iff J I :
    J.HasEnoughObjectsWithProperty J.IsWeaklyContractible →
      ∀ F : ringedSiteModuleCategory J (constantRingSheaf J Λ),
        IsIso (toAdicLimit J I F) ↔
          isDerivedCompleteSheaf J I F ∧ IsZero (kernel (toAdicLimit J I F)))

/- Proposition 61.21.1 (3): the completed constant unit sheaf is derived complete. -/
@[stacks 099Q] #check
  (RingedSite.Hom.ModuleDerived.completedUnitModule_isDerivedCompleteSheaf J I :
    J.HasEnoughObjectsWithProperty J.IsWeaklyContractible →
      isDerivedCompleteSheaf J I (completedUnitModule J I))

/- Proposition 61.21.1 (4): sequential inverse limits preserve derived completeness. -/
@[stacks 099Q] #check
  (RingedSite.Hom.ModuleDerived.limit_isDerivedCompleteSheaf J I :
    J.HasEnoughObjectsWithProperty J.IsWeaklyContractible →
      ∀ Fsys : SequentialInverseSystem
          (ringedSiteModuleCategory J (constantRingSheaf J Λ)),
        (∀ n, isDerivedCompleteSheaf J I (Fsys.obj (op n))) →
          isDerivedCompleteSheaf J I (limit Fsys))

/- Proposition 61.21.1 (5): derived completeness is detected on all cohomology sheaves. -/
@[stacks 099Q] #check
  (RingedSite.Hom.ModuleDerived.isDerivedComplete_iff_cohomologySheaf J I :
    J.HasEnoughObjectsWithProperty J.IsWeaklyContractible →
      ∀ K : RingedSiteDerived.{u, u, u, u} J (constantRingSheaf J Λ),
        IsDerivedCompleteWithRespectTo.{u, u, u, u} K (constantIdealSheaf J I) ↔
          DerivedCategory.cohomologyIn (derivedCompleteSheafProperty J I) K)

section BoundedReduction

attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
  RingedSite.Hom.RingPresentation.moduleHasDerivedCategory
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

variable [MonoidalCategory (RingedSiteDerived J (constantRingSheaf J Λ))]

/- Proposition 61.21.1 (6): reduction modulo the ideal detects boundedness above
for a derived-complete object. -/
@[stacks 099Q] #check
  (RingedSite.Hom.ModuleDerived.isBoundedAbove_iff_tensorQuotient_isBoundedAbove J I :
    J.HasEnoughObjectsWithProperty J.IsWeaklyContractible →
      ∀ K : RingedSiteDerived.{u, u, u, u} J (constantRingSheaf J Λ),
        IsDerivedCompleteWithRespectTo.{u, u, u, u} K (constantIdealSheaf J I) →
          (@DerivedCategory.IsBoundedAbove
            (ringedSiteModuleCategory J (constantRingSheaf J Λ)) _ _
            (moduleCategoryHasDerivedCategory (𝒪 := constantRingSheaf J Λ)) K ↔
            @DerivedCategory.IsBoundedAbove
              (ringedSiteModuleCategory J (constantRingSheaf J Λ)) _ _
              (moduleCategoryHasDerivedCategory (𝒪 := constantRingSheaf J Λ))
              (completionQuotientStage (constantIdealSheaf J I) K 1)))

/- Proposition 61.21.1 (7): finite Tor dimension of the reduction modulo the ideal
implies boundedness of a derived-complete object. -/
@[stacks 099Q] #check
  (RingedSite.Hom.ModuleDerived.isBounded_of_tensorQuotient_hasFiniteTorDimension J I :
    J.HasEnoughObjectsWithProperty J.IsWeaklyContractible →
      ∀ [DerivedCategory.DerivedTensor.Right.Has
        (C := ringedSiteModuleCategory.{u, u, u, u} J
          (PowerQuotient.sheaf (constantIdealSheaf J I) 1))]
        (K : RingedSiteDerived.{u, u, u, u} J (constantRingSheaf J Λ)),
        IsDerivedCompleteWithRespectTo.{u, u, u, u} K (constantIdealSheaf J I) →
          HasFiniteTorDimension
            (O := PowerQuotient.sheaf (constantIdealSheaf J I) 1)
            ((PowerQuotient.pullbackDerived (constantIdealSheaf J I) 1).obj K) →
              @DerivedCategory.IsBoundedAbove
                (ringedSiteModuleCategory J (constantRingSheaf J Λ)) _ _
                (moduleCategoryHasDerivedCategory (𝒪 := constantRingSheaf J Λ)) K ∧
                @DerivedCategory.IsBoundedBelow
                  (ringedSiteModuleCategory J (constantRingSheaf J Λ)) _ _
                  (moduleCategoryHasDerivedCategory (𝒪 := constantRingSheaf J Λ)) K)

end BoundedReduction
