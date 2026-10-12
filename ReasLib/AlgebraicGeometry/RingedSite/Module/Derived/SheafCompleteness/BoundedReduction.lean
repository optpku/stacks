/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.SheafCompleteness
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.IdealPowerQuotient
public import ReasLib.CategoryTheory.DerivedCategory.Bounded

/-!
# Boundedness of derived-complete sheaves after reduction

Reduction modulo the coefficient ideal detects upper bounds, and finite Tor
dimension of the reduction gives boundedness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite SheafOfModules.RingedSite.IdealSheaf
open RingedSite.Hom.ModuleDerived.ConstantCompletion
open ComplexShape

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (I : Ideal Λ)
variable [MonoidalCategory (RingedSiteDerived J (constantRingSheaf J Λ))]

/-- Canonical cochain-tensor totalization for sheaves of constant `Λ`-modules. -/
@[reducible]
def hasMapBifunctor_constantRingSheaf
    (K L : CochainComplex
      (ringedSiteModuleCategory.{u, u, u, u} J (constantRingSheaf J Λ)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (ringedSiteModuleCategory.{u, u, u, u} J (constantRingSheaf J Λ)))
      (up ℤ) :=
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
    (constantRingSheaf J Λ) K L

/-- Canonical derived tensoring for sheaves of constant `Λ`-modules. -/
@[reducible]
def derivedTensor_constantRingSheaf :
    @DerivedCategory.DerivedTensor.Has
      (ringedSiteModuleCategory.{u, u, u, u} J (constantRingSheaf J Λ))
      _ _ (moduleCategoryHasDerivedCategory (𝒪 := constantRingSheaf J Λ)) _ _
      (hasMapBifunctor_constantRingSheaf J (Λ := Λ)) :=
  SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor (constantRingSheaf J Λ)

/-- Canonical cochain-tensor totalization for sheaves over the constant ideal quotient. -/
@[reducible]
def hasMapBifunctor_constantIdealPowerQuotient
    (K L : CochainComplex
      (ringedSiteModuleCategory.{u, u, u, u} J
        (PowerQuotient.sheaf (constantIdealSheaf J I) 1)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (ringedSiteModuleCategory.{u, u, u, u} J
          (PowerQuotient.sheaf (constantIdealSheaf J I) 1)))
      (up ℤ) :=
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
    (PowerQuotient.sheaf (constantIdealSheaf J I) 1) K L

/-- Canonical derived tensoring for sheaves over the constant ideal quotient. -/
@[reducible]
def derivedTensor_constantIdealPowerQuotient :
    @DerivedCategory.DerivedTensor.Has
      (ringedSiteModuleCategory.{u, u, u, u} J
        (PowerQuotient.sheaf (constantIdealSheaf J I) 1))
      _ _ (moduleCategoryHasDerivedCategory
        (𝒪 := PowerQuotient.sheaf (constantIdealSheaf J I) 1)) _ _
      (hasMapBifunctor_constantIdealPowerQuotient J I) :=
  SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor
    (PowerQuotient.sheaf (constantIdealSheaf J I) 1)

/-- A derived-complete object is bounded above exactly when its derived reduction
modulo the ideal is bounded above, on a site with enough weakly contractible objects. -/
theorem isBoundedAbove_iff_tensorQuotient_isBoundedAbove
    (hEnough : J.HasEnoughObjectsWithProperty J.IsWeaklyContractible)
    (K : RingedSiteDerived.{u, u, u, u} J (constantRingSheaf J Λ))
    (hK : IsDerivedCompleteWithRespectTo.{u, u, u, u} K
      (constantIdealSheaf J I)) :
    @DerivedCategory.IsBoundedAbove
      (ringedSiteModuleCategory J (constantRingSheaf J Λ)) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := constantRingSheaf J Λ)) K ↔
      @DerivedCategory.IsBoundedAbove
        (ringedSiteModuleCategory J (constantRingSheaf J Λ)) _ _
        (moduleCategoryHasDerivedCategory (𝒪 := constantRingSheaf J Λ))
        (completionQuotientStage (constantIdealSheaf J I) K 1) := sorry

/-- A derived-complete object is bounded when its reduction modulo the ideal has
finite Tor dimension, on a site with enough weakly contractible objects. -/
theorem isBounded_of_tensorQuotient_hasFiniteTorDimension
    (hEnough : J.HasEnoughObjectsWithProperty J.IsWeaklyContractible)
    (K : RingedSiteDerived.{u, u, u, u} J (constantRingSheaf J Λ))
    (hK : IsDerivedCompleteWithRespectTo.{u, u, u, u} K
      (constantIdealSheaf J I))
    (hTor : @HasFiniteTorDimension.{u, u, u}
      (PowerQuotient.ringedSite (constantIdealSheaf J I) 1) _ _ _
      (hasMapBifunctor_constantIdealPowerQuotient J I)
      (derivedTensor_constantIdealPowerQuotient J I).right
      ((PowerQuotient.pullbackDerived (constantIdealSheaf J I) 1).obj K)) :
    @DerivedCategory.IsBoundedAbove
      (ringedSiteModuleCategory J (constantRingSheaf J Λ)) _ _
      (moduleCategoryHasDerivedCategory (𝒪 := constantRingSheaf J Λ)) K ∧
      @DerivedCategory.IsBoundedBelow
        (ringedSiteModuleCategory J (constantRingSheaf J Λ)) _ _
        (moduleCategoryHasDerivedCategory (𝒪 := constantRingSheaf J Λ)) K := sorry

end RingedSite.Hom.ModuleDerived
