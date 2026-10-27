/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.CocontinuousPushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open RingedSite.Hom

noncomputable section

universe u z

namespace RingedSite.Cocontinuous

/-- A site whose object universe is bounded by the coefficient universe is locally small there. -/
private instance siteLocallySmall {C : Type (u + 1)} [Category.{u} C]
    [UnivLE.{u + 1, z}] : LocallySmall.{z} C :=
  ⟨fun U V ↦ @Small.trans_univLE.{u + 1, z, u} (U ⟶ V) inferInstance inferInstance⟩

/-- Comma categories over a small model of a site admit limits of additive groups. -/
private instance smallModelCommaLimits {C : Type (u + 1)} [Category.{u} C]
    [UnivLE.{u + 1, z}] (V : Cᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (equivSmallModel.{z} C).inverse.op)
      AddCommGrpCat.{z} :=
  HasLimitsOfShape.of_small _ _

/-- On an essentially small site, sheafification inverts exactly the locally bijective maps. -/
private instance locallyBijective {C : Type (u + 1)} [Category.{u} C]
    [UnivLE.{u + 1, z}] (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

variable [UnivLE.{u + 1, z}]

variable {C' D' : Type (u + 1)} [Category.{u} C'] [Category.{u} D']
variable (J' : GrothendieckTopology C') (K' : GrothendieckTopology D')
variable (f : C' ⥤ D') [f.IsContinuous J' K'] [f.IsCocontinuous J' K']
variable (R : Sheaf J' RingCat.{u}) (S : Sheaf K' RingCat.{u})
variable (α : R ⟶ (f.sheafPushforwardContinuous RingCat.{u} J' K').obj S)
variable [h_coeff : IsIso α]
variable [HasSheafify J' AddCommGrpCat.{z}] [HasSheafify K' AddCommGrpCat.{z}]
variable [∀ P : C'ᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasPointwiseRightKanExtension P]
variable [(f.sheafPushforwardContinuous AddCommGrpCat.{z} J' K').Additive]
variable [(f.sheafPushforwardCocontinuous AddCommGrpCat.{z} J' K').Additive]
variable [PreservesFiniteLimits (SheafOfModules.pushforward.{z} α)]
variable [PreservesFiniteColimits (SheafOfModules.pushforward.{z} α)]

/-- Homotopy-to-derived presentation of cocontinuous module pushforward. -/
abbrev modulePushforward.toDerived :
    ModuleHomotopy.{z} (RingedSite.ofRingSheaf J' R) ⥤
      ModuleDerived.{z} (RingedSite.ofRingSheaf K' S) :=
  (modulePushforward J' K' f R S α).mapHomotopyCategory (up ℤ) ⋙
    moduleLocalization (RingedSite.ofRingSheaf K' S)

/-- Homotopy-to-derived presentation of coefficient module inverse image. -/
abbrev modulePushforward.coefficientInverseImageToDerived :
    ModuleHomotopy.{z} (RingedSite.ofRingSheaf K' S) ⥤
      ModuleDerived.{z} (RingedSite.ofRingSheaf J' R) :=
  (SheafOfModules.pushforward.{z} α).mapHomotopyCategory (up ℤ) ⋙
    moduleLocalization (RingedSite.ofRingSheaf J' R)

/-- Existence of the total right-derived functor of cocontinuous module
pushforward. -/
instance modulePushforward.toDerived.hasRightDerived :
    Functor.HasRightDerivedFunctor
      (modulePushforward.toDerived J' K' f R S α)
      (ModuleQis.{z} (RingedSite.ofRingSheaf J' R)) :=
  Functor.RightDerived.KInjective.hasDerived (modulePushforward J' K' f R S α)

/-- Exact derived coefficient inverse image is a left-derived functor of its
homotopy presentation. -/
instance modulePushforward.inverseImageIsLeftDerived :
    ((ExactFunctor.of (SheafOfModules.pushforward.{z} α)).mapDerivedCategory).IsLeftDerivedFunctor
      (ExactFunctor.of (SheafOfModules.pushforward.{z} α)).obj.mapDerivedCategoryFactorsh.hom
      (ModuleQis.{z} (RingedSite.ofRingSheaf K' S)) :=
  sorry

/-- Existence of the total left-derived functor of coefficient module inverse
image. -/
instance modulePushforward.coefficientInverseImageToDerived.hasLeftDerived :
    Functor.HasLeftDerivedFunctor
      (modulePushforward.coefficientInverseImageToDerived J' K' f R S α)
      (ModuleQis.{z} (RingedSite.ofRingSheaf K' S)) :=
  Functor.HasLeftDerivedFunctor.mk'
    (ExactFunctor.of (SheafOfModules.pushforward.{z} α)).mapDerivedCategory
    (ExactFunctor.of (SheafOfModules.pushforward.{z} α)).obj.mapDerivedCategoryFactorsh.hom

/-- The homotopy module inverse-image/pushforward adjunction descends to derived
categories. -/
instance modulePushforward.derived.hasPair :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := (SheafOfModules.pushforward.{z} α).mapHomotopyCategory (up ℤ))
      (F := (modulePushforward J' K' f R S α).mapHomotopyCategory
        (up ℤ))
      (ModuleQis.{z} (RingedSite.ofRingSheaf K' S))
      (ModuleQis.{z} (RingedSite.ofRingSheaf J' R))
      (L1 := moduleLocalization (RingedSite.ofRingSheaf K' S))
      (L2 := moduleLocalization (RingedSite.ofRingSheaf J' R)) :=
  sorry

/-- Total right-derived module pushforward. -/
abbrev modulePushforward.derived :
    ModuleDerived.{z} (RingedSite.ofRingSheaf J' R) ⥤
      ModuleDerived.{z} (RingedSite.ofRingSheaf K' S) :=
  Functor.totalRightDerived
    (modulePushforward.toDerived J' K' f R S α)
    (moduleLocalization (RingedSite.ofRingSheaf J' R))
    (ModuleQis.{z} (RingedSite.ofRingSheaf J' R))

/-- The total-derived module inverse-image/pushforward adjunction. -/
def modulePushforward.derived.totalAdjunction :
    Functor.totalLeftDerived
        (modulePushforward.coefficientInverseImageToDerived J' K' f R S α)
        (moduleLocalization (RingedSite.ofRingSheaf K' S))
        (ModuleQis.{z} (RingedSite.ofRingSheaf K' S)) ⊣
      modulePushforward.derived J' K' f R S α :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      (modulePushforward.adjunction J' K' f R S α))
    (ModuleQis.{z} (RingedSite.ofRingSheaf K' S))
    (ModuleQis.{z} (RingedSite.ofRingSheaf J' R))

/-- The total left-derived coefficient inverse image agrees with the exact
derived inverse image. -/
def modulePushforward.inverseImageTotalDerivedIso :
    Functor.totalLeftDerived
        (modulePushforward.coefficientInverseImageToDerived J' K' f R S α)
        (moduleLocalization (RingedSite.ofRingSheaf K' S))
        (ModuleQis.{z} (RingedSite.ofRingSheaf K' S)) ≅
      (ExactFunctor.of (SheafOfModules.pushforward.{z} α)).mapDerivedCategory :=
  Functor.leftDerivedNatIso
    (Functor.totalLeftDerived
      (modulePushforward.coefficientInverseImageToDerived J' K' f R S α)
      (moduleLocalization (RingedSite.ofRingSheaf K' S))
      (ModuleQis.{z} (RingedSite.ofRingSheaf K' S)))
    ((ExactFunctor.of (SheafOfModules.pushforward.{z} α)).mapDerivedCategory)
    ((modulePushforward.coefficientInverseImageToDerived J' K' f R S α).totalLeftDerivedCounit
      (moduleLocalization (RingedSite.ofRingSheaf K' S))
      (ModuleQis.{z} (RingedSite.ofRingSheaf K' S)))
    (ExactFunctor.of (SheafOfModules.pushforward.{z} α)).obj.mapDerivedCategoryFactorsh.hom
    (ModuleQis.{z} (RingedSite.ofRingSheaf K' S))
    (Iso.refl _)

/-- Derived coefficient inverse image is left adjoint to total right-derived
module pushforward. -/
def modulePushforward.derived.adjunction :
    (ExactFunctor.of (SheafOfModules.pushforward.{z} α)).mapDerivedCategory ⊣
      modulePushforward.derived J' K' f R S α :=
  (modulePushforward.derived.totalAdjunction J' K' f R S α).ofNatIsoLeft
    (modulePushforward.inverseImageTotalDerivedIso J' K' f R S α)

end RingedSite.Cocontinuous
