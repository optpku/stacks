/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension

@[expose] public section

/-!
# Local finite Tor dimension on ringed sites

This module applies the canonical derived-tensor Tor-dimension predicate after restriction to
localized ringed sites and packages the resulting covering-local condition as an object property.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived localizedRestriction localizedRestrictionDerived)

noncomputable section

-- Local instance justification (defeq pin): use the existing canonical module-category derived structure on localized ringed sites.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
  RingedSite.Hom.RingPresentation.moduleHasDerivedCategory
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

universe u v w

namespace RingedSite.Hom.ModuleDerived

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]


-- Local instance justification (defeq pin): fix the localized module derived structure to the existing canonical owner.
local instance localizedHasDerivedCategory (U : (RingedSite.ofCommRingSheaf J O)) :
    HasDerivedCategory (ModuleCat.{w} ((RingedSite.ofCommRingSheaf J O).localization U)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory ((RingedSite.ofCommRingSheaf J O).localization U)
variable [∀ U : C,
  (J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, DerivedCategory.DerivedTensor.Right.Has
  (C := SheafOfModules.RingedSite.ringedSiteModuleCategory.{max u v, v, w, w}
    (J.over U) (O.over U))]
variable [∀ U : (RingedSite.ofCommRingSheaf J O), PreservesFiniteLimits (localizedRestriction.{w} (RingedSite.ofCommRingSheaf J O) U)]
variable [∀ U : (RingedSite.ofCommRingSheaf J O), PreservesFiniteColimits (localizedRestriction.{w} (RingedSite.ofCommRingSheaf J O) U)]

/-- The object property of having finite Tor dimension locally on a covering of every object of
the underlying site. -/
@[stacks 08FZ "(3), ringed-site object property"]
def locallyFiniteTorDimension : ObjectProperty (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :=
  fun E ↦ ∀ U : (RingedSite.ofCommRingSheaf J O), ∃ T : (RingedSite.ofCommRingSheaf J O).siteTopology.Cover U, ∀ I : T.Arrow,
    HasFiniteTorDimension (O := O.over I.Y) ((localizedRestrictionDerived.{w} (RingedSite.ofCommRingSheaf J O) I.Y).obj E)

/-- Definition 21.46.1 (3): `E` locally has finite Tor dimension when every object of the site
has a covering on whose members the restriction of `E` has finite Tor dimension. -/
@[stacks 08FZ "(3)"]
abbrev LocallyHasFiniteTorDimension (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) : Prop :=
  locallyFiniteTorDimension E

/-- A locally finite-Tor-dimension object supplies a finite-Tor-dimension cover over every
object of the site. -/
theorem LocallyHasFiniteTorDimension.exists_cover
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} (hE : LocallyHasFiniteTorDimension E) (U : (RingedSite.ofCommRingSheaf J O)) :
    ∃ T : (RingedSite.ofCommRingSheaf J O).siteTopology.Cover U, ∀ I : T.Arrow,
      HasFiniteTorDimension (O := O.over I.Y) ((localizedRestrictionDerived.{w} (RingedSite.ofCommRingSheaf J O) I.Y).obj E) := sorry

end

end RingedSite.Hom.ModuleDerived
