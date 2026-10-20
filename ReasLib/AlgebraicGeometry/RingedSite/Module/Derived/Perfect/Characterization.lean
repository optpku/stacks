/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.Local

@[expose] public section

/-!
# Perfectness criteria for derived module sheaves

This module collects intrinsic criteria relating perfectness, pseudo-coherence, and Tor
amplitude for derived module sheaves with the canonical tensor product over the supplied commutative structure sheaf.
-/

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
  RingedSite.Hom.RingPresentation.moduleHasDerivedCategory
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite.Hom (ModuleDerived localizedRestriction)

noncomputable section

universe u v w

set_option checkBinderAnnotations false

namespace RingedSite.Hom.ModuleDerived

section TorAmplitudeCriterion

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable [∀ U : C,
  (J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ U : (RingedSite.ofCommRingSheaf J O),
  HasWeakSheafify ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : (RingedSite.ofCommRingSheaf J O),
  ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))]

/-- Lemma 21.47.3: an object of `D(𝒪_X)` with Tor-amplitude in `[a, b]` that is
`(a - 1)`-pseudo-coherent is perfect. -/
@[stacks 08G7]
theorem isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) (a b : ℤ)
    (hE : HasTorAmplitudeIn E a b)
    (hpc : E.IsMPseudoCoherent (a - 1)) :
    E.IsPerfect := sorry

end TorAmplitudeCriterion

section Characterization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]


-- The slice premises below use the standard model already fixed by the Tor-dimension owner.
attribute [local instance] localizedHasDerivedCategory

variable [∀ U : C,
  (J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ U : (RingedSite.ofCommRingSheaf J O),
  HasWeakSheafify ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : (RingedSite.ofCommRingSheaf J O),
  ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, DerivedCategory.DerivedTensor.Right.Has
  (C := SheafOfModules.RingedSite.ringedSiteModuleCategory.{max u v, v, w, w}
    (J.over U) (O.over U))]
variable [∀ U : (RingedSite.ofCommRingSheaf J O), PreservesFiniteLimits (localizedRestriction.{w} (RingedSite.ofCommRingSheaf J O) U)]
variable [∀ U : (RingedSite.ofCommRingSheaf J O), PreservesFiniteColimits (localizedRestriction.{w} (RingedSite.ofCommRingSheaf J O) U)]

/-- Lemma 21.47.4: a derived `𝒪_X`-module is perfect exactly when it is pseudo-coherent and
locally has finite Tor dimension. -/
@[stacks 08G8]
theorem isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :
    E.IsPerfect ↔ E.IsPseudoCoherent ∧ E.LocallyHasFiniteTorDimension := sorry

/-- A perfect derived module sheaf is pseudo-coherent and locally has finite Tor dimension. -/
theorem isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} (hE : E.IsPerfect) :
    E.IsPseudoCoherent ∧ E.LocallyHasFiniteTorDimension := sorry

/-- A perfect derived module sheaf locally has finite Tor dimension. -/
theorem locallyHasFiniteTorDimension_of_isPerfect
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} (hE : E.IsPerfect) :
    E.LocallyHasFiniteTorDimension := sorry

/-- A pseudo-coherent derived module sheaf of locally finite Tor dimension is perfect. -/
theorem isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hpc : E.IsPseudoCoherent) (htor : E.LocallyHasFiniteTorDimension) :
    E.IsPerfect := sorry

end Characterization

section PurePseudoCoherence

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : (RingedSite.ofCommRingSheaf J O),
  HasWeakSheafify ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : (RingedSite.ofCommRingSheaf J O),
  ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology.WEqualsLocallyBijective
    AddCommGrpCat.{w}]

/-- A perfect derived module sheaf is pseudo-coherent. -/
theorem isPseudoCoherent_of_isPerfect
    {E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)} (hE : E.IsPerfect) :
    E.IsPseudoCoherent := sorry

end PurePseudoCoherence

end RingedSite.Hom.ModuleDerived
