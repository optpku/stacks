module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.Local

@[expose] public section

/-!
# Perfectness criteria for derived module sheaves

This module collects intrinsic criteria relating perfectness, pseudo-coherence, and Tor
amplitude for derived module sheaves on an arbitrary bundled ringed site.
-/

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite.Hom (ModuleDerived localizedRestriction)

noncomputable section

universe u v w

set_option checkBinderAnnotations false

namespace RingedSite.Hom.ModuleDerived

section TorAmplitudeCriterion

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [∀ U : X,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [MonoidalCategory (ModuleCat.{w} X)] [MonoidalPreadditive (ModuleCat.{w} X)]
variable [∀ (K L : CochainComplex (ModuleCat.{w} X) ℤ),
  HomologicalComplex.HasMapBifunctor K L (curriedTensor (ModuleCat.{w} X)) (up ℤ)]
variable [DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat.{w} X)]

/-- Lemma 21.47.3: an object of `D(𝒪_X)` with Tor-amplitude in `[a, b]` that is
`(a - 1)`-pseudo-coherent is perfect. -/
@[stacks 08G7]
theorem isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent
    (E : ModuleDerived.{w} X) (a b : ℤ)
    (hE : HasTorAmplitudeIn E a b)
    (hpc : E.IsMPseudoCoherent (a - 1)) :
    E.IsPerfect := sorry

end TorAmplitudeCriterion

section Characterization

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [∀ U : X,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X, MonoidalCategory (ModuleCat.{w} (X.localization U))]
variable [∀ U : X, MonoidalPreadditive (ModuleCat.{w} (X.localization U))]
variable [∀ U : X, ∀ (K L : CochainComplex (ModuleCat.{w} (X.localization U)) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (ModuleCat.{w} (X.localization U))) (up ℤ)]
variable [∀ U : X,
  DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat.{w} (X.localization U))]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction.{w} X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction.{w} X U)]

/-- Lemma 21.47.4: a derived `𝒪_X`-module is perfect exactly when it is pseudo-coherent and
locally has finite Tor dimension. -/
@[stacks 08G8]
theorem isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
    (E : ModuleDerived.{w} X) :
    E.IsPerfect ↔ E.IsPseudoCoherent ∧ E.LocallyHasFiniteTorDimension := sorry

/-- A perfect derived module sheaf is pseudo-coherent and locally has finite Tor dimension. -/
theorem isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect
    {E : ModuleDerived.{w} X} (hE : E.IsPerfect) :
    E.IsPseudoCoherent ∧ E.LocallyHasFiniteTorDimension := sorry

/-- A perfect derived module sheaf is pseudo-coherent. -/
theorem isPseudoCoherent_of_isPerfect
    {E : ModuleDerived.{w} X} (hE : E.IsPerfect) :
    E.IsPseudoCoherent := sorry

/-- A perfect derived module sheaf locally has finite Tor dimension. -/
theorem locallyHasFiniteTorDimension_of_isPerfect
    {E : ModuleDerived.{w} X} (hE : E.IsPerfect) :
    E.LocallyHasFiniteTorDimension := sorry

/-- A pseudo-coherent derived module sheaf of locally finite Tor dimension is perfect. -/
theorem isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    {E : ModuleDerived.{w} X}
    (hpc : E.IsPseudoCoherent) (htor : E.LocallyHasFiniteTorDimension) :
    E.IsPerfect := sorry

end Characterization

end RingedSite.Hom.ModuleDerived
