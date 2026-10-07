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

universe u v w

namespace RingedSite.Hom.ModuleDerived

section

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]

-- Local instance justification (defeq pin): fix the localized module derived structure to the existing canonical owner.
local instance localizedHasDerivedCategory (U : X) :
    HasDerivedCategory (ModuleCat.{w} (X.localization U)) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory (X.localization U)
variable [∀ U : X, MonoidalCategory (ModuleCat.{w} (X.localization U))]
variable [∀ U : X, MonoidalPreadditive (ModuleCat.{w} (X.localization U))]
variable [∀ U : X, ∀ (K L : CochainComplex (ModuleCat.{w} (X.localization U)) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (ModuleCat.{w} (X.localization U))) (up ℤ)]
variable [∀ U : X,
  @DerivedCategory.DerivedTensor.Right.Has (ModuleCat.{w} (X.localization U)) _ _ _ _ _ _]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction.{w} X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction.{w} X U)]

/-- The object property of having finite Tor dimension locally on a covering of every object of
the underlying site. -/
@[stacks 08FZ "(3), ringed-site object property"]
def locallyFiniteTorDimension : ObjectProperty (ModuleDerived.{w} X) :=
  fun E ↦ ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    HasFiniteTorDimension ((localizedRestrictionDerived.{w} X I.Y).obj E)

/-- Definition 21.46.1 (3): `E` locally has finite Tor dimension when every object of the site
has a covering on whose members the restriction of `E` has finite Tor dimension. -/
@[stacks 08FZ "(3)"]
abbrev LocallyHasFiniteTorDimension (E : ModuleDerived.{w} X) : Prop :=
  locallyFiniteTorDimension E

/-- A locally finite-Tor-dimension object supplies a finite-Tor-dimension cover over every
object of the site. -/
theorem LocallyHasFiniteTorDimension.exists_cover
    {E : ModuleDerived.{w} X} (hE : LocallyHasFiniteTorDimension E) (U : X) :
    ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
      HasFiniteTorDimension ((localizedRestrictionDerived.{w} X I.Y).obj E) := sorry

end

end RingedSite.Hom.ModuleDerived
