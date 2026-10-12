/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.Local
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Localization

/-!
# Relative Tor-amplitude on commutative ringed sites

Restriction of scalars along `f⁻¹𝒪 ⟶ 𝒪` views a derived `𝒪_X`-module as an
object of `D(f⁻¹𝒪_Y)`. Relative Tor-amplitude and locally finite Tor dimension
are the ordinary predicates after this restriction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite.Hom
open SheafOfModules.RingedSite
open scoped RingedSite.Hom

noncomputable section

universe uC vC uD vD w

namespace RingedSite.Hom.ModuleDerived

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {𝒪 : Sheaf JC CommRingCat.{w}} {𝒪' : Sheaf JD CommRingCat.{w}}
variable [UnivLE.{max uC vC, w}]
variable [HasWeakSheafify JC AddCommGrpCat.{w}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The standard derived-category structure on modules over a commutative ring
sheaf. -/
noncomputable instance ofCommRingSheaf_hasDerivedCategory :
    HasDerivedCategory (ModuleCat.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) :=
  moduleCat_hasDerivedCategory (RingedSite.ofCommRingSheaf JC 𝒪)

/-- The standard derived-category structure on the unfolded commutative module
category. -/
noncomputable instance ofCommRingSheaf_ringedSiteModule_hasDerivedCategory :
    HasDerivedCategory (ringedSiteModuleCategory.{uC, vC, w, w} JC 𝒪) :=
  CommRingPresentation.moduleHasDerivedCategory JC 𝒪

/-- Same-site restriction of scalars along a morphism of commutative ring sheaves
is additive. -/
instance restrictionAlong_additive
    {𝒪₁ 𝒪₂ : Sheaf JC CommRingCat.{w}} (α : 𝒪₁ ⟶ 𝒪₂) :
    (restrictionAlong.{uC, vC, w, w} α).Additive := sorry

/-- Same-site restriction of scalars preserves finite limits. -/
instance restrictionAlong_preservesFiniteLimits
    {𝒪₁ 𝒪₂ : Sheaf JC CommRingCat.{w}} (α : 𝒪₁ ⟶ 𝒪₂) :
    PreservesFiniteLimits (restrictionAlong.{uC, vC, w, w} α) := sorry

/-- Same-site restriction of scalars preserves finite colimits. -/
instance restrictionAlong_preservesFiniteColimits
    {𝒪₁ 𝒪₂ : Sheaf JC CommRingCat.{w}} (α : 𝒪₁ ⟶ 𝒪₂) :
    PreservesFiniteColimits (restrictionAlong.{uC, vC, w, w} α) := sorry

/-- The source site equipped with the inverse-image structure sheaf `f⁻¹𝒪`. -/
noncomputable abbrev inverseImageSite
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    RingedSite.{uC, vC, w} :=
  RingedSite.ofCommRingSheaf JC (inverseImageStructureSheaf f)

/-- `inverseImageSite f` is the commutative presentation of the source site with
structure sheaf `f⁻¹𝒪`. -/
theorem inverseImageSite_eq
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    inverseImageSite f =
      RingedSite.ofCommRingSheaf JC (inverseImageStructureSheaf f) := sorry

/-- The standard derived-category structure on modules over `f⁻¹𝒪`. -/
noncomputable instance inverseImageSite_hasDerivedCategory
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    HasDerivedCategory (ModuleCat.{w} (inverseImageSite f)) :=
  moduleCat_hasDerivedCategory (inverseImageSite f)

/-- The unfolded commutative module category over `f⁻¹𝒪` uses the standard
derived-category structure. -/
noncomputable instance inverseImageSite_ringedSiteModule_hasDerivedCategory
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    HasDerivedCategory
      (ringedSiteModuleCategory.{uC, vC, w, w} JC
        (inverseImageStructureSheaf f)) :=
  CommRingPresentation.moduleHasDerivedCategory JC (inverseImageStructureSheaf f)

/-- Derived restriction of `𝒪_X`-modules to modules over `f⁻¹𝒪`. -/
noncomputable def relativeRestriction
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪) ⥤
      ModuleDerived.{w} (inverseImageSite f) :=
  (restrictionAlong.{uC, vC, w, w}
    (inverseImageStructureSheafMap f)).mapDerivedCategory

/-- Derived relative restriction is the derived functor of restriction of scalars
along `inverseImageStructureSheafMap f`. -/
theorem relativeRestriction_eq
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    relativeRestriction f =
      (restrictionAlong.{uC, vC, w, w}
        (inverseImageStructureSheafMap f)).mapDerivedCategory := sorry

/-- Modules over `f⁻¹𝒪` carry the canonical tensor product of commutative
ringed-site modules. -/
noncomputable instance inverseImageSite_monoidalCategory
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    MonoidalCategory (ModuleCat.{w} (inverseImageSite f)) :=
  moduleMonoidalCategory (inverseImageStructureSheaf f)

/-- The tensor product on modules over `f⁻¹𝒪` is additive in each variable. -/
instance inverseImageSite_monoidalPreadditive
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    MonoidalPreadditive (ModuleCat.{w} (inverseImageSite f)) :=
  (monoidalPreadditive :
    MonoidalPreadditive
      (ringedSiteModuleCategory.{uC, vC, w, w} JC (inverseImageStructureSheaf f)))

/-- The total tensor product of complexes of `f⁻¹𝒪`-modules exists. -/
instance inverseImageSite_hasMapBifunctor
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (K L : CochainComplex (ModuleCat.{w} (inverseImageSite f)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (ModuleCat.{w} (inverseImageSite f))) (up ℤ) :=
  moduleCategoryHasMapBifunctor (inverseImageStructureSheaf f) K L

/-- Unbounded derived tensor products exist on modules over `f⁻¹𝒪`. -/
instance inverseImageSite_hasDerivedTensor
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    DerivedCategory.DerivedTensor.Has
      (C := ModuleCat.{w} (inverseImageSite f)) :=
  moduleCategoryHasDerivedTensor (inverseImageStructureSheaf f)

/-- A derived `𝒪_X`-module has Tor-amplitude in `[a, b]` over `f` when its
restriction to `f⁻¹𝒪` has that Tor-amplitude. -/
abbrev HasTorAmplitudeInOver
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) (a b : ℤ) : Prop :=
  HasTorAmplitudeIn ((relativeRestriction f).obj E) a b

/-- Relative Tor-amplitude is the ordinary Tor-amplitude of the derived restriction
to `f⁻¹𝒪`. -/
theorem hasTorAmplitudeInOver_iff
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) (a b : ℤ) :
    HasTorAmplitudeInOver f E a b ↔
      HasTorAmplitudeIn ((relativeRestriction f).obj E) a b := sorry

/-- The object property of having Tor-amplitude in `[a, b]` after restriction from
`𝒪_X` to `f⁻¹𝒪`. -/
noncomputable def torAmplitudeInOver
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (a b : ℤ) :
    ObjectProperty (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) :=
  fun E ↦ HasTorAmplitudeInOver f E a b

/-- The object property `torAmplitudeInOver f a b` is the predicate
`HasTorAmplitudeInOver f · a b`. -/
theorem torAmplitudeInOver_eq
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) (a b : ℤ) :
    torAmplitudeInOver f a b E = HasTorAmplitudeInOver f E a b := sorry

/-- The standard derived-category structure on modules over a localization of
`f⁻¹𝒪`. -/
noncomputable instance inverseImageSite_localization_hasDerivedCategory
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (U : inverseImageSite f) :
    HasDerivedCategory (ModuleCat.{w} ((inverseImageSite f).localization U)) :=
  moduleCat_hasDerivedCategory ((inverseImageSite f).localization U)

variable [∀ U : C, HasWeakSheafify (JC.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (JC.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Slice sites of `f⁻¹𝒪` support composition with `forget₂` into rings. -/
instance inverseImageSite_over_hasSheafCompose
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (U : inverseImageSite f) :
    ((inverseImageSite f).siteTopology.over U).HasSheafCompose
      (forget₂ CommRingCat.{w} RingCat.{w}) := sorry

/-- Modules on a localization of `f⁻¹𝒪` carry the canonical slice tensor product. -/
noncomputable instance inverseImageSite_localization_monoidalCategory
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (U : inverseImageSite f)
    [HasWeakSheafify ((inverseImageSite f).siteTopology.over U) AddCommGrpCat.{w}]
    [((inverseImageSite f).siteTopology.over U).WEqualsLocallyBijective
      AddCommGrpCat.{w}] :
    MonoidalCategory (ModuleCat.{w} ((inverseImageSite f).localization U)) :=
  ModuleOver.monoidalCategory (inverseImageStructureSheaf f) U

/-- The slice tensor product on a localization of `f⁻¹𝒪` is additive. -/
instance inverseImageSite_localization_monoidalPreadditive
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (U : inverseImageSite f)
    [HasWeakSheafify ((inverseImageSite f).siteTopology.over U) AddCommGrpCat.{w}]
    [((inverseImageSite f).siteTopology.over U).WEqualsLocallyBijective
      AddCommGrpCat.{w}] :
    MonoidalPreadditive (ModuleCat.{w} ((inverseImageSite f).localization U)) :=
  ModuleOver.monoidalPreadditive (inverseImageStructureSheaf f) U

/-- The total tensor product of complexes exists on each localization of `f⁻¹𝒪`. -/
instance inverseImageSite_localization_hasMapBifunctor
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (U : inverseImageSite f)
    [HasWeakSheafify ((inverseImageSite f).siteTopology.over U) AddCommGrpCat.{w}]
    [((inverseImageSite f).siteTopology.over U).WEqualsLocallyBijective
      AddCommGrpCat.{w}]
    (K L : CochainComplex (ModuleCat.{w} ((inverseImageSite f).localization U)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (ModuleCat.{w} ((inverseImageSite f).localization U)))
      (up ℤ) :=
  moduleCategoryHasMapBifunctor ((inverseImageStructureSheaf f).over U) K L

/-- Unbounded derived tensor products exist on each localization of `f⁻¹𝒪`. -/
instance inverseImageSite_localization_hasDerivedTensor
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (U : inverseImageSite f)
    [HasWeakSheafify ((inverseImageSite f).siteTopology.over U) AddCommGrpCat.{w}]
    [((inverseImageSite f).siteTopology.over U).WEqualsLocallyBijective
      AddCommGrpCat.{w}] :
    DerivedCategory.DerivedTensor.Has
      (C := ModuleCat.{w} ((inverseImageSite f).localization U)) :=
  moduleCategoryHasDerivedTensor ((inverseImageStructureSheaf f).over U)

/-- Restriction of `f⁻¹𝒪`-modules to a localization is additive. -/
instance inverseImageSite_localizedRestriction_additive
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (U : inverseImageSite f) :
    (localizedRestriction.{w} (inverseImageSite f) U).Additive :=
  localizedRestriction_additive (inverseImageSite f) U

/-- Restriction of `f⁻¹𝒪`-modules to a localization preserves finite limits. -/
noncomputable instance inverseImageSite_localizedRestriction_preservesFiniteLimits
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (U : inverseImageSite f) :
    PreservesFiniteLimits (localizedRestriction.{w} (inverseImageSite f) U) :=
  localizedRestriction_preservesFiniteLimits (inverseImageSite f) U

/-- Restriction of `f⁻¹𝒪`-modules to a localization preserves finite colimits. -/
noncomputable instance inverseImageSite_localizedRestriction_preservesFiniteColimits
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (U : inverseImageSite f) :
    PreservesFiniteColimits (localizedRestriction.{w} (inverseImageSite f) U) :=
  localizedRestriction_preservesFiniteColimits (inverseImageSite f) U

/-- A derived `𝒪_X`-module locally has finite Tor dimension over `f` when its
restriction to `f⁻¹𝒪` locally has finite Tor dimension. -/
abbrev LocallyHasFiniteTorDimensionOver
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) : Prop :=
  LocallyHasFiniteTorDimension ((relativeRestriction f).obj E)

/-- The object property of locally finite Tor dimension after restriction from
`𝒪_X` to `f⁻¹𝒪`. -/
noncomputable def locallyFiniteTorDimensionOver
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint] :
    ObjectProperty (ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) :=
  fun E ↦ LocallyHasFiniteTorDimensionOver f E

/-- The object property `locallyFiniteTorDimensionOver f` is the predicate
`LocallyHasFiniteTorDimensionOver f`. -/
theorem locallyFiniteTorDimensionOver_eq
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) :
    locallyFiniteTorDimensionOver f E = LocallyHasFiniteTorDimensionOver f E := sorry

/-- Relative locally finite Tor dimension is the ordinary covering-local predicate
after derived restriction to `f⁻¹𝒪`. -/
theorem locallyHasFiniteTorDimensionOver_iff
    (f : RingedSite.Hom
      (RingedSite.ofCommRingSheaf JC 𝒪) (RingedSite.ofCommRingSheaf JD 𝒪'))
    [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JC 𝒪)) :
    LocallyHasFiniteTorDimensionOver f E ↔
      LocallyHasFiniteTorDimension ((relativeRestriction f).obj E) := sorry

end RingedSite.Hom.ModuleDerived
