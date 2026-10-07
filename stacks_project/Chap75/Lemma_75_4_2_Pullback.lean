module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Zariski.Flat
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.ModuleEquivalence
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Equivalence
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap75.Lemma_75_4_2_SmallEtale

/-!
# Exact derived pullback from a scheme to its small étale site

`DerivedQCoh.epsilonStar` is the composite comparison
`D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_étale)` obtained by identifying the scheme category with
the small Zariski site and then applying exact `ε^*` along `smallEtaleToZariski`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory Opposite
open AlgebraicGeometry.Scheme.SiteRestriction
open CategoryTheory.Limits
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Abelian-group-valued sheaf composition exists on the small Zariski topology of a scheme. -/
instance smallZariski_hasSheafCompose (X : Scheme.{u}) :
    X.smallZariskiTopology.HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) := sorry

/-- The category of modules on the small Zariski ringed site of a scheme is abelian. -/
instance zariskiModulesAbelian (X : Scheme.{u}) :
    Abelian (RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The category of modules on the transported small Zariski ringed site of a scheme is
abelian. -/
instance smallZariskiTransportedModulesAbelian (X : Scheme.{u}) :
    Abelian (RingedSite.ModuleCat.{u} (smallZariskiRingedSite X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The standard derived-category structure on modules on the small Zariski ringed site. -/
instance instHasDerivedCategory_zariskiModules (X : Scheme.{u}) :
    HasDerivedCategory (RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite X)) :=
  HasDerivedCategory.standard _

/-- The standard derived-category structure on modules on the transported small Zariski
ringed site. -/
instance instHasDerivedCategory_smallZariskiTransportedModules (X : Scheme.{u}) :
    HasDerivedCategory (RingedSite.ModuleCat.{u} (smallZariskiRingedSite X)) :=
  HasDerivedCategory.standard _

/-- The standard derived-category structure on modules on the opens ringed site of a
scheme. -/
instance instHasDerivedCategory_opensModules (X : Scheme.{u}) :
    HasDerivedCategory
      (RingedSite.ModuleCat.{u} (RingedSpace.opensRingedSite X.toRingedSpace)) :=
  HasDerivedCategory.standard _

namespace SiteRestriction

/-- The morphism `ε` from the small étale ringed site to the small Zariski ringed site is
flat. -/
instance instIsFlat_smallEtaleToZariski (X : Scheme.{u}) :
    IsFlat.{u} (smallEtaleToZariski X) :=
  smallEtaleToZariski_isFlat X

end SiteRestriction

namespace DerivedQCoh

/-- The property that every cohomology sheaf of a derived module on the small Zariski
ringed site is quasi-coherent. -/
abbrev zariskiSiteProperty (X : Scheme.{u}) :
    ObjectProperty
      (DerivedCategory (RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite X))) :=
  DerivedCategory.cohomologyIn
    (SheafOfModules.isQuasicoherent (Zariski.Small.structureSheaf X))

/-- The derived category of quasi-coherent modules on the small Zariski ringed site of `X`.
This is the domain of `ε^*` in the comparison of ringed sites
`(X_étale, 𝒪_étale) ⟶ (X_Zar, 𝒪_X)`. -/
abbrev ZariskiSite (X : Scheme.{u}) :=
  DerivedCategory.CohomologyIn
    (SheafOfModules.isQuasicoherent (Zariski.Small.structureSheaf X))

namespace ZariskiSite

/-- The inclusion of derived modules with quasi-coherent cohomology into `D(𝒪_Zar)`. -/
abbrev inclusion (X : Scheme.{u}) :
    ZariskiSite X ⥤
      DerivedCategory (RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite X)) :=
  (zariskiSiteProperty X).ι

/-- An object of `D(𝒪_Zar)` lies in `ZariskiSite X` iff every cohomology sheaf is
quasi-coherent. -/
theorem mem_iff (X : Scheme.{u})
    (E : DerivedCategory (RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite X))) :
    zariskiSiteProperty X E ↔
      ∀ n : ℤ,
        SheafOfModules.isQuasicoherent (Zariski.Small.structureSheaf X)
          ((DerivedCategory.homologyFunctor
              (RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite X)) n).obj E) :=
  sorry

end ZariskiSite

/-- Regard a module sheaf on the underlying ringed space of `X` as a module sheaf on its
opens ringed site. -/
def toOpensModulesObj (X : Scheme.{u}) (M : X.toRingedSpace.Modules) :
    RingedSite.ModuleCat.{u} (RingedSpace.opensRingedSite X.toRingedSpace) :=
  M

/-- Regard a morphism of module sheaves on the underlying ringed space of `X` as a morphism
on the opens ringed site. -/
def toOpensModulesMap (X : Scheme.{u}) {M N : X.toRingedSpace.Modules} (f : M ⟶ N) :
    toOpensModulesObj X M ⟶ toOpensModulesObj X N :=
  f

/-- The identity-on-data functor from modules on the underlying ringed space of `X` to
modules on its opens ringed site. -/
def toOpensModules (X : Scheme.{u}) :
    X.toRingedSpace.Modules ⥤
      RingedSite.ModuleCat.{u} (RingedSpace.opensRingedSite X.toRingedSpace) where
  obj := toOpensModulesObj X
  map := toOpensModulesMap X
  map_id := sorry
  map_comp := sorry

/-- The identity-on-data object map from the opens ringed site back to the underlying
ringed-space modules. -/
def fromOpensModulesObj (X : Scheme.{u})
    (M : RingedSite.ModuleCat.{u} (RingedSpace.opensRingedSite X.toRingedSpace)) :
    X.toRingedSpace.Modules :=
  M

/-- The identity-on-data morphism map from the opens ringed site back to the underlying
ringed-space modules. -/
def fromOpensModulesMap (X : Scheme.{u})
    {M N : RingedSite.ModuleCat.{u} (RingedSpace.opensRingedSite X.toRingedSpace)}
    (f : M ⟶ N) :
    fromOpensModulesObj X M ⟶ fromOpensModulesObj X N :=
  f

/-- The identity-on-data functor from modules on the opens ringed site of `X` back to
modules on its underlying ringed space. -/
def fromOpensModules (X : Scheme.{u}) :
    RingedSite.ModuleCat.{u} (RingedSpace.opensRingedSite X.toRingedSpace) ⥤
      X.toRingedSpace.Modules where
  obj := fromOpensModulesObj X
  map := fromOpensModulesMap X
  map_id := sorry
  map_comp := sorry

/-- The identity-on-data comparison isomorphisms satisfy the triangle identity. -/
theorem toOpensModulesEquivalence_triangle (X : Scheme.{u})
    (M : X.toRingedSpace.Modules) :
    (toOpensModules X).map (𝟙 M) ≫ 𝟙 ((toOpensModules X).obj M) =
      𝟙 ((toOpensModules X).obj M) := sorry

/-- The two identity-on-data functors identify modules on the underlying ringed space of
`X` with modules on its opens ringed site. -/
def toOpensModulesEquivalence (X : Scheme.{u}) :
    X.toRingedSpace.Modules ≌
      RingedSite.ModuleCat.{u} (RingedSpace.opensRingedSite X.toRingedSpace) where
  functor := toOpensModules X
  inverse := fromOpensModules X
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := toOpensModulesEquivalence_triangle X

/-- The forward opens-site comparison does not change the underlying module sheaf. -/
theorem toOpensModules_obj (X : Scheme.{u}) (M : X.toRingedSpace.Modules) :
    (toOpensModules X).obj M = toOpensModulesObj X M := sorry

/-- The open-range functor from the small Zariski site of `X` to its opens is a morphism of
sites. -/
instance smallZariskiRangeFunctor_isMorphismOfSites (X : Scheme.{u}) :
    IsMorphismOfSites X.smallZariskiTopology
      (RingedSpace.opensRingedSite X.toRingedSpace).siteTopology
      (smallZariskiRangeFunctor X) := sorry

/-- The component of the structure-sheaf map of `opensToSmallZariski` at an open immersion
`U ⟶ X` is the identity on `Γ(X, U.opensRange)`, i.e. the unit/counit comparison of
`smallZariskiSheafEquiv` after evaluating at the open range. -/
noncomputable def opensToSmallZariskiStructureSheafHomApp (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    (smallZariskiRingSheaf X).obj.obj U ⟶
      (((smallZariskiRangeFunctor X).sheafPushforwardContinuous RingCat.{u}
          X.smallZariskiTopology
          (RingedSpace.opensRingedSite X.toRingedSpace).siteTopology).obj
        (RingedSpace.opensRingedSite X.toRingedSpace).structureSheaf).obj.obj U :=
  𝟙 _

/-- The components of `opensToSmallZariskiStructureSheafHomApp` are identity maps on
`Γ(X, U.opensRange)`. -/
theorem opensToSmallZariskiStructureSheafHomApp_eq (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    opensToSmallZariskiStructureSheafHomApp X U = 𝟙 _ := sorry

/-- The natural transformation of structure sheaves whose components are identity maps on
`Γ(X, U.opensRange)`, the unit/counit comparison of `smallZariskiSheafEquiv`. -/
noncomputable def opensToSmallZariskiStructureSheafHom (X : Scheme.{u}) :
    smallZariskiRingSheaf X ⟶
      ((smallZariskiRangeFunctor X).sheafPushforwardContinuous RingCat.{u}
        X.smallZariskiTopology
        (RingedSpace.opensRingedSite X.toRingedSpace).siteTopology).obj
        (RingedSpace.opensRingedSite X.toRingedSpace).structureSheaf where
  hom.app := opensToSmallZariskiStructureSheafHomApp X
  hom.naturality := sorry

/-- The inverse comparison from the opens ringed site of `X` to its transported small Zariski
ringed site, with base `smallZariskiRangeFunctor` and structure-sheaf map the unit/counit
comparison of `smallZariskiSheafEquiv`. -/
noncomputable def opensToSmallZariski (X : Scheme.{u}) :
    RingedSite.Hom (RingedSpace.opensRingedSite X.toRingedSpace)
      (smallZariskiRingedSite X) where
  base := smallZariskiRangeFunctor X
  structureSheafMap := opensToSmallZariskiStructureSheafHom X

/-- The base of `opensToSmallZariski` is the open-range functor. -/
theorem opensToSmallZariski_base (X : Scheme.{u}) :
    (opensToSmallZariski X).base = smallZariskiRangeFunctor X := sorry

/-- The structure-sheaf map of `opensToSmallZariski` is the unit/counit comparison of
`smallZariskiSheafEquiv`. -/
theorem opensToSmallZariski_structureSheafMap (X : Scheme.{u}) :
    (opensToSmallZariski X).structureSheafMap =
      opensToSmallZariskiStructureSheafHom X := sorry

/-- The opens-to-small-Zariski comparison is a ringed equivalence. -/
instance instIsRingedEquivalence_opensToSmallZariski (X : Scheme.{u}) :
    (opensToSmallZariski X).IsRingedEquivalence := sorry

/-- Pushforward of modules along `opensToSmallZariski` is an equivalence. -/
instance instIsEquivalence_opensToSmallZariski_modulePushforward (X : Scheme.{u}) :
    (opensToSmallZariski X).modulePushforward.{u}.IsEquivalence := sorry

/-- Pushforward of modules along `opensToSmallZariski` preserves finite limits. -/
instance instPreservesFiniteLimits_opensToSmallZariski_modulePushforward
    (X : Scheme.{u}) :
    PreservesFiniteLimits (opensToSmallZariski X).modulePushforward.{u} := sorry

/-- Pushforward of modules along `opensToSmallZariski` preserves finite colimits. -/
instance instPreservesFiniteColimits_opensToSmallZariski_modulePushforward
    (X : Scheme.{u}) :
    PreservesFiniteColimits (opensToSmallZariski X).modulePushforward.{u} := sorry

/-- The component of the small-Zariski structure-sheaf comparison at an open immersion
`U ⟶ X` is the canonical ring map `Γ(X, U.opensRange) ⟶ Γ(U, 𝒪_U)` obtained from
`IsOpenImmersion.ΓIsoTop`. -/
noncomputable def smallZariskiStructureSheafHomApp (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    (smallZariskiRingSheaf X).obj.obj U ⟶
      (Zariski.Small.structureSheaf X).obj.obj U :=
  (forget₂ CommRingCat RingCat).map
    (@IsOpenImmersion.ΓIsoTop U.unop.left X U.unop.hom U.unop.prop).inv

/-- The components of `smallZariskiStructureSheafHomApp` are the maps
`Γ(X, U.opensRange) ⟶ Γ(U, 𝒪_U)` induced by `IsOpenImmersion.ΓIsoTop`. -/
theorem smallZariskiStructureSheafHomApp_eq (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    smallZariskiStructureSheafHomApp X U =
      (forget₂ CommRingCat RingCat).map
    (@IsOpenImmersion.ΓIsoTop U.unop.left X U.unop.hom U.unop.prop).inv :=
  sorry

/-- The natural transformation of structure sheaves whose components are the
`Γ(U, 𝒪_U)` comparisons of `IsOpenImmersion.ΓIsoTop`. -/
noncomputable def smallZariskiStructureSheafHom (X : Scheme.{u}) :
    smallZariskiRingSheaf X ⟶ Zariski.Small.structureSheaf X where
  hom.app := smallZariskiStructureSheafHomApp X
  hom.naturality := sorry

/-- The ringed-site identification of the global-sections small Zariski site of `X` with
the transported small Zariski ringed site, with identity base functor and structure-sheaf
map given by the `Γ(U, 𝒪_U)` comparisons. -/
noncomputable def smallZariskiRingedComparison (X : Scheme.{u}) :
    RingedSite.Hom (Zariski.Small.ringedSite X) (smallZariskiRingedSite X) where
  base := 𝟭 _
  structureSheafMap := smallZariskiStructureSheafHom X

/-- The base of `smallZariskiRingedComparison` is the identity on the small Zariski site. -/
theorem smallZariskiRingedComparison_base (X : Scheme.{u}) :
    (smallZariskiRingedComparison X).base = 𝟭 X.smallZariskiSite := sorry

/-- The structure-sheaf component of `smallZariskiRingedComparison` at `U` is the
`Γ(U, 𝒪_U)` comparison of `IsOpenImmersion.ΓIsoTop`. -/
theorem smallZariskiRingedComparison_app (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    (smallZariskiRingedComparison X).structureSheafMap.hom.app U =
      smallZariskiStructureSheafHomApp X U := sorry

/-- The small-Zariski ringed-site identification is a ringed equivalence. -/
instance instIsRingedEquivalence_smallZariskiRingedComparison (X : Scheme.{u}) :
    (smallZariskiRingedComparison X).IsRingedEquivalence := sorry

/-- Pushforward of modules along `smallZariskiRingedComparison` is an equivalence. -/
instance instIsEquivalence_smallZariskiRingedComparison_modulePushforward
    (X : Scheme.{u}) :
    (smallZariskiRingedComparison X).modulePushforward.{u}.IsEquivalence := sorry

/-- The component of the structure-sheaf map of `smallZariskiToZariskiSmall` at an open
immersion `U ⟶ X` is the canonical ring map `Γ(U, 𝒪_U) ⟶ Γ(X, U.opensRange)` obtained from
`IsOpenImmersion.ΓIsoTop`. -/
noncomputable def smallZariskiToZariskiSmallStructureSheafHomApp (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    (Zariski.Small.structureSheaf X).obj.obj U ⟶
      (smallZariskiRingSheaf X).obj.obj U :=
  (forget₂ CommRingCat RingCat).map
    (@IsOpenImmersion.ΓIsoTop U.unop.left X U.unop.hom U.unop.prop).hom

/-- The components of `smallZariskiToZariskiSmallStructureSheafHomApp` are the maps
`Γ(U, 𝒪_U) ⟶ Γ(X, U.opensRange)` induced by `IsOpenImmersion.ΓIsoTop`. -/
theorem smallZariskiToZariskiSmallStructureSheafHomApp_eq (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    smallZariskiToZariskiSmallStructureSheafHomApp X U =
      (forget₂ CommRingCat RingCat).map
        (@IsOpenImmersion.ΓIsoTop U.unop.left X U.unop.hom U.unop.prop).hom :=
  sorry

/-- The natural transformation of structure sheaves whose components are the
`Γ(U, 𝒪_U) ⟶ Γ(X, U.opensRange)` comparisons of `IsOpenImmersion.ΓIsoTop`. -/
noncomputable def smallZariskiToZariskiSmallStructureSheafHom (X : Scheme.{u}) :
    Zariski.Small.structureSheaf X ⟶ smallZariskiRingSheaf X where
  hom.app := smallZariskiToZariskiSmallStructureSheafHomApp X
  hom.naturality := sorry

/-- The comparison from the transported small Zariski ringed site of `X` to
`Zariski.Small.ringedSite X`, with identity base functor and structure-sheaf map given by
the `Γ(U, 𝒪_U)` comparisons. -/
noncomputable def smallZariskiToZariskiSmall (X : Scheme.{u}) :
    RingedSite.Hom (smallZariskiRingedSite X) (Zariski.Small.ringedSite X) where
  base := 𝟭 _
  structureSheafMap := smallZariskiToZariskiSmallStructureSheafHom X

/-- The base of `smallZariskiToZariskiSmall` is the identity on the small Zariski site. -/
theorem smallZariskiToZariskiSmall_base (X : Scheme.{u}) :
    (smallZariskiToZariskiSmall X).base = 𝟭 X.smallZariskiSite := sorry

/-- The structure-sheaf component of `smallZariskiToZariskiSmall` at `U` is the
`Γ(U, 𝒪_U) ⟶ Γ(X, U.opensRange)` comparison of `IsOpenImmersion.ΓIsoTop`. -/
theorem smallZariskiToZariskiSmall_app (X : Scheme.{u})
    (U : X.smallZariskiSiteᵒᵖ) :
    (smallZariskiToZariskiSmall X).structureSheafMap.hom.app U =
      smallZariskiToZariskiSmallStructureSheafHomApp X U := sorry

/-- The small-Zariski-to-`Zariski.Small` comparison is a ringed equivalence. -/
instance instIsRingedEquivalence_smallZariskiToZariskiSmall (X : Scheme.{u}) :
    (smallZariskiToZariskiSmall X).IsRingedEquivalence := sorry

/-- Pushforward of modules along `smallZariskiToZariskiSmall` is an equivalence. -/
instance instIsEquivalence_smallZariskiToZariskiSmall_modulePushforward
    (X : Scheme.{u}) :
    (smallZariskiToZariskiSmall X).modulePushforward.{u}.IsEquivalence := sorry

/-- Pushforward of modules along `smallZariskiToZariskiSmall` preserves finite limits. -/
instance instPreservesFiniteLimits_smallZariskiToZariskiSmall_modulePushforward
    (X : Scheme.{u}) :
    PreservesFiniteLimits (smallZariskiToZariskiSmall X).modulePushforward.{u} :=
  sorry

/-- Pushforward of modules along `smallZariskiToZariskiSmall` preserves finite colimits. -/
instance instPreservesFiniteColimits_smallZariskiToZariskiSmall_modulePushforward
    (X : Scheme.{u}) :
    PreservesFiniteColimits (smallZariskiToZariskiSmall X).modulePushforward.{u} :=
  sorry

/-- The exact derived functor from `D(𝒪_X)` to `D(𝒪_Zar)` obtained by comparing the
opens ringed site, pushing forward along `opensToSmallZariski`, and identifying with
`Zariski.Small.ringedSite` by `smallZariskiToZariskiSmall`. -/
noncomputable def schemeToZariskiDerived (X : Scheme.{u}) :
    RingedSpace.ModuleDerived X.toRingedSpace ⥤
      DerivedCategory (RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite X)) :=
  (toOpensModulesEquivalence X).mapDerivedCategory.functor ⋙
    (opensToSmallZariski X).modulePushforward.{u}.mapDerivedCategory ⋙
      (smallZariskiToZariskiSmall X).modulePushforward.{u}.mapDerivedCategory

namespace schemeToZariski

/-- The comparison from `D(𝒪_X)` to `D(𝒪_Zar)` preserves quasi-coherent cohomology. -/
theorem mapsTo (X : Scheme.{u}) :
    derivedQuasiCoherentModuleProperty X ≤
      (zariskiSiteProperty X).inverseImage (schemeToZariskiDerived X) :=
  sorry

end schemeToZariski

/-- The restricted comparison `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Zar)` induced by the ringed-site
identifications of `X` with its small Zariski site. -/
noncomputable def schemeToZariski (X : Scheme.{u}) :
    DerivedQCoh X ⥤ ZariskiSite X :=
  ObjectProperty.FullSubcategory.restrict
    (schemeToZariskiDerived X) (schemeToZariski.mapsTo X)

namespace schemeToZariski

/-- Forgetting quasi-coherence after `schemeToZariski` recovers the ambient derived
comparison. -/
noncomputable def inclusionIso (X : Scheme.{u}) :
    schemeToZariski X ⋙ ZariskiSite.inclusion X ≅
      DerivedQCoh.inclusion X ⋙ schemeToZariskiDerived X :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (schemeToZariskiDerived X) (mapsTo X)

/-- The underlying derived module of `schemeToZariski` is the ambient derived comparison. -/
@[simp]
theorem obj_obj (X : Scheme.{u}) (E : DerivedQCoh X) :
    ((schemeToZariski X).obj E).obj = (schemeToZariskiDerived X).obj E.obj :=
  sorry

end schemeToZariski

/-- The comparison `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Zar)` is an equivalence. -/
instance schemeToZariski_isEquivalence (X : Scheme.{u}) :
    (schemeToZariski X).IsEquivalence := sorry

namespace zariskiEpsilonStar

/-- Exact pullback along `ε` preserves quasi-coherent cohomology. -/
theorem mapsTo (X : Scheme.{u}) :
    zariskiSiteProperty X ≤
      (smallEtaleProperty X).inverseImage
        (IsFlat.exactPullback (smallEtaleToZariski X)).mapDerivedCategory :=
  sorry

end zariskiEpsilonStar

/-- Exact derived pullback `ε^*` along the morphism of ringed sites from the small étale
site of `X` to its small Zariski site, restricted to complexes with quasi-coherent
cohomology. -/
noncomputable def zariskiEpsilonStar (X : Scheme.{u}) :
    ZariskiSite X ⥤ SmallEtale X :=
  ObjectProperty.FullSubcategory.restrict
    (IsFlat.exactPullback (smallEtaleToZariski X)).mapDerivedCategory
    (zariskiEpsilonStar.mapsTo X)

namespace zariskiEpsilonStar

/-- Forgetting quasi-coherence after site-level `ε^*` recovers ambient exact derived
pullback. -/
noncomputable def inclusionIso (X : Scheme.{u}) :
    zariskiEpsilonStar X ⋙ SmallEtale.inclusion X ≅
      ZariskiSite.inclusion X ⋙
        (IsFlat.exactPullback (smallEtaleToZariski X)).mapDerivedCategory :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (IsFlat.exactPullback (smallEtaleToZariski X)).mapDerivedCategory
    (mapsTo X)

/-- The underlying derived module of site-level `ε^*` is ambient exact derived pullback. -/
@[simp]
theorem obj_obj (X : Scheme.{u}) (E : ZariskiSite X) :
    ((zariskiEpsilonStar X).obj E).obj =
      ((IsFlat.exactPullback (smallEtaleToZariski X)).mapDerivedCategory).obj E.obj :=
  sorry

end zariskiEpsilonStar

/-- Site-level exact derived pullback along `ε` is an equivalence on complexes with
quasi-coherent cohomology. -/
instance zariskiEpsilonStar_isEquivalence (X : Scheme.{u}) :
    (zariskiEpsilonStar X).IsEquivalence := sorry

/-- Exact derived pullback `ε^* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_étale)` obtained by comparing
the scheme category with the small Zariski site and then applying exact pullback along
`smallEtaleToZariski`. -/
noncomputable def epsilonStar (X : Scheme.{u}) :
    DerivedQCoh X ⥤ SmallEtale X :=
  schemeToZariski X ⋙ zariskiEpsilonStar X

namespace epsilonStar

/-- The composite `ε^*` preserves quasi-coherent cohomology in the sense that it lands in
`SmallEtale`. -/
theorem mapsTo (X : Scheme.{u}) (E : DerivedQCoh X) :
    smallEtaleProperty X ((SmallEtale.inclusion X).obj ((epsilonStar X).obj E)) :=
  sorry

/-- Forgetting quasi-coherence after composite `ε^*` recovers the ambient derived
comparison followed by exact pullback along `ε`. -/
noncomputable def inclusionIso (X : Scheme.{u}) :
    epsilonStar X ⋙ SmallEtale.inclusion X ≅
      DerivedQCoh.inclusion X ⋙
        (schemeToZariskiDerived X ⋙
          (IsFlat.exactPullback (smallEtaleToZariski X)).mapDerivedCategory) :=
  (Functor.associator (schemeToZariski X) (zariskiEpsilonStar X)
      (SmallEtale.inclusion X)).symm.trans
    ((Functor.isoWhiskerLeft (schemeToZariski X) (zariskiEpsilonStar.inclusionIso X)).trans
      ((Functor.associator (schemeToZariski X) (ZariskiSite.inclusion X)
          (IsFlat.exactPullback (smallEtaleToZariski X)).mapDerivedCategory).trans
        ((Functor.isoWhiskerRight (schemeToZariski.inclusionIso X)
            (IsFlat.exactPullback (smallEtaleToZariski X)).mapDerivedCategory).trans
          (Functor.associator (DerivedQCoh.inclusion X) (schemeToZariskiDerived X)
            (IsFlat.exactPullback (smallEtaleToZariski X)).mapDerivedCategory).symm)))

/-- The underlying derived module of composite `ε^*` is ambient exact derived pullback of
the Zariski comparison of `E`. -/
@[simp]
theorem obj_obj (X : Scheme.{u}) (E : DerivedQCoh X) :
    ((epsilonStar X).obj E).obj =
      ((IsFlat.exactPullback (smallEtaleToZariski X)).mapDerivedCategory).obj
        ((schemeToZariskiDerived X).obj E.obj) :=
  sorry

end epsilonStar

/-- Exact derived pullback along `ε` is an equivalence `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_étale)`. -/
instance epsilonStar_isEquivalence (X : Scheme.{u}) :
    (epsilonStar X).IsEquivalence := sorry


end DerivedQCoh

end AlgebraicGeometry.Scheme
