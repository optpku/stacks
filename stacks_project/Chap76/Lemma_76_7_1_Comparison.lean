module

public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import stacks_project.Chap59.Lemma_59_40_1_Hom
public import stacks_project.Chap76.Lemma_76_7_1_Instances

/-!
# Associated étale differentials versus small-étale site differentials

A morphism of schemes induces a commutative-ring presentation of its small étale
ringed-site morphism.  The associated étale module of `Ω[f.toShHom]` is then
compared with the site-theoretic relative differentials of that presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction
open SheafOfModules.RingedSite
open Scheme.Etale.Small
open scoped AlgebraicGeometry RelativeDerivation RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Small

variable {X Y : Scheme.{u}}

/-- The inclusion of open immersions among étale morphisms is a morphism of the
lifted commutative small sites. -/
instance commSmallEtaleToZariski_base_isMorphismOfSites (S : Scheme.{u}) :
    IsMorphismOfSites
      (smallCommRingedSite .zariski S).siteTopology
      (smallCommRingedSite .etale S).siteTopology
      (smallZariskiToSmallEtale S) := sorry

/-- Small Zariski base change is a morphism of the lifted commutative small
Zariski sites. -/
instance zariskiCommRingedHom_base_isMorphismOfSites (f : X ⟶ Y) :
    IsMorphismOfSites
      (smallCommRingedSite .zariski Y).siteTopology
      (smallCommRingedSite .zariski X).siteTopology
      (smallZariskiPullback f) := sorry

/-- The Zariski-to-étale inclusion is continuous on lifted commutative small
sites. -/
instance commSmallEtaleToZariski_base_isContinuous (S : Scheme.{u}) :
    (smallZariskiToSmallEtale S).IsContinuous
      (StandardTopology.Small.topology .zariski S)
      (StandardTopology.Small.topology .etale S) := sorry

/-- Small Zariski base change is continuous on lifted commutative small Zariski
sites. -/
instance zariskiCommRingedHom_base_isContinuous (f : X ⟶ Y) :
    (smallZariskiPullback f).IsContinuous
      (StandardTopology.Small.topology .zariski Y)
      (StandardTopology.Small.topology .zariski X) := sorry

/-- The Zariski-to-étale inclusion is continuous on packaged small commutative
sites. -/
instance commSmallEtaleToZariski_base_isContinuous_site (S : Scheme.{u}) :
    (smallZariskiToSmallEtale S).IsContinuous
      (smallCommRingedSite .zariski S).siteTopology
      (smallCommRingedSite .etale S).siteTopology := sorry

/-- Small Zariski base change is continuous on packaged small commutative
Zariski sites. -/
instance zariskiCommRingedHom_base_isContinuous_site (f : X ⟶ Y) :
    (smallZariskiPullback f).IsContinuous
      (smallCommRingedSite .zariski Y).siteTopology
      (smallCommRingedSite .zariski X).siteTopology := sorry

/-- Continuous pushforward of commutative-ring sheaves along `commRingedHom f`
is a right adjoint, stated on the unfolded small-standard topologies. -/
instance (priority := high) commRingedHom_sheafPushforwardContinuous_isRightAdjoint
    (f : X ⟶ Y) :
    ((commRingedHom f).base.sheafPushforwardContinuous CommRingCat.{u + 1}
      (StandardTopology.Small.topology .etale Y)
      (StandardTopology.Small.topology .etale X)).IsRightAdjoint := sorry

/-- Continuous pushforward of commutative-ring sheaves along `commRingedHom f`
is a right adjoint, stated on the packaged small commutative sites. -/
instance (priority := high) commRingedHom_sheafPushforwardContinuous_site_isRightAdjoint
    (f : X ⟶ Y) :
    ((commRingedHom f).base.sheafPushforwardContinuous CommRingCat.{u + 1}
      (smallCommRingedSite .etale Y).siteTopology
      (smallCommRingedSite .etale X).siteTopology).IsRightAdjoint := sorry

/-- Mixed-topology form of the `commRingedHom` right-adjoint instance, matching
partial unfolding of `smallCommRingedSite`. -/
instance (priority := high) commRingedHom_sheafPushforwardContinuous_mixed_isRightAdjoint
    (f : X ⟶ Y) :
    ((commRingedHom f).base.sheafPushforwardContinuous CommRingCat.{u + 1}
      (StandardTopology.Small.topology .etale Y)
      (smallCommRingedSite .etale X).siteTopology).IsRightAdjoint := sorry

/-- The structure-sheaf component of the commutative small Zariski-to-étale
restriction. -/
noncomputable def commSmallEtaleToZariskiStructureSheafMap (S : Scheme.{u}) :
    StandardSmall.commStructureSheaf .zariski S ⟶
      ((smallZariskiToSmallEtale S).sheafPushforwardContinuous CommRingCat.{u + 1}
        (StandardTopology.Small.topology .zariski S)
        (StandardTopology.Small.topology .etale S)).obj
        (StandardSmall.commStructureSheaf .etale S) where
  hom :=
    { app := fun U ↦
        (CommRingCat.universeLift.{u, u + 1}).map
          (Scheme.Γ.map
            (𝟙 ((Scheme.smallZariskiToScheme S).obj U.unop)).op)
      naturality := sorry }

/-- The commutative-ring presentation of `id_small,étale,Zar`. -/
noncomputable def commSmallEtaleToZariski (S : Scheme.{u}) :
    RingedSite.Hom
      (smallCommRingedSite .etale S) (smallCommRingedSite .zariski S) where
  base := smallZariskiToSmallEtale S
  isMorphismOfSites := commSmallEtaleToZariski_base_isMorphismOfSites S
  structureSheafMap :=
    (sheafCompose (smallCommRingedSite .zariski S).siteTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (commSmallEtaleToZariskiStructureSheafMap S)

/-- The base of `commSmallEtaleToZariski` is the inclusion of open immersions among
étale morphisms. -/
theorem commSmallEtaleToZariski_base (S : Scheme.{u}) :
    (commSmallEtaleToZariski S).base = smallZariskiToSmallEtale S := sorry

/-- Continuous pushforward of commutative-ring sheaves along
`commSmallEtaleToZariski` is a right adjoint. -/
instance (priority := high) commSmallEtaleToZariski_sheafPushforwardContinuous_isRightAdjoint
    (S : Scheme.{u}) :
    ((commSmallEtaleToZariski S).base.sheafPushforwardContinuous CommRingCat.{u + 1}
      (StandardTopology.Small.topology .zariski S)
      (StandardTopology.Small.topology .etale S)).IsRightAdjoint := sorry

/-- Module pushforward along `commSmallEtaleToZariski` has a left adjoint. -/
instance (priority := high) commSmallEtaleToZariski_modulePushforward_isRightAdjoint
    (S : Scheme.{u}) :
    ((commSmallEtaleToZariski S).modulePushforward.{u + 1}).IsRightAdjoint := sorry

/-- The structure-sheaf component of the commutative small-Zariski ringed morphism. -/
noncomputable def commZariskiStructureSheafMap (f : X ⟶ Y) :
    StandardSmall.commStructureSheaf .zariski Y ⟶
      ((smallZariskiPullback f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (StandardTopology.Small.topology .zariski Y)
        (StandardTopology.Small.topology .zariski X)).obj
        (StandardSmall.commStructureSheaf .zariski X) where
  hom :=
    { app := fun U ↦
        (CommRingCat.universeLift.{u, u + 1}).map
          (Scheme.Γ.map (pullback.fst U.unop.hom f).op)
      naturality := sorry }

/-- A scheme morphism induces a morphism of small Zariski ringed sites in the
commutative-ring presentation. -/
noncomputable def zariskiCommRingedHom (f : X ⟶ Y) :
    RingedSite.Hom
      (smallCommRingedSite .zariski X) (smallCommRingedSite .zariski Y) where
  base := smallZariskiPullback f
  isMorphismOfSites := zariskiCommRingedHom_base_isMorphismOfSites f
  structureSheafMap :=
    (sheafCompose (smallCommRingedSite .zariski Y).siteTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (commZariskiStructureSheafMap f)

/-- The base of `zariskiCommRingedHom f` is small Zariski base change along `f`. -/
theorem zariskiCommRingedHom_base (f : X ⟶ Y) :
    (zariskiCommRingedHom f).base = smallZariskiPullback f := sorry

/-- Continuous pushforward of commutative-ring sheaves along
`zariskiCommRingedHom f` is a right adjoint. -/
instance (priority := high) zariskiCommRingedHom_sheafPushforwardContinuous_isRightAdjoint
    (f : X ⟶ Y) :
    ((zariskiCommRingedHom f).base.sheafPushforwardContinuous CommRingCat.{u + 1}
      (StandardTopology.Small.topology .zariski Y)
      (StandardTopology.Small.topology .zariski X)).IsRightAdjoint := sorry

/-- An object of the small Zariski site is an open immersion into `X`. -/
instance zariski_obj_hom (U : X.smallZariskiSite) : IsOpenImmersion U.hom := U.prop

/-- The étale comparison square of an object of the small étale site over `X`. -/
theorem etaleComparisonSquare (f : X ⟶ Y) (U : X.Etale) :
    CommSq U.hom (U.hom ≫ f) f (𝟙 Y) :=
  ⟨(Category.comp_id (U.hom ≫ f)).symm⟩

/-- The pullback comparison on relative differentials associated to an étale
object of `X` over `Y`. -/
noncomputable def etaleComparison (f : X ⟶ Y) (U : X.Etale) :
    (RingedSpace.Hom.pullback U.hom.toShHom).obj Ω[f.toShHom] ⟶
      Ω[(U.hom ≫ f).toShHom] :=
  RingedSpace.Hom.Differentials.comparison
    ((etaleComparisonSquare f U).map
      (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace))

/-- An object of the small étale site is étale over `X`. -/
instance etale_obj_hom (U : X.Etale) : Etale U.hom := U.prop

/-- The étale comparison on relative differentials is an isomorphism by
Lemma 37.9.9, using that `U.hom` and `𝟙 Y` are étale. -/
instance etaleComparison_isIso (f : X ⟶ Y) (U : X.Etale) :
    IsIso (etaleComparison f U) :=
  AlgebraicGeometry.Scheme.RelativeDifferentials.comparison_isIso_of_etale
    (etaleComparisonSquare f U)

/-- The named inverse of the étale comparison on relative differentials. -/
noncomputable def etaleComparisonInv (f : X ⟶ Y) (U : X.Etale) :
    Ω[(U.hom ≫ f).toShHom] ⟶
      (RingedSpace.Hom.pullback U.hom.toShHom).obj Ω[f.toShHom] :=
  CategoryTheory.inv (etaleComparison f U)

/-- The étale comparison on relative differentials is an isomorphism, with
constructed inverse; only the two iso identities are deferred. -/
noncomputable def etaleComparisonIso (f : X ⟶ Y) (U : X.Etale) :
    (RingedSpace.Hom.pullback U.hom.toShHom).obj Ω[f.toShHom] ≅
      Ω[(U.hom ≫ f).toShHom] where
  hom := etaleComparison f U
  inv := etaleComparisonInv f U
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `etaleComparisonIso` is the canonical comparison. -/
theorem etaleComparisonIso_hom (f : X ⟶ Y) (U : X.Etale) :
    (etaleComparisonIso f U).hom = etaleComparison f U := sorry

/-- The inverse map of `etaleComparisonIso` is `etaleComparisonInv`. -/
theorem etaleComparisonIso_inv (f : X ⟶ Y) (U : X.Etale) :
    (etaleComparisonIso f U).inv = etaleComparisonInv f U := sorry

/-- Global sections of the named inverse of the étale comparison. -/
noncomputable def etaleComparisonInvSections (f : X ⟶ Y) (U : X.Etale) :
    (RingedSpace.moduleGlobalSectionsFunctor U.left.toRingedSpace).obj
        Ω[(U.hom ≫ f).toShHom] ⟶
      (RingedSpace.moduleGlobalSectionsFunctor U.left.toRingedSpace).obj
        ((RingedSpace.Hom.pullback U.hom.toShHom).obj Ω[f.toShHom]) :=
  (RingedSpace.moduleGlobalSectionsFunctor U.left.toRingedSpace).map
    (etaleComparisonIso f U).inv

/-- The objectwise associated derivation at an étale object, after transporting
along the comparison isomorphism of Lemma 37.9.9. -/
noncomputable def associatedDerivationApp (f : X ⟶ Y) (U : X.Etaleᵒᵖ) :
    ((StandardSmall.comm .etale X (Ω[f.toShHom])).val.obj U).Derivation
      ((RingedSite.Hom.inverseImageStructureSheafMap (commRingedHom f)).hom.app U) :=
  ModuleCat.Derivation.mk
    (fun r ↦
      ULift.up
        ((etaleComparisonInvSections f U.unop)
          ((d[(U.unop.hom ≫ f).toShHom]).d (ULift.down r))))
    sorry sorry sorry

/-- Naturality of the objectwise associated derivation. -/
theorem associatedDerivationApp_naturality (f : X ⟶ Y) {U V : X.Etaleᵒᵖ}
    (i : U ⟶ V) (x : (StandardSmall.commStructureSheaf .etale X).obj.obj U) :
    (associatedDerivationApp f V).d
        ((StandardSmall.commStructureSheaf .etale X).obj.map i x) =
      (StandardSmall.comm .etale X (Ω[f.toShHom])).val.map i
        ((associatedDerivationApp f U).d x) := sorry

/-- The associated étale derivation `d^a` of `Ω[f.toShHom]`, whose value on an
étale object `U` is `Γ(U, d_{U/Y})` after the comparison isomorphism of
Lemma 37.9.9. -/
noncomputable def associatedUniversalDerivation (f : X ⟶ Y) :
    SheafOfModules.RelativeDerivation.{u + 1, u, u + 1}
      (RingedSite.Hom.inverseImageStructureSheafMap (commRingedHom f))
      (StandardSmall.comm .etale X (Ω[f.toShHom])) :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦ associatedDerivationApp f U)
    (fun _ _ i x ↦ associatedDerivationApp_naturality f i x)

/-- The canonical comparison from site-theoretic small-étale relative
differentials to the associated étale module of `Ω[f.toShHom]`, induced by
`d^a`. -/
noncomputable def associatedModuleIsoHom (f : X ⟶ Y) :
    RingedSite.Hom.relativeDifferentials.{u + 1, u} (commRingedHom f) ⟶
      StandardSmall.comm .etale X (Ω[f.toShHom]) :=
  relativeDifferentialDesc
    (RingedSite.Hom.inverseImageStructureSheafMap (commRingedHom f))
    (associatedUniversalDerivation f)

/-- Objectwise restriction of `d[commRingedHom f]` along the small
Zariski-to-étale inclusion. -/
noncomputable def zariskiRestrictedDerivationApp (f : X ⟶ Y)
    (U : (StandardTopology.Small.site .zariski X)ᵒᵖ) :
    (((commSmallEtaleToZariski X).modulePushforward.{u + 1}.obj
        (RingedSite.Hom.relativeDifferentials.{u + 1, u}
          (commRingedHom f))).val.obj U).Derivation
      ((commSmallEtaleToZariskiStructureSheafMap X).hom.app U) :=
  ModuleCat.Derivation.mk
    (fun r ↦
      (RingedSite.Hom.relativeDifferential (commRingedHom f)).d
        ((commSmallEtaleToZariskiStructureSheafMap X).hom.app U r))
    sorry sorry sorry

/-- Naturality of the restricted site-theoretic derivation. -/
theorem zariskiRestrictedDerivationApp_naturality (f : X ⟶ Y)
    {U V : (StandardTopology.Small.site .zariski X)ᵒᵖ} (i : U ⟶ V)
    (x : (StandardSmall.commStructureSheaf .zariski X).obj.obj U) :
    (zariskiRestrictedDerivationApp f V).d
        ((StandardSmall.commStructureSheaf .zariski X).obj.map i x) =
      ((commSmallEtaleToZariski X).modulePushforward.{u + 1}.obj
          (RingedSite.Hom.relativeDifferentials.{u + 1, u}
            (commRingedHom f))).val.map i
        ((zariskiRestrictedDerivationApp f U).d x) := sorry

/-- Restriction of `d[commRingedHom f]` to the small Zariski site, as a
derivation of the pushforward of the site-theoretic differentials. -/
noncomputable def zariskiRestrictedDerivation (f : X ⟶ Y) :
    SheafOfModules.RelativeDerivation.{u + 1, u, u + 1}
      (commSmallEtaleToZariskiStructureSheafMap X)
      ((commSmallEtaleToZariski X).modulePushforward.{u + 1}.obj
        (RingedSite.Hom.relativeDifferentials.{u + 1, u} (commRingedHom f))) :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦ zariskiRestrictedDerivationApp f U)
    (fun _ _ i x ↦ zariskiRestrictedDerivationApp_naturality f i x)

/-- Objectwise, the Zariski restriction of `d[commRingedHom f]` as a usual
`Y`-derivation of the inverse-image structure map of `f` on the small Zariski
site. -/
noncomputable def zariskiRestrictedYDerivationApp (f : X ⟶ Y)
    (U : (StandardTopology.Small.site .zariski X)ᵒᵖ) :
    (((commSmallEtaleToZariski X).modulePushforward.{u + 1}.obj
        (RingedSite.Hom.relativeDifferentials.{u + 1, u}
          (commRingedHom f))).val.obj U).Derivation
      ((RingedSite.Hom.inverseImageStructureSheafMap
        (zariskiCommRingedHom f)).hom.app U) :=
  ModuleCat.Derivation.mk
    (fun r ↦
      (RingedSite.Hom.relativeDifferential (commRingedHom f)).d
        ((commSmallEtaleToZariskiStructureSheafMap X).hom.app U r))
    sorry sorry sorry

/-- Naturality of the restricted usual `Y`-derivation. -/
theorem zariskiRestrictedYDerivationApp_naturality (f : X ⟶ Y)
    {U V : (StandardTopology.Small.site .zariski X)ᵒᵖ} (i : U ⟶ V)
    (x : (StandardSmall.commStructureSheaf .zariski X).obj.obj U) :
    (zariskiRestrictedYDerivationApp f V).d
        ((StandardSmall.commStructureSheaf .zariski X).obj.map i x) =
      ((commSmallEtaleToZariski X).modulePushforward.{u + 1}.obj
          (RingedSite.Hom.relativeDifferentials.{u + 1, u}
            (commRingedHom f))).val.map i
        ((zariskiRestrictedYDerivationApp f U).d x) := sorry

/-- Restriction of `d[commRingedHom f]` to the small Zariski site, as a usual
`Y`-derivation into the pushforward of the site-theoretic differentials. -/
noncomputable def zariskiRestrictedYDerivation (f : X ⟶ Y) :
    SheafOfModules.RelativeDerivation.{u + 1, u, u + 1}
      (RingedSite.Hom.inverseImageStructureSheafMap (zariskiCommRingedHom f))
      ((commSmallEtaleToZariski X).modulePushforward.{u + 1}.obj
        (RingedSite.Hom.relativeDifferentials.{u + 1, u} (commRingedHom f))) :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦ zariskiRestrictedYDerivationApp f U)
    (fun _ _ i x ↦ zariskiRestrictedYDerivationApp_naturality f i x)

/-- The map `c'` on the Zariski-site relative differentials of `f`, induced by the
restricted site-theoretic derivation.  By Remark 35.8.3 this is the usual
`Y`-derivation descent `RingedSpace.Hom.differentialDesc`. -/
noncomputable def zariskiSiteDesc (f : X ⟶ Y) :
    RingedSite.Hom.relativeDifferentials.{u + 1, u} (zariskiCommRingedHom f) ⟶
      (commSmallEtaleToZariski X).modulePushforward.{u + 1}.obj
        (RingedSite.Hom.relativeDifferentials.{u + 1, u} (commRingedHom f)) :=
  relativeDifferentialDesc
    (RingedSite.Hom.inverseImageStructureSheafMap (zariskiCommRingedHom f))
    (zariskiRestrictedYDerivation f)

/-- Objectwise, the associated Zariski derivation of `Ω[f.toShHom]` as a usual
`Y`-derivation of the inverse-image structure map of `f` on the small Zariski
site, after the comparison isomorphism of Lemma 37.9.9. -/
noncomputable def associatedZariskiYDerivationApp (f : X ⟶ Y)
    (U : (StandardTopology.Small.site .zariski X)ᵒᵖ) :
    ((StandardSmall.comm .zariski X (Ω[f.toShHom])).val.obj U).Derivation
      ((RingedSite.Hom.inverseImageStructureSheafMap
        (zariskiCommRingedHom f)).hom.app U) :=
  ModuleCat.Derivation.mk
    (fun r ↦
      ULift.up
        ((etaleComparisonInvSections f
            ((smallZariskiToSmallEtale X).obj U.unop))
          ((d[(((smallZariskiToSmallEtale X).obj U.unop).hom ≫ f).toShHom]).d
            (ULift.down r))))
    sorry sorry sorry

/-- Naturality of the associated usual `Y`-derivation on the small Zariski site. -/
theorem associatedZariskiYDerivationApp_naturality (f : X ⟶ Y)
    {U V : (StandardTopology.Small.site .zariski X)ᵒᵖ} (i : U ⟶ V)
    (x : (StandardSmall.commStructureSheaf .zariski X).obj.obj U) :
    (associatedZariskiYDerivationApp f V).d
        ((StandardSmall.commStructureSheaf .zariski X).obj.map i x) =
      (StandardSmall.comm .zariski X (Ω[f.toShHom])).val.map i
        ((associatedZariskiYDerivationApp f U).d x) := sorry

/-- The associated Zariski derivation of `Ω[f.toShHom]`, as a usual `Y`-derivation. -/
noncomputable def associatedZariskiYDerivation (f : X ⟶ Y) :
    SheafOfModules.RelativeDerivation.{u + 1, u, u + 1}
      (RingedSite.Hom.inverseImageStructureSheafMap (zariskiCommRingedHom f))
      (StandardSmall.comm .zariski X (Ω[f.toShHom])) :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦ associatedZariskiYDerivationApp f U)
    (fun _ _ i x ↦ associatedZariskiYDerivationApp_naturality f i x)

/-- Descent of the associated usual `Y`-derivation through Zariski-site relative
differentials of `f`. -/
noncomputable def associatedZariskiFromSite (f : X ⟶ Y) :
    RingedSite.Hom.relativeDifferentials.{u + 1, u} (zariskiCommRingedHom f) ⟶
      StandardSmall.comm .zariski X (Ω[f.toShHom]) :=
  relativeDifferentialDesc
    (RingedSite.Hom.inverseImageStructureSheafMap (zariskiCommRingedHom f))
    (associatedZariskiYDerivation f)

/-- The comparison `Ω[f_Zar] ⟶ (Ω_{X/Y})^a|_{X_Zar}` is an isomorphism: both
sheaves represent usual `Y`-derivations on the small Zariski site. -/
instance associatedZariskiFromSite_isIso (f : X ⟶ Y) :
    IsIso (associatedZariskiFromSite f) := sorry

/-- Transport of associated Zariski sections of `Ω[f.toShHom]` onto the
Zariski-site relative differentials, inverse to `associatedZariskiFromSite`. -/
noncomputable def associatedSiteFromZariski (f : X ⟶ Y) :
    StandardSmall.comm .zariski X (Ω[f.toShHom]) ⟶
      RingedSite.Hom.relativeDifferentials.{u + 1, u} (zariskiCommRingedHom f) :=
  CategoryTheory.inv (associatedZariskiFromSite f)

/-- The map `c' : Ω_{X/Y} → Ω_étale |_{X_Zar}` induced by the restricted
site-theoretic derivation as a usual `Y`-derivation and the representing
property of Zariski-site relative differentials, transported onto the
associated Zariski module of `Ω[f.toShHom]`. -/
noncomputable def zariskiMap (f : X ⟶ Y) :
    StandardSmall.comm .zariski X (Ω[f.toShHom]) ⟶
      (commSmallEtaleToZariski X).modulePushforward.{u + 1}.obj
        (RingedSite.Hom.relativeDifferentials.{u + 1, u} (commRingedHom f)) :=
  associatedSiteFromZariski f ≫ zariskiSiteDesc f

/-- The associated Zariski derivation of `Ω[f.toShHom]`, whose value on a Zariski
object `U` is `Γ(U, d_{U/Y})` after the comparison isomorphism of Lemma 37.9.9. -/
noncomputable def zariskiAssociatedDerivationApp (f : X ⟶ Y)
    (U : (StandardTopology.Small.site .zariski X)ᵒᵖ) :
    ((StandardSmall.comm .zariski X (Ω[f.toShHom])).val.obj U).Derivation
      ((commSmallEtaleToZariskiStructureSheafMap X).hom.app U) :=
  ModuleCat.Derivation.mk
    (fun r ↦
      ULift.up
        ((etaleComparisonInvSections f
            ((smallZariskiToSmallEtale X).obj U.unop))
          ((d[(((smallZariskiToSmallEtale X).obj U.unop).hom ≫ f).toShHom]).d
            (ULift.down r))))
    sorry sorry sorry

/-- Naturality of the associated Zariski derivation. -/
theorem zariskiAssociatedDerivationApp_naturality (f : X ⟶ Y)
    {U V : (StandardTopology.Small.site .zariski X)ᵒᵖ} (i : U ⟶ V)
    (x : (StandardSmall.commStructureSheaf .zariski X).obj.obj U) :
    (zariskiAssociatedDerivationApp f V).d
        ((StandardSmall.commStructureSheaf .zariski X).obj.map i x) =
      (StandardSmall.comm .zariski X (Ω[f.toShHom])).val.map i
        ((zariskiAssociatedDerivationApp f U).d x) := sorry

/-- The associated Zariski derivation of `Ω[f.toShHom]`. -/
noncomputable def zariskiAssociatedDerivation (f : X ⟶ Y) :
    SheafOfModules.RelativeDerivation.{u + 1, u, u + 1}
      (commSmallEtaleToZariskiStructureSheafMap X)
      (StandardSmall.comm .zariski X (Ω[f.toShHom])) :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦ zariskiAssociatedDerivationApp f U)
    (fun _ _ i x ↦ zariskiAssociatedDerivationApp_naturality f i x)

/-- Presheaf pushforward of modules along `commSmallEtaleToZariski` is a right
adjoint. -/
instance (priority := high) commSmallEtaleToZariski_presheafPushforward_isRightAdjoint
    (S : Scheme.{u}) :
    (PresheafOfModules.pushforward
      (commSmallEtaleToZariski S).structureSheafMap.hom).IsRightAdjoint := sorry

/-- Global sections of the étale comparison, transporting `U.hom^* Ω[f.toShHom]`
to `Ω[(U.hom ≫ f).toShHom]`. -/
noncomputable def etaleComparisonSections (f : X ⟶ Y) (U : X.Etale) :
    (RingedSpace.moduleGlobalSectionsFunctor U.left.toRingedSpace).obj
        ((RingedSpace.Hom.pullback U.hom.toShHom).obj Ω[f.toShHom]) ⟶
      (RingedSpace.moduleGlobalSectionsFunctor U.left.toRingedSpace).obj
        Ω[(U.hom ≫ f).toShHom] :=
  (RingedSpace.moduleGlobalSectionsFunctor U.left.toRingedSpace).map
    (etaleComparison f U)

/-- Restriction of the associated étale module of `Ω[f.toShHom]` to the small
Zariski site, by comparing pullback-section presentations on open immersions. -/
noncomputable def zariskiToEtaleRestriction (f : X ⟶ Y) :
    StandardSmall.comm .zariski X (Ω[f.toShHom]) ⟶
      (commSmallEtaleToZariski X).modulePushforward.{u + 1}.obj
        (StandardSmall.comm .etale X (Ω[f.toShHom])) :=
  ⟨{ app := fun U ↦
        ModuleCat.ofHom
          (X := (StandardSmall.comm .zariski X (Ω[f.toShHom])).val.obj U)
          (Y := ((commSmallEtaleToZariski X).modulePushforward.{u + 1}.obj
            (StandardSmall.comm .etale X (Ω[f.toShHom]))).val.obj U)
          { toFun := fun x ↦ x
            map_add' := sorry
            map_smul' := sorry }
     naturality := sorry }⟩

/-- The reverse comparison of associated Zariski and restricted associated étale
modules on open immersions. -/
noncomputable def etalePushforwardToZariski (f : X ⟶ Y) :
    (commSmallEtaleToZariski X).modulePushforward.{u + 1}.obj
      (StandardSmall.comm .etale X (Ω[f.toShHom])) ⟶
      StandardSmall.comm .zariski X (Ω[f.toShHom]) :=
  ⟨{ app := fun U ↦
        ModuleCat.ofHom
          (X := ((commSmallEtaleToZariski X).modulePushforward.{u + 1}.obj
            (StandardSmall.comm .etale X (Ω[f.toShHom]))).val.obj U)
          (Y := (StandardSmall.comm .zariski X (Ω[f.toShHom])).val.obj U)
          { toFun := fun x ↦ x
            map_add' := sorry
            map_smul' := sorry }
     naturality := sorry }⟩

/-- The adjunct of `zariskiToEtaleRestriction` along `id_small,étale,Zar`. -/
noncomputable def associatedZariskiPullbackToEtale (f : X ⟶ Y) :
    (commSmallEtaleToZariski X).modulePullback.{u + 1}.obj
      (StandardSmall.comm .zariski X (Ω[f.toShHom])) ⟶
      StandardSmall.comm .etale X (Ω[f.toShHom]) :=
  (RingedSite.Hom.modulePullbackHomEquiv.{u + 1} (commSmallEtaleToZariski X)
      (StandardSmall.comm .zariski X (Ω[f.toShHom]))
      (StandardSmall.comm .etale X (Ω[f.toShHom]))).symm
    (zariskiToEtaleRestriction f)

/-- The comparison `id^* Ω_{X/Y} ⟶ (Ω_{X/Y})^a` is an isomorphism, by the
associated-module identification along `id_small,étale,Zar`. -/
instance associatedZariskiPullbackToEtale_isIso (f : X ⟶ Y) :
    IsIso (associatedZariskiPullbackToEtale f) := sorry

/-- The inverse-image comparison `(Ω_{X/Y})^a ⟶ id^* Ω_{X/Y}` is the inverse of
the `id_small,étale,Zar`-adjunct of the identity comparison of pullback-section
presentations, which is the CommRing form of Lemma 35.8.5. -/
noncomputable def associatedEtaleToZariskiPullback (f : X ⟶ Y) :
    StandardSmall.comm .etale X (Ω[f.toShHom]) ⟶
      (commSmallEtaleToZariski X).modulePullback.{u + 1}.obj
        (StandardSmall.comm .zariski X (Ω[f.toShHom])) :=
  CategoryTheory.inv (associatedZariskiPullbackToEtale f)

/-- The CommRing form of `(Ω_{X/Y})^a = id^* Ω_{X/Y}`. -/
noncomputable def associatedEtaleIsoZariskiPullback (f : X ⟶ Y) :
    StandardSmall.comm .etale X (Ω[f.toShHom]) ≅
      (commSmallEtaleToZariski X).modulePullback.{u + 1}.obj
        (StandardSmall.comm .zariski X (Ω[f.toShHom])) where
  hom := associatedEtaleToZariskiPullback f
  inv := associatedZariskiPullbackToEtale f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The inverse comparison `c''` is the `id_small,étale,Zar`-adjunct of
`zariskiMap` after identifying `(Ω_{X/Y})^a` with `id^* Ω_{X/Y}`. -/
noncomputable def associatedModuleIsoInv (f : X ⟶ Y) :
    StandardSmall.comm .etale X (Ω[f.toShHom]) ⟶
      RingedSite.Hom.relativeDifferentials.{u + 1, u} (commRingedHom f) :=
  (associatedEtaleIsoZariskiPullback f).hom ≫
    (RingedSite.Hom.modulePullbackHomEquiv.{u + 1} (commSmallEtaleToZariski X)
      (StandardSmall.comm .zariski X (Ω[f.toShHom]))
      (RingedSite.Hom.relativeDifferentials.{u + 1, u} (commRingedHom f))).symm
      (zariskiMap f)

/-- The canonical isomorphism between the étale associated module of
`Ω[f.toShHom]` and the site-theoretic relative differentials of `f_small`. -/
noncomputable def associatedModuleIso (f : X ⟶ Y) :
    RingedSite.Hom.relativeDifferentials.{u + 1, u} (commRingedHom f) ≅
      StandardSmall.comm .etale X (Ω[f.toShHom]) where
  hom := associatedModuleIsoHom f
  inv := associatedModuleIsoInv f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `associatedModuleIso` is descent of `d^a`. -/
theorem associatedModuleIso_hom (f : X ⟶ Y) :
    (associatedModuleIso f).hom = associatedModuleIsoHom f := sorry

/-- The inverse map of `associatedModuleIso` is the Zariski-restriction adjunct. -/
theorem associatedModuleIso_inv (f : X ⟶ Y) :
    (associatedModuleIso f).inv = associatedModuleIsoInv f := sorry

/-- The comparison intertwines the site-theoretic universal derivation with the
associated étale derivation `d^a`. -/
theorem associatedModuleIso_comp_universalDerivation (f : X ⟶ Y) :
    (RingedSite.Hom.relativeDifferential (commRingedHom f)).postcomp
        (associatedModuleIso f).hom.val =
      associatedUniversalDerivation f := sorry

/-- The inverse comparison sends usual differentials of local sections of `O_X`
to the corresponding site-theoretic differentials. -/
theorem associatedModuleIsoInv_map_d (f : X ⟶ Y)
    (U : (StandardTopology.Small.site .zariski X)ᵒᵖ)
    (t : (StandardSmall.commStructureSheaf .zariski X).obj.obj U) :
    (associatedModuleIsoInv f).val.app
        ((smallZariskiToSmallEtale X).op.obj U)
        ((associatedUniversalDerivation f).d
          ((commSmallEtaleToZariskiStructureSheafMap X).hom.app U t)) =
      (RingedSite.Hom.relativeDifferential (commRingedHom f)).d
        ((commSmallEtaleToZariskiStructureSheafMap X).hom.app U t) := sorry



end AlgebraicGeometry.Scheme.Etale.Small
