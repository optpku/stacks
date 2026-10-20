module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Iso
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Cocontinuous.StructureIso
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.Module
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import stacks_project.Chap85.Lemma_85_11_1_Flat
public import stacks_project.Chap85.Lemma_85_18_1_Cartesian
public import stacks_project.Chap85.Remark_85_16_5_Ringed_variant_Shriek

/-!
# Cartesian objects of `D(O)` on a ringed total localization

An object of `D(O)` on `((C / K)_total, O)` is cartesian when every simplex-operator
comparison `L(f_φ)^* E_m ⟶ E_n` is an isomorphism. Stage restriction is the exact
derived functor of `g_n^*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Sheaf.InternalModule (underlyingApp)
open Functor Grothendieck
open RingedSite RingedSite.Hom
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget
    overSite_ι_isContinuous overSite_ι_isCocontinuous overMap overSitePrecoverage
    fiber_comp_totalForget fiber_comp_isContinuous forget_isContinuous)
variable {X : RingedSite.{u, v, w}}
variable (K : SimplicialObject (FormalCoproduct.{ι} X.carrier))
variable [UnivLE.{max u v, w}] [UnivLE.{max ι u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology K) (Type w)]
variable [HasWeakSheafify (overSiteTotalTopology X.siteTopology K) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify (overTopology X.siteTopology (K.obj (op n))) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type w,
    (totalForget K).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory, ∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
    (Grothendieck.ι (overSiteDiagram K) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology K).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology X.siteTopology (K.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w} (toAmbient K).structureMap).IsRightAdjoint]
variable [∀ n : SimplexCategory,
    (SheafOfModules.restrictScalars.{w} (stageIncl K n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (stageMap K φ).structureMap).IsRightAdjoint]

/-- Chosen derived-category structure on modules over `X`. -/
abbrev ambient_hasDerivedCategory : HasDerivedCategory (ModuleCat.{w} X) :=
  moduleCat_hasDerivedCategory X

/-- Chosen derived-category structure on modules over `((C / K)_total, O)`. -/
abbrev site_hasDerivedCategory : HasDerivedCategory (ModuleCat.{w} (site K)) :=
  moduleCat_hasDerivedCategory (site K)

/-- Chosen derived-category structure on modules over a degree-`n` localization `(C / K_n, O_n)`. -/
abbrev stage_hasDerivedCategory (n : SimplexCategory) :
    HasDerivedCategory (ModuleCat.{w} (AtSR.site (K.obj (op n)))) :=
  moduleCat_hasDerivedCategory (AtSR.site (K.obj (op n)))

/-- Module pullback along `g_n` is additive. -/
theorem stageIncl_modulePullback_additive (n : SimplexCategory) :
    ((stageIncl K n).modulePullback).Additive :=
  sorry

/-- Module pullback along `g_n` preserves finite limits, by flatness of `g_n`. -/
theorem stageIncl_modulePullback_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (stageIncl K n).modulePullback :=
  (stageIncl_modulePullback_exact K n).1

/-- Module pullback along `g_n` preserves finite colimits, by flatness of `g_n`. -/
theorem stageIncl_modulePullback_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (stageIncl K n).modulePullback :=
  (stageIncl_modulePullback_exact K n).2

/-- Module pullback along `f_φ` is additive. -/
theorem stageMap_modulePullback_additive {m n : SimplexCategory} (φ : m ⟶ n) :
    ((stageMap K φ).modulePullback).Additive :=
  sorry

/-- Module pullback along `f_φ` preserves finite limits, by flatness of `f_φ`. -/
theorem stageMap_modulePullback_preservesFiniteLimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteLimits (stageMap K φ).modulePullback :=
  (stageMap_modulePullback_exact K φ).1

/-- Module pullback along `f_φ` preserves finite colimits, by flatness of `f_φ`. -/
theorem stageMap_modulePullback_preservesFiniteColimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteColimits (stageMap K φ).modulePullback :=
  (stageMap_modulePullback_exact K φ).2

/-- Module pullback along the augmentation `a` is additive. -/
theorem toAmbient_modulePullback_additive : ((toAmbient K).modulePullback).Additive :=
  sorry

/-- Module pullback along `a` preserves finite limits, by flatness of `a`. -/
theorem toAmbient_modulePullback_preservesFiniteLimits :
    PreservesFiniteLimits (toAmbient K).modulePullback :=
  (toAmbient_modulePullback_exact K).1

/-- Module pullback along `a` preserves finite colimits, by flatness of `a`. -/
theorem toAmbient_modulePullback_preservesFiniteColimits :
    PreservesFiniteColimits (toAmbient K).modulePullback :=
  (toAmbient_modulePullback_exact K).2

/-- The bundled exact functor `g_n^*` of `O`-modules. -/
abbrev stageInclExact (n : SimplexCategory) :
    ModuleCat.{w} (site K) ⥤ₑ ModuleCat.{w} (AtSR.site (K.obj (op n))) :=
  ⟨(stageIncl K n).modulePullback, stageIncl_modulePullback_exact K n⟩

/-- The bundled exact functor `f_φ^*` of `O`-modules. -/
abbrev stageMapExact {m n : SimplexCategory} (φ : m ⟶ n) :
    ModuleCat.{w} (AtSR.site (K.obj (op m))) ⥤ₑ ModuleCat.{w} (AtSR.site (K.obj (op n))) :=
  ⟨(stageMap K φ).modulePullback, stageMap_modulePullback_exact K φ⟩

/-- The bundled exact functor `a^*` of `O_C`-modules. -/
abbrev toAmbientExact :
    ModuleCat.{w} X ⥤ₑ ModuleCat.{w} (site K) :=
  ⟨(toAmbient K).modulePullback, toAmbient_modulePullback_exact K⟩

/-- Cocontinuous inverse image along `a` is isomorphic to continuous restriction. -/
def toAmbient_cocontinuousContinuousIso :
    (totalForget K).sheafPullbackCocontinuous (Type w)
        (overSiteTotalTopology X.siteTopology K) X.siteTopology ≅
      (totalForget K).sheafPushforwardContinuous (Type w)
        (overSiteTotalTopology X.siteTopology K) X.siteTopology :=
  NatIso.ofComponents
    (fun F ↦
      { hom :=
          CocontinuousPullback.comparisonApp (totalForget K)
            (overSiteTotalTopology X.siteTopology K) X.siteTopology F
        inv :=
          (((totalForget K).sheafPushforwardContinuous (Type w)
                (overSiteTotalTopology X.siteTopology K) X.siteTopology).map
              (sheafificationIso F).hom) ≫
            ((totalForget K).pushforwardContinuousSheafificationCompatibility (Type w)
                (overSiteTotalTopology X.siteTopology K) X.siteTopology).inv.app F.obj
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The localization functor of `K_n` is continuous. -/
theorem stageForget_isContinuous (n : SimplexCategory) :
    (SemiRepresentableFamily.forget (K.obj (op n))).IsContinuous
      (overTopology X.siteTopology (K.obj (op n))) X.siteTopology :=
  SemiRepresentableFamily.forget_isContinuous X.siteTopology (K.obj (op n))

/-- Restriction of scalars along the structure map of `a` does not change the
underlying type-valued sheaf of `a^* M`. -/
def toAmbient_modulePullback_restrictScalars_underlyingIso
    (M : SheafOfModules.{w} X.structureSheaf) :
    (Sheaf.InternalModule.ToInternal.underlying (site K).structureSheaf).obj
        ((toAmbient K).modulePullback.obj M) ≅
      (Sheaf.InternalModule.ToInternal.underlying
          ((toAmbient K).toTopos.ringInverseImage.obj X.structureSheaf)).obj
        ((SheafOfModules.restrictScalars (toAmbient K).structureMap).obj
          ((toAmbient K).modulePullback.obj M)) :=
  (fullyFaithfulSheafToPresheaf (site K).siteTopology (Type w)).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry)

/-- The scalar-extension unit comparing geometric inverse image with `a^*`. -/
def toAmbient_modulePullback_scalarUnit (M : SheafOfModules.{w} X.structureSheaf) :
    ((toAmbient K).toTopos.moduleInverseImage X.structureSheaf).obj M ⟶
      (SheafOfModules.restrictScalars (toAmbient K).structureMap).obj
        ((toAmbient K).modulePullback.obj M) :=
  (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
      (toAmbient K).structureMap).unit.app
    (((toAmbient K).toTopos.moduleInverseImage X.structureSheaf).obj M)

/-- The specified inverse-image structure ring with its actual reverse map. -/
def toAmbient_structureMapIso :
    (toAmbient K).toTopos.ringInverseImage.obj X.structureSheaf ≅ (site K).structureSheaf :=
  @Cocontinuous.structureMapIso (site K) X (totalForget K)
    (totalForget_isCocontinuous_site K) inferInstance inferInstance
    inferInstance inferInstance (Iso.refl _)

/-- This structure-ring isomorphism retains the original structure map. -/
@[simp]
theorem toAmbient_structureMapIso_hom :
    (toAmbient_structureMapIso K).hom = (toAmbient K).structureMap := rfl

/-- The original scalar-extension unit with its actual inverse, obtained by
reverse restriction along the displayed structure-ring isomorphism. -/
def toAmbient_modulePullback_scalarUnitIso
    (M : SheafOfModules.{w} X.structureSheaf) :
    ((toAmbient K).toTopos.moduleInverseImage X.structureSheaf).obj M ≅
      (SheafOfModules.restrictScalars (toAmbient K).structureMap).obj
        ((toAmbient K).modulePullback.obj M) :=
  @SheafOfModules.ChangeOfRings.extendRestrictUnitIso _ _ _ _ _
    (toAmbient_structureMapIso K)
    (inferInstance : (SheafOfModules.restrictScalars.{w}
      (toAmbient K).structureMap).IsRightAdjoint)
    (((toAmbient K).toTopos.moduleInverseImage X.structureSheaf).obj M)

/-- The displayed unit isomorphism has the original unit as its forward map. -/
@[simp]
theorem toAmbient_modulePullback_scalarUnitIso_hom
    (M : SheafOfModules.{w} X.structureSheaf) :
    (toAmbient_modulePullback_scalarUnitIso K M).hom =
      toAmbient_modulePullback_scalarUnit K M := rfl

/-- The scalar-extension unit of `a` is an isomorphism. -/
theorem toAmbient_modulePullback_scalarUnit_isIso
    (M : SheafOfModules.{w} X.structureSheaf) :
    IsIso (toAmbient_modulePullback_scalarUnit K M) :=
  (toAmbient_modulePullback_scalarUnitIso K M).isIso_hom

/-- Underlying type-valued sheaves identify `a^*` with continuous inverse image along
`totalForget`. -/
def toAmbient_modulePullback_underlyingIso (M : SheafOfModules.{w} X.structureSheaf) :
    (Sheaf.InternalModule.ToInternal.underlying (site K).structureSheaf).obj
        ((toAmbient K).modulePullback.obj M) ≅
      ((totalForget K).sheafPushforwardContinuous (Type w)
          (overSiteTotalTopology X.siteTopology K) X.siteTopology).obj
        ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M) :=
  toAmbient_modulePullback_restrictScalars_underlyingIso K M ≪≫
    ((Sheaf.InternalModule.ToInternal.underlying
        ((toAmbient K).toTopos.ringInverseImage.obj X.structureSheaf)).mapIso
      (toAmbient_modulePullback_scalarUnitIso K M)).symm ≪≫
    ((toAmbient K).toTopos.moduleInverseImageForgetIso X.structureSheaf).app M ≪≫
      (toAmbient_cocontinuousContinuousIso K).app
        ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M)

/-- Underlying type-valued sheaves of geometric inverse image along `totalForget`. -/
def toAmbient_moduleInverseImage_underlyingIso (M : SheafOfModules.{w} X.structureSheaf) :
    (Sheaf.InternalModule.ToInternal.underlying (site K).structureSheaf).obj
        ((Cocontinuous.moduleInverseImage
        (J := overSiteTotalTopology X.siteTopology K) (totalForget K) X.structureSheaf).obj M) ≅
      ((totalForget K).sheafPushforwardContinuous (Type w)
          (overSiteTotalTopology X.siteTopology K) X.siteTopology).obj
        ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M) :=
  (fullyFaithfulSheafToPresheaf (site K).siteTopology (Type w)).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry)

/-- The specified underlying-sheaf comparison between the two canonical module pullbacks. -/
def toAmbient_modulePullback_underlyingNatIso :
    (toAmbient K).modulePullback ⋙
        Sheaf.InternalModule.ToInternal.underlying (site K).structureSheaf ≅
      Cocontinuous.moduleInverseImage
        (J := overSiteTotalTopology X.siteTopology K) (totalForget K) X.structureSheaf ⋙
        Sheaf.InternalModule.ToInternal.underlying (site K).structureSheaf :=
  NatIso.ofComponents
    (fun M ↦
      toAmbient_modulePullback_underlyingIso K M ≪≫
        (toAmbient_moduleInverseImage_underlyingIso K M).symm)
    sorry

/-- The specified canonical comparison preserves addition in its target module structure. -/
theorem toAmbient_modulePullback_underlyingNatIso_add (M : SheafOfModules.{w} X.structureSheaf)
    (U : (Grothendieck (overSiteDiagram K))ᵒᵖ)
    (x y : ((toAmbient K).modulePullback.obj M).val.obj U) :
    underlyingApp (site K).structureSheaf
      ((toAmbient_modulePullback_underlyingNatIso K).hom.app M) U (x + y) =
      underlyingApp (site K).structureSheaf
        ((toAmbient_modulePullback_underlyingNatIso K).hom.app M) U x +
        underlyingApp (site K).structureSheaf
          ((toAmbient_modulePullback_underlyingNatIso K).hom.app M) U y :=
  sorry

/-- The specified canonical comparison preserves the target ring's scalar action. -/
theorem toAmbient_modulePullback_underlyingNatIso_smul (M : SheafOfModules.{w} X.structureSheaf)
    (U : (Grothendieck (overSiteDiagram K))ᵒᵖ) (r : (site K).structureSheaf.obj.obj U)
    (x : ((toAmbient K).modulePullback.obj M).val.obj U) :
    underlyingApp (site K).structureSheaf
      ((toAmbient_modulePullback_underlyingNatIso K).hom.app M) U (r • x) =
      r • underlyingApp (site K).structureSheaf
        ((toAmbient_modulePullback_underlyingNatIso K).hom.app M) U x :=
  sorry

/-- Module pullback along `a` identifies with geometric inverse image along `totalForget`. -/
def toAmbient_modulePullbackIso :
    (toAmbient K).modulePullback ≅
      Cocontinuous.moduleInverseImage
        (J := overSiteTotalTopology X.siteTopology K) (totalForget K) X.structureSheaf :=
  Sheaf.InternalModule.functorIsoOfUnderlying (site K).structureSheaf
    (toAmbient_modulePullback_underlyingNatIso K)
    (toAmbient_modulePullback_underlyingNatIso_add K)
    (toAmbient_modulePullback_underlyingNatIso_smul K)

/-- The forward map of `toAmbient_modulePullbackIso` is the underlying comparison lift. -/
theorem toAmbient_modulePullbackIso_hom (M : SheafOfModules.{w} X.structureSheaf) :
    (Sheaf.InternalModule.ToInternal.underlying (site K).structureSheaf).map
        ((toAmbient_modulePullbackIso K).hom.app M) =
      (toAmbient_modulePullback_underlyingIso K M).hom ≫
        (toAmbient_moduleInverseImage_underlyingIso K M).inv :=
  sorry

/-- Restriction of scalars along the structure map of `g_n` does not change the
underlying type-valued sheaf of `g_n^*`. -/
def stageIncl_modulePullback_restrictScalars_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} (ringSheaf K)) :
    (Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n)))).obj
        ((stageIncl K n).modulePullback.obj M) ≅
      (Sheaf.InternalModule.ToInternal.underlying
          ((stageIncl K n).toTopos.ringInverseImage.obj (ringSheaf K))).obj
        ((SheafOfModules.restrictScalars (stageIncl K n).structureMap).obj
          ((stageIncl K n).modulePullback.obj M)) :=
  (fullyFaithfulSheafToPresheaf (overTopology X.siteTopology (K.obj (op n))) (Type w)).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry)

/-- The scalar-extension unit comparing geometric inverse image with `g_n^*`. -/
def stageIncl_modulePullback_scalarUnit (n : SimplexCategory)
    (M : SheafOfModules.{w} (ringSheaf K)) :
    ((stageIncl K n).toTopos.moduleInverseImage (ringSheaf K)).obj M ⟶
      (SheafOfModules.restrictScalars (stageIncl K n).structureMap).obj
        ((stageIncl K n).modulePullback.obj M) :=
  (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
      (stageIncl K n).structureMap).unit.app
    (((stageIncl K n).toTopos.moduleInverseImage (ringSheaf K)).obj M)

/-- The specified inverse-image structure ring with its actual reverse map. -/
def stageIncl_structureMapIso (n : SimplexCategory) :
    (stageIncl K n).toTopos.ringInverseImage.obj (ringSheaf K) ≅ (AtSR.site (K.obj (op n))).structureSheaf :=
  @Cocontinuous.structureMapIso (AtSR.site (K.obj (op n))) (site K)
    (Grothendieck.ι (overSiteDiagram K) (op n)) (stageIncl_isCocontinuous K n)
    inferInstance inferInstance inferInstance inferInstance
    ((sheafToPresheaf (overTopology X.siteTopology (K.obj (op n))) RingCat.{w}).mapIso
      (stageRingIso K n).symm)

/-- This structure-ring isomorphism retains the original structure map. -/
@[simp]
theorem stageIncl_structureMapIso_hom (n : SimplexCategory) :
    (stageIncl_structureMapIso K n).hom = (stageIncl K n).structureMap := rfl

/-- The original scalar-extension unit with its actual inverse, obtained by
reverse restriction along the displayed structure-ring isomorphism. -/
def stageIncl_modulePullback_scalarUnitIso (n : SimplexCategory)
    (M : SheafOfModules.{w} (ringSheaf K)) :
    ((stageIncl K n).toTopos.moduleInverseImage (ringSheaf K)).obj M ≅
      (SheafOfModules.restrictScalars (stageIncl K n).structureMap).obj
        ((stageIncl K n).modulePullback.obj M) :=
  @SheafOfModules.ChangeOfRings.extendRestrictUnitIso _ _ _ _ _
    (stageIncl_structureMapIso K n)
    (inferInstance : (SheafOfModules.restrictScalars.{w}
      (stageIncl K n).structureMap).IsRightAdjoint)
    (((stageIncl K n).toTopos.moduleInverseImage (ringSheaf K)).obj M)

/-- The displayed unit isomorphism has the original unit as its forward map. -/
@[simp]
theorem stageIncl_modulePullback_scalarUnitIso_hom (n : SimplexCategory)
    (M : SheafOfModules.{w} (ringSheaf K)) :
    (stageIncl_modulePullback_scalarUnitIso K n M).hom =
      stageIncl_modulePullback_scalarUnit K n M := rfl

/-- The scalar-extension unit of `g_n` is an isomorphism. -/
theorem stageIncl_modulePullback_scalarUnit_isIso (n : SimplexCategory)
    (M : SheafOfModules.{w} (ringSheaf K)) :
    IsIso (stageIncl_modulePullback_scalarUnit K n M) :=
  (stageIncl_modulePullback_scalarUnitIso K n M).isIso_hom

/-- Underlying type-valued sheaves identify `g_n^*` with continuous restriction along `ι`. -/
def stageIncl_modulePullback_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} (ringSheaf K)) :
    (Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n)))).obj
        ((stageIncl K n).modulePullback.obj M) ≅
      (typeComponent K n).obj
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K)).obj M) :=
  stageIncl_modulePullback_restrictScalars_underlyingIso K n M ≪≫
    ((Sheaf.InternalModule.ToInternal.underlying
        ((stageIncl K n).toTopos.ringInverseImage.obj (ringSheaf K))).mapIso
      (stageIncl_modulePullback_scalarUnitIso K n M)).symm ≪≫
    moduleInverseImage_underlyingIso K M n

/-- Sequential pushforward along `j_total` then `ι` is pushforward along `ι ⋙ j_total`. -/
def fiberComp_sheafPushforwardCompIso (n : SimplexCategory) :
    (totalForget K).sheafPushforwardContinuous (Type w)
        (overSiteTotalTopology X.siteTopology K) X.siteTopology ⋙ typeComponent K n ≅
      (Grothendieck.ι (overSiteDiagram K) (op n) ⋙ totalForget K).sheafPushforwardContinuous
        (Type w) (overTopology X.siteTopology (K.obj (op n))) X.siteTopology :=
  @sheafPushforwardContinuousComp _ _ _ _ _ _
    (Grothendieck.ι (overSiteDiagram K) (op n)) (totalForget K) (Type w) _
    (overTopology X.siteTopology (K.obj (op n)))
    (overSiteTotalTopology X.siteTopology K) X.siteTopology
    inferInstance inferInstance

/-- Fiber inclusion then `j_total` pushforward identifies with localization at `K_n`. -/
def fiberComp_sheafPushforwardIso (n : SimplexCategory) :
    (totalForget K).sheafPushforwardContinuous (Type w)
        (overSiteTotalTopology X.siteTopology K) X.siteTopology ⋙ typeComponent K n ≅
      (SemiRepresentableFamily.forget (K.obj (op n))).sheafPushforwardContinuous (Type w)
        (overTopology X.siteTopology (K.obj (op n))) X.siteTopology :=
  fiberComp_sheafPushforwardCompIso K n ≪≫
    { hom :=
        @sheafPushforwardContinuousNatTrans _ _ _ _ _ _
          (fiber_comp_totalForget K n).inv (Type w) _
          (overTopology X.siteTopology (K.obj (op n))) X.siteTopology
          (stageForget_isContinuous K n) (fiber_comp_isContinuous X.siteTopology K n)
      inv :=
        @sheafPushforwardContinuousNatTrans _ _ _ _ _ _
          (fiber_comp_totalForget K n).hom (Type w) _
          (overTopology X.siteTopology (K.obj (op n))) X.siteTopology
          (fiber_comp_isContinuous X.siteTopology K n) (stageForget_isContinuous K n)
      hom_inv_id := sorry
      inv_hom_id := sorry }

/-- Underlying type-valued sheaves of geometric inverse image along `j_n`. -/
def stageForget_moduleInverseImage_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} X.structureSheaf) :
    (Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n)))).obj
        ((Cocontinuous.moduleInverseImage
            (SemiRepresentableFamily.forget (K.obj (op n))) X.structureSheaf).obj M) ≅
      ((SemiRepresentableFamily.forget (K.obj (op n))).sheafPushforwardContinuous (Type w)
          (overTopology X.siteTopology (K.obj (op n))) X.siteTopology).obj
        ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M) :=
  (fullyFaithfulSheafToPresheaf (overTopology X.siteTopology (K.obj (op n))) (Type w)).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry)

/-- The specified underlying-sheaf comparison between the two canonical module pullbacks. -/
def toAmbient_comp_stageIncl_underlyingNatIso (n : SimplexCategory) :
    ((toAmbient K).modulePullback ⋙ (stageIncl K n).modulePullback) ⋙
        Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n))) ≅
      (Cocontinuous.moduleInverseImage
        (SemiRepresentableFamily.forget (K.obj (op n))) X.structureSheaf) ⋙
          Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n))) :=
  NatIso.ofComponents
    (fun M ↦
      stageIncl_modulePullback_underlyingIso K n ((toAmbient K).modulePullback.obj M) ≪≫
        (typeComponent K n).mapIso (toAmbient_modulePullback_underlyingIso K M) ≪≫
          (fiberComp_sheafPushforwardIso K n).app
            ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M) ≪≫
            (stageForget_moduleInverseImage_underlyingIso K n M).symm)
    sorry

/-- The specified canonical comparison preserves addition in its target module structure. -/
theorem toAmbient_comp_stageIncl_underlyingNatIso_add (n : SimplexCategory)
    (M : SheafOfModules.{w} X.structureSheaf)
    (U : (OverSite (K.obj (op n)))ᵒᵖ)
    (x y : ((stageIncl K n).modulePullback.obj ((toAmbient K).modulePullback.obj M)).val.obj U) :
    underlyingApp (AtSR.ringSheaf (K.obj (op n)))
      ((toAmbient_comp_stageIncl_underlyingNatIso K n).hom.app M) U (x + y) =
      underlyingApp (AtSR.ringSheaf (K.obj (op n)))
        ((toAmbient_comp_stageIncl_underlyingNatIso K n).hom.app M) U x +
        underlyingApp (AtSR.ringSheaf (K.obj (op n)))
          ((toAmbient_comp_stageIncl_underlyingNatIso K n).hom.app M) U y :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- The specified canonical comparison preserves the target ring's scalar action. -/
theorem toAmbient_comp_stageIncl_underlyingNatIso_smul (n : SimplexCategory)
    (M : SheafOfModules.{w} X.structureSheaf)
    (U : (OverSite (K.obj (op n)))ᵒᵖ) (r : (AtSR.site (K.obj (op n))).structureSheaf.obj.obj U)
    (x : ((stageIncl K n).modulePullback.obj ((toAmbient K).modulePullback.obj M)).val.obj U) :
    underlyingApp (AtSR.ringSheaf (K.obj (op n)))
      ((toAmbient_comp_stageIncl_underlyingNatIso K n).hom.app M) U (r • x) =
      r • underlyingApp (AtSR.ringSheaf (K.obj (op n)))
        ((toAmbient_comp_stageIncl_underlyingNatIso K n).hom.app M) U x :=
  sorry

/-- Sequential pullback along `a` then `g_n` identifies with inverse image along
the degree-`n` localization functor `C / K_n ⥤ C`. -/
def toAmbient_comp_stageInclIso (n : SimplexCategory) :
    (toAmbient K).modulePullback ⋙ (stageIncl K n).modulePullback ≅
      Cocontinuous.moduleInverseImage
        (SemiRepresentableFamily.forget (K.obj (op n))) X.structureSheaf :=
  Sheaf.InternalModule.functorIsoOfUnderlying (AtSR.ringSheaf (K.obj (op n)))
    (toAmbient_comp_stageIncl_underlyingNatIso K n)
    (toAmbient_comp_stageIncl_underlyingNatIso_add K n)
    (toAmbient_comp_stageIncl_underlyingNatIso_smul K n)

/-- `toAmbient_comp_stageInclIso` is the underlying-sheaf lift of `fiber_comp_totalForget`. -/
theorem toAmbient_comp_stageInclIso_hom (n : SimplexCategory)
    (M : SheafOfModules.{w} X.structureSheaf) :
    (Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n)))).map
        ((toAmbient_comp_stageInclIso K n).hom.app M) =
      (stageIncl_modulePullback_underlyingIso K n ((toAmbient K).modulePullback.obj M)).hom ≫
        (typeComponent K n).map (toAmbient_modulePullback_underlyingIso K M).hom ≫
          (fiberComp_sheafPushforwardIso K n).hom.app
            ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M) ≫
            (stageForget_moduleInverseImage_underlyingIso K n M).inv :=
  sorry

/-- Restriction of scalars along the structure map of `f_φ` does not change the
underlying type-valued sheaf of `f_φ^*`. -/
def stageMap_modulePullback_restrictScalars_underlyingIso {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (AtSR.ringSheaf (K.obj (op m)))) :
    (Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n)))).obj
        ((stageMap K φ).modulePullback.obj M) ≅
      (Sheaf.InternalModule.ToInternal.underlying
          ((stageMap K φ).toTopos.ringInverseImage.obj (AtSR.ringSheaf (K.obj (op m))))).obj
        ((SheafOfModules.restrictScalars (stageMap K φ).structureMap).obj
          ((stageMap K φ).modulePullback.obj M)) :=
  (fullyFaithfulSheafToPresheaf (overTopology X.siteTopology (K.obj (op n))) (Type w)).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry)

/-- The scalar-extension unit comparing geometric inverse image with `f_φ^*`. -/
def stageMap_modulePullback_scalarUnit {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (AtSR.ringSheaf (K.obj (op m)))) :
    ((stageMap K φ).toTopos.moduleInverseImage (AtSR.ringSheaf (K.obj (op m)))).obj M ⟶
      (SheafOfModules.restrictScalars (stageMap K φ).structureMap).obj
        ((stageMap K φ).modulePullback.obj M) :=
  (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
      (stageMap K φ).structureMap).unit.app
    (((stageMap K φ).toTopos.moduleInverseImage (AtSR.ringSheaf (K.obj (op m)))).obj M)

/-- The specified inverse-image structure ring with its actual reverse map. -/
def stageMap_structureMapIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageMap K φ).toTopos.ringInverseImage.obj (AtSR.ringSheaf (K.obj (op m))) ≅ (AtSR.site (K.obj (op n))).structureSheaf :=
  @Cocontinuous.structureMapIso (AtSR.site (K.obj (op n))) (AtSR.site (K.obj (op m)))
    (overMap (K.map φ.op)) (AtSR.overMap_isCocontinuous_site (K.map φ.op))
    inferInstance inferInstance inferInstance inferInstance
    ((sheafToPresheaf (overTopology X.siteTopology (K.obj (op n))) RingCat.{w}).mapIso
      (AtSR.mapRingSheafIso (K.map φ.op)).symm)

/-- This structure-ring isomorphism retains the original structure map. -/
@[simp]
theorem stageMap_structureMapIso_hom {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageMap_structureMapIso K φ).hom = (stageMap K φ).structureMap := rfl

/-- The original scalar-extension unit with its actual inverse, obtained by
reverse restriction along the displayed structure-ring isomorphism. -/
def stageMap_modulePullback_scalarUnitIso {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (AtSR.ringSheaf (K.obj (op m)))) :
    ((stageMap K φ).toTopos.moduleInverseImage (AtSR.ringSheaf (K.obj (op m)))).obj M ≅
      (SheafOfModules.restrictScalars (stageMap K φ).structureMap).obj
        ((stageMap K φ).modulePullback.obj M) :=
  @SheafOfModules.ChangeOfRings.extendRestrictUnitIso _ _ _ _ _
    (stageMap_structureMapIso K φ)
    (inferInstance : (SheafOfModules.restrictScalars.{w}
      (stageMap K φ).structureMap).IsRightAdjoint)
    (((stageMap K φ).toTopos.moduleInverseImage (AtSR.ringSheaf (K.obj (op m)))).obj M)

/-- The displayed unit isomorphism has the original unit as its forward map. -/
@[simp]
theorem stageMap_modulePullback_scalarUnitIso_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (AtSR.ringSheaf (K.obj (op m)))) :
    (stageMap_modulePullback_scalarUnitIso K φ M).hom =
      stageMap_modulePullback_scalarUnit K φ M := rfl

/-- The scalar-extension unit of `f_φ` is an isomorphism. -/
theorem stageMap_modulePullback_scalarUnit_isIso {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (AtSR.ringSheaf (K.obj (op m)))) :
    IsIso (stageMap_modulePullback_scalarUnit K φ M) :=
  (stageMap_modulePullback_scalarUnitIso K φ M).isIso_hom

/-- Underlying type-valued sheaves identify `f_φ^*` with continuous restriction along `overMap`. -/
def stageMap_modulePullback_underlyingIso {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (AtSR.ringSheaf (K.obj (op m)))) :
    (Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n)))).obj
        ((stageMap K φ).modulePullback.obj M) ≅
      ((overMap (K.map φ.op)).sheafPushforwardContinuous (Type w)
          (overTopology X.siteTopology (K.obj (op n)))
          (overTopology X.siteTopology (K.obj (op m)))).obj
        ((Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op m)))).obj M) :=
  stageMap_modulePullback_restrictScalars_underlyingIso K φ M ≪≫
    ((Sheaf.InternalModule.ToInternal.underlying
        ((stageMap K φ).toTopos.ringInverseImage.obj (AtSR.ringSheaf (K.obj (op m))))).mapIso
      (stageMap_modulePullback_scalarUnitIso K φ M)).symm ≪≫
    ((stageMap K φ).toTopos.moduleInverseImageForgetIso
        (AtSR.ringSheaf (K.obj (op m)))).app M ≪≫
      (stageMap_cocontinuousContinuousIso K φ).app
        ((Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op m)))).obj M)

/-- Underlying type-valued sheaves of inverse image along an SR-morphism. -/
def mapModulePullback_underlyingIso {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (AtSR.ringSheaf (K.obj (op m)))) :
    (Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n)))).obj
        ((AtSR.mapModulePullback (K.map φ.op)).obj M) ≅
      ((overMap (K.map φ.op)).sheafPushforwardContinuous (Type w)
          (overTopology X.siteTopology (K.obj (op n)))
          (overTopology X.siteTopology (K.obj (op m)))).obj
        ((Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op m)))).obj M) :=
  (fullyFaithfulSheafToPresheaf (overTopology X.siteTopology (K.obj (op n))) (Type w)).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry)

/-- The specified underlying-sheaf comparison between the two canonical module pullbacks. -/
def stageMap_mapModulePullback_underlyingNatIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageMap K φ).modulePullback ⋙
        Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n))) ≅
      AtSR.mapModulePullback (K.map φ.op) ⋙
        Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n))) :=
  NatIso.ofComponents
    (fun M ↦
      stageMap_modulePullback_underlyingIso K φ M ≪≫
        (mapModulePullback_underlyingIso K φ M).symm)
    sorry

/-- The specified canonical comparison preserves addition in its target module structure. -/
theorem stageMap_mapModulePullback_underlyingNatIso_add {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (AtSR.ringSheaf (K.obj (op m))))
    (U : (OverSite (K.obj (op n)))ᵒᵖ)
    (x y : ((stageMap K φ).modulePullback.obj M).val.obj U) :
    underlyingApp (AtSR.ringSheaf (K.obj (op n)))
      ((stageMap_mapModulePullback_underlyingNatIso K φ).hom.app M) U (x + y) =
      underlyingApp (AtSR.ringSheaf (K.obj (op n)))
        ((stageMap_mapModulePullback_underlyingNatIso K φ).hom.app M) U x +
        underlyingApp (AtSR.ringSheaf (K.obj (op n)))
          ((stageMap_mapModulePullback_underlyingNatIso K φ).hom.app M) U y :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- The specified canonical comparison preserves the target ring's scalar action. -/
theorem stageMap_mapModulePullback_underlyingNatIso_smul {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (AtSR.ringSheaf (K.obj (op m))))
    (U : (OverSite (K.obj (op n)))ᵒᵖ) (r : (AtSR.site (K.obj (op n))).structureSheaf.obj.obj U)
    (x : ((stageMap K φ).modulePullback.obj M).val.obj U) :
    underlyingApp (AtSR.ringSheaf (K.obj (op n)))
      ((stageMap_mapModulePullback_underlyingNatIso K φ).hom.app M) U (r • x) =
      r • underlyingApp (AtSR.ringSheaf (K.obj (op n)))
        ((stageMap_mapModulePullback_underlyingNatIso K φ).hom.app M) U x :=
  sorry

/-- Module pullback along `f_φ` identifies with the explicit SR-morphism inverse image. -/
def stageMap_mapModulePullbackIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageMap K φ).modulePullback ≅
      AtSR.mapModulePullback (K.map φ.op) :=
  Sheaf.InternalModule.functorIsoOfUnderlying (AtSR.ringSheaf (K.obj (op n)))
    (stageMap_mapModulePullback_underlyingNatIso K φ)
    (stageMap_mapModulePullback_underlyingNatIso_add K φ)
    (stageMap_mapModulePullback_underlyingNatIso_smul K φ)

/-- The forward map of `stageMap_mapModulePullbackIso` is the underlying comparison lift. -/
theorem stageMap_mapModulePullbackIso_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (AtSR.ringSheaf (K.obj (op m)))) :
    (Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n)))).map
        ((stageMap_mapModulePullbackIso K φ).hom.app M) =
      (stageMap_modulePullback_underlyingIso K φ M).hom ≫
        (mapModulePullback_underlyingIso K φ M).inv :=
  sorry

namespace ModuleDerived

/-- Restriction of an object of `D(O)` to the degree-`n` site, i.e. `E_n = Lg_n^* E`. -/
abbrev moduleDerivedComponent (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (site K) ⥤ Hom.ModuleDerived.{w} (AtSR.site (K.obj (op n))) :=
  (@ExactFunctor.mapDerivedCategory _ _ _ (site_hasDerivedCategory K)
      _ _ _ (stage_hasDerivedCategory K n) (stageInclExact K n))

/-- `moduleDerivedComponent n` is the exact derived functor of module pullback along `g_n`. -/
theorem moduleDerivedComponent_eq (n : SimplexCategory) :
    moduleDerivedComponent K n = (@ExactFunctor.mapDerivedCategory _ _ _ (site_hasDerivedCategory K)
      _ _ _ (stage_hasDerivedCategory K n) (stageInclExact K n)) :=
  rfl

/-- Derived inverse image `La^*` along the ringed augmentation `a`. -/
abbrev toAmbientDerived :
    Hom.ModuleDerived.{w} X ⥤ Hom.ModuleDerived.{w} (site K) :=
  (@ExactFunctor.mapDerivedCategory _ _ _ (ambient_hasDerivedCategory (X := X))
      _ _ _ (site_hasDerivedCategory K) (toAmbientExact K))

/-- `toAmbientDerived` is the exact derived functor of module pullback along `a`. -/
theorem toAmbientDerived_eq :
    toAmbientDerived K = (@ExactFunctor.mapDerivedCategory _ _ _ (ambient_hasDerivedCategory (X := X))
      _ _ _ (site_hasDerivedCategory K) (toAmbientExact K)) :=
  rfl

/-- The underived simplex-operator comparison as a natural transformation
`g_m^* ⋙ f_φ^* ⟶ g_n^*`. -/
def moduleTransitionNatTrans {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageIncl K m).modulePullback ⋙ (stageMap K φ).modulePullback ⟶
      (stageIncl K n).modulePullback where
  app F := moduleTransition K φ F
  naturality := sorry

/-- The component of `moduleTransitionNatTrans` at a module sheaf `F` is `moduleTransition φ F`. -/
theorem moduleTransitionNatTrans_app {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (ringSheaf K)) :
    (moduleTransitionNatTrans K φ).app F = moduleTransition K φ F :=
  sorry

/-- The bundled exact-functor morphism underlying `moduleTransitionNatTrans`. -/
def moduleTransitionExact {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageInclExact K m).comp (stageMapExact K φ) ⟶ stageInclExact K n where
  hom := moduleTransitionNatTrans K φ

/-- The derived comparison `L(f_φ)^* E_m ⟶ E_n` of objects of `D(O)`. -/
def moduleDerivedTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (E : Hom.ModuleDerived.{w} (site K)) :
    (@ExactFunctor.mapDerivedCategory _ _ _ (stage_hasDerivedCategory K m)
      _ _ _ (stage_hasDerivedCategory K n) (stageMapExact K φ)).obj ((moduleDerivedComponent K m).obj E) ⟶
      (moduleDerivedComponent K n).obj E :=
  (@ExactFunctor.MapDerivedCategory.compFunctorIso
      _ _ _ (site_hasDerivedCategory K)
      _ _ _ (stage_hasDerivedCategory K m)
      _ _ _ (stage_hasDerivedCategory K n)
      (stageInclExact K m) (stageMapExact K φ)).inv.app E ≫
    (@ExactFunctor.MapDerivedCategory.map
      _ _ _ (site_hasDerivedCategory K)
      _ _ _ (stage_hasDerivedCategory K n) _ _ (moduleTransitionExact K φ)).app E

/-- `moduleDerivedTransition` is the derived functor of `moduleTransitionNatTrans` after the
exact-functor composition comparison. -/
theorem moduleDerivedTransition_eq {m n : SimplexCategory} (φ : m ⟶ n)
    (E : Hom.ModuleDerived.{w} (site K)) :
    moduleDerivedTransition K φ E =
      (@ExactFunctor.MapDerivedCategory.compFunctorIso
      _ _ _ (site_hasDerivedCategory K)
      _ _ _ (stage_hasDerivedCategory K m)
      _ _ _ (stage_hasDerivedCategory K n)
          (stageInclExact K m) (stageMapExact K φ)).inv.app E ≫
        (@ExactFunctor.MapDerivedCategory.map
      _ _ _ (site_hasDerivedCategory K)
      _ _ _ (stage_hasDerivedCategory K n) _ _ (moduleTransitionExact K φ)).app E :=
  sorry

/-- An object of `D(O)` on `((C / K)_total, O)` is cartesian when the simplex-operator
comparison `L(f_φ)^* E_m ⟶ E_n` is an isomorphism for every simplex operator `φ`. -/
class IsCartesian (E : Hom.ModuleDerived.{w} (site K)) : Prop where
  /-- Every simplex-operator comparison `L(f_φ)^* E_m ⟶ E_n` is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (moduleDerivedTransition K φ E)

/-- Cartesianness of an object of `D(O)` is equivalent to every simplex-operator comparison
being an isomorphism. -/
theorem isCartesian_iff (E : Hom.ModuleDerived.{w} (site K)) :
    IsCartesian K E ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (moduleDerivedTransition K φ E) :=
  sorry

/-- An object of `D(O)` whose every simplex-operator comparison is an isomorphism is cartesian. -/
theorem instIsCartesian_of_isIso (E : Hom.ModuleDerived.{w} (site K))
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (moduleDerivedTransition K φ E)] :
    IsCartesian K E :=
  ⟨h⟩

/-- Every simplex-operator derived comparison of a cartesian object of `D(O)` is an isomorphism. -/
theorem instIsIso_moduleDerivedTransition (E : Hom.ModuleDerived.{w} (site K))
    [IsCartesian K E] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (moduleDerivedTransition K φ E) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `L(f_φ)^* E_m ≅ E_n` attached to a cartesian object of `D(O)`. -/
def transitionIso (E : Hom.ModuleDerived.{w} (site K)) [IsCartesian K E]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (@ExactFunctor.mapDerivedCategory _ _ _ (stage_hasDerivedCategory K m)
      _ _ _ (stage_hasDerivedCategory K n) (stageMapExact K φ)).obj ((moduleDerivedComponent K m).obj E) ≅
      (moduleDerivedComponent K n).obj E :=
  @asIso _ _ _ _ (moduleDerivedTransition K φ E)
    (instIsIso_moduleDerivedTransition K E φ)

/-- The forward map of `transitionIso` is `moduleDerivedTransition`. -/
theorem transitionIso_hom (E : Hom.ModuleDerived.{w} (site K)) [IsCartesian K E]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso K E φ).hom = moduleDerivedTransition K φ E :=
  sorry

/-- Inverse image `La^* E` of an object of `D(O_C)` is a cartesian object of `D(O)`. -/
theorem toAmbientDerived_isCartesian (E : Hom.ModuleDerived.{w} X) :
    IsCartesian K ((toAmbientDerived K).obj E) :=
  sorry

end ModuleDerived

end RingedSite.Localization.AtSimplicialSR
