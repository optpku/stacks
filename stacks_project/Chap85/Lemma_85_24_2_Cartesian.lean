/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute
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
instance ambient_hasDerivedCategory : HasDerivedCategory (ModuleCat.{w} X) :=
  moduleCat_hasDerivedCategory X

/-- Chosen derived-category structure on modules over `((C / K)_total, O)`. -/
instance site_hasDerivedCategory : HasDerivedCategory (ModuleCat.{w} (site K)) :=
  moduleCat_hasDerivedCategory (site K)

/-- Chosen derived-category structure on modules over a degree-`n` localization `(C / K_n, O_n)`. -/
instance stage_hasDerivedCategory (n : SimplexCategory) :
    HasDerivedCategory (ModuleCat.{w} (AtSR.site (K.obj (op n)))) :=
  moduleCat_hasDerivedCategory (AtSR.site (K.obj (op n)))

/-- Module pullback along `g_n` is additive. -/
instance stageIncl_modulePullback_additive (n : SimplexCategory) :
    ((stageIncl K n).modulePullback).Additive :=
  sorry

/-- Module pullback along `g_n` preserves finite limits, by flatness of `g_n`. -/
instance stageIncl_modulePullback_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (stageIncl K n).modulePullback :=
  (ToposHom.IsFlat.pullback_exact (stageIncl K n)).1

/-- Module pullback along `g_n` preserves finite colimits, by flatness of `g_n`. -/
instance stageIncl_modulePullback_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (stageIncl K n).modulePullback :=
  (ToposHom.IsFlat.pullback_exact (stageIncl K n)).2

/-- Module pullback along `f_φ` is additive. -/
instance stageMap_modulePullback_additive {m n : SimplexCategory} (φ : m ⟶ n) :
    ((stageMap K φ).modulePullback).Additive :=
  sorry

/-- Module pullback along `f_φ` preserves finite limits, by flatness of `f_φ`. -/
instance stageMap_modulePullback_preservesFiniteLimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteLimits (stageMap K φ).modulePullback :=
  (ToposHom.IsFlat.pullback_exact (stageMap K φ)).1

/-- Module pullback along `f_φ` preserves finite colimits, by flatness of `f_φ`. -/
instance stageMap_modulePullback_preservesFiniteColimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteColimits (stageMap K φ).modulePullback :=
  (ToposHom.IsFlat.pullback_exact (stageMap K φ)).2

/-- Module pullback along the augmentation `a` is additive. -/
instance toAmbient_modulePullback_additive : ((toAmbient K).modulePullback).Additive :=
  sorry

/-- Module pullback along `a` preserves finite limits, by flatness of `a`. -/
instance toAmbient_modulePullback_preservesFiniteLimits :
    PreservesFiniteLimits (toAmbient K).modulePullback :=
  (ToposHom.IsFlat.pullback_exact (toAmbient K)).1

/-- Module pullback along `a` preserves finite colimits, by flatness of `a`. -/
instance toAmbient_modulePullback_preservesFiniteColimits :
    PreservesFiniteColimits (toAmbient K).modulePullback :=
  (ToposHom.IsFlat.pullback_exact (toAmbient K)).2

/-- The bundled exact functor `g_n^*` of `O`-modules. -/
abbrev stageInclExact (n : SimplexCategory) :
    ModuleCat.{w} (site K) ⥤ₑ ModuleCat.{w} (AtSR.site (K.obj (op n))) :=
  ToposHom.IsFlat.exactPullback (stageIncl K n)

/-- The bundled exact functor `f_φ^*` of `O`-modules. -/
abbrev stageMapExact {m n : SimplexCategory} (φ : m ⟶ n) :
    ModuleCat.{w} (AtSR.site (K.obj (op m))) ⥤ₑ ModuleCat.{w} (AtSR.site (K.obj (op n))) :=
  ToposHom.IsFlat.exactPullback (stageMap K φ)

/-- The bundled exact functor `a^*` of `O_C`-modules. -/
abbrev toAmbientExact :
    ModuleCat.{w} X ⥤ₑ ModuleCat.{w} (site K) :=
  ToposHom.IsFlat.exactPullback (toAmbient K)

/-- Reconstruct a module morphism from an underlying type-valued sheaf map. -/
def moduleHomOfUnderlying.{uY, vY} {C : Type uY} [Category.{vY} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})] {R : Sheaf J RingCat.{w}}
    {M N : SheafOfModules.{w} R}
    (α : (Sheaf.InternalModule.ToInternal.underlying R).obj M ⟶
      (Sheaf.InternalModule.ToInternal.underlying R).obj N) :
    M ⟶ N :=
  Sheaf.InternalModule.homOfUnderlying R α sorry sorry

/-- Reconstruct a module morphism on a ringed site from an underlying type-valued sheaf map. -/
def moduleHomOfUnderlyingOn.{uY, vY} {Y : RingedSite.{uY, vY, w}}
    [Y.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    {M N : SheafOfModules.{w} Y.structureSheaf}
    (α : (Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).obj M ⟶
      (Sheaf.InternalModule.ToInternal.underlying Y.structureSheaf).obj N) :
    M ⟶ N :=
  moduleHomOfUnderlying α

/-- Lift an underlying-sheaf isomorphism of module functors to a module-functor isomorphism. -/
def moduleNatIsoOfUnderlying.{uY, vY, uZ, vZ} {C : Type uY} [Category.{vY} C] {J : GrothendieckTopology C}
    {D : Type uZ} [Category.{vZ} D] {K : GrothendieckTopology D}
    [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [K.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    {R : Sheaf J RingCat.{w}} {S : Sheaf K RingCat.{w}}
    {F G : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S}
    (e : F ⋙ Sheaf.InternalModule.ToInternal.underlying S ≅
      G ⋙ Sheaf.InternalModule.ToInternal.underlying S) :
    F ≅ G :=
  NatIso.ofComponents
    (fun M ↦
      { hom := moduleHomOfUnderlying (e.hom.app M)
        inv := moduleHomOfUnderlying (e.inv.app M)
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Lift an underlying-sheaf isomorphism of module functors on ringed sites. -/
def moduleNatIsoOfUnderlyingOn.{uY, vY, uZ, vZ} {Y : RingedSite.{uY, vY, w}}
    {Z : RingedSite.{uZ, vZ, w}}
    [Y.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [Z.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    {F G : SheafOfModules.{w} Y.structureSheaf ⥤ SheafOfModules.{w} Z.structureSheaf}
    (e : F ⋙ Sheaf.InternalModule.ToInternal.underlying Z.structureSheaf ≅
      G ⋙ Sheaf.InternalModule.ToInternal.underlying Z.structureSheaf) :
    F ≅ G :=
  moduleNatIsoOfUnderlying (R := Y.structureSheaf) (S := Z.structureSheaf) e

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
instance stageForget_isContinuous (n : SimplexCategory) :
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

/-- The scalar-extension unit of `a` is an isomorphism. -/
instance toAmbient_modulePullback_scalarUnit_isIso
    (M : SheafOfModules.{w} X.structureSheaf) :
    IsIso (toAmbient_modulePullback_scalarUnit K M) :=
  sorry

/-- Underlying type-valued sheaves identify `a^*` with continuous inverse image along
`totalForget`. -/
def toAmbient_modulePullback_underlyingIso (M : SheafOfModules.{w} X.structureSheaf) :
    (Sheaf.InternalModule.ToInternal.underlying (site K).structureSheaf).obj
        ((toAmbient K).modulePullback.obj M) ≅
      ((totalForget K).sheafPushforwardContinuous (Type w)
          (overSiteTotalTopology X.siteTopology K) X.siteTopology).obj
        ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M) :=
  toAmbient_modulePullback_restrictScalars_underlyingIso K M ≪≫
    (asIso
      ((Sheaf.InternalModule.ToInternal.underlying
          ((toAmbient K).toTopos.ringInverseImage.obj X.structureSheaf)).map
        (toAmbient_modulePullback_scalarUnit K M))).symm ≪≫
    ((toAmbient K).toTopos.moduleInverseImageForgetIso X.structureSheaf).app M ≪≫
      (toAmbient_cocontinuousContinuousIso K).app
        ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M)

/-- Underlying type-valued sheaves of geometric inverse image along `totalForget`. -/
def toAmbient_moduleInverseImage_underlyingIso (M : SheafOfModules.{w} X.structureSheaf) :
    (Sheaf.InternalModule.ToInternal.underlying (site K).structureSheaf).obj
        ((Cocontinuous.moduleInverseImage (totalForget K) X.structureSheaf).obj M) ≅
      ((totalForget K).sheafPushforwardContinuous (Type w)
          (overSiteTotalTopology X.siteTopology K) X.siteTopology).obj
        ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M) :=
  (fullyFaithfulSheafToPresheaf (site K).siteTopology (Type w)).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry)

/-- Module pullback along `a` identifies with geometric inverse image along `totalForget`. -/
def toAmbient_modulePullbackIso :
    (toAmbient K).modulePullback ≅
      Cocontinuous.moduleInverseImage (totalForget K) X.structureSheaf :=
  moduleNatIsoOfUnderlying
    (NatIso.ofComponents
      (fun M ↦
        toAmbient_modulePullback_underlyingIso K M ≪≫
          (toAmbient_moduleInverseImage_underlyingIso K M).symm)
      sorry)

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

/-- The scalar-extension unit of `g_n` is an isomorphism. -/
instance stageIncl_modulePullback_scalarUnit_isIso (n : SimplexCategory)
    (M : SheafOfModules.{w} (ringSheaf K)) :
    IsIso (stageIncl_modulePullback_scalarUnit K n M) :=
  sorry

/-- Underlying type-valued sheaves identify `g_n^*` with continuous restriction along `ι`. -/
def stageIncl_modulePullback_underlyingIso (n : SimplexCategory)
    (M : SheafOfModules.{w} (ringSheaf K)) :
    (Sheaf.InternalModule.ToInternal.underlying (AtSR.ringSheaf (K.obj (op n)))).obj
        ((stageIncl K n).modulePullback.obj M) ≅
      (typeComponent K n).obj
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K)).obj M) :=
  stageIncl_modulePullback_restrictScalars_underlyingIso K n M ≪≫
    (asIso
      ((Sheaf.InternalModule.ToInternal.underlying
          ((stageIncl K n).toTopos.ringInverseImage.obj (ringSheaf K))).map
        (stageIncl_modulePullback_scalarUnit K n M))).symm ≪≫
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

/-- Sequential pullback along `a` then `g_n` identifies with inverse image along
the degree-`n` localization functor `C / K_n ⥤ C`. -/
def toAmbient_comp_stageInclIso (n : SimplexCategory) :
    (toAmbient K).modulePullback ⋙ (stageIncl K n).modulePullback ≅
      Cocontinuous.moduleInverseImage
        (SemiRepresentableFamily.forget (K.obj (op n))) X.structureSheaf :=
  moduleNatIsoOfUnderlying
    (NatIso.ofComponents
      (fun M ↦
        stageIncl_modulePullback_underlyingIso K n ((toAmbient K).modulePullback.obj M) ≪≫
          (typeComponent K n).mapIso (toAmbient_modulePullback_underlyingIso K M) ≪≫
            (fiberComp_sheafPushforwardIso K n).app
              ((Sheaf.InternalModule.ToInternal.underlying X.structureSheaf).obj M) ≪≫
              (stageForget_moduleInverseImage_underlyingIso K n M).symm)
      sorry)

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

/-- The scalar-extension unit of `f_φ` is an isomorphism. -/
instance stageMap_modulePullback_scalarUnit_isIso {m n : SimplexCategory} (φ : m ⟶ n)
    (M : SheafOfModules.{w} (AtSR.ringSheaf (K.obj (op m)))) :
    IsIso (stageMap_modulePullback_scalarUnit K φ M) :=
  sorry

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
    (asIso
      ((Sheaf.InternalModule.ToInternal.underlying
          ((stageMap K φ).toTopos.ringInverseImage.obj (AtSR.ringSheaf (K.obj (op m))))).map
        (stageMap_modulePullback_scalarUnit K φ M))).symm ≪≫
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

/-- Module pullback along `f_φ` identifies with the explicit SR-morphism inverse image. -/
def stageMap_mapModulePullbackIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageMap K φ).modulePullback ≅ AtSR.mapModulePullback (K.map φ.op) :=
  moduleNatIsoOfUnderlying
    (NatIso.ofComponents
      (fun M ↦
        stageMap_modulePullback_underlyingIso K φ M ≪≫
          (mapModulePullback_underlyingIso K φ M).symm)
      sorry)

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
  (stageInclExact K n).mapDerivedCategory

/-- `moduleDerivedComponent n` is the exact derived functor of module pullback along `g_n`. -/
theorem moduleDerivedComponent_eq (n : SimplexCategory) :
    moduleDerivedComponent K n = (stageInclExact K n).mapDerivedCategory :=
  rfl

/-- Derived inverse image `La^*` along the ringed augmentation `a`. -/
abbrev toAmbientDerived :
    Hom.ModuleDerived.{w} X ⥤ Hom.ModuleDerived.{w} (site K) :=
  (toAmbientExact K).mapDerivedCategory

/-- `toAmbientDerived` is the exact derived functor of module pullback along `a`. -/
theorem toAmbientDerived_eq :
    toAmbientDerived K = (toAmbientExact K).mapDerivedCategory :=
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
    (stageMapExact K φ).mapDerivedCategory.obj ((moduleDerivedComponent K m).obj E) ⟶
      (moduleDerivedComponent K n).obj E :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (stageInclExact K m) (stageMapExact K φ)).inv.app E ≫
    (ExactFunctor.MapDerivedCategory.map (moduleTransitionExact K φ)).app E

/-- `moduleDerivedTransition` is the derived functor of `moduleTransitionNatTrans` after the
exact-functor composition comparison. -/
theorem moduleDerivedTransition_eq {m n : SimplexCategory} (φ : m ⟶ n)
    (E : Hom.ModuleDerived.{w} (site K)) :
    moduleDerivedTransition K φ E =
      (ExactFunctor.MapDerivedCategory.compFunctorIso
          (stageInclExact K m) (stageMapExact K φ)).inv.app E ≫
        (ExactFunctor.MapDerivedCategory.map (moduleTransitionExact K φ)).app E :=
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
instance instIsCartesian_of_isIso (E : Hom.ModuleDerived.{w} (site K))
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (moduleDerivedTransition K φ E)] :
    IsCartesian K E where
  isIso_transition := h

/-- Every simplex-operator derived comparison of a cartesian object of `D(O)` is an isomorphism. -/
instance instIsIso_moduleDerivedTransition (E : Hom.ModuleDerived.{w} (site K))
    [IsCartesian K E] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (moduleDerivedTransition K φ E) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `L(f_φ)^* E_m ≅ E_n` attached to a cartesian object of `D(O)`. -/
def transitionIso (E : Hom.ModuleDerived.{w} (site K)) [IsCartesian K E]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageMapExact K φ).mapDerivedCategory.obj ((moduleDerivedComponent K m).obj E) ≅
      (moduleDerivedComponent K n).obj E :=
  asIso (moduleDerivedTransition K φ E)

/-- The forward map of `transitionIso` is `moduleDerivedTransition`. -/
theorem transitionIso_hom (E : Hom.ModuleDerived.{w} (site K)) [IsCartesian K E]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso K E φ).hom = moduleDerivedTransition K φ E :=
  sorry

/-- Inverse image `La^* E` of an object of `D(O_C)` is a cartesian object of `D(O)`. -/
instance toAmbientDerived_isCartesian (E : Hom.ModuleDerived.{w} X) :
    IsCartesian K ((toAmbientDerived K).obj E) :=
  sorry

end ModuleDerived

end RingedSite.Localization.AtSimplicialSR
