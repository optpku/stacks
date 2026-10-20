module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Lemma_85_17_1_Cartesian
public import stacks_project.Chap85.Remark_85_16_5_Ringed_variant_Ringed

/-!
# Cartesian modules on a ringed total localization

An `O`-module on `((C / K)_total, O)` is cartesian when every simplex-operator comparison
`f_φ^* F_m ⟶ F_n` is an isomorphism. Inverse and direct image of modules along the ringed
augmentation `a` are `toAmbient.modulePullback` and `toAmbient.modulePushforward`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor Grothendieck
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget
    overSite_ι_isContinuous overSite_ι_isCocontinuous overMap overSitePrecoverage)

variable {X : RingedSite.{u, v, w}}
variable (K : SimplicialObject (FormalCoproduct.{ι} X.carrier))
variable [UnivLE.{max ι u v, w}]
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

/-- Inverse image `a^*` of `O_C`-modules along the ringed augmentation
`a : (Sh((C / K)_total), O) ⟶ (Sh(C), O_C)`. -/
abbrev modulePullback :
    SheafOfModules.{w} X.structureSheaf ⥤ SheafOfModules.{w} (ringSheaf K) :=
  (toAmbient K).modulePullback

/-- `modulePullback` is module pullback along `toAmbient`. -/
theorem modulePullback_eq :
    modulePullback K = (toAmbient K).modulePullback :=
  sorry

/-- Direct image `a_*` of `O`-modules along the ringed augmentation `a`. -/
abbrev modulePushforward :
    SheafOfModules.{w} (ringSheaf K) ⥤ SheafOfModules.{w} X.structureSheaf :=
  (toAmbient K).modulePushforward

/-- `modulePushforward` is module pushforward along `toAmbient`. -/
theorem modulePushforward_eq :
    modulePushforward K = (toAmbient K).modulePushforward :=
  sorry

/-- Because `O = a⁻¹ O_C`, module pullback `a^*` agrees with geometric inverse image
`a⁻¹` of modules along `totalForget`. -/
theorem modulePullback_eq_inverseImage :
    modulePullback K =
      Cocontinuous.moduleInverseImage (totalForget K) X.structureSheaf :=
  sorry

/-- Restriction of an `O`-module on `((C / K)_total, O)` to the degree-`n` site,
i.e. `F_n = g_n^* F`. -/
abbrev moduleComponent (n : SimplexCategory) :
    SheafOfModules.{w} (ringSheaf K) ⥤
      SheafOfModules.{w} (AtSR.ringSheaf (K.obj (op n))) :=
  (stageIncl K n).modulePullback

/-- `moduleComponent n` is module pullback along the stage inclusion `g_n`. -/
theorem moduleComponent_eq (n : SimplexCategory) :
    moduleComponent K n = (stageIncl K n).modulePullback :=
  sorry

/-- Relocalization `u_φ : C / K_n ⥤ C / K_m` is continuous for the inherited topologies. -/
instance diagramMap_isContinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    ((overSiteDiagram K).map φ.op).toFunctor.IsContinuous
      (overTopology X.siteTopology (K.obj (op n)))
      (overTopology X.siteTopology (K.obj (op m))) :=
  sorry

/-- The composite `u_φ ⋙ ι` is continuous, as a composite of continuous stage and fiber
functors. -/
instance overMap_comp_ι_isContinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    (((overSiteDiagram K).map φ.op).toFunctor ⋙
        Grothendieck.ι (overSiteDiagram K) (op m)).IsContinuous
      (overTopology X.siteTopology (K.obj (op n)))
      (overSiteTotalTopology X.siteTopology K) :=
  sorry

/-- Restriction of a type-valued sheaf on `(C / K)_total` to the degree-`n` site. -/
def typeComponent (n : SimplexCategory) :
    Sheaf (overSiteTotalTopology X.siteTopology K) (Type w) ⥤
      Sheaf (overTopology X.siteTopology (K.obj (op n))) (Type w) :=
  (Grothendieck.ι (overSiteDiagram K) (op n)).sheafPushforwardContinuous (Type w)
    (overTopology X.siteTopology (K.obj (op n)))
    (overSiteTotalTopology X.siteTopology K)

/-- `typeComponent n` is continuous sheaf pushforward along the fiber inclusion `ι`. -/
theorem typeComponent_eq (n : SimplexCategory) :
    typeComponent K n =
      (Grothendieck.ι (overSiteDiagram K) (op n)).sheafPushforwardContinuous (Type w)
        (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K) :=
  sorry

/-- Type-valued comparison `(u_φ ⋙ ι_m)⁻¹ G ⟶ ι_n⁻¹ G` obtained from `ιNatTrans`. -/
def typeTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (overSiteTotalTopology X.siteTopology K) (Type w)) :
    ((((overSiteDiagram K).map φ.op).toFunctor ⋙
          Grothendieck.ι (overSiteDiagram K) (op m)).sheafPushforwardContinuous (Type w)
        (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K)).obj G ⟶
      (typeComponent K n).obj G :=
  (@sheafPushforwardContinuousNatTrans _ _ _ _ _ _ (ιNatTrans φ.op) (Type w) _
      (overTopology X.siteTopology (K.obj (op n)))
      (overSiteTotalTopology X.siteTopology K)
      (overSite_ι_isContinuous X.siteTopology K n)
      (overMap_comp_ι_isContinuous K φ)).app G

/-- Geometric inverse image of an `O`-module along the stage inclusion `g_n`. -/
def moduleInverseImageComponent (n : SimplexCategory) :
    SheafOfModules.{w} (ringSheaf K) ⥤
      SheafOfModules.{w}
        ((stageIncl K n).toTopos.ringInverseImage.obj (ringSheaf K)) :=
  (stageIncl K n).toTopos.moduleInverseImage (ringSheaf K)

/-- Cocontinuous inverse image along `ι` is isomorphic to continuous restriction. -/
def stageIncl_cocontinuousContinuousIso (n : SimplexCategory) :
    (Grothendieck.ι (overSiteDiagram K) (op n)).sheafPullbackCocontinuous (Type w)
        (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K) ≅
      typeComponent K n :=
  NatIso.ofComponents
    (fun F ↦
      { hom :=
          CocontinuousPullback.comparisonApp
            (Grothendieck.ι (overSiteDiagram K) (op n))
            (overTopology X.siteTopology (K.obj (op n)))
            (overSiteTotalTopology X.siteTopology K) F
        inv :=
          ((typeComponent K n).map (sheafificationIso F).hom) ≫
            ((Grothendieck.ι (overSiteDiagram K) (op n)).pushforwardContinuousSheafificationCompatibility
                (Type w)
                (overTopology X.siteTopology (K.obj (op n)))
                (overSiteTotalTopology X.siteTopology K)).inv.app F.obj
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Underlying type-valued sheaves identify geometric inverse image along `g_n` with
restriction of the underlying sheaf of `F` along `ι`. -/
def moduleInverseImage_underlyingIso
    (F : SheafOfModules.{w} (ringSheaf K)) (n : SimplexCategory) :
    (Sheaf.InternalModule.ToInternal.underlying
        ((stageIncl K n).toTopos.ringInverseImage.obj (ringSheaf K))).obj
      ((moduleInverseImageComponent K n).obj F) ≅
      (typeComponent K n).obj
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K)).obj F) :=
  ((stageIncl K n).toTopos.moduleInverseImageForgetIso (ringSheaf K)).app F ≪≫
    (stageIncl_cocontinuousContinuousIso K n).app
      ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K)).obj F)

/-- Cocontinuous inverse image along `overMap` is isomorphic to continuous restriction. -/
def stageMap_cocontinuousContinuousIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (overMap (K.map φ.op)).sheafPullbackCocontinuous (Type w)
        (overTopology X.siteTopology (K.obj (op n)))
        (overTopology X.siteTopology (K.obj (op m))) ≅
      (overMap (K.map φ.op)).sheafPushforwardContinuous (Type w)
        (overTopology X.siteTopology (K.obj (op n)))
        (overTopology X.siteTopology (K.obj (op m))) :=
  NatIso.ofComponents
    (fun F ↦
      { hom :=
          CocontinuousPullback.comparisonApp (overMap (K.map φ.op))
            (overTopology X.siteTopology (K.obj (op n)))
            (overTopology X.siteTopology (K.obj (op m))) F
        inv :=
          (((overMap (K.map φ.op)).sheafPushforwardContinuous (Type w)
                (overTopology X.siteTopology (K.obj (op n)))
                (overTopology X.siteTopology (K.obj (op m)))).map
              (sheafificationIso F).hom) ≫
            ((overMap (K.map φ.op)).pushforwardContinuousSheafificationCompatibility (Type w)
                (overTopology X.siteTopology (K.obj (op n)))
                (overTopology X.siteTopology (K.obj (op m)))).inv.app F.obj
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Restriction along `u_φ ⋙ ι_m` identifies with the composite of fiber restriction
and stage restriction. -/
def typeComponentCompIso {m n : SimplexCategory} (φ : m ⟶ n)
    (hι : (Grothendieck.ι (overSiteDiagram K) (op m)).IsContinuous
      (overTopology X.siteTopology (K.obj (op m)))
      (overSiteTotalTopology X.siteTopology K)) :
    typeComponent K m ⋙
      ((overSiteDiagram K).map φ.op).toFunctor.sheafPushforwardContinuous (Type w)
        (overTopology X.siteTopology (K.obj (op n)))
        (overTopology X.siteTopology (K.obj (op m))) ≅
      (((overSiteDiagram K).map φ.op).toFunctor ⋙
          Grothendieck.ι (overSiteDiagram K) (op m)).sheafPushforwardContinuous (Type w)
        (overTopology X.siteTopology (K.obj (op n)))
        (overSiteTotalTopology X.siteTopology K) :=
  @sheafPushforwardContinuousComp _ _ _ _ _ _
    ((overSiteDiagram K).map φ.op).toFunctor
    (Grothendieck.ι (overSiteDiagram K) (op m)) (Type w) _
    (overTopology X.siteTopology (K.obj (op n)))
    (overTopology X.siteTopology (K.obj (op m)))
    (overSiteTotalTopology X.siteTopology K) _ hι

/-- The forward map of `typeComponentCompIso` is invertible. -/
theorem typeComponentCompIso_hom_inv_id {m n : SimplexCategory} (φ : m ⟶ n)
    (hι : (Grothendieck.ι (overSiteDiagram K) (op m)).IsContinuous
      (overTopology X.siteTopology (K.obj (op m)))
      (overSiteTotalTopology X.siteTopology K)) :
    (typeComponentCompIso K φ hι).hom ≫ (typeComponentCompIso K φ hι).inv = 𝟙 _ :=
  sorry

/-- Direct-image form of the type-valued comparison: `F_m ⟶ (f_φ)_* F_n`. -/
def typeTransitionDirect {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (overSiteTotalTopology X.siteTopology K) (Type w)) :
    (typeComponent K m).obj G ⟶
      ((overMap (K.map φ.op)).sheafPushforwardCocontinuous (Type w)
        (overTopology X.siteTopology (K.obj (op n)))
        (overTopology X.siteTopology (K.obj (op m)))).obj
        ((typeComponent K n).obj G) :=
  ((overMap (K.map φ.op)).sheafPullbackCocontinuousAdjunction
      (overTopology X.siteTopology (K.obj (op n)))
      (overTopology X.siteTopology (K.obj (op m)))).homEquiv
    ((typeComponent K m).obj G) ((typeComponent K n).obj G)
    ((stageMap_cocontinuousContinuousIso K φ).hom.app ((typeComponent K m).obj G) ≫
      (typeComponentCompIso K φ (overSite_ι_isContinuous X.siteTopology K m)).hom.app G ≫
      typeTransition K φ G)

/-- The adjunction mate of `typeTransitionDirect` recovers the composite inverse-image
comparison of `typeTransition`. -/
theorem typeTransitionDirect_homEquiv {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (overSiteTotalTopology X.siteTopology K) (Type w)) :
    ((overMap (K.map φ.op)).sheafPullbackCocontinuousAdjunction
        (overTopology X.siteTopology (K.obj (op n)))
        (overTopology X.siteTopology (K.obj (op m)))).homEquiv
      ((typeComponent K m).obj G) ((typeComponent K n).obj G)
      ((stageMap_cocontinuousContinuousIso K φ).hom.app ((typeComponent K m).obj G) ≫
        (typeComponentCompIso K φ (overSite_ι_isContinuous X.siteTopology K m)).hom.app G ≫
        typeTransition K φ G) =
    typeTransitionDirect K φ G :=
  sorry

/-- Restriction of scalars does not change the underlying type-valued sheaf. -/
def restrictScalars_underlyingIso (n : SimplexCategory)
    {R R' : Sheaf (overTopology X.siteTopology (K.obj (op n))) RingCat.{w}} (α : R ⟶ R') :
    SheafOfModules.restrictScalars.{w} α ⋙
        Sheaf.InternalModule.ToInternal.underlying R ≅
      Sheaf.InternalModule.ToInternal.underlying R' :=
  Iso.refl _

/-- Restriction of scalars is the identity on underlying type-valued sheaves. -/
theorem restrictScalars_underlyingIso_hom (n : SimplexCategory)
    {R R' : Sheaf (overTopology X.siteTopology (K.obj (op n))) RingCat.{w}} (α : R ⟶ R') :
    (restrictScalars_underlyingIso K n α).hom = 𝟙 _ :=
  sorry

/-- Underlying type-valued comparison of `moduleTransitionDirect`, as a map of sheaves of
types on `C / K_m`. -/
def moduleTransitionDirect_underlying {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (ringSheaf K)) :
    (Sheaf.InternalModule.ToInternal.underlying
        ((stageIncl K m).toTopos.ringInverseImage.obj (ringSheaf K))).obj
      ((moduleInverseImageComponent K m).obj F) ⟶
    (Sheaf.InternalModule.ToInternal.underlying
        ((stageIncl K m).toTopos.ringInverseImage.obj (ringSheaf K))).obj
      ((SheafOfModules.restrictScalars.{w} (stageIncl K m).structureMap).obj
        ((stageMap K φ).modulePushforward.obj ((moduleComponent K n).obj F))) :=
  (moduleInverseImage_underlyingIso K F m).hom ≫
    typeTransitionDirect K φ
      ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K)).obj F) ≫
      ((overMap (K.map φ.op)).sheafPushforwardCocontinuous (Type w)
          (overTopology X.siteTopology (K.obj (op n)))
          (overTopology X.siteTopology (K.obj (op m)))).map
        ((moduleInverseImage_underlyingIso K F n).inv ≫
          (Sheaf.InternalModule.ToInternal.underlying
              ((stageIncl K n).toTopos.ringInverseImage.obj (ringSheaf K))).map
            ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction
                (stageIncl K n).structureMap).unit.app
              ((moduleInverseImageComponent K n).obj F))) ≫
      (ToposHom.ModulePushforward.forgetIso (stageMap K φ)).inv.app
        ((moduleComponent K n).obj F) ≫
      (restrictScalars_underlyingIso K m (stageIncl K m).structureMap).inv.app
        ((stageMap K φ).modulePushforward.obj ((moduleComponent K n).obj F))

/-- Geometric module comparison `g_m⁻¹ F ⟶ (f_φ)_* F_n` over the inverse-image ring of `g_m`. -/
def moduleTransitionDirect_geom {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (ringSheaf K)) :
    (moduleInverseImageComponent K m).obj F ⟶
      (SheafOfModules.restrictScalars.{w} (stageIncl K m).structureMap).obj
        ((stageMap K φ).modulePushforward.obj ((moduleComponent K n).obj F)) :=
  Sheaf.InternalModule.homOfUnderlying
    ((stageIncl K m).toTopos.ringInverseImage.obj (ringSheaf K))
    (moduleTransitionDirect_underlying K φ F) sorry sorry

/-- Direct-image comparison `F_m ⟶ (f_φ)_* F_n` of `O`-modules, obtained by extending scalars
along the stage structure map and applying the scalar-extension counit. -/
def moduleTransitionDirect {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (ringSheaf K)) :
    (moduleComponent K m).obj F ⟶
      (stageMap K φ).modulePushforward.obj ((moduleComponent K n).obj F) :=
  (SheafOfModules.ChangeOfRings.extendScalars (stageIncl K m).structureMap).map
      (moduleTransitionDirect_geom K φ F) ≫
    (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
        (stageIncl K m).structureMap).counit.app
      ((stageMap K φ).modulePushforward.obj ((moduleComponent K n).obj F))

/-- The source comparison `F(φ) : f_φ^* F_m ⟶ F_n` of `O`-modules. -/
def moduleTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (ringSheaf K)) :
    (stageMap K φ).modulePullback.obj ((moduleComponent K m).obj F) ⟶
      (moduleComponent K n).obj F :=
  ((stageMap K φ).moduleAdjunction.homEquiv
      ((moduleComponent K m).obj F) ((moduleComponent K n).obj F)).symm
    (moduleTransitionDirect K φ F)

/-- The adjunction mate of `moduleTransition` is `moduleTransitionDirect`. -/
theorem moduleTransition_homEquiv {m n : SimplexCategory} (φ : m ⟶ n)
    (F : SheafOfModules.{w} (ringSheaf K)) :
    ((stageMap K φ).moduleAdjunction.homEquiv
        ((moduleComponent K m).obj F) ((moduleComponent K n).obj F))
      (moduleTransition K φ F) =
    moduleTransitionDirect K φ F :=
  sorry

/-- An `O`-module on `((C / K)_total, O)` is cartesian when the simplex-operator comparison
`F(φ) : f_φ^* F_m ⟶ F_n` is an isomorphism for every simplex operator `φ`. -/
class IsCartesian (F : SheafOfModules.{w} (ringSheaf K)) : Prop where
  /-- Every simplex-operator comparison `F(φ)` is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (moduleTransition K φ F)

/-- Cartesianness of an `O`-module is equivalent to every simplex-operator comparison
`F(φ)` being an isomorphism. -/
theorem isCartesian_iff (F : SheafOfModules.{w} (ringSheaf K)) :
    IsCartesian K F ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (moduleTransition K φ F) :=
  sorry

/-- Cartesianness of an `O`-module is equivalent to cartesianness of its underlying
type-valued sheaf on `(C / K)_total`. -/
theorem isCartesian_iff_underlying (F : SheafOfModules.{w} (ringSheaf K)) :
    IsCartesian K F ↔
      Grothendieck.Sheaf.IsCartesian (overSiteDiagram K)
        (overSitePrecoverage X.siteTopology K) (Type w)
        ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf K)).obj F) :=
  sorry

/-- An `O`-module whose every simplex-operator comparison `F(φ)` is an isomorphism is
cartesian. -/
instance instIsCartesian_of_isIso (F : SheafOfModules.{w} (ringSheaf K))
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (moduleTransition K φ F)] :
    IsCartesian K F where
  isIso_transition := h

/-- Every simplex-operator module comparison of a cartesian `O`-module is an isomorphism. -/
instance instIsIso_moduleTransition (F : SheafOfModules.{w} (ringSheaf K))
    [IsCartesian K F] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (moduleTransition K φ F) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `F(φ) : f_φ^* F_m ≅ F_n` attached to a cartesian `O`-module. -/
def transitionIso (F : SheafOfModules.{w} (ringSheaf K)) [IsCartesian K F]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageMap K φ).modulePullback.obj ((moduleComponent K m).obj F) ≅
      (moduleComponent K n).obj F :=
  asIso (moduleTransition K φ F)

/-- The forward map of `transitionIso` is `moduleTransition`. -/
theorem transitionIso_hom (F : SheafOfModules.{w} (ringSheaf K)) [IsCartesian K F]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso K F φ).hom = moduleTransition K φ F :=
  sorry

/-- The object property of being a cartesian `O`-module on `((C / K)_total, O)`. -/
abbrev cartesianProperty : ObjectProperty (SheafOfModules.{w} (ringSheaf K)) :=
  fun F ↦ IsCartesian K F

/-- The category of cartesian `O`-modules on `((C / K)_total, O)`. -/
abbrev Cartesian := (cartesianProperty K).FullSubcategory

/-- The underlying module of an object of `Cartesian` is cartesian. -/
theorem cartesian_isCartesian (F : Cartesian K) : IsCartesian K F.obj :=
  sorry

/-- Inverse image `a^* F` of an `O_C`-module is a cartesian `O`-module. -/
instance modulePullback_isCartesian (F : SheafOfModules.{w} X.structureSheaf) :
    IsCartesian K ((modulePullback K).obj F) :=
  sorry

end RingedSite.Localization.AtSimplicialSR
