/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommAssociatedSections
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
public import Mathlib.CategoryTheory.Sites.Point.Category
public import stacks_project.Chap59.Remark_59_65_3

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.GeometricPoint
noncomputable section
universe u

namespace NoncommAssociatedBaseChange
open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable (f : X ⟶ Y) (xbar : GeometricPoint X)

/-- The small-site fiber comparison uses actual pullback projection/lift, uniformly in coefficients. -/
def siteFiberBaseChangeIso : smallEtalePullback f ⋙ (geometricPointEtalePoint xbar).fiber ≅
    (geometricPointEtalePoint (geometricPointPostcomp xbar f)).fiber :=
  NatIso.ofComponents
    (fun V ↦
      { hom := TypeCat.ofHom fun a ↦ Over.homMk (a.left ≫ pullback.fst V.hom f) sorry
        inv := TypeCat.ofHom fun b ↦ Over.homMk (pullback.lift b.left xbar.hom sorry) sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun _ ↦ sorry)

/-- The comapped point has a small initial neighborhood category, via the image geometric point. -/
instance baseChangeFiber_initiallySmall :
    InitiallySmall (smallEtalePullback f ⋙ (geometricPointEtalePoint xbar).fiber).Elements := sorry

variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback f).op.HasLeftKanExtension P]

/-- The specified sheaf pullback is left adjoint to continuous direct image. -/
instance baseChangePushforward_isRightAdjoint :
    ((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint :=
  (smallEtalePullback_sheafAdjunction f (ModuleCat.{u + 1} Λ)).isRightAdjoint

/-- The comapped module fiber is identified with the image-point fiber through
the actual natural transformation on geometric points. -/
def comapModuleFiberIso :
    ((geometricPointEtalePoint xbar).comapOfMorphismOfSites (smallEtalePullback f)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) ≅ StalkRepresentation.stalk Λ (geometricPointPostcomp xbar f) where
  hom := CategoryTheory.GrothendieckTopology.Point.Hom.sheafFiber
    ⟨(siteFiberBaseChangeIso f xbar).hom⟩
  inv := CategoryTheory.GrothendieckTopology.Point.Hom.sheafFiber
    ⟨(siteFiberBaseChangeIso f xbar).inv⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The module stalk/pullback comparison is the canonical site-point comap
comparison followed by the actual projection/lift map on geometric fibers. -/
def stalkBaseChangeIso :
    (smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
      Y.smallEtaleTopology X.smallEtaleTopology ⋙ StalkRepresentation.stalk Λ xbar ≅
        StalkRepresentation.stalk Λ (geometricPointPostcomp xbar f) :=
  -- Local instance justification (search instability): fix the module-carrier universe for products in the site-point skyscraper adjunction; generic max-universe search is ambiguous.
  letI : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  let e : ((geometricPointEtalePoint xbar).comapOfMorphismOfSites
      (smallEtalePullback f)).sheafFiber (A := ModuleCat.{u + 1} Λ) ≅
      (smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology ⋙ StalkRepresentation.stalk Λ xbar :=
    @CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIsoOfMorphismOfSites.{u, u + 1, u, u + 1, u, u + 1, u + 2}
      Y.Etale X.Etale _ _ Y.smallEtaleTopology X.smallEtaleTopology
      (geometricPointEtalePoint xbar) (smallEtalePullback f) _ _ (ModuleCat.{u + 1} Λ) _
      (inferInstance : HasProducts.{u} (ModuleCat.{u + 1} Λ))
      (baseChangePushforward_isRightAdjoint Λ f)
      (inferInstance : HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ))
  e.symm ≪≫ comapModuleFiberIso Λ f xbar

variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- Pull the published finite associated sheaf back as a finite locally constant module sheaf. -/
def finitePulledSheaf
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))).FullSubcategory) :=
  (finiteTypeLocallyConstantModulePullback f Λ).obj
    ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ
      (geometricPointPostcomp xbar f)).inverse.obj M)

/-- Restrict a finite representation along the geometric fundamental-group map. -/
def finiteRestricted
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))).FullSubcategory) :=
  (etaleFundamentalGroupMap_resFiniteTypeDiscreteModule f Λ xbar).obj M

/-- The finite pullback stalk is mapped to the restricted coefficient by the
actual site-point base-change comparison and published germ counit. -/
def finitePullbackStalkIso
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))).FullSubcategory) :
    (StalkRepresentation.stalk Λ xbar).obj (finitePulledSheaf Λ f xbar M).obj ≅
      (finiteRestricted Λ f xbar M).obj.obj.V :=
  (stalkBaseChangeIso Λ f xbar).app ((associatedSheafFunctor Λ (geometricPointPostcomp xbar f)).obj M) ≪≫
    (ModuleSheafInverse.counitLinearEquiv (geometricPointPostcomp xbar f) Λ M).toModuleIso

/-- Geometric base change intertwines monodromy through the actual projection/lift fiber map. -/
theorem finitePullbackStalkIso_equivariant
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))).FullSubcategory)
    (g : Aut (standardFiniteEtaleFiber xbar)) :
    ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj
        (finitePulledSheaf Λ f xbar M)).obj.obj.ρ g ≫ (finitePullbackStalkIso Λ f xbar M).hom =
      (finitePullbackStalkIso Λ f xbar M).hom ≫ (finiteRestricted Λ f xbar M).obj.obj.ρ g := sorry

/-- The finite representation comparison upgrades the specified linear stalk map equivariantly. -/
def finitePullbackRepIso
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))).FullSubcategory) :
    (finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).obj
        (finitePulledSheaf Λ f xbar M) ≅ finiteRestricted Λ f xbar M :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (Action.mkIso (finitePullbackStalkIso Λ f xbar M) (finitePullbackStalkIso_equivariant Λ f xbar M)))

/-- The finite associated-sheaf base-change map uses the published sheaf unit and
inverse functor applied to the specified equivariant stalk comparison. -/
def finiteBaseChangeIso
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))).FullSubcategory) :
    ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology).obj
      ((associatedSheafFunctor Λ (geometricPointPostcomp xbar f)).obj M) ≅
        (associatedSheafFunctor Λ xbar).obj (finiteRestricted Λ f xbar M) :=
  (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).ι.mapIso
    ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).unitIso.app
        (finitePulledSheaf Λ f xbar M) ≪≫
      (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).inverse.mapIso
        (finitePullbackRepIso Λ f xbar M))

/-- Restriction of all discrete representations along the actual induced map. -/
def restriction : DiscreteModuleCat Λ
      (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f))) ⥤
    DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar)) :=
  discreteModuleRes (etaleFundamentalGroupMap f xbar)

/-- Restriction retains the same finite submodule and restricts its stability proof. -/
def restrictedIndex
    {M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))}
    (S : FiniteSubrepresentation Λ (geometricPointPostcomp xbar f) M) :
    FiniteSubrepresentation Λ xbar ((restriction Λ f xbar).obj M) :=
  ⟨S.val, ⟨fun g m hm ↦ S.property.1 (etaleFundamentalGroupMap f xbar g) m hm, S.property.2⟩⟩

/-- The two finite restrictions agree through the identity linear map on the submodule. -/
def restrictedIndexIso
    {M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))}
    (S : FiniteSubrepresentation Λ (geometricPointPostcomp xbar f) M) :
    finiteRestricted Λ f xbar (finiteObject S) ≅ finiteObject (restrictedIndex Λ f xbar S) :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _) (fun _ ↦ sorry)))

/-- A finite arithmetic stage pulls back to its actual restricted geometric stage. -/
def baseChangeStageIso
    {M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))}
    (S : FiniteSubrepresentation Λ (geometricPointPostcomp xbar f) M) :=
  finiteBaseChangeIso Λ f xbar (finiteObject S) ≪≫
    (associatedSheafFunctor Λ xbar).mapIso (restrictedIndexIso Λ f xbar S)

/-- Pullback preserves the realization colimit through its existing geometric adjunction. -/
instance baseChangePullback_isLeftAdjoint :
    ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
      Y.smallEtaleTopology X.smallEtaleTopology).IsLeftAdjoint :=
  (smallEtalePullback_sheafAdjunction f (ModuleCat.{u + 1} Λ)).isLeftAdjoint

/-- The finite-stage base-change maps followed by the geometric colimit inclusions. -/
def baseChangeCocone
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))) :
    Cocone (diagram M ⋙ (smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
      Y.smallEtaleTopology X.smallEtaleTopology) where
  pt := obj ((restriction Λ f xbar).obj M)
  ι := { app := fun S ↦ (baseChangeStageIso Λ f xbar S).hom ≫
           colimit.ι (diagram ((restriction Λ f xbar).obj M)) (restrictedIndex Λ f xbar S)
         naturality := sorry }

/-- The ambient associated-sheaf base-change map is the colimit of the specified finite maps. -/
def baseChangeMap
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))) :
    ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
      Y.smallEtaleTopology X.smallEtaleTopology).obj (obj M) ⟶
      obj ((restriction Λ f xbar).obj M) :=
  (preservesColimitIso ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
    Y.smallEtaleTopology X.smallEtaleTopology) (diagram M)).hom ≫
      colimit.desc _ (baseChangeCocone Λ f xbar M)

/-- The restricted arithmetic finite stages are cofinal among geometric finite stages. -/
instance baseChangeMap_isIso
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))) :
    IsIso (baseChangeMap Λ f xbar M) := sorry

/-- Base change of the actual ambient realization agrees with restriction of the representation. -/
def baseChangeIso
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))) :=
  @asIso _ _ _ _ (baseChangeMap Λ f xbar M) (baseChangeMap_isIso Λ f xbar M)

/-- The associated-sheaf base-change map retains precisely the canonical stalk comparison. -/
theorem baseChangeMap_stalk
    (M : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))) :
    (StalkRepresentation.stalk Λ xbar).map (baseChangeMap Λ f xbar M) ≫
        stalkComparison ((restriction Λ f xbar).obj M) =
      (stalkBaseChangeIso Λ f xbar).hom.app (obj M) ≫ stalkComparison M := sorry

/-- The geometric colimit comparison is natural in all arithmetic coefficient maps. -/
theorem baseChangeMap_naturality
    {M N : DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f)))}
    (a : M ⟶ N) :
    ((smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology).map (functor.map a) ≫ baseChangeMap Λ f xbar N =
      baseChangeMap Λ f xbar M ≫ functor.map ((restriction Λ f xbar).map a) := sorry

/-- The natural geometric base-change comparison has the explicitly constructed components. -/
def baseChangeNatIso :
    functor (Λ := Λ) (xbar := geometricPointPostcomp xbar f) ⋙
        (smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
          Y.smallEtaleTopology X.smallEtaleTopology ≅
      restriction Λ f xbar ⋙ functor (Λ := Λ) (xbar := xbar) :=
  NatIso.ofComponents (baseChangeIso Λ f xbar) (fun a ↦ baseChangeMap_naturality Λ f xbar a)

end NoncommAssociatedBaseChange
